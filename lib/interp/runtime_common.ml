open Common
open Evaluation_ir

module VarMap = Map.Make(Var)
module RuntimeMap = Map.Make(RuntimeName)

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

(* A runtime value, i.e., a value that results from evaluation.
   This includes closures (that capture their environment) and explicitly
   doesn't include variables (as all runtime values will be closed).
*)
module RuntimeValue = struct
  type value_env = t VarMap.t
  and t =
    | Atom of atom_name
    | Constant of constant
    | Primitive of primitive_name
    | Name of RuntimeName.t
    | Tuple of t list
    | Inject of (string * t list)
    | Closure of {
        lambda: lambda;
        value_env: value_env;
      }
    (* An unresolved reference to a top-level declaration. *)
    | Declaration of Var.t

  let rec of_ir value_env value =
    match value with
    | Evaluation_ir.Atom a -> Atom a
    | Evaluation_ir.Constant c -> Constant c
    | Evaluation_ir.Primitive p -> Primitive p
    | Evaluation_ir.Name n -> Name n
    | Evaluation_ir.Tuple vs -> Tuple (List.map (of_ir value_env) vs)
    | Evaluation_ir.Inject (s, vs) -> Inject (s, List.map (of_ir value_env) vs)
    | Evaluation_ir.Lam lambda ->
      Closure { lambda; value_env }
    | Evaluation_ir.Variable v ->
      begin
      match VarMap.find_opt v value_env with
        | Some irv -> irv
        | None ->
          runtime_error
            (Format.asprintf "Unbound variable during IR conversion: %a" Var.pp v)
      end

  let rec to_ir runtime_value =
    match runtime_value with
    | Atom a -> Evaluation_ir.Atom a
    | Constant c -> Evaluation_ir.Constant c
    | Primitive p -> Evaluation_ir.Primitive p
    | Name n -> Evaluation_ir.Name n
    | Tuple vs -> Evaluation_ir.Tuple (List.map to_ir vs)
    | Inject (s, vs) -> Evaluation_ir.Inject (s, List.map to_ir vs)
    | Closure { lambda; value_env = _ } -> Evaluation_ir.Lam lambda
    | Declaration var -> Evaluation_ir.Variable var

  let pp ppf runtime_value =
    Evaluation_ir.pp_value ppf (to_ir runtime_value)
end

type value_env = RuntimeValue.value_env

type runtime_message = (message_tag * RuntimeValue.t list)

(* Only closures and tuples need to be reference counted (data constructors
   are not yet representable as runtime values). *)
let should_ref_count =
  let open RuntimeValue in
  function
    | Closure _ | Tuple _ | Inject _ -> true
    | _ -> false


let rec find_empty_guard guards =
  match guards with
  (* Shouldn't happen in a well-typed program -- must always have an empty guard
     if there's the possibility that a mailbox will be empty *)
  | [] -> runtime_error "No messages available but no 'empty' guard."
  | guard :: rest ->
    begin
      match guard with
      | Empty (mailbox_binder, cont) -> (mailbox_binder, cont)
      | _ -> find_empty_guard rest
    end

(* Finds the first matching guard for a given mailbox. Returns None if no messages match. *)
let rec find_first_matching_message tags mailbox =
  let remove_first_tagged_message tag messages =
    let rec aux prefix = function
      | [] -> None
      | ((msg_tag, _) as msg) :: rest ->
        if String.equal msg_tag tag then
          Some (msg, List.rev_append prefix rest)
        else
          aux (msg :: prefix) rest
    in
    aux [] messages
  in
  match tags with
    (* No more guards to try; nothing in mailbox matches *)
    | [] -> None
    | tag :: rest ->
      begin
        match remove_first_tagged_message tag mailbox with
          (* Mailbox doesn't contain any message for guards; continue *)
          | None -> find_first_matching_message rest mailbox
          (* Mailbox contains message for guard; return payloads and remaining messages *)
          | Some (msg, remaining_messages) -> Some (msg, remaining_messages)
      end

(* Find guard for a given tag. *)
let rec find_receive_guard tag guards =
  match guards with
  | [] -> runtime_error
      (Format.asprintf "No receive guard available for message tag %s. This should not happen." tag)
  | guard :: rest ->
    begin
      match guard with
      | Receive recv_guard when recv_guard.tag = tag -> recv_guard
      | _ -> find_receive_guard tag rest 
    end