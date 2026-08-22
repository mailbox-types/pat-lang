open Common
open Common_types
open Evaluation_ir

module VarMap = Map.Make(Var)
module RuntimeNameMap = Map.Make(RuntimeName)

let count_names names =
  List.fold_left
    (fun acc n -> RuntimeNameMap.update n (function Some c -> Some (c + 1) | None -> Some 1) acc)
    RuntimeNameMap.empty names
  |> RuntimeNameMap.bindings

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
    | Declaration of Var.t

  let resolve_var value_env v =
    match VarMap.find_opt v value_env with
      | Some irv -> irv
      | None ->
        runtime_error
          (Format.asprintf "Unbound variable during IR conversion: %a" Var.pp v)

  let of_ir value_env value =
    match value with
    | Evaluation_ir.Atom a -> Atom a
    | Evaluation_ir.Constant c -> Constant c
    | Evaluation_ir.Primitive p -> Primitive p
    | Evaluation_ir.Name n -> Name n
    | Evaluation_ir.Tuple vs -> Tuple (List.map (resolve_var value_env) vs)
    | Evaluation_ir.Inject (s, vs) -> Inject (s, List.map (resolve_var value_env) vs)
    | Evaluation_ir.Lam lambda ->
      Closure { lambda; value_env }
    | Evaluation_ir.Variable v -> resolve_var value_env v

  let rec pp ppf runtime_value =
    match runtime_value with
    | Atom a -> Format.pp_print_string ppf (":" ^ a)
    | Constant c -> Constant.pp ppf c
    | Primitive p -> Format.pp_print_string ppf p
    | Name n -> RuntimeName.pp ppf n
    | Tuple ts -> Format.fprintf ppf "%a" (Util.Utility.pp_print_comma_list pp) ts
    | Inject (s, ts) -> Format.fprintf ppf "%s(%a)" s (Util.Utility.pp_print_comma_list pp) ts
    | Closure { lambda; _ } -> Format.fprintf ppf "fun(%a) { ... }" (Util.Utility.pp_print_comma_list Binder.pp) lambda.parameters
    | Declaration var -> Var.pp ppf var
end

type value_env = RuntimeValue.value_env

type runtime_message = (message_tag * RuntimeValue.t list)

(* All runtime names reachable from a value, descending through any nesting of
   Tuple/Inject (e.g. a mailbox stored inside a variant stored inside a tuple). *)
let rec runtime_names_in_runtime_value value =
  let open RuntimeValue in
  match value with
  | Name runtime_name -> [runtime_name]
  | Tuple vs
  | Inject (_, vs) -> List.concat_map runtime_names_in_runtime_value vs
  | Atom _ | Constant _ | Primitive _ | Closure _ | Declaration _ -> []

(* When returning from a frame, any value for which this predicate returns true
    will be tracked & RCed by the runtime *)
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