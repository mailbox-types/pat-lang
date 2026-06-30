open Common
open Ir

module VarMap = Map.Make(Var)
module RuntimeMap = Map.Make(RuntimeName)

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

module RuntimeValue = struct
  type value_env = t VarMap.t
  and t =
    | Atom of atom_name
    | Constant of constant
    | Primitive of primitive_name
    | Name of RuntimeName.t
    | Tuple of t list
    | Nil
    | Cons of t * t
    | Inl of t
    | Inr of t
    | Closure of {
        lambda: lambda;
        value_env: value_env;
      }

  let rec of_ir value_env value =
    match WithIrMetadata.node value with
    | Ir.VAnnotate (v, _) -> of_ir value_env v
    | Ir.Atom a -> Atom a
    | Ir.Constant c -> Constant c
    | Ir.Primitive p -> Primitive p
    | Ir.Name n -> Name n
    | Ir.Tuple vs -> Tuple (List.map (of_ir value_env) vs)
    | Ir.Nil -> Nil
    | Ir.Cons (v1, v2) -> Cons (of_ir value_env v1, of_ir value_env v2)
    | Ir.Inl v -> Inl (of_ir value_env v)
    | Ir.Inr v -> Inr (of_ir value_env v)
    | Ir.Lam lambda ->
      Closure { lambda; value_env }
    | Ir.Variable (v, _) ->
      begin
      match VarMap.find_opt v value_env with
        | Some irv -> irv
        | None ->
          runtime_error
            (Format.asprintf "Unbound variable during IR conversion: %a" Var.pp v)
      end

  let rec to_ir runtime_value =
    match runtime_value with
    | Atom a ->
      WithIrMetadata.make (Ir.Atom a)
    | Constant c ->
      WithIrMetadata.make (Ir.Constant c)
    | Primitive p ->
      WithIrMetadata.make (Ir.Primitive p)
    | Name n ->
      WithIrMetadata.make (Ir.Name n)
    | Tuple vs ->
      WithIrMetadata.make (Ir.Tuple (List.map to_ir vs))
    | Nil ->
      WithIrMetadata.make Ir.Nil
    | Cons (v1, v2) ->
      WithIrMetadata.make (Ir.Cons (to_ir v1, to_ir v2))
    | Inl v ->
      WithIrMetadata.make (Ir.Inl (to_ir v))
    | Inr v ->
      WithIrMetadata.make (Ir.Inr (to_ir v))
    | Closure { lambda; value_env = _ } ->
      WithIrMetadata.make (Ir.Lam lambda)

  let pp ppf runtime_value =
    Ir.pp_value ppf (to_ir runtime_value)
end

type value_env = RuntimeValue.value_env

type runtime_message = (Ir.message_tag * RuntimeValue.t list)


let rec find_empty_guard guards =
  match guards with
  (* Shouldn't happen in a well-typed program -- must always have an empty guard
     if there's the possibility that a mailbox will be empty *)
  | [] -> runtime_error "No messages available but no 'empty' guard."
  | guard :: rest ->
    begin
      match WithIrMetadata.node guard with
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
      match WithIrMetadata.node guard with
      | Receive recv_guard when recv_guard.tag = tag -> recv_guard
      | _ -> find_receive_guard tag rest 
    end