open Common
open Ir

module VarMap = Map.Make(Var)
module RuntimeMap = Map.Make(RuntimeName)

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

module RuntimeValue = struct
  type value_env = t VarMap.t
  and t =
    | VAnnotate of t * Type.t
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
    | Ir.VAnnotate (v, ty) -> VAnnotate (of_ir value_env v, ty)
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
    | VAnnotate (v, ty) ->
      WithIrMetadata.make (Ir.VAnnotate (to_ir v, ty))
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
end

type value_env = RuntimeValue.value_env

type runtime_message = (Ir.message_tag * RuntimeValue.t list)

type environment = value_env

type computation_frame =
  | SeqFrame of {
    saved_env: environment;
    next_comp: comp;
  }
  | LetFrame of {
    binder: Var.t;
    saved_env: environment;
    next_comp: comp;
  }

type computation_state = {
  current_comp: comp;
  env: environment;
  stack: computation_frame list
}