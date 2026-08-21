(* IR used for evaluation: produced after typechecking (and reference counting) but before
   interpretation. Structurally similar to Common.Ir, except:
   - All type information (Type.t / Pretype.t) is discarded.
   - App's function, Case's scrutinee, and LetTuple's source are variables, not arbitrary values.
   - There's no per-node metadata (position / free variables). *)

open Common
open Common_types
open Format
open Util.Utility

module Var = Ir.Var
module Binder = Ir.Binder
module RuntimeName = Ir.RuntimeName
module VarSet = Ir.VarSet

type program = {
    prog_decls: decl list;
    prog_body: comp option
}
and decl = {
    decl_name: Binder.t;
    decl_parameters: Binder.t list;
    decl_body: comp
}
and function_target =
    | PrimitiveFunction of string
    | UserFunction of Var.t
and comp =
    | Let of {
        binder: Binder.t;
        term: comp;
        cont: comp
      }
    | Seq of (comp * comp)
    | Return of value
    | App of {
        func: function_target;
        args: Var.t list
      }
    | If of { test: value; then_expr: comp; else_expr: comp }
    | LetTuple of {
        binders: Binder.t list;
        tuple: Var.t;
        cont: comp
    }
    | Case of {
        scrutinee: Var.t;
        branches: (Binder.t list * comp * string) list
    }
    | New of string
    | Spawn of comp
    | Send of {
        target: value;
        message: message;
        iname: string
      }
    | Free of (value * string)
    | Guard of {
        target: value;
        pattern: Type.Pattern.t;
        guards: guard list;
        iname: string
      }
    (* Reference counting instructions inserted after typechecking *)
    | Drop of {
            vars: (Var.t * int) list;
            names: (RuntimeName.t * int) list
        }
    | Dup of (Var.t * int) list
and value =
    | Atom of atom_name
    | Constant of constant
    | Primitive of primitive_name
    | Variable of Var.t
    | Name of RuntimeName.t
    | Tuple of Var.t list
    | Inject of string * Var.t list
    | Lam of lambda
and lambda = {
    parameters: Binder.t list;
    (* Free variables of the lambda as a whole, computed during reference counting.
       Retained here so the runtime can drop a dying closure's captured refs without
       having to recompute free variables by re-traversing the body. *)
    fvs: VarSet.t;
    body: comp
}
and message_tag = string
and message = (message_tag * Var.t list)
and primitive_name = string
and atom_name = string
and constant = Constant.t
and guard =
    | Receive of receive_guard
    | Empty of (Binder.t * comp)
    | Fail
and receive_guard = {
        tag: string;
        payload_binders: Binder.t list;
        mailbox_binder: Binder.t;
        cont: comp
    }

(* Pretty-printing of the evaluation IR *)
let rec pp_program ppf { prog_decls; prog_body } =
    fprintf ppf "%a@.@.%a"
        (pp_print_double_newline_list pp_decl) prog_decls
        (pp_print_option pp_comp) prog_body
and pp_decl ppf { decl_name; decl_parameters; decl_body } =
    fprintf ppf "def %a(%a) {@,@[<v 2>  %a@]@,}"
        Binder.pp decl_name
        (pp_print_comma_list Binder.pp) decl_parameters
        pp_comp decl_body
and pp_message ppf (tag, vs) =
    fprintf ppf "%s(%a)"
        tag
        (pp_print_comma_list Var.pp) vs
and pp_branch name ppf (bnds, c) =
    fprintf ppf "%s(%a) -> @[<v>%a@]"
        name
        (pp_print_comma_list Binder.pp) bnds
        pp_comp c
and pp_comp ppf comp =
    match comp with
    | Let { binder; term; cont } ->
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            Binder.pp binder
            pp_comp term
            pp_comp cont
    | Seq (c1, c2) ->
        fprintf ppf "(%a;@,%a)" pp_comp c1 pp_comp c2
    | Return v -> pp_value ppf v
    | App { func; args } ->
        let f_name =
            match func with
                | PrimitiveFunction f -> f
                | UserFunction v -> Format.asprintf "%a" Var.pp v
        in
        fprintf ppf "%s(%a)"
            f_name
            (pp_print_comma_list Var.pp) args
    | If { test; then_expr; else_expr } ->
        fprintf ppf "if (%a) {@[<v>%a@]} else {@[<v>%a@]}}"
            pp_value test
            pp_comp then_expr
            pp_comp else_expr
    | LetTuple { binders; tuple; cont } ->
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            (pp_print_comma_list Binder.pp) binders
            Var.pp tuple
            pp_comp cont
    | Case { scrutinee; branches } ->
        fprintf ppf
            "case %a of {@[<v>%a@]}"
            Var.pp scrutinee
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,")
                (fun ppf (bnds, c, name) -> pp_branch name ppf (bnds, c))) branches
    | New iname -> fprintf ppf "new[%s]" iname
    | Spawn e -> fprintf ppf "spawn {@[<v>@,%a@]@,}" pp_comp e
    | Send { target; message; iname = _ } ->
        (* Special-case the common case of sending to a variable.
           Bracket the rest for readability. *)
        begin
            match target with
                | Variable _ ->
                    fprintf ppf "%a ! %a"
                        pp_value target
                        pp_message message
                | _ ->
                    fprintf ppf "(@[<v 2>%a@]) ! %a"
                        pp_value target
                        pp_message message
        end
    | Free (v, _iname) ->
        fprintf ppf "free(%a)" pp_value v
    | Guard { target; pattern; guards; _ } ->
        fprintf ppf
            "guard %a : %a {@,@[<v 2>  %a@]@,}"
            pp_value target
            Type.Pattern.pp pattern
            (pp_print_newline_list pp_guard) guards
    | Drop { vars; names } ->
        let pp_var ppf (var, count) = fprintf ppf "\"%s\":%d" (Var.unique_name var) count in
        let pp_name ppf (name, count) = fprintf ppf "\"%a\":%d" RuntimeName.pp name count in
        begin
            match (vars, names) with
            | (_, []) ->
                fprintf ppf "drop (%a)"
                    (pp_print_comma_list pp_var) vars
            | ([], _) ->
                fprintf ppf "drop_names (%a)"
                    (pp_print_comma_list pp_name) names
            | _ ->
                fprintf ppf "drop (vars=[%a], names=[%a])"
                    (pp_print_comma_list pp_var) vars
                    (pp_print_comma_list pp_name) names
        end
    | Dup vars ->
        let pp_var ppf (var, count) = fprintf ppf "\"%s\":%d" (Var.unique_name var) count in
        fprintf ppf "dup (%a)"
            (pp_print_comma_list pp_var) vars
and pp_value ppf value =
    match value with
    | Atom name -> Format.pp_print_string ppf (":" ^ name)
    | Primitive prim -> Format.pp_print_string ppf prim
    | Variable var -> Var.pp ppf var
    | Name runtime_name -> RuntimeName.pp ppf runtime_name
    | Constant c -> Constant.pp ppf c
    | Tuple vs ->
        fprintf ppf "%a" (pp_print_comma_list Var.pp) vs
    | Inject (name, vs) ->
        fprintf ppf "%s(%a)" name (pp_print_comma_list Var.pp) vs
    | Lam { parameters; body; _ } ->
        fprintf ppf "fun(%a) {@,  @[<v>%a@]@,}"
            (pp_print_comma_list Binder.pp) parameters
            pp_comp body
and pp_guard ppf guard =
    match guard with
    | Receive { tag; payload_binders; mailbox_binder; cont } ->
            fprintf ppf "receive %s(%a) from %a ->@,@[<v 2>  %a@]"
            tag
            (pp_print_comma_list Binder.pp) payload_binders
            Binder.pp mailbox_binder
            pp_comp cont
    | Empty (x, e) ->
        fprintf ppf "empty(%a) ->@,  @[<v>%a@]" Binder.pp x pp_comp e
    | Fail ->
        fprintf ppf "fail"
