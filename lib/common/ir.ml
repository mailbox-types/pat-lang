(* FGCBV IR *)
open Common_types
open Format
open Util.Utility
open Source_code

module Binder = struct
    type t = { id: int; name: string }
    [@@name "binder"]
    [@@deriving visitors { variety = "map"; data = false }]

    (* Accessors *)
    let id x = x.id
    let name x = x.name

    let source = ref 0

    let gen () =
        let res = !source in
        incr source;
        res

    let make ?(name="") () =
        { id = gen (); name = name }

    (* Display *)
    let pp ppf x =
        let prefix =
            if x.name = "" then "_" else x.name in
        Format.pp_print_string ppf (prefix ^ (string_of_int x.id))
end

module Var = struct
    type t = { id: int; name: string }
    [@@name "var"]
    [@@deriving visitors { variety = "map"; data = false }]

    (* Accessors *)
    let id x = x.id
    let name x = x.name

    (* Display *)
    let pp ppf x =
        let prefix =
            if x.name = "" then "_" else x.name in
        Format.pp_print_string ppf (prefix ^ (string_of_int x.id))

    let pp_name ppf x =
        Format.pp_print_string ppf x.name

    let unique_name =
        Format.asprintf "%a" pp

    let of_binder : Binder.t -> t = fun x ->
        { id = Binder.id x; name = Binder.name x }

    let compare x1 x2 =
        compare (unique_name x1) (unique_name x2)
end

module type VarSet = (Set.S with type elt = Var.t)
module VarSet = Set.Make(Var)
type varset = VarSet.t

type program = {
    prog_interfaces: ((Interface.t[@name "interface"]) WithPos.t [@name "withP"]) list;
    prog_decls: (decl WithPos.t [@name "withP"]) list;
    prog_body: comp option
}
and decl = {
    decl_name: (Binder.t[@name "binder"]);
    decl_parameters: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) list;
    decl_return_type: (Type.t[@name "ty"]);
    decl_body: comp
}
and comp = (comp_node WithPos.t [@name "withP"])
and comp_node =
    | Annotate of comp * (Type.t[@name "ty"])
    | Let of {
        binder: (Binder.t[@name "binder"]);
        term: comp;
        cont: comp
      }
    | Seq of (comp * comp)
    | Return of value
    | App of {
        func: value;
        args: value list
      }
    | If of { test: value; then_expr: comp; else_expr: comp }
    | LetTuple of {
        (* By annotating with inferred pretypes, we can always use a checking rule
           during inference, irrespective of whether both of the binders are used. *)
        binders: ((Binder.t[@name "binder"]) * (Pretype.t[@name "pretype"]) option) list;
        tuple: value;
        cont: comp
    }
    | Case of {
        term: value;
        branch1: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) * comp;
        branch2: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) * comp
    }
    | CaseL of {
        term: value;
        ty: (Type.t[@name "ty"]);
        nil: comp;
        cons: ((Binder.t[@name "binder"]) * (Binder.t[@name "binder"])) * comp
    }
    | New of string
    | Spawn of comp
    | Send of {
        target: value;
        message: (message[@name "msg"]);
        iname: string option
      }
    | Free of (value * string option)
    | Guard of {
        target: value;
        pattern: (Type.Pattern.t[@name "pattern"]);
        guards: guard list;
        iname: string option
      }
    (* Reference counting instructions inserted after typechecking *)
    | Drop of ((Var.t[@name "var"]) * int) list
    | Dup of ((Var.t[@name "var"]) * int) list
and value = (value_node WithPos.t [@name "withP"])
and value_node =
    | VAnnotate of value * (Type.t[@name "ty"])
    | Atom of atom_name
    | Constant of constant
    | Primitive of primitive_name
    | Variable of (Var.t[@name "var"]) * (Pretype.t[@name "pretype"]) option
    | Tuple of value list
    | Nil
    | Cons of value * value
    | Inl of value
    | Inr of value
    | Lam of {
        linear: bool;
        parameters: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) list;
        result_type: (Type.t[@name "ty"]);
        body: comp
    }
and message = (string * value list)
    [@@name "msg"]
and primitive_name = string
and atom_name = string
and constant =
    [%import: Common_types.Constant.t]
and guard = (guard_node WithPos.t [@name "withP"])
and guard_node =
    | Receive of {
        tag: string;
        payload_binders: (Binder.t[@name "binder"]) list;
        mailbox_binder: (Binder.t[@name "binder"]);
        strategy: Settings.ReceiveTypingStrategy.t option;
        cont: comp
    }
    | Empty of ((Binder.t[@name "binder"]) * comp)
    | Fail
    [@@deriving visitors {
        variety = "map";
        ancestors = [
            "Type.map"; "Pretype.map"; "Binder.map";
            "Interface.map"; "Var.map"; "WithPos.map"];
        data = false }]


let remove_decl_names (decls : Binder.t list) (vars : VarSet.t) : VarSet.t =
    let decl_vars =
        decls
        |> List.map Var.of_binder
        |> VarSet.of_list
    in
    VarSet.diff vars decl_vars

let rec free_variables ?(decls = []) comp : VarSet.t =
    let union_many = List.fold_left VarSet.union VarSet.empty in
    let delete_binders binders vars =
        List.fold_left (fun acc binder -> VarSet.remove (Var.of_binder binder) acc) vars binders
    in
    let vars =
        match WithPos.node comp with
        | Annotate (comp, _) ->
            free_variables ~decls comp
        | Let { binder; term; cont } ->
            VarSet.union
                (free_variables ~decls term)
                (VarSet.remove (Var.of_binder binder) (free_variables ~decls cont))
        | Seq (comp1, comp2) ->
            VarSet.union (free_variables ~decls comp1) (free_variables ~decls comp2)
        | Return value ->
            free_variables_value ~decls value
        | App { func; args } ->
            union_many (free_variables_value ~decls func :: List.map (free_variables_value ~decls) args)
        | If { test; then_expr; else_expr } ->
            union_many [free_variables_value ~decls test; free_variables ~decls then_expr; free_variables ~decls else_expr]
        | LetTuple { binders; tuple; cont } ->
            let tuple_vars = free_variables_value ~decls tuple in
            let cont_vars =
                binders
                |> List.map fst
                |> fun binders -> delete_binders binders (free_variables ~decls cont)
            in
            VarSet.union tuple_vars cont_vars
        | Case { term; branch1 = ((binder1, _), comp1); branch2 = ((binder2, _), comp2) } ->
            union_many
                [ free_variables_value ~decls term
                ; VarSet.remove (Var.of_binder binder1) (free_variables ~decls comp1)
                ; VarSet.remove (Var.of_binder binder2) (free_variables ~decls comp2)
                ]
        | CaseL { term; ty = _; nil; cons = ((binder1, binder2), comp) } ->
            union_many
                [ free_variables_value ~decls term
                ; free_variables ~decls nil
                ; free_variables ~decls comp |> VarSet.remove (Var.of_binder binder1) |> VarSet.remove (Var.of_binder binder2)
                ]
        | New _ ->
            VarSet.empty
        | Spawn comp ->
            free_variables ~decls comp
        | Send { target; message = (_, values); iname = _ } ->
            union_many (free_variables_value ~decls target :: List.map (free_variables_value ~decls) values)
        | Free (value, _) ->
            free_variables_value ~decls value
        | Guard { target; pattern = _; guards; iname = _ } ->
            union_many (free_variables_value ~decls target :: List.map (free_variables_guard ~decls) guards)
        | Drop vars
        | Dup vars ->
            List.fold_left (fun acc (var, _) -> VarSet.add var acc) VarSet.empty vars
    in
    remove_decl_names decls vars
and free_variables_value ?(decls = []) value : VarSet.t =
    let union_many = List.fold_left VarSet.union VarSet.empty in
    let vars =
        match WithPos.node value with
        | VAnnotate (value, _) ->
            free_variables_value ~decls value
        | Atom _
        | Constant _
        | Primitive _
        | Nil ->
            VarSet.empty
        | Variable (var, _) ->
            VarSet.singleton var
        | Tuple values ->
            union_many (List.map (free_variables_value ~decls) values)
        | Cons (value1, value2) ->
            VarSet.union (free_variables_value ~decls value1) (free_variables_value ~decls value2)
        | Inl value
        | Inr value ->
            free_variables_value ~decls value
        | Lam { linear = _; parameters; result_type = _; body } ->
            let body_vars = free_variables ~decls body in
            parameters
            |> List.map fst
            |> List.fold_left (fun acc binder -> VarSet.remove (Var.of_binder binder) acc) body_vars
    in
    remove_decl_names decls vars
and free_variables_guard ?(decls = []) guard : VarSet.t =
    let vars =
        match WithPos.node guard with
        | Receive { tag = _; payload_binders; mailbox_binder; strategy = _; cont } ->
            List.fold_left
                (fun acc binder -> VarSet.remove (Var.of_binder binder) acc)
                (free_variables ~decls cont)
                (mailbox_binder :: payload_binders)
        | Empty (binder, comp) ->
            VarSet.remove (Var.of_binder binder) (free_variables ~decls comp)
        | Fail ->
            VarSet.empty
    in
    remove_decl_names decls vars

let insert_dup (dups : (Var.t * int) list) (comp : comp) : comp =
    if List.is_empty dups then
        comp
    else
        let pos = WithPos.pos comp in
        WithPos.make ~pos (Seq (WithPos.make (Dup dups), comp))

(* Pretty-printing of the AST *)
(* Programs *)
let rec pp_program ppf { prog_interfaces; prog_decls; prog_body } =
    fprintf ppf "%a@.%a@.@.%a"
        (pp_print_newline_list pp_interface) prog_interfaces
        (pp_print_double_newline_list pp_decl) prog_decls
        (pp_print_option pp_comp) prog_body
(* Interfaces *)
and pp_interface ppf iface =
    let pp_msg_ty ppf (tag, tys) =
        fprintf ppf "%s(%a)" tag
        (pp_print_comma_list Type.pp) tys
    in
    let xs = Interface.bindings (WithPos.node iface) in
    fprintf ppf "interface %s { %a }"
        (Interface.name (WithPos.node iface))
        (pp_print_comma_list pp_msg_ty) xs
(* Declarations *)
and pp_decl ppf decl_with_pos =
    let { WithPos.node = { decl_name; decl_parameters; decl_return_type; decl_body }; _ } = decl_with_pos in
    fprintf ppf "def %a(%a): %a {@,@[<v 2>  %a@]@,}"
        Binder.pp decl_name
        (pp_print_comma_list pp_param) decl_parameters
        Type.pp decl_return_type
        pp_comp decl_body
(* Messages *)
and pp_message ppf (tag, vs) =
    fprintf ppf "%s(%a)"
        tag
        (pp_print_comma_list pp_value) vs
(* Parameters *)
and pp_param ppf (param, ty) = fprintf ppf "%a: %a" Binder.pp param Type.pp ty
and pp_branch name ppf ((bnd, ty), c) =
    fprintf ppf "%s(%a): %a -> @[<v>%a@]"
        name
        Binder.pp bnd
        Type.pp ty
        pp_comp c
and pp_nil name ppf c =
  fprintf ppf "%s([]) -> @[<v>%a@]"
    name
    pp_comp c
and pp_cons name ppf ((bnd1, bnd2), c) =
    fprintf ppf "%s(%a :: %a) -> @[<v>%a@]"
        name
        Binder.pp bnd1
        Binder.pp bnd2
        pp_comp c
(* Expressions *)
and pp_comp ppf comp_with_pos =
    let comp_node = WithPos.node comp_with_pos in
    match comp_node with
    | Annotate (c, ty) ->
        fprintf ppf "(%a : %a)" pp_comp c Type.pp ty
    | Seq (c1, c2) ->
        fprintf ppf "(%a;@,%a)" pp_comp c1 pp_comp c2
    | Let { binder; term; cont } ->
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            Binder.pp binder
            pp_comp term
            pp_comp cont
    | Return v -> pp_value ppf v
    | Free (v, _) ->
            fprintf ppf "free(%a)" pp_value v
    | If { test; then_expr; else_expr } ->
            fprintf ppf "if (%a) {@[<v>%a@]} else {@[<v>%a@]}}"
            pp_value test
            pp_comp then_expr
            pp_comp else_expr
    | App { func; args } ->
        fprintf ppf "%a(%a)"
            pp_value func
            (pp_print_comma_list pp_value) args
    | New iname -> fprintf ppf "new[%s]" iname
    | Spawn e -> fprintf ppf "spawn {@[<v>@,%a@]@,}" pp_comp e
    | Send { target; message; _ (* iname *) } ->
        (* Special-case the common case of sending to a variable.
           Bracket the rest for readability. *)
        begin
            match WithPos.node target with
                | Variable _ ->
                    fprintf ppf "%a ! %a"
                        pp_value target
                        pp_message message
                | _ ->
                    fprintf ppf "(@[<v 2>%a@]) ! %a"
                        pp_value target
                        pp_message message
        end
    | LetTuple { binders = bs; tuple; cont } ->
        let bs = List.map fst bs in
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            (pp_print_comma_list Binder.pp) bs
            pp_value tuple
            pp_comp cont
    | Case { term; branch1; branch2 } ->
        fprintf ppf
            "case %a of {@[<v>@[<v>%a@]@,@[<v>%a@]@]}"
            pp_value term
            (pp_branch "inl") branch1
            (pp_branch "inr") branch2
    | CaseL { term; ty; nil; cons } ->
        fprintf ppf
            "caseL %a: %a of {@[<v>@[<v>%a@]@,@[<v>%a@]@]}"
            pp_value term
            Type.pp ty
            (pp_nil "nil") nil
            (pp_cons "cons") cons
    | Guard { target; pattern; guards; _ } ->
        fprintf ppf
            "guard %a : %a {@,@[<v 2>  %a@]@,}"
            pp_value target
            Type.Pattern.pp pattern
            (pp_print_newline_list pp_guard) guards
    | Drop vars ->
        let pp_var ppf (var, count) = fprintf ppf "\"%s\":%d" (Var.unique_name var) count in
        fprintf ppf "drop (%a)"
            (pp_print_comma_list pp_var) vars
    | Dup vars ->
        let pp_var ppf (var, count) = fprintf ppf "\"%s\":%d" (Var.unique_name var) count in
        fprintf ppf "dup (%a)"
            (pp_print_comma_list pp_var) vars
and pp_value ppf v =
    let value = WithPos.node v in
    match value with
    (* Might want, at some stage, to print out pretype info *)
    | VAnnotate (value, ty) ->
        fprintf ppf "(%a : %a)" pp_value value Type.pp ty
    | Atom name -> Format.pp_print_string ppf (":" ^ name)
    | Primitive prim -> Format.pp_print_string ppf prim
    | Variable (var, _) -> Var.pp ppf var
    | Constant c -> Constant.pp ppf c
    | Tuple vs ->
        fprintf ppf "%a" (pp_print_comma_list pp_value) vs
    | Nil -> Format.pp_print_string ppf "Nil"
    | Cons (v1, v2) ->
        fprintf ppf "%a :: %a" pp_value v1 pp_value v2
    | Inl v -> fprintf ppf "inl(%a)" pp_value v
    | Inr v -> fprintf ppf "inr(%a)" pp_value v
    | Lam { linear; parameters; result_type; body } ->
        let lin = if linear then "linfun" else "fun" in
        fprintf ppf "%s(%a): %a {@,  @[<v>%a@]@,}"
            lin
            (pp_print_comma_list pp_param) parameters
            Type.pp result_type
            pp_comp body
and pp_guard ppf guard_with_pos =
    let guard_node = WithPos.node guard_with_pos in
    match guard_node with
    | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            let receive_keyword = match strategy with
                | Some Nothing -> "receive*"
                | _ -> "receive"
            in
            fprintf ppf "%s %s(%a) from %a ->@,@[<v 2>  %a@]"
            receive_keyword
            tag
            (pp_print_comma_list Binder.pp) payload_binders
            Binder.pp mailbox_binder
            pp_comp cont
    | Empty (x, e) ->
        fprintf ppf "empty(%a) ->@,  @[<v>%a@]" Binder.pp x pp_comp e
    | Fail ->
        fprintf ppf "fail"

let unit = Tuple []

let is_receive_guard = function
    | Receive _ -> true
    | _ -> false

let is_free_guard = function
    | Free _ -> true
    | _ -> false

let is_fail_guard guard =
    match WithPos.node guard with
    | Fail -> true
    | _ -> false


(* Substitutes a pattern solution through the program *)
let substitute_solution sol =
    let visitor =
        object
            inherit [_] map

            method! visit_PatVar _env x =
                match StringMap.find_opt x sol with
                    | Some ty -> ty
                    | None -> Type.Pattern.PatVar x
            
            method visit_Settings_ReceiveTypingStrategy_t _env x = x
            
            method visit_t _env x = x
        end
    in
    visitor#visit_program ()
