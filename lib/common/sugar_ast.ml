open Common_types
open Util.Utility
open Format


module WithPos = Source_code.WithPos

(* Basic sugared AST *)
(* Expressions *)
type expr = expr_node WithPos.t [@name "withP"]
and expr_node =
    | Var of sugar_var
    | Atom of atom_name
    | Primitive of (primitive_name[@name "primitive_name"])
    (* Type annotation, used for synthesis --> checking switch. *)
    | Annotate of expr * (Type.t[@name "ty"])
    | Constant of constant
    | Lam of {
        linear: bool;
        parameters: (sugar_binder * (Type.t[@name "ty"])) list;
        result_type: (Type.t[@name "ty"]);
        body: expr }
    | Let of {
        binder: sugar_binder;
        annot: (Type.t[@name "ty"]) option;
        term: expr;
        body: expr }
    | Seq of expr * expr
    | App of {
        func: expr;
        args: expr list
    }
    | If of { test: expr; then_expr: expr; else_expr: expr }
    (* Tuples *)
    | Tuple of expr list
    | LetTuple of {
        binders: sugar_binder list;
        annot: ((Type.t[@name "ty"]) list) option;
        term: expr;
        cont: expr
    }
    (* Value constructor for recursive types (e.g., inl, inr, nil, cons, leaf, node) *)
    | Inject of string * expr list
    | Case of {
        term: expr;
        branches: (sugar_binder list * expr * string) list
    }
    (* Note that we're using the versions of new and spawn where they are
       not wired to their continuations. I've experimented with the
       bidirectional rules and it seems that this does not pose any problems. *)
    (* That said, we may revisit this later when we look at deadlock detection. *)
    | New of string (* interface name *)
    | Spawn of expr
    (* interface names for Send and Guard will be added after pre-type checking *)
    | Send of {
        target: expr;
        message: (string * (expr list));
        iname: string option
    }
    | Guard of {
        target: expr;
        (* At least at the moment, each guard must be annotated with a pattern *)
        pattern: (Type.Pattern.t [@name "pattern"]);
        guards: guard list;
        iname: string option
    }
    | Free of expr
    | Fail of expr
and constant =
    [%import: Common_types.Constant.t]
and sugar_var = string
and atom_name = string
and sugar_binder = string
and primitive_name = string
(* Guards are either a receive expression, free, or fail *)
and guard = guard_node WithPos.t [@name "withP"]
and guard_node =
    | Receive of {
        tag: string;
        payload_binders: sugar_binder list;
        mailbox_binder: sugar_binder;
        strategy: Settings.ReceiveTypingStrategy.t option;
        cont: expr
    }
    | GFree of expr
    | Empty of (sugar_var * expr)
and decl = {
    decl_name: string;
    decl_parameters: (string * (Type.t[@name "ty"])) list;
    decl_return_type: (Type.t[@name "ty"]);
    decl_body: expr
}
and prog_interfaces_node = (Interface.t[@name "interface"])
and program = {
    prog_interfaces: (prog_interfaces_node WithPos.t [@name "withP"]) list;
    prog_decls: (decl WithPos.t [@name "withP"]) list;
    prog_body: expr option
}
    [@@deriving visitors {
        variety = "map";
        ancestors = ["Type.map"; "Interface.map"; "WithPos.map"];
        data = false } ]

let is_receive_guard = function
    | Receive _ -> true
    | _ -> false

let is_free_guard = function
    | GFree _ -> true
    | _ -> false

let is_empty_guard = function
    | Empty _ -> true
    | _ -> false

(* Pretty-printing of the AST *)
(* Programs *)
let rec pp_program ppf { prog_interfaces; prog_decls; prog_body } =
    fprintf ppf "%a@.%a@.@.%a"
        (pp_print_newline_list pp_interface) prog_interfaces
        (pp_print_double_newline_list pp_decl) prog_decls
        (pp_print_option pp_expr) prog_body
(* Interfaces *)
and pp_interface ppf iface =
    let pp_msg_ty ppf (tag, tys) =
        fprintf ppf "%s(%a)" tag
        (pp_print_comma_list Type.pp) tys
    in
    let xs = Interface.bindings (WithPos.node iface) in
    fprintf ppf "interface %s { %a }"
    (Interface.name (WithPos.node iface) )
        (pp_print_comma_list pp_msg_ty) xs
(* Declarations *)
and pp_decl ppf decl =
    let  { decl_name; decl_parameters; decl_return_type; decl_body } =
        WithPos.node decl
    in
    fprintf ppf "def %s(%a): %a {@,@[<v 2>  %a@]@,}"
      decl_name
      (pp_print_comma_list pp_param) decl_parameters
      Type.pp decl_return_type
      pp_expr decl_body
(* Messages *)
and pp_message ppf (tag, es) =
    fprintf ppf "%s(%a)"
        tag
        (pp_print_comma_list pp_expr) es
(* Parameters *)
and pp_param ppf (param, ty) = fprintf ppf "%s: %a" param Type.pp ty
and pp_let_annot ppf ty = fprintf ppf ": %a" Type.pp ty
and pp_bnd_ann ppf (bnd, ann) =
    fprintf ppf
        "%s%a"
        bnd
        pp_let_annot ann
(* Expressions *)
and pp_sugar_branch ppf (bnds, e, name) =
    fprintf ppf "%s(%a) -> %a"
        name
        (pp_print_comma_list pp_print_string) bnds
        pp_expr e
and pp_expr ppf expr_with_pos =
    (* Might want, at some stage, to print out pretype info *)
    let expr_node = WithPos.node expr_with_pos in
    match expr_node with
    | Var x -> pp_print_string ppf x
    | Atom x -> pp_print_string ppf (":" ^ x)
    | Primitive x -> pp_print_string ppf x
    | Annotate (expr, ty) ->
        fprintf ppf "(%a : %a)" pp_expr expr Type.pp ty
    | Constant c -> Constant.pp ppf c
    | Lam { linear; parameters; body; result_type } ->
        let lin = if linear then "linfun" else "fun" in
        fprintf ppf "%s(%a): %a {@,  @[<v>%a@]@,}"
            lin
            (pp_print_comma_list pp_param) parameters
            Type.pp result_type
            pp_expr body
    | Let { binder; annot; term; body } ->
        fprintf ppf "let %s%a = @[<v>%a@] in@,%a"
            binder
            (pp_print_option pp_let_annot) annot
            pp_expr term
            pp_expr body
    | If { test; then_expr; else_expr } ->
            fprintf ppf "if (%a) {@[<v>%a@]} else {@[<v>%a@]}}"
            pp_expr test
            pp_expr then_expr
            pp_expr else_expr
    | Seq (e1, e2) ->
        fprintf ppf "(%a;@,%a)" pp_expr e1 pp_expr e2
    | App { func; args } ->
        fprintf ppf "%a(%a)"
            pp_expr func
            (pp_print_comma_list pp_expr) args
    | New iname -> fprintf ppf "new[%s]" iname
    | Spawn e -> fprintf ppf "spawn {@[<v>@,%a@]@,}" pp_expr e
    | Send { target; message; _ (* iname *) } ->
        (* Special-case the common case of sending to a variable.
           Bracket the rest for readability. *)
        begin
            match WithPos.node target with
                | Var _ ->
                    fprintf ppf "%a ! %a"
                        pp_expr target
                        pp_message message
                | _ ->
                    fprintf ppf "(@[<v 2>%a@]) ! %a"
                        pp_expr target
                        pp_message message
        end
    | Inject (name, es) ->
        fprintf ppf "%s(%a)" name (pp_print_comma_list pp_expr) es
    | Case { term; branches } ->
        fprintf ppf "case %a of { %a }"
            pp_expr term
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf " | ") pp_sugar_branch) branches
    | Tuple es ->
        fprintf ppf "(%a)" (pp_print_comma_list pp_expr) es
    | LetTuple { binders = bs; annot = None; term; cont } ->
        fprintf ppf "let (%a) = %a in %a"
            (pp_print_comma_list pp_print_string) bs
            pp_expr term
            pp_expr cont
    | LetTuple { binders = bs; annot = Some ts; term; cont } ->
        assert (List.length bs = List.length ts);
        fprintf ppf "let (%a) : (%a) = %a in %a"
            (pp_print_comma_list pp_print_string) bs
            (pp_print_comma_list Type.pp) ts
            pp_expr term
            pp_expr cont
    | Guard { target; pattern; guards; _ } ->
        fprintf ppf
            "guard %a : %a {@,@[<v 2>  %a@]@,}"
            pp_expr target
            Type.Pattern.pp pattern
            (pp_print_newline_list pp_guard) guards
    | Free e -> fprintf ppf "free(%a)" pp_expr e
    | Fail e -> fprintf ppf "fail(%a)" pp_expr e
and pp_guard ppf guard_with_node =
    let guard_node = WithPos.node guard_with_node in
    match guard_node with
    | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            let receive_keyword = match strategy with
                | Some Nothing -> "receive*"
                | _ -> "receive"
            in
            fprintf ppf "%s %s(%a) from %s ->@,@[<v 2>  %a@]"
            receive_keyword
            tag
            (pp_print_comma_list pp_print_string) payload_binders
            mailbox_binder
            pp_expr cont
    (*
       free -> M
       can be treated as syntactic sugar for
       empty(x) -> free(x); M
    *)
    | GFree e ->
        fprintf ppf "free ->@,  @[<v>%a@]" pp_expr e
    | Empty (x, e) ->
        fprintf ppf "empty(%s) ->@,  @[<v>%a@]" x pp_expr e

(* Probably prettier ways of doing this... *)
let show_program prog = asprintf "%a" pp_program prog
let show_expr expr = asprintf "%a" pp_expr expr

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

let rec is_syntactic_value x =
    match WithPos.node x with
        | Var _
        | Atom _
        | Primitive _
        | Constant _
        | Lam _ -> true
        | Tuple xs
        | Inject (_, xs) -> List.for_all is_syntactic_value xs
        | _ -> false
