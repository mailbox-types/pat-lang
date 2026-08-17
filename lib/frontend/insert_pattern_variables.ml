(* Annotation *)
(* Annotation takes partially-defined mailbox types (i.e., MB types with
 * interface information but no pattern annotations) and annotates them with
 * fresh pattern variables so that we can generate constraints.
 * This is done for all user-specified mailbox types. *)
(* Additionally, for interfaces, sets default quasilinearity: if unspecified,
   sets QL to reasonable defaults:
     - Returnable for mailbox types in datatype annotations
     - Usable for ! mailbox types
 *)
open Common
open Sugar_ast
open Source_code

let rec annotate_type =
    let open Type in
    function
        | Base t -> Base t
        | Mailbox mb -> Mailbox mb
        | Fun { linear; args; result } ->
            Fun {
                linear;
                args = List.map annotate_type args;
                result = annotate_type result
            }
        | Tuple ts ->
            Tuple (List.map annotate_type_as_returnable ts)
        | Rec (s, ts) ->
            Rec (s, List.map annotate_type_as_returnable ts)
        | UserMailbox { 
            umb_capability;
            umb_interface;
            umb_quasilinearity;
            umb_pattern
          } ->
              (* Sensible default QL is usable for ! and returnable for ? *)
              let quasilinearity =
                  let open Capability in
                  match (umb_quasilinearity, umb_capability) with
                    | (Some ql, _) -> ql
                    | (None, Out) -> Usable
                    | (None, In) -> Returnable
              in
              let pattern =
                  match umb_pattern with
                    | Some p -> p
                    | None -> Pattern.fresh ()
              in
              Mailbox { capability = umb_capability; interface = umb_interface;
                    quasilinearity; pattern }

(* Biased annotation that will default to annotating QL as returnable if
    undefined *)
and annotate_type_as_returnable =
    let open Type in
    function
        | UserMailbox { umb_capability; umb_interface;
                umb_pattern; umb_quasilinearity } ->
            let pattern =
                match umb_pattern with
                    | Some p -> p
                    | None -> Pattern.fresh ()
            in
            let quasilinearity =
                match umb_quasilinearity with
                    | Some ql -> ql
                    | None -> Quasilinearity.Returnable
            in
            Mailbox {
                capability = umb_capability;
                interface = umb_interface;
                pattern;
                quasilinearity
            }
        | Tuple ts -> Tuple (List.map annotate_type_as_returnable ts)
        | Rec (s, ts) ->
            Rec (s, List.map annotate_type_as_returnable ts)
        | t -> annotate_type t

let annotate_interface_type pos ty =
    let open Type in
    match ty with
        (* Outermost MB types (i.e., payloads) are treated as usable. *)
        | UserMailbox { umb_quasilinearity = Some Returnable ; _ } ->
            raise (Errors.desugar_error
                "Mailbox message payloads cannot be returnable."
                [pos]
            )
        | UserMailbox { umb_capability; umb_interface; umb_pattern; _ } ->
            let pattern =
                match umb_pattern with
                    | Some pat -> pat
                    | None -> Pattern.fresh ()
            in
            Mailbox {
                capability = umb_capability;
                interface = umb_interface;
                pattern;
                quasilinearity = Quasilinearity.Usable
            }
        | Mailbox mb -> Mailbox mb
        | t -> annotate_type t

(* Annotates all types in an interface *)
let annotate_interface iface =
    let iface_pos = WithPos.pos iface in
    let iface_node = WithPos.node iface in
    Interface.bindings iface_node
    |> List.map (fun (tag, tys) ->
            (tag, List.map (annotate_interface_type iface_pos) tys))
    |> Interface.(make (name iface_node))

(* The visitor traverses the AST to annotate parameters of higher-order
   functions. *)
let visitor =
    object(self)
        inherit [_] Sugar_ast.map as super

        method! visit_decl env decl =
            { decl with
                decl_parameters =
                    List.map (fun (x, t) -> (x, annotate_type t))
                        decl.decl_parameters;
                decl_return_type = annotate_type decl.decl_return_type;
                decl_body = self#visit_expr env decl.decl_body }

        method! visit_expr env expr_with_pos =
            let open Sugar_ast in
            let expr = WithPos.node expr_with_pos in
            match expr with
            | Annotate (e, ty) ->
                let new_e = self#visit_expr env e in
                let new_annotate = Annotate (new_e, annotate_type ty) in
                { expr_with_pos with node = new_annotate }
            | Lam { linear; parameters; result_type; body } ->
                let parameters =
                    List.map (fun (x, y) -> (x, annotate_type y)) parameters in
                let result_type = annotate_type result_type in
                let new_body = self#visit_expr env body in
                let new_lam = Lam { linear; parameters; result_type; body = new_body } in
                { expr_with_pos with node = new_lam }
            | Let { annot = Some ty; binder; term; body } ->
                let ty = annotate_type ty in
                let term = self#visit_expr env term in
                let body = self#visit_expr env body in
                let new_let = Let { annot = Some ty; binder; term; body } in
                { expr_with_pos with node = new_let }
            | LetTuple { annot = Some tys; binders; term; cont } ->
                let tys = List.map annotate_type_as_returnable tys in
                let term = self#visit_expr env term in
                let cont = self#visit_expr env cont in
                let new_let = LetTuple { annot = Some tys; binders; term; cont } in
                { expr_with_pos with node = new_let }
            | Case { term; ty; branches } ->
                let term = self#visit_expr env term in
                let ty_ann = annotate_type ty in
                let branches = List.map (fun (bnds, e, s) ->
                    (bnds, self#visit_expr env e, s)) branches in
                let new_case = Case { term; ty = ty_ann; branches } in
                { expr_with_pos with node = new_case }
            | _ -> super#visit_expr env expr_with_pos

        method! visit_program env p =
            let prog_interfaces =
                List.map annotate_interface p.prog_interfaces in
            let prog_interfaces_with_pos =
                List.map2 (fun iface pos -> WithPos.make ~pos iface) prog_interfaces (List.map WithPos.pos p.prog_interfaces) in
            let prog_decls =
                let (poses, nodes) = WithPos.split_with_pos_list p.prog_decls in
                let visited_nodes = self#visit_list (self#visit_decl) env nodes in
                WithPos.combine_with_pos_list poses visited_nodes in
            let prog_body =
                self#visit_option (self#visit_expr) env p.prog_body in
            { prog_interfaces = prog_interfaces_with_pos; prog_decls; prog_body }
        
        method visit_t _env x = x
    end

let annotate prog =
    let prog = visitor#visit_program () prog in
    Settings.if_verbose (fun () ->
        Format.(fprintf std_formatter "=== Annotated Program ===\n%a\n\n"
        Sugar_ast.pp_program prog));
    prog
