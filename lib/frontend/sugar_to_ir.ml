open Common
open Util.Utility
open Source_code

(* Transforms the sugared AST to the FGCBV IR *)
(* Takes a rather naive approach by assigning each subexpression
 * to a variable. We can likely do some administrative reductions
 * on the fly a little later.
 *)

(* Maps Strings (source-level variables) to IR variables (Ir.Var) *)
type env = { var_env: Ir.Var.t stringmap }
let empty_env = { var_env = StringMap.empty }

let bind_var bnd env = { var_env = StringMap.add (Ir.Binder.name bnd) (Ir.Var.of_binder bnd) (env.var_env) }

let bind_vars bnds env = List.fold_left (fun acc bnd -> bind_var bnd acc) env bnds


let lookup_var key env pos =
    match StringMap.find_opt key (env.var_env) with
        | Some ty -> ty
        | None ->
            raise (Errors.transform_error ("Unbound variable " ^ key) [pos] )


let id = fun _ x -> x

let add_name env name =
    let bnd = Ir.Binder.make ~name:name () in
    let env' = bind_var bnd env in
    (bnd, env')

(* f : 'a -> string, where names : 'a list
 * this allows for add_names to accept a list of non-strings,
 * provided that an appropriate function f is given
 * if names : string list, pass (fun x->x) as f
 *
 * add_names env f names = add_names env (fun x->x) (List.map f names)
 * *)
let add_names env f names =
    List.fold_right
    (fun name (bnds, env) ->
        let (bnd, env') = add_name env (f name) in
        (bnd::bnds, env'))
    names
    ([], env)

let rec transform_prog :
    env ->
    Sugar_ast.program ->
        (env -> Ir.program -> Ir.program) -> Ir.program =
            fun env {prog_interfaces;prog_decls;prog_body} k ->
    let (poses, nodes) = WithPos.split_with_pos_list prog_decls in
    let (bnds, env') = add_names env (fun d -> d.Sugar_ast.decl_name) nodes in
    {
        prog_interfaces;
        prog_decls = WithPos.combine_with_pos_list poses
                    (List.map (fun (b, d) -> transform_decl env' d b id) (List.combine bnds nodes));
        prog_body =
            match prog_body with
            | Some prog_body -> Some (transform_expr env' prog_body id)
            | None -> None
    } |> k env
and transform_decl :
    env ->
    Sugar_ast.decl ->
    Ir.Binder.t ->
        (env -> Ir.decl -> Ir.decl) -> Ir.decl =
            fun env {decl_parameters; decl_return_type; decl_body; _} decl_binder k ->
    let (bnds, env') = add_names env fst decl_parameters in
    {
        decl_name = decl_binder;
        decl_parameters = List.combine bnds (List.map snd decl_parameters);
        decl_return_type;
        decl_body = transform_expr env' decl_body id
    } |> k env

and transform_exprs env xs k = transform_exprs' env xs [] k
and transform_exprs' :
    env ->
    Sugar_ast.expr list ->
    Ir.value list ->
    (env -> Ir.value list -> Ir.comp) -> Ir.comp
    = fun env es vs k ->
        match es with
            | [] -> k env (List.rev vs)
            | x :: xs ->
                transform_subterm env x (fun _ v ->
                    transform_exprs' env xs (v :: vs) k)
and transform_expr :
    env ->
    Sugar_ast.expr ->
        (env -> Ir.comp -> Ir.comp) -> Ir.comp = fun env x k ->
    let pos = WithPos.pos x in
    (* Explicit eta here to allow with_same_pos to be used polymorphically *)
    let with_same_pos v = WithPos.make ~pos v in
    match WithPos.node x with
        (* Looks up a term-level variable in the environment,
           returns IR variable *)
        | Var v ->
            let v = lookup_var v env pos in
            with_same_pos (Ir.Return (with_same_pos (Ir.Variable (v, None)))) |> k env
        | Primitive x -> with_same_pos (Ir.Return (with_same_pos (Ir.Primitive x))) |> k env
        | Atom x -> with_same_pos (Ir.(Return (with_same_pos (Atom x)))) |> k env
        | Constant x ->
            with_same_pos (Ir.Return (with_same_pos (Ir.Constant x))) |> k env
        | Lam {linear; parameters; result_type; body} ->
            let (bnds, env') = add_names env fst parameters in
            with_same_pos (
            Ir.Return (with_same_pos (Ir.Lam {
                linear;
                parameters = List.combine bnds (List.map snd parameters);
                result_type;
                body = transform_expr env' body id }))) |> k env
        | Annotate (body, annotation) ->
            with_same_pos (Ir.Annotate (transform_expr env body id, annotation))
            |> k env
        | Inject (name, es) ->
            transform_exprs env es (fun _ vs ->
                with_same_pos (Ir.Return (with_same_pos (Ir.Inject (name, vs)))) |> k env)
        (* Note that annotation will have been desugared to subject annotation *)
        | Let {binder; term; body; _} ->
            (* let x = M in N*)
            (* Create an IR variable based on x *)
            let bnd = Ir.Binder.make ~name:binder () in
            (* Transform M under *old* environment *)
            (* The continuation *)
            transform_expr env term
                (fun env c ->
                    (* Bind it in the environment *)
                    let env' = bind_var bnd env in
                    with_same_pos (
                    Ir.Let {
                        binder = bnd;
                        term = c;
                        cont = transform_expr env' body k }))
        | Tuple es ->
            transform_exprs env es (fun _ vs ->
                with_same_pos (Ir.Return (with_same_pos (Ir.Tuple vs))) |> k env)
        | LetTuple {binders = bs; term; cont; _ } ->
            (* let x = M in N*)
            (* Create IR variables based on the binders *)
            let bnds = List.map (fun name -> Ir.Binder.make ~name ()) bs in
            (* Transform M under *old* environment *)
            (* The continuation *)
            transform_subterm env term
                (fun env v ->
                    (* Bind it in the environment *)
                    let env' = bind_vars bnds env in
                    let binders = List.map (fun bnd -> (bnd, None)) bnds in
                    with_same_pos (
                    Ir.LetTuple {
                        binders;
                        tuple = v;
                        cont = transform_expr env' cont k }))
        | Case {
            term;
            ty = ty1;
            branches } ->
            transform_subterm env term (fun env v ->
                let ir_branches = List.map (fun (bnds, comp, s) ->
                    let (ir_bnds, branch_env) = add_names env (fun x -> x) bnds in
                    (ir_bnds, (transform_expr branch_env comp id), s)) branches in
                with_same_pos (
                Ir.Case {
                    term = v;
                    ty = ty1;
                    branches = ir_branches;
                }) |> k env)
        | Seq (e1, e2) ->
            transform_expr env e1 (fun env c1 ->
            let pos' = WithPos.pos c1 in
            match WithPos.node c1 with
                | Ir.Return ({ node = Ir.Tuple []; _ }) ->
                    transform_expr env e2 k
                | _ -> WithPos.make ~pos:pos' (Ir.Seq (c1, transform_expr env e2 k)))
        | App {func; args} ->
            transform_subterm env func (fun env funcv ->
            transform_list env args (fun argvs ->
                with_same_pos (Ir.App { func = funcv; args = argvs })) k)
        | If {test; then_expr; else_expr} ->
                transform_subterm env test (fun env v ->
                with_same_pos (
                Ir.If {
                    test = v;
                    then_expr = transform_expr env then_expr id;
                    else_expr = transform_expr env else_expr id }) |> k env)
        | New i -> with_same_pos (Ir.New i) |> k env
        | Spawn e -> with_same_pos (Ir.Spawn (transform_expr env e id)) |> k env
        | Free e ->
            transform_subterm env e (fun _ v -> with_same_pos (Ir.Free (v, None))) |> k env
        | Send {target; message; iname} ->
            let (tag, payloads) = message in
            transform_subterm env target (fun env pid ->
                transform_list env payloads (fun payload_vs ->
                    with_same_pos (
                    Ir.Send {
                        target = pid;
                        message = (tag, payload_vs);
                        iname })) k)
        | Guard {target; pattern; guards; iname} ->
            transform_subterm env target (fun env v ->
                let gs = List.map (fun x -> transform_guard env x) guards in
                with_same_pos (
                Ir.Guard {
                    target = v;
                    pattern;
                    guards = gs;
                    iname
                }) |> k env )
        |  SugarFail (_, _) -> (* shouldn't ever match *)
                raise (Errors.internal_error "sugar_to_ir.ml" "Encountered SugarFree/SugarFail expression during the IR translation stage")

(* Transforms a subterm into an IR computation, naming if necessary. *)
and transform_subterm
    (env: env)
    (x: Sugar_ast.expr)
    (k: env -> Ir.value -> Ir.comp) =
    (* env: current environment
       x: sugared expression
       k: continuation which takes a *value*
     *)
    (* Return type is an IR computation *)
    (* Call transform_expr on the sugared expression.
       Based on the result, either call continuation if the computation is
       trivial (i.e., Return v) -- keeping in mind Return v doesn't exist in
       sugared AST anymore! (Var, Lam, Constant)
     *)
    transform_expr env x (fun env c ->
        let pos = WithPos.pos x in
        let wrap v = WithPos.make ~pos v in
        match WithPos.node x with
            (* Translate syntactic values directly to avoid a needless
               administrative reduction.
             *)
            | Primitive p -> wrap (Ir.Primitive p) |> k env
            | Atom a -> wrap (Ir.Atom a) |> k env
            | Var var ->
                let v = lookup_var var env pos in
                wrap (Ir.Variable (v, None)) |> k env
            | Constant c -> wrap (Ir.Constant c) |> k env
            | Lam {linear; parameters; result_type; body} ->
                let (bnds, env') = add_names env fst parameters in
                wrap (
                    Ir.Lam {
                        linear;
                        parameters = List.combine bnds (List.map snd parameters);
                        result_type;
                        body = transform_expr env' body id }) |> k env
            (* Other expressions need to be bound to an intermediate variable *)
            | _ ->
                (* Create a new binder *)
                let bnd = Ir.Binder.make () in
                (* Create a new variable from the binder *)
                let var = Ir.Variable ((Ir.Var.of_binder bnd), None) in
                (* If we are translating an annotation, we need to create a value annotation
                   in the IR such that we do not lose the type information and needlessly resort
                   to synthesis *)
                let var' =
                    match WithPos.node x with
                        | Annotate (_, ty) -> Ir.VAnnotate (wrap var, ty)
                        | _ -> var
                in
                (* Return a 'let' expression with the binder, binding the computation,
                   and apply the continuation to the bound variable *)
                WithPos.make ~pos (Ir.Let { binder = bnd; term = c; cont = (k env (wrap var')) }))

and transform_guard :
    env ->
    Sugar_ast.guard -> Ir.guard = fun env x ->
    let guard_node = WithPos.node x in
    let pos = WithPos.pos x in
    match guard_node with
    | Receive { tag; payload_binders; mailbox_binder; cont } ->
        let (payload_bnds, env) = add_names env (id 1) payload_binders in
        let (mailbox_bnd, env') = add_name env mailbox_binder in
        let cont = transform_expr env' cont id in
        WithPos.make ~pos (
        Ir.Receive {
            tag;
            payload_binders = payload_bnds;
            mailbox_binder = mailbox_bnd;
            cont
        })
    | Empty (bnd, cont) ->
        let (mailbox_bnd, env) = add_name env bnd in
        let cont = transform_expr env cont id in
        WithPos.make ~pos (Ir.Empty (mailbox_bnd, cont))
    | GFree _ -> raise (Errors.internal_error "sugar_to_ir.ml" "Encountered Free guard during the IR translation stage")
    (* type will have been expanded into an annotation by this point *)
    | Fail _ -> WithPos.make ~pos (Ir.Fail)

and transform_list :
    env ->
    Sugar_ast.expr list ->
    (Ir.value list -> Ir.comp) ->
        (env -> Ir.comp -> Ir.comp) -> Ir.comp = fun env vals f k ->
    let rec aux env acc vals f k =
        match vals with
        | [] -> f (List.rev acc) |> k env
        | sugar_v :: sugar_vs -> transform_subterm env sugar_v (fun env v ->
            aux env (v::acc) sugar_vs f k) in
    aux env [] vals f k


(* Externally-facing function *)
let transform : Sugar_ast.program -> Ir.program = fun p ->
    transform_prog empty_env p id
