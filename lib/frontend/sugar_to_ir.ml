open Common
open Util.Utility
open Source_code

(* We don't want to import all of IR, but it's useful to use the submodules unqualified *)
module Var = Ir.Var
module VarSet = Ir.VarSet
module WithIrMetadata = Ir.WithIrMetadata

(* Helper functions *)
let get_fvs = WithIrMetadata.fvs
let with_fvs ?(pos = Position.dummy) fvs v = WithIrMetadata.make ~pos ~fvs v
let with_fv ?(pos = Position.dummy) fv v = with_fvs ~pos (VarSet.singleton fv) v

let with_val_fvs ?pos value =
    let pos = Option.value pos ~default:(WithIrMetadata.pos value) in
    WithIrMetadata.make ~pos ~fvs:(get_fvs value)
let value_list_fvs vs = List.map get_fvs vs |> VarSet.union_many
let no_fvs ?(pos = Position.dummy) v = WithIrMetadata.make ~pos ~fvs:(VarSet.empty) v


(* Transforms the sugared AST to the FGCBV IR *)
(* Takes a rather naive approach by assigning each subexpression
 * to a variable. We can likely do some administrative reductions
 * on the fly a little later.
 *)

(* Maps source-level variable names to runtime IR variables.
   decl_var_env stores top-level declaration variables. *)
type env = {
    var_env: Ir.Var.t stringmap;
    decl_var_env: Ir.Var.t stringmap;
}

let empty_env = { var_env = StringMap.empty; decl_var_env = StringMap.empty }

let is_decl_var env (v : Ir.Var.t) =
    StringMap.exists (fun _ decl_v -> decl_v = v) env.decl_var_env

let bind_var bnd env =
    { env with var_env = StringMap.add (Ir.Binder.name bnd) (Ir.Var.of_binder bnd) (env.var_env) }

let bind_vars bnds env = List.fold_left (fun acc bnd -> bind_var bnd acc) env bnds


let lookup_var key env =
    match StringMap.find_opt key (env.var_env) with
        | Some ty -> ty
        | None ->
            raise (Errors.transform_error ("Unbound variable " ^ key) [] )


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
            fun env {prog_interfaces; prog_decls; prog_body} k ->
    let stripped_decls = List.map WithPos.node prog_decls in
            let (bnds, env_with_decls) = add_names env (fun d -> d.Sugar_ast.decl_name) stripped_decls in
            let env' = { env_with_decls with decl_var_env = env_with_decls.var_env } in
    let decls = stripped_decls in
    {
        prog_interfaces = List.map (WithPos.node) prog_interfaces;
        prog_decls =
            (List.map (fun (b, d) -> transform_decl decls env' d b id)
                (List.combine bnds stripped_decls));
        prog_body =
            Option.map (fun prog_body -> transform_expr decls env' prog_body id) prog_body
    } |> k env
and transform_decl :
    Sugar_ast.decl list ->
    env ->
    Sugar_ast.decl ->
    Ir.Binder.t ->
        (env -> Ir.decl -> Ir.decl) -> Ir.decl =
            fun decls env {decl_parameters; decl_return_type; decl_body; _} decl_binder k ->
    let (bnds, env') = add_names env fst decl_parameters in
    {
        decl_name = decl_binder;
        decl_parameters = List.combine bnds (List.map snd decl_parameters);
        decl_return_type;
        decl_body = transform_expr decls env' decl_body id
    } |> k env

and transform_exprs decls env xs k = transform_exprs' decls env xs [] k
and transform_exprs' :
    Sugar_ast.decl list ->
    env ->
    Sugar_ast.expr list ->
    Ir.value list ->
    (env -> Ir.value list -> Ir.comp) -> Ir.comp
    = fun decls env es vs k ->
        match es with
            | [] -> k env (List.rev vs)
            | x :: xs ->
                transform_subterm decls env x (fun _ v ->
                    transform_exprs' decls env xs (v :: vs) k)
and transform_expr :
    Sugar_ast.decl list ->
    env ->
    Sugar_ast.expr ->
        (env -> Ir.comp -> Ir.comp) -> Ir.comp = fun decls env x k ->
    let pos = WithPos.pos x in
    let with_fvs fvs node = with_fvs ~pos fvs node in
    let with_val_fvs value node = with_val_fvs ~pos value node in
    let no_fvs node = no_fvs ~pos node in
    (* Explicit eta here to allow with_same_pos to be used polymorphically *)
    match WithPos.node x with
        (* Looks up a term-level variable in the environment,
           returns IR variable *)
        | Var v ->
            let v = lookup_var v env in
            let fvs = if is_decl_var env v then VarSet.empty else VarSet.singleton v in
            with_fvs fvs (Ir.Return (with_fvs fvs (Ir.Variable (v, None)))) |> k env
        (* Primitives are implicitly globally bound *)
        | Primitive x -> no_fvs (Ir.Return (no_fvs (Ir.Primitive x))) |> k env
        | Atom x -> no_fvs (Ir.(Return (no_fvs (Atom x)))) |> k env
        | Constant x ->
            no_fvs (Ir.Return (no_fvs (Ir.Constant x))) |> k env
        | Lam {linear; parameters; result_type; body} ->
            let (bnds, env') = add_names env fst parameters in
            let body = transform_expr decls env' body id in
            let params_vars = List.map (Ir.Var.of_binder) bnds in
            let fvs = VarSet.diff (get_fvs body) (VarSet.of_list params_vars) in
            with_fvs fvs (
            Ir.Return (with_fvs fvs (Ir.Lam {
                linear;
                parameters = List.combine bnds (List.map snd parameters);
                result_type;
                body}))) |> k env
        | Annotate (body, annotation) ->
            if Sugar_ast.is_syntactic_value body then
                transform_subterm decls env
                    body 
                    (fun env v ->
                        let v_fvs = get_fvs v in
                        with_fvs v_fvs (Ir.Return (with_fvs v_fvs (Ir.VAnnotate (v, annotation)))) |> k env)
            else
                let body' = transform_expr decls env body id in
                let fvs =  get_fvs body' in
                with_fvs fvs (Ir.Annotate (body', annotation))
                |> k env
        | Inject (name, es) ->
            transform_exprs decls env es (fun _ vs ->
                let fvs = VarSet.union_many (List.map WithIrMetadata.fvs vs) in
                with_fvs fvs (Ir.Return (with_fvs fvs (Ir.Inject (name, vs)))) |> k env)
        (* Note that annotation will have been desugared to subject annotation *)
        | Let {binder; term; body; _} ->
            (* let x = M in N*)
            (* Create an IR variable based on x *)
            let bnd = Ir.Binder.make ~name:binder () in
            (* Transform M under *old* environment *)
            (* The continuation *)
            transform_expr decls env term
                (fun env term_comp ->
                    (* Bind it in the environment *)
                    let env' = bind_var bnd env in
                    (* FVs of let: fvs(c) U fvs(cont - bnd) *)
                    let cont = transform_expr decls env' body k in
                    let bnd_var = Var.of_binder bnd in
                    let fvs =
                        VarSet.union
                            (get_fvs term_comp)
                            (VarSet.diff (get_fvs cont) (VarSet.singleton bnd_var))
                    in
                    with_fvs fvs (
                    Ir.Let {
                        binder = bnd;
                        term = term_comp;
                        cont }))
        | Tuple es ->
            transform_exprs decls env es (fun _ vs ->
                let fvs = VarSet.union_many (List.map (get_fvs) vs) in
                with_fvs fvs (Ir.Return (with_fvs fvs (Ir.Tuple vs))) |> k env)
        | LetTuple {binders = bs; term; cont; _ } ->
            (* let x = M in N*)
            (* Create IR variables based on the binders *)
            let bnds = List.map (fun name -> Ir.Binder.make ~name ()) bs in
            (* Transform M under *old* environment *)
            (* The continuation *)
            transform_subterm decls env term
                (fun env v ->
                    (* Bind it in the environment *)
                    let env' = bind_vars bnds env in
                    let binders = List.map (fun bnd -> (bnd, None)) bnds in
                    let bnd_vars = List.map Var.of_binder bnds |> VarSet.of_list in
                    let cont' = transform_expr decls env' cont k in
                    let fvs =
                        VarSet.union
                            (get_fvs v)
                            (VarSet.diff (get_fvs cont') bnd_vars)
                    in
                    with_fvs fvs (
                    Ir.LetTuple {
                        binders;
                        tuple = v;
                        cont = cont' }))
(* OLD:
        | Case {
            branch1 = ((bnd1, ty1), comp1);
            branch2 = ((bnd2, ty2), comp2) } ->
            transform_subterm decls env term (fun env v ->
                let (ir_bnd1, env1) = add_name env bnd1 in
                let (ir_bnd2, env2) = add_name env bnd2 in
                let comp1' = transform_expr decls env1 comp1 id in
                let comp2' = transform_expr decls env2 comp2 id in
                let fvs =
                    VarSet.union_many 
                        [
                            (get_fvs v);
                            (VarSet.remove (Var.of_binder ir_bnd1) (get_fvs comp1') );
                            (VarSet.remove (Var.of_binder ir_bnd2) (get_fvs comp2') );
                        ]
                in
                with_fvs fvs (
                Ir.Case {
                    term = v;
                    branch1 = (ir_bnd1, ty1), comp1';
                    branch2 = (ir_bnd2, ty2), comp2';
                }) |> k env)
*)

        | Case {
            term;
            ty;
            branches } ->
            transform_subterm decls env term (fun env v ->
                let ir_branches = List.map (fun (bnds, comp, s) ->
                    let (ir_bnds, branch_env) = add_names env (fun x -> x) bnds in
                    (ir_bnds, (transform_expr decls branch_env comp id), s)) branches in
                let fvs =
                    (* Union of FVs in branches *)
                    ir_branches
                    |> List.map (fun (bnds, comp, _) ->
                        let bnd_vars = List.map (Var.of_binder) bnds in
                        VarSet.diff (WithIrMetadata.fvs comp) (VarSet.of_list bnd_vars))
                    |> VarSet.union_many
                    (* Union with FVs in scrutinee *)
                    |> VarSet.union (WithIrMetadata.fvs v)
                in
                with_fvs fvs (
                Ir.Case {
                    term = v;
                    ty = ty;
                    branches = ir_branches;
                }) |> k env)
        | Seq (e1, e2) ->
            transform_expr decls env e1 (fun env c1 ->
            match WithIrMetadata.node c1 with
                | Ir.Return ({ node = Ir.Tuple []; _ }) ->
                    transform_expr decls env e2 k
                | _ ->
                    let c2 = transform_expr decls env e2 k in
                    let fvs = VarSet.union_many (List.map get_fvs [c1; c2]) in
                    WithIrMetadata.make ~pos ~fvs (Ir.Seq (c1, c2)))
        | App {func; args} ->
            transform_subterm decls env func (fun env funcv ->
            transform_list decls env args (fun argvs ->
                let fvs = value_list_fvs (funcv :: argvs) in
                with_fvs fvs (Ir.App { func = funcv; args = argvs })) k);
        | If {test; then_expr; else_expr} ->
                transform_subterm decls env test (fun env v ->
                let then_expr = transform_expr decls env then_expr id in
                let else_expr = transform_expr decls env else_expr id in
                let fvs = VarSet.union_many [
                    get_fvs v;
                    get_fvs then_expr;
                    get_fvs else_expr ]
                in
                with_fvs fvs (
                Ir.If {
                    test = v;
                    then_expr = then_expr;
                    else_expr = else_expr }) |> k env)
        | New i -> no_fvs (Ir.New i) |> k env
        | Spawn e ->
            let body = transform_expr decls env e id in
            with_fvs (get_fvs body) (Ir.Spawn body) |> k env
        | Free e ->
            transform_subterm decls env e (fun _ v ->
                with_val_fvs v (Ir.Free (v, None))) |> k env
        | Send {target; message; iname} ->
            let (tag, payloads) = message in
            transform_subterm decls env target (fun env pid ->
                transform_list decls env payloads (fun payload_vs ->
                    let fvs =
                        VarSet.union_many (List.map get_fvs (pid :: payload_vs))
                    in
                    with_fvs fvs (
                    Ir.Send {
                        target = pid;
                        message = (tag, payload_vs);
                        iname })) k)
        | Guard {target; pattern; guards; iname} ->
            transform_subterm decls env target (fun env v ->
                let gs = List.map (fun x -> transform_guard decls env x) guards in
                let g_fvs = List.map get_fvs gs in
                let fvs = VarSet.union_many ((get_fvs v) :: g_fvs) in
                with_fvs fvs (
                Ir.Guard {
                    target = v;
                    pattern;
                    guards = gs;
                    iname
                }) |> k env )
        |  SugarFail (_, _) -> (* shouldn't ever match *)
                raise (Errors.internal_error "sugar_to_ir.ml" "Encountered SugarFail expression during the IR translation stage")
(* Transforms an expression into a syntactic value, if possible *)
and transform_syntactic_value
    (decls: Sugar_ast.decl list)
    (env: env)
    (x: Sugar_ast.expr)
    (* : Ir.value option *)
    =
    let pos = WithPos.pos x in
    let with_fvs fvs node = with_fvs ~pos fvs node in
    let with_val_fvs value node = with_val_fvs ~pos value node in
    let no_fvs node = no_fvs ~pos node in
    let transform_many f xs =
        List.map (transform_syntactic_value decls env) xs
                |> sequence_options
                |> Option.map (fun vs ->
                    let fvs = value_list_fvs vs in
                    f fvs vs)
    in
    match WithPos.node x with
        | Var var ->
             let v = lookup_var var env in
                            let fvs = if is_decl_var env v then VarSet.empty else VarSet.singleton v in
               Some (with_fvs fvs @@ Ir.Variable (v, None))
        | Atom x -> Some (no_fvs @@ Ir.Atom x)
        | Primitive x -> Some (no_fvs @@ Ir.Primitive x)
        | Constant x -> Some (no_fvs @@ Ir.Constant x)
        | Lam {linear; parameters; result_type; body} ->
            let (bnds, env') = add_names env fst parameters in
            let body' = transform_expr decls env' body id in
            let fvs = VarSet.remove_many (get_fvs body') (List.map Var.of_binder bnds) in
            Some (
                with_fvs fvs @@  
                    Ir.Lam {
                        linear;
                        parameters = List.combine bnds (List.map snd parameters);
                        result_type;
                        body = body'
                    })
        | Annotate (e, ty) -> 
            Option.map
                (fun v -> with_val_fvs v @@ Ir.VAnnotate (v, ty))
                (transform_syntactic_value decls env e)
        | Inject (s, xs) ->
            transform_many (fun fvs vs ->
                with_fvs fvs <| Ir.Inject (s, vs)
            ) xs
        | Tuple xs ->
            transform_many (fun fvs vs ->
                with_fvs fvs <| Ir.Tuple vs
            ) xs
        | _ -> None
(* Transforms a subterm into an IR computation, naming if necessary. *)
and transform_subterm
    (decls: Sugar_ast.decl list)
    (env: env)
    (x: Sugar_ast.expr)
    (k: env -> Ir.value -> Ir.comp) =
    (* env: current environment
       x: sugared expression
       k: continuation which takes a *value*
       Return type is an IR computation
     *)
    (* If we have a syntactic value already then we can just do the direct conversion *)
    let pos = WithPos.pos x in
    let with_fvs fvs node = with_fvs ~pos fvs node in
    let with_fv fv node = with_fv ~pos fv node in
    match transform_syntactic_value decls env x with
        | Some value -> k env value
        | None ->
            (* Otherwise we need to insert a binder *)
            transform_expr decls env x (fun env c ->
                (* Create a new binder *)
                let bnd = Ir.Binder.make () in
                let bnd_var = Ir.Var.of_binder bnd in
                (* Create a new variable from the binder *)
                let var = Ir.Variable (bnd_var, None) in
                (* If we are translating an annotation, we need to create a value annotation
                   in the IR such that we do not lose the type information and needlessly resort
                   to synthesis *)
                let var' =
                    match WithPos.node x with
                        | Annotate (_, ty) ->
                            Ir.VAnnotate (with_fv bnd_var var, ty)
                        | _ -> var
                in
                let cont' = k env (with_fvs (VarSet.singleton bnd_var) var') in
                let fvs = VarSet.union
                    (WithIrMetadata.fvs c) 
                    (VarSet.remove bnd_var (get_fvs cont'))
                in
                (* Return a 'let' expression with the binder, binding the computation,
                   and apply the continuation to the bound variable *)
                (* WithPos.make ~pos (Ir.Let { binder = bnd; term = c; cont = (k env (wrap var')) })) *)
                WithIrMetadata.make ~pos ~fvs (Ir.Let {
                    binder = bnd;
                    term = c;
                    cont = cont' }))

and transform_guard :
    Sugar_ast.decl list ->
    env ->
    Sugar_ast.guard -> Ir.guard = fun decls env x ->
    let pos = WithPos.pos x in
    let with_fvs fvs node = with_fvs ~pos fvs node in
    let no_fvs node = no_fvs ~pos node in
    let guard_node = WithPos.node x in
    match guard_node with
    | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
        let (payload_bnds, env) = add_names env (id 1) payload_binders in
        let (mailbox_bnd, env') = add_name env mailbox_binder in
        let cont = transform_expr decls env' cont id in
        let bnd_vars = List.map (Var.of_binder) (mailbox_bnd :: payload_bnds) in
        let fvs = VarSet.diff (get_fvs cont) (VarSet.of_list bnd_vars) in
        with_fvs fvs (
        Ir.Receive {
            tag;
            payload_binders = payload_bnds;
            mailbox_binder = mailbox_bnd;
            strategy;
            cont
        })
    | Empty (bnd, cont) ->
        let (mailbox_bnd, env) = add_name env bnd in
        let cont = transform_expr decls env cont id in
        let fvs = VarSet.remove (Var.of_binder mailbox_bnd) (get_fvs cont) in
        with_fvs fvs (Ir.Empty (mailbox_bnd, cont))
    | GFree _ -> raise (Errors.internal_error "sugar_to_ir.ml" "Encountered Free guard during the IR translation stage")
    (* type will have been expanded into an annotation by this point *)
    | Fail _ -> no_fvs Ir.Fail

and transform_list :
    Sugar_ast.decl list ->
    env ->
    Sugar_ast.expr list ->
    (Ir.value list -> Ir.comp) ->
        (env -> Ir.comp -> Ir.comp) -> Ir.comp = fun decls env vals f k ->
    let rec aux decls env acc vals f k =
        match vals with
        | [] -> f (List.rev acc) |> k env
        | sugar_v :: sugar_vs -> transform_subterm decls env sugar_v (fun env v ->
            aux decls env (v::acc) sugar_vs f k) in
    aux decls env [] vals f k


(* Externally-facing function *)
let transform : Sugar_ast.program -> Ir.program = fun p ->
    transform_prog empty_env p id
