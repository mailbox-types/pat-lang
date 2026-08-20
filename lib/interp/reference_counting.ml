open Common
open Ir
open Util.Utility

module VarMultiset = Multiset.Make(Var)

let get_fvs = Ir.WithIrMetadata.fvs

let pp_varset ppf s =
    Format.pp_print_string ppf "{";
    VarSet.iter (fun v -> Format.fprintf ppf "%a " Var.pp v) s;
    Format.pp_print_string ppf "}"


(* Let-insertion: ensures the subject of a Case, LetTuple, or function
   application is always a bare variable, hoisting it into a fresh
   let-binding otherwise. Required before reference counting / evaluation
   in order to better support Perceus heap semantics. Also simplifies the pass. *)
let bind_subject (comp : comp) (subject : value) (rest_fvs : varset) (rebuild : value -> comp_node) : comp =
    match WithIrMetadata.node subject with
        | Variable _ -> comp
        | _ ->
            let binder = Binder.make () in
            let var = Var.of_binder binder in
            let var_val = WithIrMetadata.make ~fvs:(VarSet.singleton var) (Variable (var, None)) in
            let term = WithIrMetadata.make ~fvs:(get_fvs subject) (Return subject) in
            let cont = WithIrMetadata.make ~fvs:(VarSet.add var rest_fvs) (rebuild var_val) in
            { comp with node = Let { binder; term; cont } }

let let_insert : comp -> comp =
    let visitor =
        object
            inherit [_] Ir.map as super

            method! visit_comp env comp =
                let comp = super#visit_comp env comp in
                match WithIrMetadata.node comp with
                    | App { func; args } ->
                        let rest_fvs = List.fold_left (fun acc a -> VarSet.union acc (get_fvs a)) VarSet.empty args in
                        bind_subject comp func rest_fvs (fun func -> App { func; args })
                    | LetTuple { binders; tuple; cont } ->
                        let bnd_vars = binders |> List.map (fun (b, _) -> Var.of_binder b) |> VarSet.of_list in
                        let rest_fvs = VarSet.diff (get_fvs cont) bnd_vars in
                        bind_subject comp tuple rest_fvs (fun tuple -> LetTuple { binders; tuple; cont })
                    | Case { term; ty; branches } ->
                        let rest_fvs =
                            branches
                            |> List.map (fun (params, body, _) ->
                                let bound_vars = List.map Var.of_binder params |> VarSet.of_list in
                                VarSet.diff (get_fvs body) bound_vars)
                            |> VarSet.union_many
                        in
                        bind_subject comp term rest_fvs (fun term -> Case { term; ty; branches })
                    | _ -> comp

            method visit_t _env x = x
        end
    in
    visitor#visit_comp ()

let unwrap_var = function
    | Variable (v, _) -> v
    | _ -> raise <| Errors.internal_error "reference_counting.ml" "Tried to unwrap non-variable."

let insert_dup (dups : (Var.t * int) list) (comp : Evaluation_ir.comp) : Evaluation_ir.comp =
    let open Evaluation_ir in
    if List.is_empty dups then
        comp
    else
        Seq (Dup dups, comp)

let insert_drop ?(names = []) (drops : (Var.t * int) list) (comp : Evaluation_ir.comp) : Evaluation_ir.comp =
    let open Evaluation_ir in
    if List.is_empty drops && List.is_empty names then
        comp
    else
        Seq (Drop { vars = drops; names }, comp)


let mk_var_drop vars comp =
    insert_drop (VarSet.elements vars |> List.map (fun v -> (v, 1))) comp

let rec insert_reference_counting_comp decls borrowed owned comp : Evaluation_ir.comp =
    let irc = insert_reference_counting_comp decls in
    let ircv borrowed owned v = 
        let (dups, v') = insert_reference_counting_val decls borrowed owned v in
        (VarMultiset.bindings dups, v')
    in
    let ircg borrowed guards_owned g = insert_reference_counting_guard decls borrowed guards_owned g in
    match WithIrMetadata.node comp with
        | Annotate (c, _ty) ->
            (* Evaluation_ir discards type annotations entirely *)
            irc borrowed owned c
        | Let { binder; term; cont } ->
            let binder_var = Var.of_binder binder in
            let cont_fvs = get_fvs cont in
            let e2_owned = VarSet.(inter owned (diff cont_fvs (singleton binder_var))) in
            let e1_owned = VarSet.diff owned e2_owned in
            let e1_trans = irc borrowed e1_owned term in
            let e2_trans = irc borrowed (VarSet.(union e2_owned (singleton binder_var))) cont in
            (* Insert a drop if binder is unused in e2 *)
            if VarSet.mem binder_var cont_fvs then
                Evaluation_ir.Let { binder; term = e1_trans; cont = e2_trans }
            else
                let e2_trans_with_drop = insert_drop [ (binder_var, 1) ] e2_trans in
                Evaluation_ir.Let { binder; term = e1_trans; cont = e2_trans_with_drop }
        | Seq (e1, e2) ->
            (* e2_owned : owned environment of e2. Calculated by the intersection of owned environment and FVs of e2. *)
            let e2_owned = VarSet.inter owned (get_fvs e2) in
            (* e1_borrowed: borrowed env for typing e1. union of borrowed variables and e2_owned *)
            let e1_borrowed = VarSet.union borrowed e2_owned in
            (* e1_owned: everything in owned environment that's not in e2_owned. *)
            let e1_owned = VarSet.diff owned e2_owned in
            (* e2_borrowed is just the current borrowed refs. *)
            let e2_borrowed = borrowed in
            let e1' = irc e1_borrowed e1_owned e1 in
            let e2' = irc e2_borrowed e2_owned e2 in
            Evaluation_ir.Seq (e1', e2')
        | Return v ->
            let (dups, v') = ircv borrowed owned v in
            insert_dup dups (Evaluation_ir.Return v')
        | App { func; args } ->
            (* func is guaranteed a bare variable post let-insertion *)
            let func_var = unwrap_var (WithIrMetadata.node func) in
            let (dups, args') = transform_val_sequence decls borrowed owned args in
            insert_dup (VarMultiset.bindings dups) (Evaluation_ir.App { func = func_var; args = args' })
        (* When doing branching control flow: when processing each subexpression, owned environment is the
              intersection of the current owned environment and the free variables of the subexpression.
              Then in the body, drop everything that is in the owned environment but not the current environment.
              Borrowed environment is just the current borrowed environment. *)
        (* The 'match' schema in the Perceus paper has a variable literal as the scrutinee.
           'If' is a specialisation of that rule. Drops will ensure same FVs in each branch. Then we can just
            say that the borrowed environment for the test is the union of the borrowed env and the owned env of the branches. *)
        | If { test; then_expr; else_expr } ->
            let branches_owned = VarSet.inter owned
                (VarSet.union
                    (get_fvs then_expr)
                    (get_fvs else_expr)) in
            (* Drop everything in the branches_owned set that is not in the current *)
            let test_borrowed = VarSet.union borrowed branches_owned in
            let test_owned = VarSet.diff owned branches_owned in
            let (dups, translated_test) = ircv test_borrowed test_owned test in

            let then_owned = VarSet.inter branches_owned (get_fvs then_expr) in
            let else_owned = VarSet.inter branches_owned (get_fvs else_expr) in
            let translated_then = irc borrowed then_owned then_expr in
            let translated_else = irc borrowed else_owned else_expr in

            let final_then_expr = mk_var_drop (VarSet.diff branches_owned then_owned) translated_then in
            let final_else_expr = mk_var_drop (VarSet.diff branches_owned else_owned) translated_else in
            insert_dup dups
                (Evaluation_ir.If { test = translated_test; then_expr = final_then_expr; else_expr = final_else_expr })
        | LetTuple { binders; tuple; cont } ->
            (* tuple is guaranteed a bare variable post let-insertion *)
            let tuple_var = unwrap_var (WithIrMetadata.node tuple) in
            let cont_fvs = get_fvs cont in
            let binders_set = 
                binders
                    |> List.map (Var.of_binder << fst)
                    |> VarSet.of_list
            in
            let cont_owned = VarSet.(
                inter owned
                    (diff cont_fvs binders_set)
            )
            in
            (* cont_drop: everything in binders that isn't used in cont *)
            let cont_drop = VarSet.diff binders_set cont_fvs in
            let translated_cont =  irc borrowed cont_owned cont in
            let final_translated_cont = mk_var_drop cont_drop translated_cont in
            Evaluation_ir.LetTuple { binders = List.map fst binders; tuple = tuple_var; cont = final_translated_cont }
        | Case { term; branches; _ } ->
            let var = unwrap_var (WithIrMetadata.node term) in
            let mk_drop vars transformed_comp =
                let var_list =
                    VarSet.elements vars
                    |> List.map (fun v -> (v, 1))
                in
                insert_drop var_list transformed_comp
            in
            (* The owned set of each branch is the owned environment overall,
               extended with bound vars, intersected with FVs of body*)
            (* Collect all envs along with transformed (incl. drops) bodies *)
            let transformed_branches =
                List.map (fun (params, comp, constr)  ->
                    let params_vars = List.map Var.of_binder params |> VarSet.of_list in
                    let owned_with_params = VarSet.union owned params_vars in
                    let comp_owned =
                        VarSet.inter
                            owned_with_params
                            (WithIrMetadata.fvs comp)
                    in
                    let to_drop = VarSet.diff owned_with_params comp_owned in
                    let transformed_comp =
                        mk_drop 
                            to_drop
                            (irc borrowed comp_owned comp)
                    in
                    (params, transformed_comp, constr)
                ) branches
            in
            Evaluation_ir.Case { scrutinee = var; branches = transformed_branches }
        | New interface ->
            Evaluation_ir.New interface
        | Spawn e ->
            (* We need any reference counting that's done inside the expression
               to happen in the parent thread, **not** the spawned thread. Otherwise we end up
               with a concurrency bug: required duplications will be deferred until the 
               spawned thread is scheduled. By hoisting any duplications to the parent thread we
               ensure the continuation is evaluated in a consistent state regardless of scheduling. *)
            let counted_body = irc borrowed owned e in
            begin
                match counted_body with
                    | Evaluation_ir.Seq ((Evaluation_ir.Dup _ as dup_node), e2) ->
                        Evaluation_ir.Seq (dup_node, Evaluation_ir.Spawn e2)
                    | _ -> Evaluation_ir.Spawn counted_body
            end
        | Send { target; message = (tag, message_values); iname } -> 
            begin
                match transform_val_sequence decls borrowed owned (target :: message_values) with
                    | (dups, target' :: message_values') ->
                        insert_dup (VarMultiset.bindings dups)
                            (Evaluation_ir.Send { target = target'; message = (tag, message_values'); iname = Option.get iname })
                    (* impossible; transform_val_sequence always gives the same number of values back *)
                    | _ -> assert false
            end
        | Free (v, iname) ->
            let (dups, v') = ircv borrowed owned v in
            insert_dup dups (Evaluation_ir.Free (v', Option.get iname))
        | Guard { target; pattern; guards; iname } ->
            let guards_fvs =
                List.fold_left
                    (fun acc g -> VarSet.union acc (get_fvs g))
                    VarSet.empty
                    guards
            in
            let guards_owned = VarSet.inter owned guards_fvs in
            let target_borrowed = VarSet.union borrowed guards_owned in
            let target_owned = VarSet.diff owned guards_owned in
            let (dups, translated_target) = ircv target_borrowed target_owned target in
            let translated_guards = List.map (ircg borrowed guards_owned) guards in
            insert_dup dups
                (Evaluation_ir.Guard { target = translated_target; pattern; guards = translated_guards; iname = Option.get iname })
(* Helper function to annotate an ordered sequence of values. We need to consider all subsequent
    variables used in a sequence as borrowed. The best way of doing this is to reverse the
    list of variables and keep the borrow set as an accumulator, then reverse again at the end. *)
and transform_val_sequence decls borrowed owned vs =
    let rec transform_vals fvs_acc = function
        | [] -> ([], VarMultiset.empty)
        | (cur_val :: vals) ->
            let cur_borrowed = VarSet.union borrowed fvs_acc in
            let cur_owned = VarSet.(inter (diff owned fvs_acc) (get_fvs cur_val)) in 
            let (new_dups, transformed_val) =
                insert_reference_counting_val decls cur_borrowed cur_owned cur_val
            in
            let (remaining_vals, remaining_dups) =
                transform_vals
                    (VarSet.union fvs_acc cur_owned)
                    vals
            in
            (transformed_val :: remaining_vals, VarMultiset.combine new_dups remaining_dups)
    in
    let (transformed_vals_rev, dups) =
        transform_vals VarSet.empty (List.rev vs)
    in
    (dups, List.rev transformed_vals_rev)
(* Since we're in FGCBV, we need to depart from the Perceus algorithm slightly.
Rules like `D,x | . |- x ~~> dup x; x` no longer work as we are making a value into a computation.
We can only ever return syntactic values.
Instead we return a set of variables to dup (drops only happen on computations, which is fine);
then we can insert the dups next to the computation.

As an example, consider the following code fragment:
  x ! M(y); guard y { ... }
According to the original Perceus algorithm the generated code would be:
  x ! M(dup y; y); guard y { ... }

However this doesn't work because we can only send syntactic values. Instead we'd generate:
  dup y;
  x ! M(y); guard y { ... }
It's not as exactly local as Perceus but it's safe.
*)
and insert_reference_counting_val decls borrowed owned value : VarMultiset.t * Evaluation_ir.value =
    let decl_vars =
        decls |> List.map Var.of_binder |> VarSet.of_list
    in
    match WithIrMetadata.node value with
        | VAnnotate (v, _ty) ->
            (* Evaluation_ir discards type annotations entirely *)
            insert_reference_counting_val decls borrowed owned v
        | Atom s -> (VarMultiset.empty, Evaluation_ir.Atom s)
        | Constant c -> (VarMultiset.empty, Evaluation_ir.Constant c)
        | Primitive p -> (VarMultiset.empty, Evaluation_ir.Primitive p)
        | Name n -> (VarMultiset.empty, Evaluation_ir.Name n)
        | Inject (s, vs) ->
            let (dups, vs') = transform_val_sequence decls borrowed owned vs in 
            (dups, Evaluation_ir.Inject (s, vs'))
        | Variable (x, _) ->
            if VarSet.mem x owned || VarSet.mem x decl_vars then
              (* Owned or global declaration -- no dup needed *)
              (VarMultiset.empty, Evaluation_ir.Variable x)
            else
              (VarMultiset.singleton x, Evaluation_ir.Variable x)
        | Tuple vs -> 
            let (dups, vs') = transform_val_sequence decls borrowed owned vs in 
            (dups, Evaluation_ir.Tuple vs')
        | Lam { linear = _; parameters; result_type = _; body } ->
            let fvs = get_fvs value in
            let body_fvs = get_fvs body in
            let (used_vars, unused_vars) =
                List.partition
                    (fun v -> VarSet.mem v body_fvs)
                    (List.map (fun (p, _) -> Ir.Var.of_binder p ) parameters)
            in
            (* Transform expression under empty borrowed environment; owned environment of
               fvs (of *whole* lambda -- not just body!) + used parameters *)
            let body_owned_vars = VarSet.union fvs (VarSet.of_list used_vars) in
            (* to_drop: FVs not in owned environment *)
            let to_dup = VarSet.diff fvs owned |> VarSet.to_list |> VarMultiset.of_list in
            let to_drop = List.map (fun v -> (v, 1)) unused_vars in
            let body_trans = insert_reference_counting_comp decls VarSet.empty body_owned_vars body in
            let transformed_body = insert_drop to_drop body_trans in
            (to_dup, Evaluation_ir.Lam { parameters = List.map fst parameters; fvs; body = transformed_body })
and insert_reference_counting_guard decls borrowed guards_owned guard : Evaluation_ir.guard =
    let irc borrowed owned c = insert_reference_counting_comp decls borrowed owned c in
    match WithIrMetadata.node guard with
        | Receive { tag; payload_binders; mailbox_binder; strategy = _; cont } ->
            let binders_set =
                mailbox_binder :: payload_binders
                |> List.map Var.of_binder
                |> VarSet.of_list
            in
            let cont_fvs = get_fvs cont in
            (* Variables owned by all guards + binders *)
            let guards_owned_with_binders = VarSet.union guards_owned binders_set in
            (* owned env: intersection of this environment with vars actually used *)
            let cont_owned = VarSet.inter guards_owned_with_binders cont_fvs in
            (* to drop: all vars incl. binders minus what is actually used *)
            let cont_drop = VarSet.diff guards_owned_with_binders cont_owned in
            let translated_cont = irc borrowed cont_owned cont in
            let final_cont = mk_var_drop cont_drop translated_cont in
            Evaluation_ir.Receive { tag; payload_binders; mailbox_binder; cont = final_cont }
        (* Similar to case-expressions, just processed in isolation *)
        | Empty (binder, e) ->
            let binder_var = Var.of_binder binder in
            let e_fvs = get_fvs e in
            let guards_owned_plus_binder = VarSet.union guards_owned (VarSet.singleton binder_var) in
            let e_owned =
                VarSet.inter guards_owned_plus_binder e_fvs
            in
            let e_drop = VarSet.diff guards_owned_plus_binder e_owned in
            let translated_e = irc borrowed e_owned e in
            let final_e = mk_var_drop e_drop translated_e in
            Evaluation_ir.Empty (binder, final_e)
        | Fail ->
            Evaluation_ir.Fail

let insert_reference_counting prog : Evaluation_ir.program =
    let decls =
        prog.prog_decls
        |> List.map (fun (decl : Ir.decl) -> decl.decl_name)
    in
    let transform_body c =
        let c = let_insert c in
        insert_reference_counting_comp
            decls
            Ir.VarSet.empty
            Ir.VarSet.empty
            c
    in
    let transform_decl (decl : Ir.decl) : Evaluation_ir.decl =
        let decl_body = let_insert decl.decl_body in
        let parameter_vars =
            decl.decl_parameters
            |> List.map (fun (b, _) -> Ir.Var.of_binder b)
        in
        let body_fvs = get_fvs decl_body in
        let (used_params, unused_params) =
            List.partition (fun v -> VarSet.mem v body_fvs) parameter_vars
        in
        let body_owned_vars = used_params |> Ir.VarSet.of_list in
        let body_trans =
            insert_reference_counting_comp decls Ir.VarSet.empty body_owned_vars decl_body
        in
        let decl_body = insert_drop (List.map (fun v -> (v, 1)) unused_params) body_trans in
        {
            Evaluation_ir.decl_name = decl.decl_name;
            decl_parameters = List.map fst decl.decl_parameters;
            decl_body;
        }
    in
    {
        Evaluation_ir.prog_decls = List.map transform_decl prog.prog_decls;
        prog_body = Option.map transform_body prog.prog_body;
    }