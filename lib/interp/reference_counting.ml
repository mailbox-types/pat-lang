open Common
open Ir
open Util.Utility

module VarMultiset = Multiset.Make(Var)

let get_fvs = Ir.WithIrMetadata.fvs

let pp_varset ppf s =
    Format.pp_print_string ppf "{";
    VarSet.iter (fun v -> Format.fprintf ppf "%a " Var.pp v) s;
    Format.pp_print_string ppf "}"

let rec insert_reference_counting_comp decls borrowed owned comp =
    let irc = insert_reference_counting_comp decls in
    let ircv borrowed owned v = 
        let (dups, v') = insert_reference_counting_val decls borrowed owned v in
        (VarMultiset.bindings dups, v')
    in
    let ircg borrowed guards_owned g = insert_reference_counting_guard decls borrowed guards_owned g in
    match WithIrMetadata.node comp with
        | Annotate (c, ty) ->
            let c' = irc borrowed owned c in
            let fvs = get_fvs c' in
            WithIrMetadata.make ~fvs (Annotate (c', ty))
        | Let { binder; term; cont } ->
            let binder_var = Var.of_binder binder in
            let cont_fvs = get_fvs cont in
            let e2_owned = VarSet.(inter owned (diff cont_fvs (singleton binder_var))) in
            let e1_owned = VarSet.diff owned e2_owned in
            let e1_trans = irc borrowed e1_owned term in
            (* Insert a drop if binder is unused in e2 *)
            if VarSet.mem binder_var cont_fvs then
                let e2_trans = irc borrowed (VarSet.(union e2_owned (singleton binder_var))) cont in
                let fvs = VarSet.union (get_fvs e1_trans) (get_fvs e2_trans) in
                WithIrMetadata.make ~fvs (Let { binder; term = e1_trans; cont = e2_trans })
            else
                let e2_trans = irc borrowed (VarSet.(union e2_owned (singleton binder_var))) cont in
                let drop_node =
                    WithIrMetadata.make ~fvs:(VarSet.singleton binder_var)
                        (Drop { vars = [ (binder_var, 1) ]; names = [] })
                in
                let e2_trans_with_drop = 
                    let fvs = VarSet.union (get_fvs drop_node) (get_fvs e2_trans) in
                    WithIrMetadata.make ~fvs (Seq (drop_node, e2_trans))
                in
                let fvs = VarSet.union (get_fvs e1_trans) (get_fvs e2_trans_with_drop) in
                WithIrMetadata.make ~fvs (Let { binder; term = e1_trans; cont = e2_trans_with_drop })
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
            let fvs = VarSet.union (get_fvs e1') (get_fvs e2') in
            WithIrMetadata.make ~fvs (Seq (e1', e2'))
        | Return v ->
            let (dups, v') = ircv borrowed owned v in
            let return_node = WithIrMetadata.make ~fvs:(get_fvs v') (Return v') in
            Ir.insert_dup dups return_node
        | App { func; args } ->
            begin
                match transform_val_sequence decls borrowed owned (func :: args) with
                    | (dups, func' :: args') ->
                        let dups_list = VarMultiset.bindings dups in
                        let fvs = List.fold_left (fun acc v -> VarSet.union acc (get_fvs v)) VarSet.empty (func' :: args') in
                        Ir.insert_dup dups_list (WithIrMetadata.make ~fvs (App { func = func'; args = args' }))
                    (* impossible; transform_val_sequence always gives the same number of values back *)
                    | _ -> assert false
            end
        (* When doing branching control flow: when processing each subexpression, owned environment is the
              intersection of the current owned environment and the free variables of the subexpression.
              Then in the body, drop everything that is in the owned environment but not the current environment.
              Borrowed environment is just the current borrowed environment. *)
        (* The 'match' schema in the Perceus paper rather unhelpfully has a variable literal as the scrutinee.
           However this isn't too big a deal -- drops will ensure same FVs in each branch. Then we can just
            say that the borrowed environment for the test is the union of the borrowed env and the owned env of the branches. *)
        | If { test; then_expr; else_expr } ->
            let branches_owned = VarSet.inter owned
                (VarSet.union
                    (get_fvs then_expr)
                    (get_fvs else_expr)) in
            let mk_drop vars cont =
                let var_list =
                    vars
                    |> VarSet.elements
                    |> List.map (fun v -> (v, 1))
                in
                Ir.insert_drop var_list cont
            in
            (* Drop everything in the branches_owned set that is not in the current *)
            let test_borrowed = VarSet.union borrowed branches_owned in
            let test_owned = VarSet.diff owned branches_owned in
            let (dups, translated_test) = ircv test_borrowed test_owned test in

            let then_owned = VarSet.inter branches_owned (get_fvs then_expr) in
            let else_owned = VarSet.inter branches_owned (get_fvs else_expr) in
            let translated_then = irc borrowed then_owned then_expr in
            let translated_else = irc borrowed else_owned else_expr in

            let final_then_expr = mk_drop (VarSet.diff branches_owned then_owned) translated_then in
            let final_else_expr = mk_drop (VarSet.diff branches_owned else_owned) translated_else in
            let fvs = VarSet.union (get_fvs translated_test) (VarSet.union (get_fvs final_then_expr) (get_fvs final_else_expr)) in
            let translated_if = 
                WithIrMetadata.make ~fvs (If { 
                    test = translated_test; then_expr = final_then_expr; else_expr = final_else_expr })
            in
            Ir.insert_dup dups translated_if
        | LetTuple { binders; tuple; cont } ->
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
            let tuple_borrowed = VarSet.union borrowed cont_owned in
            let tuple_owned = VarSet.diff owned tuple_borrowed in
            let (dups, translated_tuple) = ircv tuple_borrowed tuple_owned tuple in
            let translated_cont =  irc borrowed cont_owned cont in
            let final_translated_cont = 
                if VarSet.is_empty cont_drop then
                    translated_cont
                else
                    (* Drop binders if variables unused *)
                    let drop_node =
                        WithIrMetadata.make ~fvs:cont_drop
                            (Drop { vars = (VarSet.to_list cont_drop |> List.map (fun v -> (v, 1))); names = [] })
                    in
                    let fvs = VarSet.union (get_fvs drop_node) (get_fvs translated_cont) in
                    WithIrMetadata.make ~fvs (Seq (drop_node, translated_cont))
                in
            let translated_let_tuple =
                let fvs = VarSet.union (get_fvs translated_tuple) (get_fvs final_translated_cont) in
                WithIrMetadata.make ~fvs (LetTuple { binders; tuple = translated_tuple; cont = final_translated_cont })
            in
            Ir.insert_dup dups translated_let_tuple
        | Case { term; branch1 = ((bnd1, ty1), e1); branch2 = ((bnd2, ty2), e2) } ->
            let bnd1_var = Var.of_binder bnd1 in
            let bnd2_var = Var.of_binder bnd2 in
            let e1_fvs = get_fvs e1 in
            let e2_fvs = get_fvs e2 in
            let e1_owned = VarSet.inter (VarSet.union owned (VarSet.singleton bnd1_var)) e1_fvs in
            let e2_owned = VarSet.inter (VarSet.union owned (VarSet.singleton bnd2_var)) e2_fvs in
            let e1_owned_without_binder = VarSet.diff e1_owned (VarSet.singleton bnd1_var) in
            let e2_owned_without_binder = VarSet.diff e2_owned (VarSet.singleton bnd2_var) in
            (* branches_owned: all owned variables occurring in either branch *)
            let branches_owned =
                VarSet.inter owned (VarSet.union e1_owned_without_binder e2_owned_without_binder)
            in
            let mk_drop vars =
                let var_list =
                    VarSet.elements vars
                    |> List.map (fun v -> (v, 1))
                in
                WithIrMetadata.make ~fvs:vars (Drop { vars = var_list; names = [] })
            in
            (* ei_drop: variables owned by branches (+binder), but not used. 
               ensures variables are dropped if they're not used in that branch. *)
            let e1_drop = mk_drop (
                VarSet.diff 
                    (VarSet.union branches_owned (VarSet.singleton (Var.of_binder bnd1)))
                    e1_owned
            )
            in
            let e2_drop = mk_drop (
                VarSet.diff 
                    (VarSet.union branches_owned (VarSet.singleton (Var.of_binder bnd2)))
                    e2_owned
            )
            in
            (* borrowed variables for the term: borrowed variables + variables used in branches *)
            let term_borrowed = VarSet.union borrowed branches_owned in
            let term_owned = VarSet.diff owned branches_owned in
            let (dups, translated_term) = ircv term_borrowed term_owned term in
            let translated_e1 = irc borrowed e1_owned e1 in
            let translated_e2 = irc borrowed e2_owned e2 in
            let final_e1_fvs = VarSet.union (get_fvs e1_drop) (get_fvs translated_e1) in
            let final_e2_fvs = VarSet.union (get_fvs e2_drop) (get_fvs translated_e2) in
            let final_e1 =
                WithIrMetadata.make ~fvs:final_e1_fvs (Seq (e1_drop, translated_e1))
            in
            let final_e2 =
                WithIrMetadata.make ~fvs:final_e2_fvs (Seq (e2_drop, translated_e2))
            in
            let translated_case_fvs = VarSet.union (get_fvs translated_term) (VarSet.union (get_fvs final_e1) (get_fvs final_e2)) in
            let translated_case =
                WithIrMetadata.make ~fvs:translated_case_fvs (Case {
                    term = translated_term;
                    branch1 = ((bnd1, ty1), final_e1);
                    branch2 = ((bnd2, ty2), final_e2)
                })
            in
            Ir.insert_dup dups translated_case
        | CaseL { term; ty; nil; cons = ((bnd1, bnd2), e) } ->
            let bnd1_var = Var.of_binder bnd1 in
            let bnd2_var = Var.of_binder bnd2 in
            let nil_fvs = get_fvs nil in
            let cons_fvs = get_fvs e in
            let nil_owned = VarSet.inter owned nil_fvs in
            let cons_owned =
                VarSet.inter
                    (VarSet.union owned (VarSet.of_list [bnd1_var; bnd2_var]))
                    cons_fvs
            in
            let cons_owned_without_binders =
                VarSet.diff cons_owned (VarSet.of_list [bnd1_var; bnd2_var])
            in
            (* branches_owned: all owned variables occurring in either branch *)
            let branches_owned =
                VarSet.inter owned (VarSet.union nil_fvs cons_owned_without_binders)
            in
            let mk_drop vars =
                let var_list =
                    VarSet.elements vars
                    |> List.map (fun v -> (v, 1))
                in
                WithIrMetadata.make ~fvs:vars (Drop { vars = var_list; names = [] })
            in
            let nil_drop = mk_drop (VarSet.diff branches_owned nil_owned) in
            let cons_drop = mk_drop (
                VarSet.diff
                    (VarSet.union branches_owned (VarSet.of_list [bnd1_var; bnd2_var]))
                    cons_owned
            )
            in
            (* borrowed variables for the term: borrowed variables + variables used in branches *)
            let term_borrowed = VarSet.union borrowed branches_owned in
            let term_owned = VarSet.diff owned branches_owned in
            let (dups, translated_term) = ircv term_borrowed term_owned term in
            let translated_nil = irc borrowed nil_owned nil in
            let translated_cons = irc borrowed cons_owned e in
            let final_nil_fvs = VarSet.union (get_fvs nil_drop) (get_fvs translated_nil) in
            let final_cons_fvs = VarSet.union (get_fvs cons_drop) (get_fvs translated_cons) in
            let final_nil =
                WithIrMetadata.make ~fvs:final_nil_fvs (Seq (nil_drop, translated_nil))
            in
            let final_cons =
                WithIrMetadata.make ~fvs:final_cons_fvs (Seq (cons_drop, translated_cons))
            in
            let translated_case_l_fvs = VarSet.union (get_fvs translated_term) (VarSet.union (get_fvs final_nil) (get_fvs final_cons)) in
            let translated_case_l =
                WithIrMetadata.make ~fvs:translated_case_l_fvs (CaseL {
                    term = translated_term;
                    ty;
                    nil = final_nil;
                    cons = ((bnd1, bnd2), final_cons)
                })
            in
            Ir.insert_dup dups translated_case_l
        | New interface ->
            WithIrMetadata.make ~fvs:VarSet.empty (New interface)
        | Spawn e ->
            (* We need any reference counting that's done inside the expression
               to happen in the parent thread, **not** the spawned thread. Otherwise we end up
               with a concurrency bug: required duplications will be deferred until the 
               spawned thread is scheduled. By hoisting any duplications to the parent thread we
               ensure the continuation is evaluated in a consistent state regardless of scheduling. *)
            let counted_body = irc borrowed owned e in
            let unchanged = WithIrMetadata.make ~fvs:(get_fvs counted_body) (Spawn counted_body) in
            begin
                match WithIrMetadata.node counted_body with
                    | Seq (e1, e2) ->
                        begin match WithIrMetadata.node e1 with
                            | Dup _dups ->
                                let spawn_fvs = get_fvs e2 in
                                WithIrMetadata.make ~fvs:(VarSet.union (get_fvs e1) spawn_fvs) (Seq (e1, WithIrMetadata.make ~fvs:spawn_fvs (Spawn e2)))
                            | _ -> unchanged
                        end
                    | _ -> unchanged
            end
        | Send { target; message = (tag, message_values); iname } -> 
            begin
                match transform_val_sequence decls borrowed owned (target :: message_values) with
                    | (dups, target' :: message_values') ->
                        let dups_list = VarMultiset.bindings dups in
                        let fvs = List.fold_left (fun acc v -> VarSet.union acc (get_fvs v)) VarSet.empty (target' :: message_values') in
                        Ir.insert_dup dups_list
                            (WithIrMetadata.make ~fvs (Send { target = target'; message = (tag, message_values'); iname }))
                    (* impossible; transform_val_sequence always gives the same number of values back *)
                    | _ -> assert false
            end
        | Free (v, iname) ->
            let (dups, v') = ircv borrowed owned v in
            Ir.insert_dup dups (WithIrMetadata.make ~fvs:(get_fvs v') (Free (v', iname)))
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
            let guard_fvs = List.fold_left (fun acc g -> VarSet.union acc (get_fvs g)) (get_fvs translated_target) translated_guards in
            let translated_guard =
                WithIrMetadata.make ~fvs:guard_fvs (Guard { target = translated_target; pattern; guards = translated_guards; iname })
            in
            Ir.insert_dup dups translated_guard
        | Drop _
        | Dup _ -> raise <| 
            Errors.internal_error
                "reference_counting.ml"
                "Reference counting pass should not see Drop or Dup nodes"
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
and insert_reference_counting_val decls borrowed owned value =
    let decl_vars =
        decls |> List.map Var.of_binder |> VarSet.of_list
    in
    match WithIrMetadata.node value with
        | VAnnotate (v, ty) ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, WithIrMetadata.make ~fvs:(get_fvs v) (VAnnotate (v, ty)))
        | Atom _
        | Constant _
        | Primitive _
        | Name _
        | Nil ->
            (VarMultiset.empty, value)
        | Variable (x, _) ->
            if VarSet.mem x owned || VarSet.mem x decl_vars then
              (* Owned or global declaration -- no dup needed *)
              (VarMultiset.empty, value)
            else
              (VarMultiset.singleton x, value)
        | Tuple vs -> 
            let (dups, vs') = transform_val_sequence decls borrowed owned vs in 
            let fvs = List.fold_left (fun acc v -> VarSet.union acc (get_fvs v)) VarSet.empty vs' in
            (dups, WithIrMetadata.make ~fvs (Tuple vs'))
        | Cons (v1, v2) ->
            (* Similar to tuple case but binary *)
            let (dups, vs') = transform_val_sequence decls borrowed owned [v1; v2] in 
            begin
                match vs' with
                    | [v1'; v2'] -> 
                        let fvs = VarSet.union (get_fvs v1') (get_fvs v2') in
                        (dups, WithIrMetadata.make ~fvs (Cons (v1', v2')))
                    | _ -> assert false
            end
        | Inl v ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, WithIrMetadata.make ~fvs:(get_fvs v) (Inl v))
        | Inr v ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, WithIrMetadata.make ~fvs:(get_fvs v) (Inr v))
        | Lam { linear; parameters; result_type; body } ->
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
            let transformed_body =
                let drop_node =
                    WithIrMetadata.make ~fvs:(VarSet.of_list unused_vars)
                        (Drop { vars = to_drop; names = [] })
                in
                let body_trans = insert_reference_counting_comp decls VarSet.empty body_owned_vars body in
                let seq_fvs = VarSet.union (get_fvs drop_node) (get_fvs body_trans) in
                if List.is_empty unused_vars then
                    body_trans
                else 
                    WithIrMetadata.make ~fvs:seq_fvs (Seq (drop_node, body_trans))
            in
            (to_dup, WithIrMetadata.make ~fvs:(VarSet.union (VarSet.of_list used_vars) fvs) (Lam { linear; parameters; result_type; body = transformed_body }))
and insert_reference_counting_guard decls borrowed guards_owned guard =
    let irc borrowed owned c = insert_reference_counting_comp decls borrowed owned c in
    match WithIrMetadata.node guard with
        | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
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
            let final_cont =
                if VarSet.is_empty cont_drop then
                    translated_cont
                else
                    let drop_node =
                        WithIrMetadata.make ~fvs:cont_drop
                            (Drop { vars = (VarSet.elements cont_drop |> List.map (fun v -> (v, 1))); names = [] })
                    in
                    let seq_fvs = VarSet.union (get_fvs drop_node) (get_fvs translated_cont) in
                    WithIrMetadata.make ~fvs:seq_fvs (Seq (drop_node, translated_cont))
            in
            let receive_fvs = get_fvs final_cont in
            WithIrMetadata.make ~fvs:receive_fvs (Receive { tag; payload_binders; mailbox_binder; strategy; cont = final_cont })
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
            let final_e =
                if VarSet.is_empty e_drop then
                    translated_e
                else
                    let drop_node =
                        WithIrMetadata.make ~fvs:e_drop
                            (Drop { vars = (VarSet.elements e_drop |> List.map (fun v -> (v, 1))); names = [] })
                    in
                    let seq_fvs = VarSet.union (get_fvs drop_node) (get_fvs translated_e) in
                    WithIrMetadata.make ~fvs:seq_fvs (Seq (drop_node, translated_e))
            in
            let empty_fvs = get_fvs final_e in
            WithIrMetadata.make ~fvs:empty_fvs (Empty (binder, final_e))
        | Fail ->
            WithIrMetadata.make ~fvs:VarSet.empty Fail

let insert_reference_counting prog =
    let decls =
        prog.prog_decls
        |> List.map (fun (decl : Ir.decl) -> decl.decl_name)
    in
    let transform_body c =
        insert_reference_counting_comp
            decls
            Ir.VarSet.empty
            Ir.VarSet.empty
            c
        |> Ir.normalise_seq
    in
    let transform_decl (decl : Ir.decl) =
        let parameter_vars =
            decl.decl_parameters
            |> List.map (fun (b, _) -> Ir.Var.of_binder b)
        in
        let body_fvs = get_fvs decl.decl_body in
        let (used_params, unused_params) =
            List.partition (fun v -> VarSet.mem v body_fvs) parameter_vars
        in
        let body_owned_vars = used_params |> Ir.VarSet.of_list in
        let body_trans =
            insert_reference_counting_comp decls Ir.VarSet.empty body_owned_vars decl.decl_body
            |> Ir.normalise_seq
        in
        let decl_body =
            if List.is_empty unused_params then
                body_trans
            else
                let unused_set = unused_params |> Ir.VarSet.of_list in
                let drop_node =
                    WithIrMetadata.make ~fvs:unused_set
                        (Drop { vars = (List.map (fun v -> (v, 1)) unused_params); names = [] })
                in
                let fvs = VarSet.union (get_fvs drop_node) (get_fvs body_trans) in
                WithIrMetadata.make ~fvs (Seq (drop_node, body_trans))
        in
        { decl with decl_body }
    in
    {
        prog with
            prog_decls = List.map transform_decl prog.prog_decls;
            prog_body = Option.map transform_body prog.prog_body;
    }