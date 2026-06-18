open Common
open Ir
open Source_code
open Util.Utility

module VarMultiset = Multiset.Make(Var)

let pp_varset ppf s =
    Format.pp_print_string ppf "{";
    VarSet.iter (fun v -> Format.fprintf ppf "%a " Var.pp v) s;
    Format.pp_print_string ppf "}"

let print_var_set note varset =
    Format.printf "%s%a\n" note pp_varset varset

let rec insert_reference_counting_comp decls borrowed owned comp =
    let pos = WithPos.pos comp in
    let wrap = WithPos.make ~pos in
    let irc = insert_reference_counting_comp decls in
    let ircv borrowed owned v = 
        let (dups, v') = insert_reference_counting_val decls borrowed owned v in
        (VarMultiset.bindings dups, v')
    in
    let ircg borrowed guards_owned g = insert_reference_counting_guard decls borrowed guards_owned g in
    match WithPos.node comp with
        | Annotate (c, ty) -> (* OK *)
            wrap (Annotate (irc borrowed owned c, ty))
        | Let { binder; term; cont } -> (* LOL! Thought I'd finished this! *)
            let binder_var = Var.of_binder binder in
            let cont_fvs = Ir.free_variables cont in
            let e2_owned = VarSet.(inter owned (diff cont_fvs (singleton binder_var))) in
            let e1_owned = VarSet.diff owned e2_owned in
            let e1_trans = irc borrowed e1_owned term in
            (* Insert a drop if binder is unused in e2 *)
            if VarSet.mem binder_var cont_fvs then
                let e2_trans = irc borrowed (VarSet.(union e2_owned (singleton binder_var))) cont in
                wrap (Let { binder; term = e1_trans; cont = e2_trans })
            else
                let e2_trans = irc borrowed (VarSet.(union e2_owned (singleton binder_var))) cont in
                let e2_trans_with_drop = 
                    wrap (Seq (WithPos.make <| Drop ([(binder_var, 1)]), e2_trans))
                in
                wrap (Let { binder; term = e1_trans; cont = e2_trans_with_drop })
        | Seq (e1, e2) -> (* DONE *)
            print_var_set "in Seq. owned set: " owned; 
            (* e2_owned : owned environment of e2. Calculated by the intersection of owned environment and FVs of e2. *)
            let e2_owned = VarSet.inter owned (Ir.free_variables ~decls e2) in
            (* e1_borrowed: borrowed env for typing e1. union of borrowed variables and e2_owned *)
            let e1_borrowed = VarSet.union borrowed e2_owned in
            (* e1_owned: everything in owned environment that's not in e2_owned. *)
            let e1_owned = VarSet.diff owned e2_owned in
            (* e2_borrowed is just the current borrowed refs. *)
            let e2_borrowed = borrowed in
            let e1' = irc e1_borrowed e1_owned e1 in
            let e2' = irc e2_borrowed e2_owned e2 in
            wrap (Seq (e1', e2'))
        | Return v -> (* DONE *)
            let (dups, v') = ircv borrowed owned v in
            Ir.insert_dup dups (wrap <| Return v')
        | App { func; args } ->
            print_var_set "in App case. borrowed: " borrowed;
            print_var_set "in App case. owned: " owned;
            begin
                match transform_val_sequence decls borrowed owned (func :: args) with
                    | (dups, func' :: args') ->
                        let dups_list = VarMultiset.bindings dups in
                        Ir.insert_dup dups_list (wrap <| App { func = func'; args = args' })
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
                    (Ir.free_variables ~decls then_expr)
                    (Ir.free_variables ~decls else_expr)) in
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

            let then_owned = VarSet.inter branches_owned (Ir.free_variables ~decls then_expr) in
            let else_owned = VarSet.inter branches_owned (Ir.free_variables ~decls else_expr) in
            print_var_set "Then branch owned: " then_owned;
            print_var_set "Else branch owned: " else_owned;
            let translated_then = irc borrowed then_owned then_expr in
            let translated_else = irc borrowed else_owned else_expr in

            let final_then_expr = mk_drop (VarSet.diff branches_owned then_owned) translated_then in
            let final_else_expr = mk_drop (VarSet.diff branches_owned else_owned) translated_else in
            let translated_if = 
                wrap (If { 
                    test = translated_test; then_expr = final_then_expr; else_expr = final_else_expr })
            in
            Ir.insert_dup dups translated_if
        | LetTuple { binders; tuple; cont } ->
            let cont_fvs = Ir.free_variables ~decls cont in
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
                    wrap (Seq 
                        (WithPos.make (Drop (VarSet.to_list cont_drop |> List.map (fun v -> (v, 1)))),
                        translated_cont))
                in
            let translated_let_tuple =
                wrap (LetTuple { binders; tuple = translated_tuple; cont = final_translated_cont })
            in
            Ir.insert_dup dups translated_let_tuple
        | Case { term; branch1 = ((bnd1, ty1), e1); branch2 = ((bnd2, ty2), e2) } ->
            let bnd1_var = Var.of_binder bnd1 in
            let bnd2_var = Var.of_binder bnd2 in
            let e1_fvs = Ir.free_variables ~decls e1 in
            let e2_fvs = Ir.free_variables ~decls e2 in
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
                WithPos.make (Drop var_list)
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
            let final_e1 =
                WithPos.make ~pos:(WithPos.pos e1) (Seq (e1_drop, translated_e1))
            in
            let final_e2 =
                WithPos.make ~pos:(WithPos.pos e2) (Seq (e2_drop, translated_e2))
            in
            let translated_case =
                wrap (Case {
                    term = translated_term;
                    branch1 = ((bnd1, ty1), final_e1);
                    branch2 = ((bnd2, ty2), final_e2)
                })
            in
            Ir.insert_dup dups translated_case
        | CaseL { term; ty; nil; cons = ((bnd1, bnd2), e) } ->
            let bnd1_var = Var.of_binder bnd1 in
            let bnd2_var = Var.of_binder bnd2 in
            let nil_fvs = Ir.free_variables ~decls nil in
            let cons_fvs = Ir.free_variables ~decls e in
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
                WithPos.make (Drop var_list)
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
            let final_nil =
                WithPos.make ~pos:(WithPos.pos nil) (Seq (nil_drop, translated_nil))
            in
            let final_cons =
                WithPos.make ~pos:(WithPos.pos e) (Seq (cons_drop, translated_cons))
            in
            let translated_case_l =
                wrap (CaseL {
                    term = translated_term;
                    ty;
                    nil = final_nil;
                    cons = ((bnd1, bnd2), final_cons)
                })
            in
            Ir.insert_dup dups translated_case_l
        | New interface -> (* DONE *)
            wrap (New interface)
        | Spawn e -> (* DONE *)
            wrap (Spawn (irc borrowed owned e))
        | Send { target; message = (tag, message_values); iname } -> 
            (* Issue is that we seem to not own the reference? Are we not getting parameters maybe? *)
            let () = Format.printf "send %s owned %a\n%!" tag pp_varset owned in
            begin
                match transform_val_sequence decls borrowed owned (target :: message_values) with
                    | (dups, target' :: message_values') ->
                        let dups_list = VarMultiset.bindings dups in
                        Ir.insert_dup dups_list
                            (wrap <| Send { target = target'; message = (tag, message_values'); iname })
                    (* impossible; transform_val_sequence always gives the same number of values back *)
                    | _ -> assert false
            end
        | Free (v, iname) -> (* DONE *)
            let (dups, v') = ircv borrowed owned v in
            Ir.insert_dup dups (wrap <| Free (v', iname))
        | Guard { target; pattern; guards; iname } ->
            let guards_fvs =
                List.fold_left
                    (fun acc g -> VarSet.union acc (Ir.free_variables_guard ~decls g))
                    VarSet.empty
                    guards
            in
            let guards_owned = VarSet.inter owned guards_fvs in
            let target_borrowed = VarSet.union borrowed guards_owned in
            let target_owned = VarSet.diff owned guards_owned in
            let (dups, translated_target) = ircv target_borrowed target_owned target in
            let translated_guards = List.map (ircg borrowed guards_owned) guards in
            let translated_guard =
                wrap (Guard { target = translated_target; pattern; guards = translated_guards; iname })
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
    (* 
    Issue: for some reason we don't get consumerRef3 as owned...?
    consumerRef3 ! Msg() -->
    (dup ("consumerRef3":1);
           (consumerRef3 ! Msg();*)
           (* WIP: Go from here, sort this out *)
and transform_val_sequence decls borrowed owned vs : (VarMultiset.t * value list) =
    let rec transform_vals fvs_acc = function
        | [] -> ([], VarMultiset.empty)
        | (cur_val :: vals) ->
            let cur_borrowed = VarSet.union borrowed fvs_acc in
            let cur_owned = VarSet.(inter (diff owned fvs_acc) (Ir.free_variables_value ~decls cur_val)) in 
            let () =
                Format.printf "cur_borrowed: %a\ncur_owned: %a\n%!"
                    pp_varset cur_borrowed
                    pp_varset cur_owned
            in
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
It's not as exactly local as Perceus but it's (hopefully!) safe.
*)
and insert_reference_counting_val decls borrowed owned value : (VarMultiset.t * value)=
    let pos = WithPos.pos value in
    let wrap = WithPos.make ~pos in
    let decl_vars =
        decls |> List.map Var.of_binder |> VarSet.of_list
    in
    match WithPos.node value with
        | VAnnotate (v, ty) ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, wrap (VAnnotate (v, ty)))
        | Atom _
        | Constant _
        | Primitive _
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
            (dups, wrap (Tuple vs'))
        | Cons (v1, v2) ->
            (* Similar to tuple case but binary *)
            let (dups, vs') = transform_val_sequence decls borrowed owned [v1; v2] in 
            begin
                match vs' with
                    | [v1'; v2'] -> 
                        (dups, wrap (Cons (v1', v2')))
                    | _ -> assert false
            end
        | Inl v ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, wrap (Inl v))
        | Inr v ->
            let (dups, v) = insert_reference_counting_val decls borrowed owned v in
            (dups, wrap (Inr v))
        | Lam { linear; parameters; result_type; body } ->
            let fvs = Ir.free_variables_value ~decls value in
            let body_pos = WithPos.pos body in
            let (used_vars, unused_vars) =
                List.partition
                    (fun v -> VarSet.mem v fvs)
                    (List.map (fun (p, _) -> Ir.Var.of_binder p ) parameters)
            in
            (* Transform expression under empty borrowed environment; owned environment of
               fvs (of *whole* lambda -- not just body!) + used parameters *)
            let body_owned_vars = VarSet.union fvs (VarSet.of_list used_vars) in
            (* to_drop: FVs not in owned environment *)
            let to_dup = VarSet.diff fvs owned |> VarSet.to_list |> VarMultiset.of_list in
            let to_drop = List.map (fun v -> (v, 1)) unused_vars in
            let transformed_body =
                WithPos.make ~pos:body_pos
                (Seq (
                    WithPos.make (Drop to_drop),
                    insert_reference_counting_comp decls VarSet.empty body_owned_vars body
                ))
            in
            (to_dup, wrap (Lam { linear; parameters; result_type; body = transformed_body }))
and insert_reference_counting_guard decls borrowed guards_owned guard =
    let pos = WithPos.pos guard in
    let wrap = WithPos.make ~pos in
    let irc borrowed owned c = insert_reference_counting_comp decls borrowed owned c in
    match WithPos.node guard with
        | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            let binders_set =
                mailbox_binder :: payload_binders
                |> List.map Var.of_binder
                |> VarSet.of_list
            in
            let cont_fvs = Ir.free_variables ~decls cont in
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
                    WithPos.make ~pos:(WithPos.pos cont)
                        (Seq (
                            WithPos.make (Drop (VarSet.elements cont_drop |> List.map (fun v -> (v, 1)))),
                            translated_cont
                        ))
            in
            wrap (Receive { tag; payload_binders; mailbox_binder; strategy; cont = final_cont })
        (* Similar to case-expressions, just processed in isolation *)
        | Empty (binder, e) ->
            let binder_var = Var.of_binder binder in
            let e_fvs = Ir.free_variables ~decls e in
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
                    WithPos.make ~pos:(WithPos.pos e)
                        (Seq (
                            WithPos.make (Drop (VarSet.elements e_drop |> List.map (fun v -> (v, 1)))),
                            translated_e
                        ))
            in
            wrap (Empty (binder, final_e))
        | Fail ->
            wrap Fail

let insert_reference_counting prog =
    let decls =
            prog.prog_decls
            |> List.map (fun d ->
                let (decl : Ir.decl) = Source_code.WithPos.node d in
                decl.decl_name)
        in
    let () =
        let decl_names = List.map (Format.asprintf "%a" Ir.Binder.pp) decls in
        Format.printf "=== RC Decls: [%s] ===\n%!" (String.concat ", " decl_names)
    in
    let transform_body c =
        insert_reference_counting_comp
            decls
            Ir.VarSet.empty
            Ir.VarSet.empty
            c
        |> Ir.normalise_seq
    in
    let transform_decl decl_with_pos =
        let pos = Source_code.WithPos.pos decl_with_pos in
        let (decl : Ir.decl) = Source_code.WithPos.node decl_with_pos in
        let parameter_vars =
            decl.decl_parameters
            |> List.map (fun (b, _) -> Ir.Var.of_binder b)
            |> Ir.VarSet.of_list
        in
        (* Nothing should be free in a declaration other than the variables
        bound in the parameters, so our initial owned set is parameter_vars. *)
        let decl_body =
            insert_reference_counting_comp decls Ir.VarSet.empty parameter_vars decl.decl_body
            |> Ir.normalise_seq
        in
        Source_code.WithPos.make ~pos { decl with decl_body }
    in
    {
        prog with
            prog_decls = List.map transform_decl prog.prog_decls;
            prog_body = Option.map transform_body prog.prog_body;
    }