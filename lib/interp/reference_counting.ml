open Common
open Ir
open Source_code
open Util.Utility

module VarMultiset = Multiset.Make(Var)

let rec insert_reference_counting borrowed owned comp =
    let pos = WithPos.pos comp in
    let wrap = WithPos.make ~pos in
    let irc = insert_reference_counting in
    let ircv = insert_reference_counting_val in
    let ircg = insert_reference_counting_guard in
    match WithPos.node comp with
        | Annotate (c, ty) ->
            wrap (Annotate (irc borrowed owned c, ty))
        | Let { binder; term; cont } ->
            wrap (Let { binder; term = irc borrowed owned term; cont = irc borrowed owned cont })
        | Seq (e1, e2) ->
            wrap (Seq (irc borrowed owned e1, irc borrowed owned e2))
        | Return v ->
            wrap (Return (ircv borrowed owned v))
        | App { func; args } ->
            wrap (App { func = ircv borrowed owned func; args = List.map (ircv borrowed owned) args })
        | If { test; then_expr; else_expr } ->
            wrap (If { test = ircv borrowed owned test; then_expr = irc borrowed owned then_expr; else_expr = irc borrowed owned else_expr })
        | LetTuple { binders; tuple; cont } ->
            wrap (LetTuple { binders; tuple = ircv borrowed owned tuple; cont = irc borrowed owned cont })
        | Case { term; branch1 = ((bnd1, ty1), e1); branch2 = ((bnd2, ty2), e2) } ->
            wrap (Case { term = ircv borrowed owned term; branch1 = ((bnd1, ty1), irc borrowed owned e1); branch2 = ((bnd2, ty2), irc borrowed owned e2) })
        | CaseL { term; ty; nil; cons = ((bnd1, bnd2), e) } ->
            wrap (CaseL { term = ircv borrowed owned term; ty; nil = irc borrowed owned nil; cons = ((bnd1, bnd2), irc borrowed owned e) })
        | New interface ->
            wrap (New interface)
        | Spawn e ->
            wrap (Spawn (irc borrowed owned e))
        | Send { target; message = (tag, message_values); iname } ->
            wrap (Send { target = ircv borrowed owned target; message = (tag, List.map (ircv borrowed owned) message_values); iname })
        | Free (v, iname) ->
            wrap (Free (ircv borrowed owned v, iname))
        | Guard { target; pattern; guards; iname } ->
            wrap (Guard { target = ircv borrowed owned target; pattern; guards = List.map (ircg borrowed owned) guards; iname })
        | Drop vars ->
            wrap (Drop vars)
        | Dup vars ->
            wrap (Dup vars)
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
and insert_reference_counting_val borrowed owned value : (VarMultiset.t * value)=
    let pos = WithPos.pos value in
    let wrap = WithPos.make ~pos in
    (* Helper function to annotate a sequence of values. We need to consider all subsequent
       variables used in a sequence as borrowed. The best way of doing this is to reverse the
       list of variables and keep the borrow set as an accumulator, then reverse again at the end. *)
    let transform_val_sequence borrowed owned vs =
        let rec transform_vals fvs_acc = function
            | [] -> ([], VarMultiset.empty)
            | (cur_val :: vals) ->
                let cur_borrowed = VarSet.union borrowed fvs_acc in
                let cur_owned = VarSet.(inter (diff owned fvs_acc) (Ir.free_variables_value cur_val)) in
                let (new_dups, transformed_val) =
                    insert_reference_counting_val cur_borrowed cur_owned cur_val
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
    in
    match WithPos.node value with
        | VAnnotate (v, ty) ->
            let (dups, v) = insert_reference_counting_val borrowed owned v in
            (dups, wrap (VAnnotate (v, ty)))
        | Atom _
        | Constant _
        | Primitive _
        | Nil ->
            (VarMultiset.empty, value)
        | Variable (x, _) ->
            if VarSet.mem x owned then
              (* Owned -- no need to do anything here *)
              (VarMultiset.empty, value)
            else
              (VarMultiset.singleton x, value)
        | Tuple vs -> 
            let (dups, vs') = transform_val_sequence borrowed owned vs in 
            (dups, wrap (Tuple vs'))
        | Cons (v1, v2) ->
            (* Similar to tuple case but binary *)
            let (dups, vs') = transform_val_sequence borrowed owned [v1; v2] in 
            begin
                match vs' with
                    | [v1'; v2'] -> 
                        (dups, wrap (Cons (v1', v2')))
                    | _ -> assert false
            end
        | Inl v ->
            let (dups, v) = insert_reference_counting_val borrowed owned v in
            (dups, wrap (Inl v))
        | Inr v ->
            let (dups, v) = insert_reference_counting_val borrowed owned v in
            (dups, wrap (Inr v))
        | Lam { linear; parameters; result_type; body } ->
            let fvs = Ir.free_variables_value value in
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
                    insert_reference_counting VarSet.empty body_owned_vars body
                ))
            in
            (to_dup, wrap (Lam { linear; parameters; result_type; body = transformed_body }))
and insert_reference_counting_guard borrowed owned guard =
    let pos = WithPos.pos guard in
    let wrap = WithPos.make ~pos in
    let irc = insert_reference_counting in
    match WithPos.node guard with
        | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            wrap (Receive { tag; payload_binders; mailbox_binder; strategy; cont = irc borrowed owned cont })
        | Empty (binder, e) ->
            wrap (Empty (binder, irc borrowed owned e))
        | Fail ->
            wrap Fail
