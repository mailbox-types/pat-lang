(* Pre-type checking.
   This is a small, basic pass which is used to rule out basic type errors,
   but primarily exists to annotate guards and variables with interfaces for
   use in the constraint generation phase. *)
open Common
open Common_types
open Ir
open Util.Utility
open Source_code

let pretype_error msg pos_list = Errors.Pretype_error (msg,pos_list)

module Gripers = struct
    open Format

    (* Agreement helpers, so that we don't report "1 arguments were provided". *)
    let plural n noun = if n = 1 then noun else noun ^ "s"
    let was_were n = if n = 1 then "was" else "were"

    let arity_error pos expected_len actual_len =
        let msg =
            asprintf "Arity error. Expects %d %s, but %d %s provided."
                expected_len (plural expected_len "argument")
                actual_len (was_were actual_len)
        in
        raise (pretype_error msg [pos])

    let tuple_arity_error pos expected_len actual_len =
        let msg =
            asprintf "Arity error. Tuple deconstructor has %d %s, but tuple has %d %s."
                expected_len (plural expected_len "binder")
                actual_len (plural actual_len "component")
        in
        raise (pretype_error msg [pos])

    let message_arity_error pos tag expected_len actual_len =
        let msg =
            asprintf "Arity error. Message '%s' expects %d %s, but %d %s provided."
                tag
                expected_len (plural expected_len "argument")
                actual_len (was_were actual_len)
        in
        raise (pretype_error msg [pos])

    let ctor_arity_error pos ctor_name expected_len actual_len =
        let msg =
            asprintf "Arity error. Constructor '%s' expects %d %s, but %d %s provided."
                ctor_name
                expected_len (plural expected_len "argument")
                actual_len (was_were actual_len)
        in
        raise (pretype_error msg [pos])

    let ctor_pattern_arity_error pos ctor_name expected_len actual_len =
        let msg =
            asprintf "Arity error. Pattern for constructor '%s' has %d %s, but the constructor has %d %s."
                ctor_name
                actual_len (plural actual_len "binder")
                expected_len (plural expected_len "argument")
        in
        raise (pretype_error msg [pos])

    let unbound_variable pos var =
        let msg =
            asprintf "Unbound variable %s." var
        in
        raise (pretype_error msg [pos])

    let type_mismatch pos_list expected actual =
        let msg =
            asprintf "Type mismatch. Expected %a but got %a."
                Pretype.pp expected
                Pretype.pp actual
        in
        raise (pretype_error msg pos_list)

    let type_mismatch_with_expected pos expected_msg actual =
        let msg =
            asprintf "Type mismatch. Expected %s but got %a."
                expected_msg
                Pretype.pp actual
        in
        raise (pretype_error msg [pos])

    let branch_mismatch_with_expected pos typ branch =
        let msg =
            asprintf "Invalid branch. Type is %a but constructor '%s' was matched."
                Pretype.pp typ
                branch
        in
        raise (pretype_error msg [pos])

    let branch_overlap pos dups =
        let names = String.concat ", " (List.map (fun s -> "'" ^ s ^ "'") dups) in
        let msg =
            asprintf "Invalid case statement - %s matched more than once."
                (if List.length dups = 1
                 then "constructor " ^ names ^ " is"
                 else "constructors " ^ names ^ " are")
        in
        raise (pretype_error msg [pos])

    let branch_not_enough pos =
        let msg =
            asprintf "Invalid case statement - missing branches."
        in
        raise (pretype_error msg [pos])

    let branch_not_exhaustive pos typ missing =
        let names = String.concat ", " (List.map (fun s -> "'" ^ s ^ "'") missing) in
        let msg =
            asprintf "Non-exhaustive case: missing %s for type %a."
                (if List.length missing = 1
                 then "a branch for constructor " ^ names
                 else "branches for constructors " ^ names)
                Pretype.pp typ
        in
        raise (pretype_error msg [pos])

    let cannot_synth_ctor_arg pos ctor_name prety =
        let msg =
            asprintf
                "Cannot synthesise a type for argument of constructor '%s': its type %a mentions a mailbox type. Please give the constructor a type annotation."
                ctor_name
                Pretype.pp prety
        in
        raise (pretype_error msg [pos])

    let cannot_synth_empty_guards pos () =
        let msg =
            asprintf "Need at least one non-fail guard to synthesise the type for a 'guard' expression."
        in
        raise (pretype_error msg [pos])

    let cannot_synth_fail pos () =
        let msg =
            asprintf "Cannot synthesise a type for a 'fail' construct."
        in
        raise (pretype_error msg [pos])

end

let list_eq eq xs ys =
    List.length xs = List.length ys && List.for_all2 eq xs ys

(* Structural equality on pretypes since
   syntactic equality is too strong in the presence of arbitrary types
   contained in PFun and PRec.
   In particular, if constituent types contain mailbox patterns then
    we'd be syntactically comparing patterns / pattern variables, which
    is wrong. During pretyping we just need to check whether the capabilities
    and interfaces match. *)
let rec pretype_eq (t1 : Pretype.t) (t2 : Pretype.t) =
    let open Pretype in
    match t1, t2 with
        | PBase b1, PBase b2 -> b1 = b2
        | PInterface i1, PInterface i2 -> i1 = i2
        | PTuple ts1, PTuple ts2 -> list_eq pretype_eq ts1 ts2
        | PFun { linear = lin1; args = args1; result = res1 },
          PFun { linear = lin2; args = args2; result = res2 } ->
            lin1 = lin2 && list_eq ty_eq args1 args2 && ty_eq res1 res2
        | PRec (name1, ts1), PRec (name2, ts2) ->
            name1 = name2 && list_eq ty_eq ts1 ts2
        | _, _ -> false
(* Equality on the types included in PFun / PRec. Mailbox types need to have
    same capabilities and interfaces. *)
and ty_eq (ty1 : Type.t) (ty2 : Type.t) =
    match ty1, ty2 with
        | Type.Mailbox { capability = cap1; interface = iface1; _ },
          Type.Mailbox { capability = cap2; interface = iface2; _ } ->
            cap1 = cap2 && iface1 = iface2
        | _, _ -> pretype_eq (Pretype.of_type ty1) (Pretype.of_type ty2)

(* Note: This basically works since we only have mailbox subtyping at present.
 If we were to allow subtyping on other types (e.g., records), we would need
 to expand this. *)
let check_tys pos_list expected actual =
    if not (pretype_eq expected actual) then
        Gripers.type_mismatch pos_list expected actual

module PretypeEnv = struct
    type t = Pretype.t StringMap.t

    let lookup pos x (env: t) =
        let var_str = Var.unique_name x in
        match StringMap.find_opt var_str env with
            | Some x -> x
            | None -> Gripers.unbound_variable pos var_str

    let bind x =
        StringMap.add (Var.unique_name x)

    let bind_many =
        List.fold_right (fun (v, prety) acc ->
            StringMap.add (Var.unique_name v) prety acc)

    let from_list xs = bind_many xs StringMap.empty
end

module IEnv = Interface_env

(* We take a bidirectional approach. Unlike in gen_constraints,
   as with most bidirectional systems, we try and synthesise as much
   as we can, since we carry around the type environment with us and
   don't need to preserve as much contextual type information. *)
let rec synthesise_val ienv env value : (value * Pretype.t) =
    let (v, pos, fvs) =
        (WithIrMetadata.node value, WithIrMetadata.pos value, WithIrMetadata.fvs value)
    in
    let wrap = WithIrMetadata.make ~pos ~fvs in
    match v with
        | VAnnotate (v, ty) ->
            let check_ty = Pretype.of_type ty in
            let v = check_val ienv env v check_ty in
            wrap (VAnnotate (v, ty)), check_ty
        | Atom a -> wrap (Atom a), Pretype.PBase (Base.Atom)
        | Constant c ->
            wrap (Constant c), Pretype.PBase (Constant.type_of c)
        | Variable (x, _) ->
            let ty = PretypeEnv.lookup pos x env in
            wrap (Variable (x, Some ty)), ty
        | Primitive prim ->
            (* Look up primitive type from Lib_types *)
            (* The only way something should be parsed as a primitive
               is if its type is present in this map. *)
            let ty =
                List.assoc prim Lib_types.signatures
                |> Pretype.of_type
            in
            wrap (Primitive prim), ty
        | Tuple vs ->
            let vs_and_tys = List.map (synthesise_val ienv env) vs in
            let (vs, tys) = List.split vs_and_tys in
            wrap (Tuple vs), Pretype.PTuple tys
        | Inject (ctor_name, args) ->
            begin match Recursive_types.find_constructor ctor_name with
            | None ->
                raise (Errors.internal_error "pretypecheck.ml"
                    ("Unknown constructor: " ^ ctor_name))
            | Some (rec_def, ctor_def) ->
                (* In synthesis mode we need to find a way of instantiating the
                   type parameters. We often can't synthesise everything, especially
                   the 'self' references. So try and synthesise the Params.
                   Workflow: synthesise to try and instantiate params, then
                   check everything (including 'self') later.

                   The converse is also true: an argument with a
                   PInterface pretype, or with a pretype that
                   contains a mailbox types (e.g. PFun/PRec that contain types),
                   can't fix a parameter whose pretype mentions a mailbox can't
                   resolve to a Type.t and so it can't fix a parameter by
                   itself, but things might be saved by an annotation later in the
                   structure.  So we record where such an argument was and only
                   report an error if its parameter is still undetermined once
                   we've looked at all arguments. *)
                (* Check arity before we start combining *)
                let () =
                    let expected_len = List.length ctor_def.binder_sources in
                    let actual_len = List.length args in
                    if expected_len <> actual_len then
                        Gripers.ctor_arity_error pos ctor_name expected_len actual_len
                in
                let params = Array.make rec_def.param_count None in
                let blocked = Array.make rec_def.param_count None in
                let args_with_srcs = List.combine args ctor_def.binder_sources in
                let undetermined () = Array.exists (fun p -> p = None) params in
                (* A `Param` argument fixes its parameter directly. *)
                List.iter (fun (arg, src) ->
                    match src with
                    | Recursive_types.Param i when params.(i) = None ->
                        let (_, pty) = synthesise_val ienv env arg in
                        begin match Pretype.to_type pty with
                        | Some ty -> params.(i) <- Some ty
                        | None ->
                            if blocked.(i) = None then
                                blocked.(i) <- Some (WithIrMetadata.pos arg, pty)
                        end
                    | Recursive_types.Param _
                    | Recursive_types.Self
                    | Recursive_types.Fixed _ -> ()
                ) args_with_srcs;
                (* Any parameter still unknown may yet be recoverable from a
                   `Self` argument (e.g. the annotated tail of a list). If
                   synthesising one fails it just means it couldn't tell us
                   anything, so fall through to the diagnostics below, which
                   report the argument actually responsible. *)
                List.iter (fun (arg, src) ->
                    match src with
                    | Recursive_types.Self when undetermined () ->
                        let synthesised =
                            try Pretype.to_type (snd (synthesise_val ienv env arg))
                            with Errors.Pretype_error _ -> None
                        in
                        begin match synthesised with
                        | Some (Type.Rec (_, ps)) ->
                            List.iteri (fun i p ->
                                if params.(i) = None then params.(i) <- Some p) ps
                        | Some _ | None -> ()
                        end
                    | Recursive_types.Self
                    | Recursive_types.Param _
                    | Recursive_types.Fixed _ -> ()
                ) args_with_srcs;
                (* Check all params are known *)
                Array.iteri (fun i param ->
                    if param = None then
                        match blocked.(i) with
                        | Some (arg_pos, pty) ->
                            Gripers.cannot_synth_ctor_arg arg_pos ctor_name pty
                        | None ->
                            Gripers.type_mismatch_with_expected pos
                                "a fully-determined recursive type" (Pretype.PTuple [])
                            |> raise
                ) params;
                let params = Array.to_list (Array.map Option.get params) in
                let self_ty = Type.Rec (rec_def.type_name, params) in
                (* Re-check args against expected types *)
                let checked_args = List.map2 (fun src arg ->
                    let expected = match src with
                        | Recursive_types.Param i -> List.nth params i
                        | Recursive_types.Self -> self_ty
                        | Recursive_types.Fixed ty -> ty
                    in
                    check_val ienv env arg (Pretype.of_type expected)
                ) ctor_def.binder_sources args in
                wrap (Inject (ctor_name, checked_args)), (Pretype.of_type self_ty)
            end
        | Lam { linear; parameters; result_type; body } ->
            (* Defer linearity checking to constraint generation. *)
            let param_types  = List.map snd parameters in
            let pretype_params =
                List.map
                    (fun (b, ty) -> Var.of_binder b, Pretype.of_type ty)
                    parameters
            in
            let env = PretypeEnv.bind_many pretype_params env in
            let body = check_comp ienv env body (Pretype.of_type result_type) in
            wrap (Lam { linear; parameters; body; result_type }),
            Pretype.PFun {
                linear = linear;
                args = param_types;
                result = result_type
            }
        | Name _ -> assert false
and check_val ienv env value ty =
    let (value_node, pos, fvs) =
        (WithIrMetadata.node value, WithIrMetadata.pos value, WithIrMetadata.fvs value)
    in
    let wrap = WithIrMetadata.make ~pos ~fvs in
    match value_node, ty with
        | Inject (ctor_name, args), Pretype.PRec (tname, params) ->
            begin match Recursive_types.find_constructor ctor_name with
            | Some (rec_def, ctor_def) when rec_def.type_name = tname ->
                let self_ty = Type.Rec (tname, params) in
                let expected_tys =
                    Recursive_types.instantiate_binder_types params self_ty
                        ctor_def.binder_sources
                in
                (* Check arity before we start combining *)
                let () =
                    let expected_len = List.length expected_tys in
                    let actual_len = List.length args in
                    if expected_len <> actual_len then
                        Gripers.ctor_arity_error pos ctor_name expected_len actual_len
                in
                let checked_args =
                    List.map2
                        (check_val ienv env) args
                        (List.map Pretype.of_type expected_tys)
                in
                wrap (Inject (ctor_name, checked_args))
            | _ ->
                let value, inferred_ty = synthesise_val ienv env value in
                check_tys [pos] ty inferred_ty;
                value
            end
        | Inject (ctor_name, _), ty ->
            begin match Recursive_types.find_constructor ctor_name with
            | Some (rec_def, _) ->
                raise
                    (Gripers.type_mismatch_with_expected pos
                        ("a " ^ rec_def.type_name ^ " type") ty)
            | None ->
                let value, inferred_ty = synthesise_val ienv env value in
                check_tys [pos] ty inferred_ty;
                value
            end
        | _ ->
            let value, inferred_ty = synthesise_val ienv env value in
            check_tys [pos] ty inferred_ty;
            value
and synthesise_comp ienv env comp =
    let pos = WithIrMetadata.pos comp in
    let fvs = WithIrMetadata.fvs comp in
    let wrap = WithIrMetadata.make ~pos ~fvs in
    let synth = synthesise_comp ienv env in
    let synthv = synthesise_val ienv env in
    match WithIrMetadata.node comp with
        | Annotate (c, ty) ->
            let check_ty = Pretype.of_type ty in
            let c = check_comp ienv env c check_ty in
            wrap (Annotate (c, ty)), check_ty
        | Return v ->
            let (v, ty) = synthv v in
            wrap (Return v), ty
        | New iname ->
            wrap (New iname), Pretype.PInterface iname
        | Spawn e ->
            let e =
                check_comp ienv env e (Pretype.unit)
            in
            wrap (Spawn e), Pretype.unit
        | If { test; then_expr; else_expr } ->
            let test =
                check_val ienv env test (Pretype.PBase Bool)
            in
            let then_expr, ty = synth then_expr in
            let else_expr = check_comp ienv env else_expr ty in
            wrap (If { test; then_expr; else_expr }), ty
        | Let { binder; term; cont } ->
            let term, term_ty = synth term in
            let env' = PretypeEnv.bind (Var.of_binder binder) term_ty env in
            let cont, cont_ty = synthesise_comp ienv env' cont in
            wrap (Let { binder; term; cont }), cont_ty
        | Case { term; branches; _ } ->
            let (term, prety) =
                synthesise_val ienv env term
            in
            let branch_tys =
                match prety with
                    | Pretype.PRec (tname, params) ->
                        begin match Recursive_types.find_type tname with
                        | Some def ->
                            (* Option.get safe here as we know PRec -> Rec is always defined *)
                            Recursive_types.constructor_types def params (Pretype.to_type prety |> Option.get)
                        | None ->
                            raise
                                (Gripers.type_mismatch_with_expected pos
                                 "a recursive type" prety)
                        end
                    | _ ->
                        raise
                            (Gripers.type_mismatch_with_expected pos
                             "a recursive type" prety)
            in
            (* Validate branch names and check for duplicates *)
            let () = List.iter (fun (_, _, bname) ->
                if not (List.mem_assoc bname branch_tys) then
                    raise (Gripers.branch_mismatch_with_expected pos prety bname)
            ) branches in
            let branch_names = List.map (fun (_, _, s) -> s) branches in
            let () =
                let dups = List.sort_uniq String.compare
                    (List.filter (fun x ->
                        List.length (List.filter (( = ) x) branch_names) > 1
                    ) branch_names)
                in
                if dups <> [] then raise (Gripers.branch_overlap pos dups)
            in
            (* Check exhaustiveness: every constructor of the type must have a branch *)
            let () =
                let all_ctors = List.map fst branch_tys in
                let missing = List.filter (fun c -> not (List.mem c branch_names)) all_ctors in
                if missing <> [] then raise (Gripers.branch_not_exhaustive pos prety missing)
            in
            (* Sort branches into canonical order *)
            let sorted_branches = List.sort (fun (_, _, s1) (_, _, s2) -> String.compare s1 s2) branches in
            (* Look up binder types for each branch *)
            let lookup_tys bname =
                match List.assoc_opt bname branch_tys with
                    | Some tys -> List.map Pretype.of_type tys
                    | None -> raise (Gripers.branch_mismatch_with_expected pos prety bname)
            in
            (* Look up the binder types for a branch, checking arity before we
               start combining *)
            let binders_and_tys bname bnds =
                let tys = lookup_tys bname in
                let expected_len = List.length tys in
                let actual_len = List.length bnds in
                let () =
                    if expected_len <> actual_len then
                        Gripers.ctor_pattern_arity_error pos bname expected_len actual_len
                in
                List.combine (List.map Var.of_binder bnds) tys
            in
            (* Type-check each branch *)
            let checked_branches, result_ty =
                match sorted_branches with
                | [] -> raise (Gripers.branch_not_enough pos)
                | (bnds1, e1, s1) :: rest ->
                    let vars_and_tys1 = binders_and_tys s1 bnds1 in
                    let e1_env = PretypeEnv.bind_many vars_and_tys1 env in
                    let e1, e1_ty = synthesise_comp ienv e1_env e1 in
                    let checked_rest = List.map (fun (bnds, e, sname) ->
                        let vars_and_tys = binders_and_tys sname bnds in
                        let e_env = PretypeEnv.bind_many vars_and_tys env in
                        let e = check_comp ienv e_env e e1_ty in
                        (bnds, e, sname)
                    ) rest in
                    (bnds1, e1, s1) :: checked_rest, e1_ty
            in
            wrap
                (Case { term; prety = Some prety; branches = checked_branches }), result_ty
        | LetTuple { binders; tuple; cont } ->
            let bnds = List.map fst binders in
            let tuple, tuple_ty = synthv tuple in
            let tys =
                match tuple_ty with
                    | Pretype.PTuple tys -> tys
                    | _ ->
                        raise
                            (Gripers.type_mismatch_with_expected pos
                             "a tuple type" tuple_ty)
            in
            (* Check arity before we start combining *)
            let () =
                let bnds_len = List.length bnds in
                let tys_len = List.length tys in
                if bnds_len <> tys_len then
                    Gripers.tuple_arity_error pos bnds_len tys_len
            in
            let vars_and_tys = List.combine (List.map Var.of_binder bnds) tys in
            let env' =
                PretypeEnv.bind_many vars_and_tys env
            in
            let binders =
                List.combine bnds tys
                |> List.map (fun (b, t) -> (b, Some t))
            in
            let cont, cont_ty = synthesise_comp ienv env' cont in
            wrap
                (LetTuple { binders; tuple; cont }), cont_ty
        | Seq (e1, e2) ->
            let e1 = check_comp ienv env e1 (Pretype.unit) in
            let e2, e2_ty = synth e2 in
            wrap (Seq (e1, e2)), e2_ty
        | App { func; args } ->
            let open Pretype in
            (* Synthesise type for function; ensure it is a function type *)
            let (func, f_ty) = synthv func in
            let arg_anns, result_ann =
                begin
                    match f_ty with
                        | PFun { args; result; _ } ->
                            List.map Pretype.of_type args, result
                        | t ->
                            Gripers.type_mismatch_with_expected pos "a function type" t
                end
            in
            (* Basic arity checking *)
            let spec_len = List.length arg_anns in
            let arg_len = List.length args in
            let () =
                if spec_len <> arg_len then
                    Gripers.arity_error pos spec_len  arg_len
            in
            (* Check argument types *)
            let args =
                List.combine args arg_anns
                |> List.map (fun (arg, arg_ty) ->
                    check_val ienv env arg arg_ty)
            in
            (* Synthesise result type *)
            wrap (App { func; args }), Pretype.of_type result_ann
        | Send { target; message = (tag, vals); _ } ->
            let open Pretype in
            (* Typecheck target *)
            let target, target_ty = synthv target in
            (* Ensure target has interface type *)
            begin
                match target_ty with
                    | PInterface iname ->
                        (* Check that:
                            - Message tag is contained within interface
                            - Message payload pretype matches that of the interface *)
                        let interface_withPos = IEnv.lookup iname ienv [pos] in
                        let payload_target_tys =
                            WithPos.node interface_withPos
                            |> Interface.lookup ~pos_list:[WithPos.pos interface_withPos; pos] tag
                            |> List.map Pretype.of_type
                        in
                        let () =
                            let iface_len = List.length payload_target_tys in
                            let val_len = List.length vals in
                            if val_len <> iface_len then
                                Gripers.message_arity_error pos tag iface_len val_len
                        in
                        let vals =
                            List.combine vals payload_target_tys
                            |> List.map (fun (e, iface_ty) ->
                                check_val ienv env e iface_ty
                            )
                        in
                        wrap (
                        Send {
                            target;
                            message = (tag, vals);
                            iname = Some iname
                         }), Pretype.unit
                    | ty -> Gripers.type_mismatch_with_expected pos "an interface type" ty
            end
        | Free (v, _) ->
            let (v, v_ty) = synthv v in
            let iface =
                match v_ty with
                    | PInterface iface -> iface
                    | t -> Gripers.type_mismatch_with_expected pos "an interface type" t
            in
            wrap (Free (v, Some iface)), Pretype.unit
        | Fail _ ->
            Gripers.cannot_synth_fail pos ()
        | Guard { target; pattern; guards; _ } ->
            let (target, iname) = synth_guard_target ienv env pos target in
            (* Without an expected type we must synthesise one from somewhere,
               so the first guard has to be synthesisable; the rest are then
               checked against it. *)
            let guards, g_ty =
                match guards with
                    | [] ->
                        Gripers.cannot_synth_empty_guards pos ()
                    | g :: gs ->
                        let g, g_ty = synth_guard ienv env iname g in
                        let gs =
                            List.map (fun g -> check_guard ienv env iname g g_ty) gs
                        in
                        g :: gs, g_ty
            in
            wrap (Guard { target; pattern; guards; iname = Some iname }), g_ty
and synth_guard_target ienv env pos target =
    match synthesise_val ienv env target with
        | (target, PInterface iname) -> (target, iname)
        | (_, t) -> Gripers.type_mismatch_with_expected pos "an interface type" t
and check_comp ienv env comp ty  =
    let pos = WithIrMetadata.pos comp in
    let fvs = WithIrMetadata.fvs comp in
    let wrap = WithIrMetadata.make ~pos ~fvs in
    match WithIrMetadata.node comp with
        | Return v ->
            let v = check_val ienv env v ty in
            wrap (Return v)
        | Fail (mb, _) -> 
            begin match synthesise_val ienv env mb with
                | (mb, PInterface iface) ->
                    wrap (Fail (mb, Some iface))
                | (_, prety) ->
                    Gripers.type_mismatch_with_expected pos "a mailbox type" prety
            end
        | Guard { target; pattern; guards; _ } ->
            (* With an expected type in hand, every branch can be checked, so a
               branch whose body only has a checking rule needs no annotation. *)
            let (target, iname) = synth_guard_target ienv env pos target in
            let guards = List.map (fun g -> check_guard ienv env iname g ty) guards in
            wrap (Guard { target; pattern; guards; iname = Some iname })
        | _ ->
            let comp, inferred_ty = synthesise_comp ienv env comp in
            check_tys [pos] ty inferred_ty;
            comp
(* Binder structure shared by synthesising and checking a guard: performs the
   arity check, binds the payloads and mailbox, and returns the extended
   environment, the continuation, and a function rebuilding the guard around a
   checked continuation. Only the treatment of the continuation differs between
   the two modes, so it is the only thing left to the caller. *)
and guard_parts ienv env iname g =
    let interface_withPos = IEnv.lookup iname ienv [WithIrMetadata.pos g] in
    let iface = WithPos.node interface_withPos in
    let pos = WithIrMetadata.pos g in
    let fvs = WithIrMetadata.fvs g in
    let wrap = WithIrMetadata.make ~pos ~fvs in
    match WithIrMetadata.node g with
        | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            let payload_tys = Interface.lookup ~pos_list:[(WithPos.pos interface_withPos);pos] tag iface in
            let expected_len = List.length payload_tys in
            (* Arity check *)
            let actual_len = List.length payload_binders in
            let () =
                if expected_len <> actual_len then
                    Gripers.message_arity_error pos tag expected_len actual_len
            in

            let payload_entries =
                List.combine
                    (List.map Var.of_binder payload_binders)
                    (List.map Pretype.of_type payload_tys)
            in
            let env =
                env
                |> PretypeEnv.bind_many payload_entries
                |> PretypeEnv.bind
                    (Var.of_binder mailbox_binder)
                    (Pretype.PInterface iname)
            in
            let rebuild cont =
                wrap (Receive { tag; payload_binders; mailbox_binder; strategy; cont })
            in
            (env, cont, rebuild)
        | Empty (x, e) ->
            let env = PretypeEnv.bind (Var.of_binder x) (Pretype.PInterface iname) env in
            let rebuild e = wrap (Empty (x, e)) in
            (env, e, rebuild)
and synth_guard ienv env iname g =
    let (env, cont, rebuild) = guard_parts ienv env iname g in
    let cont, cont_ty = synthesise_comp ienv env cont in
    rebuild cont, cont_ty
(* Checks a guard against a known type, pushing the check into the
   continuation rather than synthesising it and comparing afterwards. This
   lets constructs that only have a checking rule -- `fail` -- appear
   directly as a guard body. *)
and check_guard ienv env iname g ty =
    let (env, cont, rebuild) = guard_parts ienv env iname g in
    rebuild (check_comp ienv env cont ty)

(* Top-level typechecker *)
let check { prog_interfaces; prog_decls; prog_body } =

    (* Construct interface environment from interface list *)
    let ienv =
        prog_interfaces
        |> List.map (WithPos.make ~pos:Position.dummy)
        |> IEnv.from_list
    in
    let param_pretypes =
        List.map
            (fun (x, t) -> (Var.of_binder x, Pretype.of_type t))
    in

    (* At the moment, I'm doing the Haskell thing of assuming
       that all declarations can refer to each other.
       The alternative is that we have ML-style lexical scoping
       and explicit mutual blocks, which I might do later. *)
    let decl_env =
        List.map (fun d ->
            let param_tys =
                List.map (snd) d.decl_parameters in
            (Var.of_binder d.decl_name,
                Pretype.PFun {
                    linear = false;
                    args = param_tys;
                    result = d.decl_return_type
                })) prog_decls
        |> PretypeEnv.from_list
    in

    (* Checks a declaration *)
    let check_decl d =
        (* Add parameters to environment *)
        let params = param_pretypes d.decl_parameters in
        let env = PretypeEnv.bind_many params decl_env in
        (* Typecheck according to return annotation *)
        let decl_body =
            check_comp ienv env d.decl_body (Pretype.of_type d.decl_return_type)
        in
        { d with decl_body }
    in

    let prog_decls = List.map check_decl prog_decls in

    let prog_body, ty =
        match prog_body with
            | Some x ->
                let body, ty = synthesise_comp ienv decl_env x in
                Some body, Some ty
            | None -> None, None
    in
    { prog_interfaces; prog_decls; prog_body }, ty
