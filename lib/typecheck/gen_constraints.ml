(* Constraint generation.
   Given a source AST annotated with pre-types, in the right place, generate a
   set of constraints and return a (full) type and type environment. *)

(* Since our goal is to propagate contextual information to variables, so that
   we can assign them the correct types and generate the correct constraints,
   the type system uses a form of Zeilberger's backwards bidirectional
   typechecking.  The key point is that unlike regular systems, we *check*
   variables, rather than synthesising them. *)

open Util.Utility
open Common
open Common_types
open Ir
open Type_utils
open Source_code

(* Modules *)

module IEnv = Interface_env

(* Bidirectional constraint generation *)

(* Synthesis mode *)
let rec synthesise_val :
    IEnv.t -> Ty_env.t -> Ir.value -> Type.t * Ty_env.t * Constraint_set.t =
        fun ienv decl_env v ->
    let pos = WithIrMetadata.pos v in
    match WithIrMetadata.node v with
        | VAnnotate (v, ty) ->
            let (env, constrs) = check_val ienv decl_env v ty in
            ty, env, constrs
        | Atom _ -> Type.Base (Base.Atom), Ty_env.empty, Constraint_set.empty
        | Constant c ->
            Type.Base (Constant.type_of c),
            Ty_env.empty,
            Constraint_set.empty
        | Primitive prim ->
            let ty = List.assoc prim Lib_types.signatures in
            ty, Ty_env.empty, Constraint_set.empty
        (* No harm having this as a synth case as well. *)
        | Tuple vs ->
            let tys_envs_constrss = List.map (synthesise_val ienv decl_env) vs in
            let tys, envs, constrss = split3 tys_envs_constrss in
            let constrs = Constraint_set.union_many constrss in
            let env, constrs2 = Ty_env.combine_many ienv envs pos in
            (* Ensure any synthesised types are returnable *)
            let () =
                if not <| Settings.(get liberal_datatypes) then
                    List.iter (fun ty ->
                        if not (Type.is_returnable ty) then
                            Gripers.tuples_returnable ty [pos]) tys
            in
            Type.Tuple tys,
                env,
                Constraint_set.union constrs constrs2
        | Variable (_v, None) -> assert false
        | Variable (v, Some ty) ->
            (* Start by checking in the declaration environment *)
            begin
                match Ty_env.lookup_opt v decl_env, ty with
                    | Some decl_ty, _ ->
                        decl_ty, Ty_env.singleton v decl_ty, Constraint_set.empty
                    (* Otherwise resort to pretyping information *)
                    | _, PBase b ->
                        let ty = Type.Base b in
                        ty, Ty_env.singleton v ty, Constraint_set.empty
                    (* In limited circumstances we can use a pretype annotation to
                       synthesise a function *)
                    | _, PFun { linear; args; result } ->
                        let ty = Type.function_type linear args result in
                        ty, Ty_env.singleton v ty, Constraint_set.empty
                    | _, _ ->
                        Gripers.synth_variable v [pos]
            end
        | Name _ ->
            raise (Errors.internal_error "gen_constraints.ml" "RuntimeName values should only be inserted after typechecking")
        (* In the formalism, this is a checking case
           rather than a synthesis case. However, we can treat it as a synthesis
           case here since we have annotations on arguments and the body (which
           is exactly the same as having a type annotation on an unannotated
           lambda).
         *)
        | Lam { linear; parameters; result_type; body } ->
            let (env, body_constrs) =
                check_comp ienv decl_env body result_type
            in
            (* As usual, annotations form a lower bound on the inferred types. *)
            let parameter_constrs =
                let lookup_type (bnd, _ty) =
                    Ty_env.lookup_opt (Var.of_binder bnd) env
                in
                let (used_parameters, unused_parameters) =
                    List.partition
                        (Option.is_some << lookup_type)
                        parameters
                in
                let used_constrs =
                    (* Get the lists of declared and inferred types for used parameters,
                       and zip them together. *)
                    let inferred_types =
                        List.map (
                            fst >>
                            Var.of_binder >>
                            (flip Ty_env.lookup) env)
                        used_parameters
                    in
                    let declared_types =
                        List.map snd used_parameters
                    in
                    (* Zip together both lists *)
                    let zipped =
                        List.combine inferred_types declared_types
                    in
                    (* Finally, ensure that the declared type is a subtype of
                       the inferred type *)
                    List.fold_left (fun acc (inferred, declared) ->
                        Constraint_set.union acc (subtype ienv declared inferred pos))
                        Constraint_set.empty
                        zipped
                in
                (* All unused parameters should be unrestricted. *)
                let unused_constrs =
                    List.fold_left (fun acc (_, ty) ->
                        Constraint_set.union acc (make_unrestricted ty pos)
                    ) Constraint_set.empty unused_parameters in
                Constraint_set.union used_constrs unused_constrs
            in
            (* Hide the parameters in the returned environment *)
            let parameter_tys = List.map snd parameters in
            let env =
                List.fold_left (fun acc x -> Ty_env.delete (fst x |> Var.of_binder) acc)
                env parameters in
            (* If the function is unrestricted, all environment entries required
               to type the body must also be unrestricted. *)
            let unr_constrs =
                if (not linear) then
                    Ty_env.make_unrestricted env pos
                else Constraint_set.empty
            in
            (* We can only close over variables that are returnable (to avoid issues with aliasing) *)
            let returnable_env = Ty_env.make_returnable env in
            let constrs = Constraint_set.union_many
                [body_constrs; parameter_constrs; unr_constrs]
            in
            let ty = Type.function_type linear parameter_tys result_type in
            (ty, returnable_env, constrs)
        | _ -> Gripers.cannot_synthesise_value v [pos]
and check_val :
    IEnv.t -> Ty_env.t -> Ir.value -> Type.t -> Ty_env.t * Constraint_set.t =
        fun ienv decl_env v ty ->
    let pos = WithIrMetadata.pos v in
    (* Checks consistency between a pretype annotation and the check type *)
    let rec check_pretype_consistency ty pty =
        let open Type in
        let open Pretype in
        match ty, pty with
            | Mailbox { interface; _ }, PInterface iname when interface = iname -> ()
            | Base b1, PBase b2 when b1 = b2 -> ()
            | Fun _, PFun _ -> 
                (* Function pretypes are now fully typed, so any errors will be
                   picked up in constraint generation or constraint resolution. *)
                ()
            | Tuple ts, PTuple pts ->
                List.combine ts pts
                |> List.iter (uncurry check_pretype_consistency)
            | Rec (_, ts), PRec (_, ts_p) ->
                List.combine ts (List.map Pretype.of_type ts_p)
                |> List.iter (uncurry check_pretype_consistency)
            | _, _ -> Gripers.pretype_consistency ty pty [pos]
    in
    match WithIrMetadata.node v with
        (* Crucial case: note that we are *checking* this variable's type, not
           synthesising! This is how we propagate the type information upwards.
           We check the interfaces, and then assign the type. *)
        | Variable (_v, None) -> assert false (* Should not happen after pre-typing. *)
        | Variable (v, Some pty) ->
            check_pretype_consistency ty pty;
            Ty_env.singleton v ty, Constraint_set.empty
        | Name _ ->
            raise (Errors.internal_error "gen_constraints.ml" "RuntimeName values should only be inserted after typechecking")
        | Inject (ctor_name, args) ->
            begin match Recursive_types.find_constructor ctor_name with
            | None ->
                raise (Errors.internal_error "gen_constraints.ml"
                    ("Unknown constructor: " ^ ctor_name))
            | Some (rec_def, ctor_def) ->
                match ty with
                | Type.Rec (tname, params) when tname = rec_def.type_name ->
                    let self_ty = ty in
                    let expected_tys =
                        Recursive_types.instantiate_binder_types params self_ty
                            ctor_def.binder_sources
                    in
                    (* Apply make_returnable to Param types when no Self sources *)
                    let expected_tys =
                        if Recursive_types.has_self_source ctor_def then expected_tys
                        else List.map Type.make_returnable expected_tys
                    in
                    let envs_and_constrs =
                        List.map2 (check_val ienv decl_env) args expected_tys
                    in
                    let envs = List.map fst envs_and_constrs in
                    let constrs = List.map snd envs_and_constrs in
                    let env, combine_constrs =
                        Ty_env.combine_many ienv envs pos
                    in
                    env, Constraint_set.union_many (combine_constrs :: constrs)
                | _ -> Gripers.expected_recursive_type ty [pos]
            end
        | Tuple vs ->
            let ts =
                begin
                    match ty with
                        | Type.Tuple ts -> ts
                        | _ -> Gripers.expected_tuple_type ty [pos]
                end
            in
            let vs_and_ts = List.combine vs ts in
            let (check_envs, check_constrss) =
                List.map (fun (v, ty) ->
                    let ty =
                        if not @@ Settings.(get liberal_datatypes) then
                            Type.make_returnable ty
                        else ty
                    in
                    check_val ienv decl_env v ty) vs_and_ts
                |> List.split
            in
            let check_constrs = Constraint_set.union_many check_constrss in
            let (env, combine_constrs) = Ty_env.combine_many ienv check_envs pos in
            env, Constraint_set.union check_constrs combine_constrs
        | _ ->
            let synth_ty, synth_env, synth_constrs =
                synthesise_val ienv decl_env v
            in
            let subty_constrs = subtype ienv synth_ty ty pos in
            synth_env, Constraint_set.union synth_constrs subty_constrs
and synthesise_comp :
    IEnv.t -> Ty_env.t -> Ir.comp -> Type.t * Ty_env.t * Constraint_set.t =
        fun ienv decl_env e ->
    let synth = synthesise_comp ienv decl_env in
    let pos = WithIrMetadata.pos e in
    match (WithIrMetadata.node e) with
        | Annotate (e, ty) ->
            (* Mode switch: synthesis --> checking *)
            let env, constrs = check_comp ienv decl_env e ty in
            ty, env, constrs
        | Return v -> synthesise_val ienv decl_env v
        | New interface ->
            let open Type in
            Mailbox {
                capability = Capability.In;
                interface; pattern = One;
                (* 'New' always produces a returnable MB type *)
                quasilinearity = Quasilinearity.Returnable;
            },
            Ty_env.empty,
            Constraint_set.empty
        | Free (v, Some interface) ->
            let goal =
                let open Type in
                Mailbox {
                    capability = Capability.In;
                    interface; pattern = One;
                    (* 'New' always produces a returnable MB type *)
                    quasilinearity = Quasilinearity.Returnable;
                }
            in
            let env, constrs = check_val ienv decl_env v goal in
            (Type.unit_type, env, constrs)
        | Free (_, None) -> assert false
        (* Application is a synthesis case, since functions are always annotated. *)
        | App { func; args } ->
            (* Synthesise the type for the function.
               Note that the function will always be annotated. *)
            let fun_ty, fun_env, fun_constrs = synthesise_val ienv decl_env func in
            let arg_tys, result_ty =
                match fun_ty with
                    | Type.Fun { args; result; _ } ->
                        (args, result)
                    | ty -> Gripers.expected_function func ty [pos]
            in
            (* Check that all argument types are compatible with the annotation *)
            let zipped = List.combine args arg_tys in
            let (arg_env, arg_constrs) =
                List.fold_right (fun (x, ty) (acc_env, acc_constrs) ->
                    let (arg_env, arg_constrs) = check_val ienv decl_env x ty in
                    (* Note: arguments must have disjoint type environments *)
                    let (env, env_constrs) = Ty_env.combine ienv arg_env acc_env pos in
                    let constrs =
                        Constraint_set.union_many
                            [arg_constrs; env_constrs; acc_constrs]
                    in
                    (env, constrs))
                zipped (Ty_env.empty, Constraint_set.empty)
            in
            (* No nested evaluation contexts, so we combine function and
               argument environments, expecting disjointness. *)
            let (env, env_constrs) =
                Ty_env.combine ienv fun_env arg_env pos
            in
            (* Union constraint sets *)
            let constrs =
                Constraint_set.union_many
                [fun_constrs; arg_constrs; env_constrs]
            in
            (result_ty, env, constrs)
        | Send { target; message = (tag, payloads) ; iname } ->
            let open Type in
            (* Option.get safe since interface name will have been filled in
               by pre-type checking *)
            let iname = Option.get iname in
            let interface_withPos = IEnv.lookup iname ienv [pos] in
            let payload_types =
                Interface.lookup ~pos_list:[WithPos.pos interface_withPos; pos] tag (WithPos.node interface_withPos)
            in
            (* Check target has correct output type *)
            let target_ty =
                Mailbox {
                    capability = Out;
                    interface = iname;
                    pattern = (Message tag);
                    (* 'Send' gives the MB type the least specific
                       quasilinearity (Usable). It can be coerced to Returnable
                       via subtyping later if necessary, but we don't *need*
                       something to be Returnable for us to be able to send on
                       it. *)
                    quasilinearity = Quasilinearity.Usable
                } in
            let (mb_env, mb_constrs) = check_val ienv decl_env target target_ty in
            (* Check arguments have type specified by interface *)
            (* Now that we're TC-ing the IR, this is much more precise since
               intermediate computations will be A-normalised. *)
            let arg_env, arg_constrs =
                List.combine payloads payload_types
                |> List.fold_left (fun (env, constrs) (payload, iface_ty)  ->
                    let (chk_env, chk_constrs) = check_val ienv decl_env payload iface_ty in
                    let (env, env_constrs) = Ty_env.combine ienv env chk_env pos in
                    (env, Constraint_set.union_many
                        [constrs; chk_constrs; env_constrs])
                ) (Ty_env.empty, Constraint_set.empty)
            in
            let (env, env_constrs) = Ty_env.combine ienv mb_env arg_env pos in
            let constrs =
                Constraint_set.union_many
                [ mb_constrs; arg_constrs; env_constrs ] in
            (Type.unit_type, env, constrs)
        (* Note: Let in synthesis mode is only useful in certain situations
           because of the lack of contextual type information.

           In essence, this should only really be used when typing a top-level
           'let'. This commonly occurs due to IR conversion.
         *)
        | Let { binder; term; cont = body } ->
            let body_ty, body_env, body_constrs = synth body in
            let binder_var = Var.of_binder binder in
            let env, constrs =
                match Ty_env.lookup_opt (Var.of_binder binder) body_env with
                    | Some binder_ty ->
                        let (term_env, term_constrs) =
                            check_comp ienv decl_env term (Type.make_returnable binder_ty)
                        in
                        (* Join environments, union constraints *)
                        let (env, env_constrs) =
                            Ty_env.join ienv term_env body_env pos
                        in
                        let constrs =
                            Constraint_set.union_many
                                [body_constrs; term_constrs; env_constrs] in
                        env, constrs
                    | None ->
                        (* In this case, all we can really do is synthesise and
                           check it's not linear. *)
                        let (binder_ty, binder_env, binder_constrs) =
                            synthesise_comp ienv decl_env term in
                        (* The synthesised type must be returnable *)
                        let () =
                            if not (Type.is_returnable binder_ty) then
                                Gripers.let_not_returnable binder_ty [pos]
                        in
                        let () =
                            if Type.is_lin binder_ty then
                                Gripers.unused_synthesised_linear_var
                                binder_var binder_ty [pos]
                        in
                        let (env, env_constrs) =
                            Ty_env.join ienv binder_env body_env pos
                        in
                        let constrs =
                            Constraint_set.union_many
                                [body_constrs; binder_constrs; env_constrs]
                        in
                        env, constrs
            in
            body_ty, Ty_env.delete binder_var env, constrs
        | Seq (e1, e2) ->
            (* Check e1 has type unit, synthesise body type *)
            let (e1_env, e1_constrs) = check_comp ienv decl_env e1 Type.unit_type in
            let (e2_type, e2_env, e2_constrs) = synth e2 in
            let (env, env_constrs) = Ty_env.join ienv e1_env e2_env pos in
            let constrs =
                Constraint_set.union_many
                    [ e1_constrs; e2_constrs; env_constrs ] in
            (e2_type, env, constrs)
        | Spawn e ->
            let (env, constrs) = check_comp ienv decl_env e Type.unit_type in
            (* Since 'e' will be evaluated in a separate thread, we don't
               care about usage information. (It is of no consequence to the
               spawning thread if the child thread aliases the name, for
               example).
               For the purposes of the spawning thread, we treat all inferred
               usages as Usable. *)
            Type.unit_type, Ty_env.make_usable env, constrs
        | _ -> Gripers.cannot_synthesise e [pos]

(* Check --> Synth switch. Ensures synthesised type is subtype of checked type. *)
(* Note: This results in the loss of contextual checking information. Really,
   should only be invoked when checking constants, base variables, or
   side-effecting terms. *)
and check_to_synth : IEnv.t -> Ty_env.t -> Ir.comp -> Type.t -> Ty_env.t * Constraint_set.t =
    fun ienv decl_env e check_ty ->
        let synth_ty, synth_env, synth_constrs =
            synthesise_comp ienv decl_env e
        in
        let subty_constrs = subtype ienv synth_ty check_ty (WithIrMetadata.pos e) in
        synth_env, Constraint_set.union synth_constrs subty_constrs
(* Checking mode *)
and check_comp : IEnv.t -> Ty_env.t -> Ir.comp -> Type.t -> Ty_env.t * Constraint_set.t =
        fun ienv decl_env e ty ->
    let chk = check_comp ienv decl_env in
    let chkv = check_val ienv decl_env in
    let pos = WithIrMetadata.pos e in
    match (WithIrMetadata.node e) with
        | Return v -> check_val ienv decl_env v ty
        | Case { prety = None; _ } -> assert false
        | Case { term; prety = Some pty; branches } ->
            let (scrutinee_ty, term_env, term_constrs) =
                (* Try to check against lifted pretype.
                   If this does not work, then revert to synthesis, which will require an annotation. *)
                match Pretype.to_type pty with
                    | Some ty ->
                        let (env, constrs) = check_val ienv decl_env term ty in
                        (ty, env, constrs)
                    | None -> synthesise_val ienv decl_env term
            in
            let branch_tys =
                match scrutinee_ty with
                    | Type.Rec (tname, params) ->
                        begin match Recursive_types.find_type tname with
                        | Some def -> Recursive_types.constructor_types def params scrutinee_ty
                        | None -> raise (Gripers.expected_recursive_type scrutinee_ty [pos])
                        end
                    | _ ->
                        raise
                            (Gripers.expected_recursive_type scrutinee_ty [pos])
            in
            let lookup_tys bname =
                match List.assoc_opt bname branch_tys with
                    | Some tys -> tys
                    | None -> raise (Gripers.expected_recursive_type scrutinee_ty [pos])
            in
            (* Check each branch and collect environments and constraints *)
            let branch_results = List.map (fun (bnds, comp, bname) ->
                let expected_tys = lookup_tys bname in
                let vars = List.map Var.of_binder bnds in
                let (comp_env, comp_constrs) = chk comp ty in
                let comp_env_no_binders = Ty_env.delete_many vars comp_env in
                let () =
                    if (not (Type.is_returnable scrutinee_ty)) then
                        Ty_env.check_free_mailbox_variables [scrutinee_ty] comp_env_no_binders
                in
                let env_constrs =
                    Constraint_set.union_many
                        (List.map2 (fun var ty -> Ty_env.check_type ienv var ty comp_env pos) vars expected_tys)
                in
                (comp_env_no_binders, Constraint_set.union comp_constrs env_constrs)
            ) branches in
            (* Calculate intersection of all branch environments *)
            let (isect_env, isect_constrs) =
                match branch_results with
                | [] -> (Ty_env.empty, Constraint_set.empty)
                | (env0, _) :: rest ->
                    List.fold_left (fun (acc_env, acc_constrs) (env_i, _) ->
                        let (new_env, new_constrs) = Ty_env.intersect acc_env env_i pos in
                        (new_env, Constraint_set.union acc_constrs new_constrs)
                    ) (env0, Constraint_set.empty) rest
            in
            (* Finally combine the term env with the intersected env *)
            let env, combine_constrs =
                Ty_env.combine ienv term_env isect_env pos
            in
            let all_branch_constrs =
                Constraint_set.union_many
                    (List.map snd branch_results)
            in
            let constrs =
                Constraint_set.union_many
                    [ all_branch_constrs; isect_constrs; combine_constrs; term_constrs ]
            in
            (env, constrs)
        | Seq (e1, e2) ->
            (* Check e1 has type unit, check body type *)
            let (e1_env, e1_constrs) = chk e1 Type.unit_type in
            let (e2_env, e2_constrs) = chk e2 ty in
            let (env, env_constrs) = Ty_env.join ienv e1_env e2_env pos in
            let constrs =
                Constraint_set.union_many
                    [ e1_constrs; e2_constrs; env_constrs ] in
            (env, constrs)

        | If { test; then_expr; else_expr } ->
            let (test_env, test_constrs) = chkv test Type.bool_type in
            let (then_env, then_constrs) = chk then_expr ty in
            let (else_env, else_constrs) = chk else_expr ty in
            let (branches_env, env1_constrs) = Ty_env.intersect then_env else_env pos in
            (* Doesn't actually matter whether this is 'join' or 'combine',
               since there's no typable value with type 'bool' which will
               involve sending along a mailbox type. Using 'combine' for
               uniformity. *)
            let (env, env2_constrs) = Ty_env.combine ienv test_env branches_env pos in
            let constrs =
                Constraint_set.union_many
                    [ test_constrs; then_constrs;
                      else_constrs; env1_constrs; env2_constrs ]
            in
            (env, constrs)
        | Let { binder; term; cont = body } ->
            (* Standard BBT let-checking rule. Check body, grab type for binder,
               check binding term has compatible type. Allows us to maintain
               checking context. *)
            let body_env, body_constrs = chk body ty in
            (* Binder might be unused. This is fine if the type is unrestricted. *)
            (* Strategy:
                  - If it's used in the continuation, then check as usual
                  - Otherwise, we need to revert back to synthesis
               This has the potential for incompleteness (for example if we
               have an unrestricted mailbox type)
             *)
            let binder_var = Var.of_binder binder in
            let env, constrs =
                match Ty_env.lookup_opt (Var.of_binder binder) body_env with
                    | Some binder_ty ->
                        (* Check subject of the let, based on the inferred type. *)
                        (* Regardless of whether the inferred type was inferred
                         to be Usable or Returnable, it *must* be treatable as
                         Returnable in the subject of the let. *)
                        let (term_env, term_constrs) =
                            chk term (Type.make_returnable binder_ty)
                        in
                        (* Join environments, union constraints *)
                        let (env, env_constrs) =
                            Ty_env.join ienv term_env body_env pos
                        in
                        let constrs =
                            Constraint_set.union_many
                                [body_constrs; term_constrs; env_constrs] in
                        (env, constrs)
                    | None ->
                        (* In this case, all we can really do is synthesise and
                           check it's not linear. *)
                        let (binder_ty, binder_env, binder_constrs) =
                            synthesise_comp ienv decl_env term in
                        (* The synthesised type must be returnable *)
                        let () =
                            if not (Type.is_returnable binder_ty) then
                                Gripers.let_not_returnable binder_ty [pos]
                        in
                        let unr_constrs = Type_utils.make_unrestricted binder_ty pos in
                        let (env, env_constrs) =
                            Ty_env.join ienv binder_env body_env pos
                        in
                        let constrs =
                            Constraint_set.union_many
                                [body_constrs; binder_constrs; env_constrs; unr_constrs]
                        in
                        (env, constrs)
            in
            (Ty_env.delete binder_var env, constrs)
        (* LetTuple is similar to Let. Annoyingly we must revert to synthesis of the tuple if
           *any* binder is unused in the continuation. Wildcard patterns / addition of type
           constraints could help. *)
        | LetTuple { binders; tuple; cont = body } ->
            (* Check body type and extract types for binders *)
            let body_env, body_constrs = chk body ty in
            (* Either binder might be unused.
               Revert to synthesis if we don't have type info for both. *)
            let bnd_vars =
                List.map fst binders
                |> List.map (Var.of_binder)
            in
            let inferred_tys =
                List.map (fun var -> Ty_env.lookup_opt var body_env) bnd_vars
            in
            (* Default type: special case interface types -- only way something can be an MB but
               not used is if it's a returnable !1 mailbox type*)
            let default_ty = function
                | Pretype.PInterface iname ->
                        Some Type.(mailbox_send_unit iname Quasilinearity.Returnable)
                | pty -> Pretype.to_type pty
            in
            let get_check_ty pty = function
                | Some ty ->
                    if not @@ Settings.(get liberal_datatypes) then
                        Some (Type.make_returnable ty)
                    else
                        Some ty
                | None -> default_ty pty
            in
            (* Precondition: pretypes have already been filled in during pre-typing,
               so Option.get is safe *)
            let ptys = List.map (Option.get << snd) binders in
            let check_tys =
                List.map (uncurry get_check_ty) (List.combine ptys inferred_tys)
            in
            let env, constrs =
                (* In this case we check consistency with the declared types. *)
                if (List.for_all Option.is_some check_tys) then
                    let check_tys = List.map Option.get check_tys in
                    let target_ty = Type.make_tuple_type check_tys in
                    let (term_env, term_constrs) =
                            check_val ienv decl_env tuple target_ty
                    in
                    let body_env_no_binders = Ty_env.delete_many bnd_vars body_env in
                    (* Combine environments, union constraints *)
                    let (env, env_constrs) =
                        Ty_env.combine ienv term_env body_env_no_binders pos
                    in
                    (* Do continuation aliasing check if any component is non-returnable
                       (e.g. if we are using liberal DTs) *)
                    let () =
                        if not @@ List.for_all (Type.is_returnable) check_tys then
                            Ty_env.check_free_mailbox_variables check_tys body_env_no_binders
                    in
                    let constrs =
                        Constraint_set.union_many
                            [body_constrs; term_constrs; env_constrs] in
                    (env, constrs)
                else
                    (* In this case, all we can really do is synthesise and
                       check it's not linear.
                       This should only happen for the case where we have a
                       function returning an MB type.*)
                    let (tuple_ty, tuple_env, tuple_constrs) =
                        synthesise_val ienv decl_env tuple
                    in
                    let component_tys =
                        match tuple_ty with
                            | Type.Tuple tys ->
                                if not @@ Settings.(get liberal_datatypes) then
                                    List.map Type.make_returnable tys
                                else
                                    tys
                            | _ -> Gripers.expected_tuple_type tuple_ty [pos]
                    in
                    (* If any of the types are actually found in the continuation, then check subtype.
                       If not, then we need to generate unrestrictedness constraints *)
                    let ty_constrs declared maybe_ty =
                        match maybe_ty with
                            | Some inferred -> Type_utils.subtype ienv inferred declared
                            | None -> Type_utils.make_unrestricted declared
                    in
                    (* maybe_ty --> inferred_tys *)
                    let ty_consistency_constrs =
                        List.combine component_tys inferred_tys
                        |> List.map (fun (cty, ity) -> ty_constrs cty ity pos)
                        |> Constraint_set.union_many
                    in
                    let body_env_no_binders = Ty_env.delete_many bnd_vars body_env in
                    let (env, env_constrs) =
                        Ty_env.combine ienv tuple_env body_env_no_binders pos
                    in
                    (* Do continuation aliasing check if any component is non-returnable
                       (e.g. if we are using liberal DTs) *)
                    let () =
                        if not @@ List.for_all (Type.is_returnable) component_tys then
                            Ty_env.check_free_mailbox_variables component_tys body_env_no_binders
                    in
                    let constrs =
                        Constraint_set.union_many
                            [body_constrs; tuple_constrs; env_constrs; ty_consistency_constrs]
                    in
                    (env, constrs)
            in
            (env, constrs)
        | Guard { iname = None; _ } -> (* Should have been filled in by pre-typing *)
            assert false
        | Guard { target; pattern; guards; iname = Some iname } ->
            let open Type in
            (* Check guard types, and generate constraints, and pattern for guards *)
            let (guards_env, guards_pat, guards_constrs) =
                check_guards ienv decl_env iname pattern guards ty in
            (* Check to see whether the MB handle can be given a type that's
               compatible with the synthesised pattern. *)
            let target_ty = Mailbox {
                capability = In;
                interface = iname;
                pattern = guards_pat;
                (* We can only receive on a Returnable guard (since the name
                   goes out of scope afterwards) *)
                quasilinearity = Quasilinearity.Returnable
            } in
            (* Regardless of how it is used in the continuation, the mailbox
               we're receiving from must be returnable. *)
            let (target_env, target_constrs) =
                chkv target (Type.make_returnable target_ty)
            in
            let (env, env_constrs) =
                Nullable_env.combine ienv target_env guards_env pos
            in
            (* The pattern annotation must be *included* in the inferred pattern.
               The reason this is inclusion rather than equivalence is that we
               should be able to add in additional guards which are not included
               in the annotation (which will necessarily have the unreliable
               mailbox in their continuation and need to discard the MB using
               'fail'.)
             *)
            let pat_constrs =
                Constraint_set.single_constraint pattern guards_pat
            in
            let constrs =
                Constraint_set.union_many
                    [guards_constrs;
                     target_constrs;
                     env_constrs;
                     pat_constrs]
            in
            (env, constrs)
        | _ ->
            (* If we don't have a checking rule, it might be possible to
               synthesise and then check the result. *)
            (* This is certainly the case for base variables and constants. *)
            (* We want to avoid this if we can otherwise, though, since it means
               we've lost any contextual information about variable typing. *)
            check_to_synth ienv decl_env e ty

(* Synthesises types for all guards, checks that their types are compatible, and
 * returns the intersection of the resulting environments and generated pattern. *)
and check_guards :
    IEnv.t -> Ty_env.t -> interface_name -> Type.Pattern.t -> Ir.guard list ->
        Type.t -> Nullable_env.t * Type.Pattern.t * Constraint_set.t =
        fun ienv decl_env iname guard_pat gs ty ->
          let open Ir in
          let open Type in
          (* Do a duplication check on guards *)
          let _ =
            List.fold_left (fun (empty, fail, tags) x ->
              let pos = WithIrMetadata.pos x in
              match WithIrMetadata.node x with
                | Empty _ ->
                    if empty then
                      Gripers.multiple_empty () [pos]
                    else
                      (true, fail, tags)
                | Fail ->
                    if fail then
                      Gripers.multiple_fail () [pos]
                    else
                      (empty, true, tags)
                | Receive { tag; _ } ->
                    if List.mem tag tags then
                      Gripers.multiple_receive tag [pos]
                    else
                      (empty, fail, tag :: tags)
            ) (false, false, []) gs in

          (* Typecheck each non-fail guard, and infer an environment. *)
          (* Check types are the same, and calculate the environment merge,
             pattern, and final constraint set. *)
          List.fold_left (fun (env, pat, acc_constrs) g ->
            (* TC Guard *)
            let (g_env, g_pat, g_constrs) =
              check_guard ienv decl_env iname guard_pat g ty
            in
            (* Calculate environment intersection *)
            let (env, env_constrs) = Nullable_env.intersect g_env env (WithIrMetadata.pos g) in
            let constrs =
              Constraint_set.union_many
                [g_constrs; env_constrs; acc_constrs] in
            (env, Pattern.Plus (pat, g_pat), constrs) )
          (Nullable_env.null, Pattern.Zero, Constraint_set.empty) gs

(* Checks the type for a single guard, returning type, environment, pattern,
   and constraint set. *)
and check_guard :
    IEnv.t -> Ty_env.t -> interface_name -> Type.Pattern.t -> Ir.guard -> Type.t ->
        Nullable_env.t * Type.Pattern.t * Constraint_set.t =
        fun ienv decl_env iname pat g ty ->
          let open Ir in
          let open Type in
          let pos = WithIrMetadata.pos g in
          match (WithIrMetadata.node g) with
            | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
                let (env, cont_constrs) = check_comp ienv decl_env cont ty in
                let payload_iface_tys =
                    let interface_withPos = IEnv.lookup iname ienv [pos] in
                    Interface.lookup ~pos_list:[(WithPos.pos interface_withPos); pos] tag (WithPos.node interface_withPos)
                in
                (* Check that the received values have types consistent with the
                   interface annotations. *)
                let check_payload_ty payload_binder interface_ty =
                    match Ty_env.lookup_opt (Var.of_binder payload_binder) env with
                        | Some payload_ty ->
                            (* The type we're checking against has to only be usable:
                               we can't have the received value escaping the
                               receive block, otherwise we get the potential for
                               aliasing. *)
                            subtype ienv
                                (Type.make_usable interface_ty)
                                payload_ty
                        | None ->
                            Type_utils.make_unrestricted interface_ty
                in
                let payload_ty_constrs =
                    List.combine payload_binders payload_iface_tys
                    |> List.fold_left (fun constrs (bnd, iface_ty) ->
                        check_payload_ty bnd iface_ty pos
                        |> Constraint_set.union constrs
                    ) Constraint_set.empty
                in
                let mb_ty =
                    Ty_env.lookup_opt (Var.of_binder mailbox_binder) env in
                (* Grab types for payload and MB binders *)
                let mb_pat =
                  match mb_ty with
                    | Some Mailbox {
                        capability = Capability.In; pattern = pat; _ } -> pat
                    | Some ty ->
                        Gripers.expected_receive_mailbox
                            (Var.of_binder mailbox_binder)
                            ty
                            [pos]
                    | None ->
                        Gripers.unused_mailbox_variable
                            (Var.of_binder mailbox_binder)
                            [pos]
                in

                (* Delete payload and MB binders from calculated env *)
                let env =
                  List.fold_right (Ty_env.delete_binder) payload_binders env
                  |> Ty_env.delete_binder mailbox_binder
                in
                (* Ensure that we check aliases based on the specified strategy
                -- if None then we will default to system setting *)
                Ty_env.check_free_mailbox_variables ?strategy payload_iface_tys env;
                (* Calculate the derivative wrt. the tag, and ensure via a
                   constraint that it is included in the calculated payload
                   type. *)
                let deriv = Pattern.tag_derivative tag pat in
                let constrs =
                      Constraint_set.single_constraint deriv mb_pat
                      |> Constraint_set.union cont_constrs
                      |> Constraint_set.union payload_ty_constrs
                in
                (* Final calculated pattern is the message concatenated with the
                   calculated resulting pattern. *)
                let res_pat =  Pattern.(Concat (Message tag, deriv)) in
                (Nullable_env.of_env env, res_pat, constrs)
            | Empty (mailbox_binder, e) ->
                let (env, constrs) = check_comp ienv decl_env e ty in
                let mb_ty =
                    Ty_env.lookup_opt (Var.of_binder mailbox_binder) env
                in
                (* Inferred type should be ?1 *)
                let goal =
                    Type.Mailbox {
                        capability = Capability.In;
                        interface = iname;
                        pattern = One;
                        quasilinearity = Quasilinearity.Returnable;
                    }
                in
                let mb_empty_constr =
                    match mb_ty with
                        | Some mb_ty -> Type_utils.subtype ienv goal mb_ty pos
                        | None ->
                            Gripers.unused_mailbox_variable
                                (Var.of_binder mailbox_binder)
                                [pos]
                in
                let env =
                    env
                    |> Ty_env.delete_binder mailbox_binder
                    |> Nullable_env.of_env
                in
                (env, One,
                    Constraint_set.union mb_empty_constr constrs)
            | Fail ->
                (Nullable_env.null, Zero, Constraint_set.empty)

(* Declarations have a top-level annotation, so it only makes sense to check them. *)
(* The result of checking each definition should be a typing environment with a
   reference to the definition, and calls to any other definition. We should
   check that each variable contained in the output is unbound.

   NOTE: Although it may be the case that a call to a function is inferred to
   have subtypes of arguments & supertype of result, we must retain the original
   type for each declaration.
*)
let check_decls ienv decls =
    let decl_nodes = decls in
    (* List of allowed free names: all declaration names. Primitive names won't
     get added into the environment at all. *)
    let allowed_free_names =
        List.map (fun d -> Var.of_binder d.decl_name) decl_nodes
    in
    let decl_env =
        let decl_entry d =
            let args = List.map snd d.decl_parameters in
            Var.of_binder d.decl_name,
            Type.make_function_type false args d.decl_return_type
        in
        List.map decl_entry decl_nodes
        |> Ty_env.from_list
    in

    (* Function which checks inferred environment against reference environment,
       returning subtyping constraints *)
    (* Note: we don't need to do any checks to ensure that the variables have
       been used in a way consistent with the annotations on each declaration;
       this will have been done in the App case. *)
    let check_free_vars : Ir.Var.t -> Ty_env.t -> unit =
        fun decl_name env ->
            Ty_env.iter (fun x _ ->
                if not (List.mem x allowed_free_names) then
                    Gripers.unexpected_free_var x decl_name []) env
    in

    (* Function which typechecks the body of a declaration, ensuring usages of
       arguments are consistent with their annotations.
       Returns the inferred typing environment for the declaration (with
       arguments removed), along with generated constraints. *)
    let check_decl d =
        let pos = WithIrMetadata.pos d.decl_body in
        let (env, body_constrs) =
            check_comp ienv decl_env d.decl_body d.decl_return_type
        in
        (* Check arguments; remove from environment *)
        let (env, arg_constrs) =
            (* Each inferred argument type should be a subtype of the
               declared type. *)
            List.fold_left (fun (acc_env, acc_constrs) (param, param_ty) ->
                let param_constrs =
                    (* It may be the case that the parameter is actually unused
                       in the function body. This is fine, as long as the type
                       is unrestricted.
                     *)
                    match Ty_env.lookup_opt (Var.of_binder param) acc_env with
                        | Some inferred_param_ty ->
                            subtype ienv param_ty inferred_param_ty pos
                        | None ->
                            make_unrestricted param_ty pos
                in
                (Ty_env.delete_binder param acc_env,
                 Constraint_set.union param_constrs acc_constrs)
            ) (env, Constraint_set.empty) d.decl_parameters
        in
        (* Check environment is consistent with reference environment *)
        check_free_vars (Var.of_binder d.decl_name) env;
        Constraint_set.union
            body_constrs
            arg_constrs
    in

    let decl_constrs =
        List.map check_decl decl_nodes
        |> Constraint_set.union_many
    in
    (* Finally, return reference environment and gathered constraints *)
    decl_env, decl_constrs


(* PRECONDITION: By now, annotation pass should have run, so each of the
   interfaces should be decorated with at least a pattern variable. *)
let synthesise_program { prog_interfaces; prog_decls; prog_body } =
    let ienv =
        prog_interfaces
        |> List.map (WithPos.make ~pos:Position.dummy)
        |> IEnv.from_list
    in
    let (decl_env, decl_constrs) = check_decls ienv prog_decls in
    (* If we have a body, synthesise type and combine environments.
       Otherwise, return unit and the decl env / constraints. *)
    match prog_body with
        | Some body ->
            let ty, body_env, body_constrs = synthesise_comp ienv decl_env body in
            let env, env_constrs = Ty_env.combine ienv decl_env body_env (WithIrMetadata.pos body) in
            let constrs =
                Constraint_set.union_many
                    [decl_constrs; body_constrs; env_constrs]
            in
            ty, env, constrs
        | None ->
            Type.unit_type, decl_env, decl_constrs

(* Similar to the above, but checks the body type rather than
   synthesising it. *)
let check_program { prog_interfaces; prog_decls; prog_body } ty =
    let ienv =
        prog_interfaces
        |> List.map (WithPos.make ~pos:Position.dummy)
        |> IEnv.from_list
    in
    let (decl_env, decl_constrs) = check_decls ienv prog_decls in
    (* If we have a body, synthesise type and combine environments.
       Otherwise,  *)
    match prog_body with
        | Some body ->
            let body_env, body_constrs = check_comp ienv decl_env body ty in
            let env, env_constrs = Ty_env.combine ienv decl_env body_env (WithIrMetadata.pos body) in
            let constrs =
                Constraint_set.union_many
                    [decl_constrs; body_constrs; env_constrs]
            in
            env, constrs
        | None ->
            decl_env, decl_constrs
