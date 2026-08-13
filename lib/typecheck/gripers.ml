(* Type errors. *)
open Common

let constraint_gen_error ?subsystem message pos_list =
    Errors.Constraint_gen_error { subsystem; message; pos_list}

let synth_variable v pos_list =
    let msg =
        Format.asprintf
            "Cannot synthesise type for variable %a: Only able to synthesise
            base variable types" Ir.Var.pp_name v
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSynth) msg pos_list)

let subtype_cap_mismatch t1 t2 pos_list =
    let msg =
      Format.asprintf
        "%a and %a incompatible due to mismatching capabilities."
        Type.pp t1 Type.pp t2
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSubtype) msg pos_list)

let subtype_mismatch t1 t2 pos_list =
    let msg =
        Format.asprintf
            "Types %a and %a are incompatible."
            Type.pp t1 Type.pp t2
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSubtype) msg pos_list)

let desugaring () pos_list =
    raise (constraint_gen_error "SugarFree / SugarFail should have been desugared." pos_list )

let cannot_synthesise c pos_list =
    let msg =
        Format.asprintf
            "Unable to synthesise a type for %a. Try adding a type annotation."
            Ir.pp_comp c
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSynth) msg pos_list)

let cannot_synthesise_value v pos_list =
    let msg =
        Format.asprintf
            "Unable to synthesise a type for %a. Try adding a type annotation."
            Ir.pp_value v
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSynth) msg pos_list)


let interface_mismatch expected actual pos_list =
    let msg =
        Printf.sprintf
            "Interface mismatch: expected %s but got %s"
            expected actual
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheck) msg pos_list)

let var_expected_mailbox v ty pos_list =
    let msg =
        Format.asprintf
            "Expected a mailbox type for variable %a, got %a."
            Ir.Var.pp_name v Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheck) msg pos_list)

let var_expected_function v ty pos_list =
    let msg =
        Format.asprintf
            "Expected a function type for variable %a, got %a."
            Ir.Var.pp_name v Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheck) msg pos_list)
let unused_synthesised_linear_var v ty pos_list =
    let msg =
        Format.asprintf
            "Synthesised type for variable %a (%a) is linear, but is not used in the body of the let-binding."
            Ir.Var.pp_name v Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheck) msg pos_list)

let multiple_empty () pos_list =
    raise (constraint_gen_error
        ~subsystem:(Errors.GenCheckGuard)
        "At most one `empty` guard allowed." pos_list)

let multiple_fail () pos_list =
    raise (constraint_gen_error
        ~subsystem:(Errors.GenCheckGuard)
        "At most one `fail` guard allowed." pos_list)

let multiple_receive tag pos_list =
    let msg =
        Printf.sprintf "At most one receive guard allowed for each tag (%s duplicated)"
        tag
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckGuard) msg pos_list)

let unused_guard_payload var ty pos_list =
    let msg =
        Format.asprintf
            "Variable %a of linear type %a unused in guard body"
            Ir.Var.pp_name var Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckGuard) msg pos_list)

let expected_receive_mailbox v ty pos_list =
    let msg =
        Format.asprintf
           "Expected %a to have a receive mailbox type. Instead, it has type %a"
           Ir.Var.pp_name v Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckGuard) msg pos_list)

let unused_mailbox_variable v pos_list =
    let msg =
        Format.asprintf
            "Mailbox variable %a unused in receive guard body"
            Ir.Var.pp_name v
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckGuard) msg pos_list)

let unexpected_free_var v decl pos_list =
    let msg =
        Format.asprintf
            "Variable %a appears free in declaration %a"
            Ir.Var.pp_name v Ir.Var.pp_name decl in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckDecls) msg pos_list)

let unused_parameter v fn_name ty pos_list =
    let msg =
        Format.asprintf
            "Parameter %s of function %s has linear type %a but was unused"
            v fn_name Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenCheckDecls) msg pos_list )


let subtype_linearity_mismatch t1 t2 pos_list =
    let msg =
        Format.asprintf
            "Function types %a and %a have mismatching linearities."
            Type.pp t1 Type.pp t2
    in
    raise (constraint_gen_error ~subsystem:(Errors.GenSubtype) msg pos_list )

let cannot_make_unrestricted t pos_list=
    let msg =
        Format.asprintf
            "Type %a cannot be treated as unrestricted."
            Type.pp t
    in
    raise (constraint_gen_error msg pos_list )

(* let constraint_gen_error ?subsystem message =
    Errors.Constraint_gen_error { subsystem; message } *)

let undefined_env op pos_list =
    let msg =
        Printf.sprintf
            "Cannot perform operation %s on an undefined typing environment."
            op
    in
    raise (constraint_gen_error msg pos_list )

let join_two_recvs var pos_list =
    let msg =
        Format.asprintf
            "Cannot join two input capabilities for variable %a (linearity violation)"
            Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem:Errors.GenJoin msg pos_list )

let env_interface_mismatch is_join t1 t2 var iface1 iface2 pos_list =
    let subsystem =
        if is_join then Errors.GenJoin else Errors.GenIntersect
    in
    let msg =
        Format.asprintf
            "Unable to combine types %a and %a for variable %a as they have different interfaces (%s and %s)."
            Type.pp t1 Type.pp t2 Ir.Var.pp_name var iface1 iface2
    in
    raise (constraint_gen_error ~subsystem msg pos_list )

let type_mismatch is_join t1 t2 var pos_list =
    let subsystem =
        if is_join then Errors.GenJoin else Errors.GenIntersect
    in
    let msg =
        Format.asprintf
            "Unable to combine types %a and %a for variable %a."
            Type.pp t1 Type.pp t2 Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem msg pos_list )

let inconsistent_branch_capabilities var pos_list =
    let msg =
        Format.asprintf "Variable %a used at inconsistent capabilities across branches."
        Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem:Errors.GenJoin msg pos_list )

let branch_linearity var pos_list =
    let msg =
        Format.asprintf
            "Linear variable %a must appear in every branch."
            Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem:Errors.GenIntersect msg pos_list )


let combine_mailbox_type var pos_list =
    let msg =
        Format.asprintf
            "Linear variable %a which contains a mailbox type cannot be used in two separate environments. This typically happens when aliasing a mailbox type, or attempting to use a mailbox variable both as a target for a guard and in its continuation."
            Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCombine msg pos_list )

let guard_send_return_type ty pos_list =
    let msg =
        Format.asprintf
            "The return type of a guard cannot be a send mailbox type, but got %a."
            Type.pp ty
    in
    raise (constraint_gen_error msg pos_list )

let unrestricted_recv_env var ty pos_list =
    let msg =
        Format.asprintf
            "The body of a receive guard or case expression cannot contain free mailbox variables, but variable %a has type %a."
            Ir.Var.pp_name var Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheckGuard msg pos_list)

let function_annotation result pos_list =
    let msg =
        Format.asprintf
            "Cannot synthesise the type of a function which returns a mailbox type. Here, the function has pretype %a. Consider adding an annotation."
            Pretype.pp result
    in
    raise (constraint_gen_error ~subsystem:Errors.GenSynth msg pos_list )

let expected_function func instead pos_list =
    let msg =
        Format.asprintf
            "Cannot apply non-function %a with type %a."
            Ir.pp_value func
            Type.pp instead
    in
    raise (constraint_gen_error ~subsystem:Errors.GenSynth msg pos_list )

let expected_tuple_type instead pos_list =
    let msg =
        Format.asprintf
            "Expected a tuple type, but got %a."
            Type.pp instead
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheck msg pos_list)

let expected_recursive_type instead pos_list =
    let msg =
        Format.asprintf
            "Expected a recursive type, but got %a."
            Type.pp instead
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheck msg pos_list)

let invalid_ql_sequencing var pos_list =
    let msg =
        Format.asprintf
            "Mailbox variable %a was used after being consumed by a 'guard' or a 'let' binding."
            Ir.Var.pp_name var
    in
    raise (constraint_gen_error ~subsystem:Errors.GenJoin msg pos_list)

let quasilinearity_mismatch x1 x2 pos_list =
    (* Not the best error message, alas. *)
    let ql1 = Type.get_quasilinearity x1 in
    let ql2 = Type.get_quasilinearity x2 in
    let msg =
        Format.asprintf
            "Mailbox type %a is not a subtype of %a, as the former is %a and the latter is %a. Allowed: Usable < Usable, Returnable < Returnable, Returnable < Usable."
            Type.pp x1
            Type.pp x2
            Type.Quasilinearity.pp ql1
            Type.Quasilinearity.pp ql2
    in
    raise (constraint_gen_error ~subsystem:Errors.GenSubtype msg pos_list )

let let_not_returnable ty pos_list =
    let msg =
        Format.asprintf
            "The subject of a let-binding must be returnable. However, type %a is only usable."
            Type.pp ty
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheck msg pos_list)

let duplicate_interface_receive_env var iface pos_list =
    let msg =
        Format.asprintf
            "To prevent unsafe aliasing, no other variables of the same interface as a received variable may be present in the body of a receive guard or a case expression. However, variable %a also has interface name %s."
            Ir.Var.pp_name var
            iface
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheck msg pos_list)

let pretype_consistency ty pty pos_list =
    let msg =
        Format.asprintf
            "Type %a is not consistent with pretype %a."
            Type.pp ty
            Pretype.pp pty
    in
    raise (constraint_gen_error ~subsystem:Errors.GenCheck msg pos_list)
