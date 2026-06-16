open Common

let desugar p =
    p
    |> Insert_pattern_variables.annotate
    |> Desugar_let_annotations.desugar
    |> Desugar_sugared_guards.desugar

let with_reference_counting (ir : Ir.program) =
    let transform_comp c =
        Interp.Reference_counting.insert_reference_counting Ir.VarSet.empty (Ir.free_variables c) c
    in
    let transform_decl decl_with_pos =
        let pos = Source_code.WithPos.pos decl_with_pos in
        let (decl : Ir.decl) = Source_code.WithPos.node decl_with_pos in
        let parameter_vars =
            decl.decl_parameters
            |> List.map (fun (b, _) -> Ir.Var.of_binder b)
            |> Ir.VarSet.of_list
        in
        let decl_owned = Ir.VarSet.union parameter_vars (Ir.free_variables decl.decl_body) in
        let decl_body =
            Interp.Reference_counting.insert_reference_counting Ir.VarSet.empty decl_owned decl.decl_body
        in
        Source_code.WithPos.make ~pos { decl with decl_body }
    in
    {
        ir with
            prog_decls = List.map transform_decl ir.prog_decls;
            prog_body = Option.map transform_comp ir.prog_body;
    }

let typecheck p ir = 
    let () =
        if Settings.(get show_ir) then
            Format.printf
                "=== Intermediate Representation: ===\n%a\n\n"
                (Ir.pp_program) ir
    in
    let () =
        if Settings.(get show_ref_counting) then
            Format.printf
                "=== With Reference Counting: ===\n%a\n\n"
                Ir.pp_program
                (with_reference_counting ir)
    in
    let ir, prety_opt = Typecheck.Pretypecheck.check ir in
    let (ty, env, constrs) = Typecheck.Gen_constraints.synthesise_program ir in
    let solution = Typecheck.Solve_constraints.solve_constraints constrs in
    let p = Sugar_ast.substitute_solution solution p in
    let ir = Ir.substitute_solution solution ir in
    (p, prety_opt, ir, ty, env, constrs)

(* Frontend pipeline *)
let pipeline p =
    let p = desugar p in
    let ir = Sugar_to_ir.transform p in
    let benchmark_count = Settings.(get benchmark) in
    let () =
        if benchmark_count >= 0 then
            Benchmark.benchmark benchmark_count (fun () -> typecheck p ir)
    in
    typecheck p ir
