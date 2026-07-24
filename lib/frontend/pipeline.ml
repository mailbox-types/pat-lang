open Common

let desugar p =
    p
    |> Insert_pattern_variables.annotate
    |> Desugar_let_annotations.desugar
    |> Desugar_sugared_guards.desugar

let with_reference_counting prog : Ir.program = 
    Interp.Reference_counting.insert_reference_counting prog 

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
    let () =
        if not Settings.(get typecheck_only) then
            let rc_ir = with_reference_counting ir in
            Interp.Eval.run_program rc_ir
    in
    (p, prety_opt, ir, ty, env, constrs)

(* Frontend pipeline *)
let pipeline p =
    let p = desugar p in
    let ir = Sugar_to_ir.transform p in
    let benchmark_count = Settings.(get benchmark) in
    let () =
        if benchmark_count >= 0 then
            Util.Benchmark.benchmark benchmark_count (fun () -> typecheck p ir)
    in
    typecheck p ir
