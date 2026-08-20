open Common
open Common_types
open Evaluation_ir
open Runtime_common

let max_steps_before_yield = 20

module VarMap = Runtime_common.VarMap
module RuntimeNameMap = Map.Make(RuntimeName)

let unit_value = Tuple []
let mk_const c = Constant c
let mk_name a = Name a

let runtime_of_ir env value = RuntimeValue.of_ir env value

type environment = value_env

type computation_frame =
  | SeqFrame of {
    saved_env: environment;
    next_comp: comp;
  }
  | LetFrame of {
    binder: Var.t;
    saved_env: environment;
    next_comp: comp;
  }

type computation_state = {
  decls: decl VarMap.t;
  current_comp: comp;
  env: environment;
  stack: computation_frame list
}

type step_result =
  | Stepped of computation_state
  | Finished

let lookup_env env var =
  match VarMap.find_opt var env with
  | Some value -> value
  | None ->
    runtime_error (Format.asprintf "Unbound runtime variable %a" Var.pp var)

let decl_map program =
  List.fold_left
    (fun acc decl ->
      let var = Var.of_binder decl.decl_name in
      VarMap.add var decl acc)
    VarMap.empty
    program.prog_decls

(* Resolves a bare variable to a closed runtime value. An unbound variable referring
   to a top-level declaration resolves to a [Declaration], rather than being an error. *)
let force_var decls env var : RuntimeValue.t =
  match VarMap.find_opt var env with
  | Some bound -> bound
  | None ->
    begin
      match VarMap.find_opt var decls with
      | Some _ -> RuntimeValue.Declaration var
      | None -> runtime_error (Format.asprintf "Unbound variable: %a" Var.pp var)
    end

(* Fully resolves a value to a closed runtime value, substituting any free variables from the
   environment. *)
let force_value decls env value : RuntimeValue.t =
  match value with
  | Variable var -> force_var decls env var
  | _ -> RuntimeValue.of_ir env value

let runtime_name_of_value env value =
  match RuntimeValue.of_ir env value with
  | RuntimeValue.Name runtime_name -> runtime_name
  | v ->
    runtime_error
      (Format.asprintf "Expected a mailbox runtime name value, got: %a" RuntimeValue.pp v)

let runtime_name_of_runtime_value value =
  match value with
  | RuntimeValue.Name runtime_name -> Some runtime_name
  | _ -> None

let runtime_name_of_var env var =
  match VarMap.find_opt var env with
  | Some (RuntimeValue.Name n) -> n
  | Some _ -> runtime_error "Non runtime-name in runtime_name_of_var"
  | None -> runtime_error (Format.asprintf "Unbound variable: %a" Var.pp var)


let lookup_runtime_names env vars =
  List.filter_map
    (fun (var, count) ->
      match lookup_env env var |> runtime_name_of_runtime_value with
      | None -> None
      | Some name -> Some (name, count))
    vars

(* Looks up the definition, free variable set, and stored environment of a closure. *)
let lookup_lambda runtime name =
  match Runtime.lookup_tracked_value runtime name with
    | RuntimeValue.Closure { lambda; value_env } ->
      let fvs =
        value_env
        |> VarMap.bindings
        |> List.map fst
        |> VarSet.of_list
      in
      (lambda, fvs, value_env)
    | bad ->
      runtime_error
        (Format.asprintf "Looking up lambda in RC map: name %a maps to non-lambda %a"
          RuntimeName.pp name Evaluation_ir.pp_value (RuntimeValue.to_ir bad))

let lookup_constructor runtime name =
  match Runtime.lookup_tracked_value runtime name with
    | RuntimeValue.Inject (tag, values) -> (tag, values)
    | bad ->
      runtime_error
        (Format.asprintf "Looking up inject in RC map: name %a maps to non-inject %a"
          RuntimeName.pp name Evaluation_ir.pp_value (RuntimeValue.to_ir bad))

let lookup_tuple runtime name =
  match Runtime.lookup_tracked_value runtime name with
    | RuntimeValue.Tuple values -> values
    | bad ->
      runtime_error
        (Format.asprintf "Looking up tuple in RC map: name %a maps to non-tuple %a"
          RuntimeName.pp name Evaluation_ir.pp_value (RuntimeValue.to_ir bad))

let init_state program comp =
  { decls = decl_map program; current_comp = comp; env = VarMap.empty; stack = [] }

let install_seq_frame saved_env next_comp state =
  { state with stack = SeqFrame { saved_env; next_comp } :: state.stack }

let install_let_frame binder saved_env next_comp state =
  { state with stack = LetFrame { binder; saved_env; next_comp } :: state.stack }

(* If the returned expression is a closure, tuple, or data constructor, then we
   need to reference count it and return a runtime name. *)
let handle_return runtime state value =
  (* We can only store a closed runtime value in the environment, so we need to substitute any FVs. *)
  let forced = force_value state.decls state.env value in
  match state.stack with
    | [] -> Finished
    | SeqFrame { saved_env; next_comp } :: other_frames ->
        Stepped { state with current_comp = next_comp; env = saved_env; stack = other_frames }
    | LetFrame { binder; saved_env; next_comp } :: other_frames ->
      if Runtime_common.should_ref_count forced then
        let new_ref = Runtime.record_value runtime forced in
        let env' =
          VarMap.add binder (RuntimeValue.Name new_ref) saved_env
        in
        Stepped { state with current_comp = next_comp; env = env'; stack = other_frames }
      else
        let env' = VarMap.add binder forced saved_env in
        Stepped { state with current_comp = next_comp; env = env'; stack = other_frames }

let rec bind_many binders values env =
  match binders, values with
  | [], [] -> env
  | binder :: binders, value :: values ->
    bind_many binders values (VarMap.add (Var.of_binder binder) (runtime_of_ir env value) env)
  | _ -> runtime_error "Arity mismatch while binding values"

let rec bind_many_rt binders values env =
  match binders, values with
  | [], [] -> env
  | binder :: binders, value :: values ->
    bind_many_rt binders values (VarMap.add (Var.of_binder binder) value env)
  | _ -> runtime_error "Arity mismatch while binding values"


let bind binder value env =
  VarMap.add (Var.of_binder binder) (runtime_of_ir env value) env

let bool_of_value decls env value =
  match force_value decls env value with
  | RuntimeValue.Constant (Constant.Bool b) -> b
  | forced ->
    runtime_error
      (Format.asprintf "Expected boolean test value, got: %a" RuntimeValue.pp forced)

let tuple_values_of_var decls env var =
  (* FIXME: if the tuple was heap-allocated (returned via a `let`), var resolves to a
     RuntimeValue.Name rather than a Tuple; need a Perceus-style borrow/dereference through
     the RC table here (cf. lookup_lambda, which only handles the Closure case). *)
  match force_var decls env var with
  | RuntimeValue.Tuple values -> values
  | forced ->
    runtime_error
      (Format.asprintf "Expected tuple value, got: %a" RuntimeValue.pp forced)

let int_of_value value =
  match value with
  | RuntimeValue.Constant (Constant.Int i) -> i
  | _ ->
    runtime_error
      (Format.asprintf "Expected integer value, got: %a" RuntimeValue.pp value)

let string_of_value value =
  match value with
  | RuntimeValue.Constant (Constant.String s) -> s
  | _ ->
    runtime_error
      (Format.asprintf "Expected string value, got: %a" RuntimeValue.pp value)

let bool_runtime_of_value value =
  match value with
  | RuntimeValue.Constant (Constant.Bool b) -> b
  | _ ->
    runtime_error
      (Format.asprintf "Expected boolean value, got: %a" RuntimeValue.pp value)

let expect_arity prim expected args =
  let actual = List.length args in
  if actual <> expected then
    runtime_error
      (Printf.sprintf "Primitive '%s' expected %d arguments but got %d" prim expected actual)

let int_const i =
  mk_const (Constant.Int i)

let bool_const b =
  mk_const (Constant.Bool b)

let string_const s =
  mk_const (Constant.String s)

let apply_primitive runtime prim args =
  match prim with
  | "+" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value x + int_of_value y)
      | _ -> assert false
    end
  | "-" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value x - int_of_value y)
      | _ -> assert false
    end
  | "*" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value x * int_of_value y)
      | _ -> assert false
    end
  | "/" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] ->
        let denom = int_of_value y in
        if denom = 0 then runtime_error "Division by zero in primitive '/'";
        int_const (int_of_value x / denom)
      | _ -> assert false
    end
  | "<" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x < int_of_value y)
      | _ -> assert false
    end
  | "<=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x <= int_of_value y)
      | _ -> assert false
    end
  | ">" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x > int_of_value y)
      | _ -> assert false
    end
  | ">=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x >= int_of_value y)
      | _ -> assert false
    end
  | "==" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x = int_of_value y)
      | _ -> assert false
    end
  | "!=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value x <> int_of_value y)
      | _ -> assert false
    end
  | "&&" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (bool_runtime_of_value x && bool_runtime_of_value y)
      | _ -> assert false
    end
  | "||" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (bool_runtime_of_value x || bool_runtime_of_value y)
      | _ -> assert false
    end
  | "print" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        print_endline (string_of_value x);
        unit_value
      | _ -> assert false
    end
  | "concat" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> string_const (string_of_value x ^ string_of_value y)
      | _ -> assert false
    end
  | "rand" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        let bound = int_of_value x in
        if bound <= 0 then runtime_error "Primitive 'rand' expects a positive integer bound";
        int_const (Random.int bound)
      | _ -> assert false
    end
  | "randBool" ->
    expect_arity prim 0 args;
    bool_const (Random.bool ())
  | "sleep" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        let duration = int_of_value x in
        if duration <= 0 then runtime_error "Primitive 'sleep' expects a positive integer duration";
        Runtime.sleep runtime duration;
        unit_value
      | _ -> assert false
    end
    (* Intentionally a no-op for now *)
  | "intToString" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] -> string_const (string_of_int (int_of_value x))
      | _ -> assert false
    end
  | _ ->
    runtime_error (Printf.sprintf "Unknown primitive '%s'" prim)

let rec step_current runtime state =
  let finish_current state = Stepped state
  in
  let step_to comp_state next =
    finish_current { comp_state with current_comp = next }
  in
  let return comp_state value =
    step_to comp_state (Return value)
  in
  let return_unit comp_state =
    return comp_state (Tuple [])
  in
  match state.current_comp with
    (* Seq: install frame for comp2, evaluate comp1 *)
    | Seq (comp1, comp2) ->
      let next_current =
        { state with current_comp = comp1 }
        |> install_seq_frame state.env comp2
      in
      finish_current next_current
    (* Let: install frame for env/binder/cont, evaluate subject *)
    | Let { binder; term; cont } ->
      let next_current =
        { state with current_comp = term }
        |> install_let_frame (Var.of_binder binder) state.env cont
      in
      finish_current next_current
    (* Return: subcomputation has finished. Inspect stack; if there's a continuation
        then evaluate that, otherwise the thread's finished. *)
    | Return value -> handle_return runtime state value
    (* App: Check whether applying a primitive or variable. If a primitive, handle separately.
        If a variable, looks up in declarations; if a primitive, handles directly *)
    | App { func; args } ->
      let func = force_var state.decls state.env func in
      let args = List.map (force_value state.decls state.env) args in
      begin
        let open RuntimeValue in
        (* We will never map the function variable directly to a closure as this
          is always reference-counted, so no need to handle that case. *)
        match func with
        | Primitive prim ->
          let result = apply_primitive runtime prim args in
          finish_current { state with current_comp = Return result }
        | Declaration var ->
          begin
            match VarMap.find_opt var state.decls with
            | None ->
              runtime_error
                (Format.asprintf "Attempted to call unknown declaration %a" Var.pp var)
            | Some decl ->
              let call_env = bind_many_rt decl.decl_parameters args VarMap.empty in
              finish_current { state with current_comp = decl.decl_body; env = call_env }
          end
        (* We've previously bound the function. Need to dup its FVs, drop a
          ref, extend the env with param -> arg mappings, and eval body *) 
        | Name name ->
          let (lambda, fvs, closure_env) = lookup_lambda runtime name in
          let dup_names = lookup_runtime_names state.env (List.map (fun n -> (n, 1)) (VarSet.elements fvs)) in
          Runtime.dup runtime dup_names;
          Runtime.drop runtime [ (name, 1) ];
          let extended_env = bind_many_rt lambda.parameters args closure_env in
          finish_current { state with current_comp = lambda.body; env = extended_env }
        | other ->
          runtime_error
            (Format.asprintf
              "Function position must be a declaration, lambda, or primitive, but got %a"
              RuntimeValue.pp other)
      end
    | If { test; then_expr; else_expr } ->
      if bool_of_value state.decls state.env test then
        finish_current { state with current_comp = then_expr }
      else
        finish_current { state with current_comp = else_expr }
    | LetTuple { binders; tuple; cont } ->
      let tuple_values = tuple_values_of_var state.decls state.env tuple in
      if List.length binders <> List.length tuple_values then
        runtime_error "Tuple arity mismatch in let-tuple";
      let env' = bind_many_rt binders tuple_values state.env in
      finish_current { state with current_comp = cont; env = env' }
    | Case _ ->
      (*
        let scrutinee_name = runtime_name_of_var state.env scrutinee in
        let (constructor, arguments) = lookup_constructor runtime scrutinee_name in
        let dup_names = lookup_runtime_names state.env (List.map (fun n -> (n, 1)) (VarSet.elements fvs)) in
        Runtime.dup runtime dup_names;
        Runtime.drop runtime [ (name, 1) ];
        let extended_env = bind_many_rt lambda.parameters args closure_env in
        finish_current { state with current_comp = lambda.body; env = extended_env }
        *)
        failwith "TODO"
(*

        (* FIXME: same Name-vs-Inject dereferencing gap as tuple_values_of_var above. *)
        match force_var state.decls state.env scrutinee with
        | RuntimeValue.Inject (tag, values) ->
          begin
            match List.find_opt (fun (_, _, name) -> String.equal name tag) branches with
            | None ->
              runtime_error
                (Format.asprintf "No matching case branch for constructor '%s'" tag)
            | Some (binders, branch_body, _) ->
              if List.length binders <> List.length values then
                runtime_error "Constructor arity mismatch in case expression";
              let env' = bind_many_rt binders values state.env in
              finish_current { state with current_comp = branch_body; env = env' }
          end
        | other ->
          runtime_error
            (Format.asprintf "Expected a data constructor for case analysis, got: %a" RuntimeValue.pp other)
      end
      *)
    | New _ -> return state (Name (Runtime.new_mailbox runtime))
    | Send { target; message = (tag, payloads); iname = _ } ->
      let mb_name = runtime_name_of_value state.env target in
      let runtime_message = (tag, List.map (RuntimeValue.of_ir state.env) payloads) in
      Runtime.send runtime mb_name runtime_message;
      return_unit state
    | Guard { target; guards; _ } ->
      let mb_name = runtime_name_of_value state.env target in
      let tags = List.concat_map (fun g ->
        match g with
          | Receive recv -> [recv.tag]
          | _ -> []
        ) guards
      in
      begin
        match Runtime.await_message runtime mb_name tags with
        | Received (tag, rt_vals) ->
            let recv_guard = find_receive_guard tag guards in
            let env' =
              state.env
              |> bind_many_rt recv_guard.payload_binders rt_vals
              |> bind recv_guard.mailbox_binder (Name mb_name)
            in
            finish_current { state with env = env'; current_comp = recv_guard.cont } 
        | Freed ->
            let (bnd, cont) = find_empty_guard guards in
            let env' = bind bnd (Name mb_name) state.env in
            finish_current { state with env = env'; current_comp = cont } 
      end
    | Free (target, _iname) ->
      let rt_name = runtime_name_of_value state.env target in
      Runtime.free_mailbox runtime rt_name;
      return_unit state
    | Dup vars ->
      let names = lookup_runtime_names state.env vars in
      Runtime.dup runtime names;
      return_unit state
    | Drop { vars; names } ->
      let var_names = lookup_runtime_names state.env vars in
      Runtime.drop runtime (var_names @ names);
      return_unit state
    | Spawn comp ->
      Runtime.spawn runtime
        (fun () -> 
          let st = { decls = state.decls; current_comp = comp;
                     env = state.env; stack = [] } in
          step runtime st);
      return_unit state
and step runtime state =
  match step_current runtime state with
    | Stepped updated_state ->
        Runtime.yield runtime (fun () ->
          step runtime updated_state
        ) 
    | Finished -> 
        Runtime.finish_thread runtime

let run_program program =
  Runtime.run program (fun runtime ->
    match program.prog_body with
    | None -> ()
    | Some body -> step runtime (init_state program body))