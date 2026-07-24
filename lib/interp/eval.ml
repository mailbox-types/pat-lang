open Common
open Common_types
open Util.Utility
open Ir
open Runtime_common

let max_steps_before_yield = 20

module VarMap = Runtime_common.VarMap
module RuntimeNameMap = Map.Make(RuntimeName)

let get_node = WithIrMetadata.node
let get_fvs = WithIrMetadata.fvs
let with_val_fvs value = WithIrMetadata.make ~fvs:(get_fvs value)

let unit_value = WithIrMetadata.make (Tuple [])
let mk_const c = WithIrMetadata.make (Constant c)
let mk_name a = WithIrMetadata.make (Name a)

let runtime_of_ir env value = RuntimeValue.of_ir env value
let ir_of_runtime value = RuntimeValue.to_ir value

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
  program: Ir.program;
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

let rec force_value env value =
  match get_node value with
  | VAnnotate (v, _) -> force_value env v
  | Variable (var, _) -> force_value env (ir_of_runtime (lookup_env env var))
  | _ -> value

let rec normalise_function_value env value =
  match get_node value with
  | VAnnotate (v, _) -> normalise_function_value env v
  | Variable (var, _) ->
    begin
      match VarMap.find_opt var env with
      | Some bound -> ir_of_runtime bound
      | None -> value
    end
  | _ -> value

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

let lookup_runtime_names env vars =
  List.filter_map
    (fun (var, count) ->
      match lookup_env env var |> runtime_name_of_runtime_value with
      | None -> None
      | Some name -> Some (name, count))
    vars

let decl_map program =
  List.fold_left
    (fun acc decl ->
      let var = Var.of_binder decl.decl_name in
      VarMap.add var decl acc)
    VarMap.empty
    program.prog_decls


let init_state program comp =
  { program; current_comp = comp; env = VarMap.empty; stack = [] }

let install_seq_frame saved_env next_comp state =
  { state with stack = SeqFrame { saved_env; next_comp } :: state.stack }

let install_let_frame binder saved_env next_comp state =
  { state with stack = LetFrame { binder; saved_env; next_comp } :: state.stack }

let handle_return runtime state value =
  (* We can only store a closed runtime value in the environment, so we need to substitute any FVs. *)
  let forced = force_value state.env value in
  let irv = runtime_of_ir state.env value in
  match (get_node forced, state.stack) with
    | (_, []) -> Finished
    | (_, SeqFrame { saved_env; next_comp } :: other_frames) ->
      Stepped { state with current_comp = next_comp; env = saved_env; stack = other_frames }
    | (Lam _, LetFrame { binder; saved_env; next_comp } :: other_frames) ->
      (* If we're returning a function or constructor, we need to generate a new 
          function runtime name, store in the reference counted heap,
          and return this instead of the lambda binding. *)
      let new_ref = Runtime.record_value runtime irv in
      let env' =
        VarMap.add binder (RuntimeValue.Name new_ref) saved_env
      in
      Stepped { state with current_comp = next_comp; env = env'; stack = other_frames }
    | (_, LetFrame { binder; saved_env; next_comp } :: other_frames) ->
      let env' = VarMap.add binder irv saved_env in
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

let bool_of_value env value =
  let forced = force_value env value in
  match get_node forced with
  | Constant (Constant.Bool b) -> b
  | _ ->
    runtime_error
      (Format.asprintf "Expected boolean test value, got: %a" pp_value forced)

let tuple_values_of_value env value =
  let forced = force_value env value in
  match get_node forced with
  | Tuple values -> values
  | _ ->
    runtime_error
      (Format.asprintf "Expected tuple value, got: %a" pp_value forced)

let int_of_value env value =
  let forced = force_value env value in
  match get_node forced with
  | Constant (Constant.Int i) -> i
  | _ ->
    runtime_error
      (Format.asprintf "Expected integer value, got: %a" pp_value forced)

let string_of_value env value =
  let forced = force_value env value in
  match get_node forced with
  | Constant (Constant.String s) -> s
  | _ ->
    runtime_error
      (Format.asprintf "Expected string value, got: %a" pp_value forced)

let bool_runtime_of_value env value =
  let forced = force_value env value in
  match get_node forced with
  | Constant (Constant.Bool b) -> b
  | _ ->
    runtime_error
      (Format.asprintf "Expected boolean value, got: %a" pp_value forced)

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

let apply_primitive runtime prim env args =
  match prim with
  | "+" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value env x + int_of_value env y)
      | _ -> assert false
    end
  | "-" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value env x - int_of_value env y)
      | _ -> assert false
    end
  | "*" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const (int_of_value env x * int_of_value env y)
      | _ -> assert false
    end
  | "/" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] ->
        let denom = int_of_value env y in
        if denom = 0 then runtime_error "Division by zero in primitive '/'";
        int_const (int_of_value env x / denom)
      | _ -> assert false
    end
  | "<" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x < int_of_value env y)
      | _ -> assert false
    end
  | "<=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x <= int_of_value env y)
      | _ -> assert false
    end
  | ">" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x > int_of_value env y)
      | _ -> assert false
    end
  | ">=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x >= int_of_value env y)
      | _ -> assert false
    end
  | "==" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x = int_of_value env y)
      | _ -> assert false
    end
  | "!=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (int_of_value env x <> int_of_value env y)
      | _ -> assert false
    end
  | "&&" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (bool_runtime_of_value env x && bool_runtime_of_value env y)
      | _ -> assert false
    end
  | "||" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const (bool_runtime_of_value env x || bool_runtime_of_value env y)
      | _ -> assert false
    end
  | "print" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        print_endline (string_of_value env x);
        unit_value
      | _ -> assert false
    end
  | "concat" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> string_const (string_of_value env x ^ string_of_value env y)
      | _ -> assert false
    end
  | "rand" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        let bound = int_of_value env x in
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
        let duration = int_of_value env x in
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
      | [x] -> string_const (string_of_int (int_of_value env x))
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
    step_to comp_state (WithIrMetadata.make (Ir.Return value))
  in
  let return_unit comp_state =
    return comp_state (WithIrMetadata.make (Tuple []))
  in
  match get_node state.current_comp with
    | Annotate (comp, _) ->
      step_to state comp
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
      let func = normalise_function_value state.env func in
      let args = List.map (force_value state.env) args in
      begin
        match get_node func with
        | Primitive prim ->
          let result = apply_primitive runtime prim state.env args in
          finish_current { state with current_comp = with_val_fvs result (Return result) }
        | Variable (var, _) ->
          let decls = decl_map state.program in
          begin
            match VarMap.find_opt var decls with
            | None -> runtime_error "Attempted to call unknown declaration"
            | Some decl ->
              let binders = List.map fst decl.decl_parameters in
              let call_env = bind_many binders args VarMap.empty in
              finish_current { state with current_comp = decl.decl_body; env = call_env }
          end
        (* Applying a function literal. We don't need to heap-allocate this, or do anything
            special with closures, as it can't be re-called. *)
        | Lam lambda ->
            let binders = List.map fst lambda.parameters in
            let extended_env = bind_many binders args state.env in
            finish_current { state with current_comp = lambda.body; env = extended_env  }
        (* We've previously bound the function. Need to dup its FVs, drop a
          ref, extend the env with param -> arg mappings, and eval body *) 
        | Name name ->
          let (lambda, fvs, closure_env) = Runtime.lookup_lambda runtime name in
          let dup_cmd = WithIrMetadata.make (Ir.Dup (List.map (fun n -> (n, 1)) (VarSet.elements fvs))) in
          let drop_cmd = WithIrMetadata.make (Ir.Drop { vars = []; names = [ (name, 1) ] }) in
          let extended_env = bind_many (List.map fst lambda.parameters) args closure_env in
          let new_stack =
            SeqFrame { saved_env = state.env; next_comp = drop_cmd }
            :: SeqFrame { saved_env = extended_env; next_comp = lambda.body }
            :: state.stack
          in
          finish_current { state with current_comp = dup_cmd; stack = new_stack }
        | other ->
          runtime_error
            (Format.asprintf
              "Function position must be a declaration, lambda, or primitive, but got %a"
              Ir.pp_value_node other)
      end
    | If { test; then_expr; else_expr } ->
      if bool_of_value state.env test then
        finish_current { state with current_comp = then_expr }
      else
        finish_current { state with current_comp = else_expr }
    | LetTuple { binders; tuple; cont } ->
      let tuple_values = tuple_values_of_value state.env tuple in
      let tuple_binders = List.map fst binders in
      if List.length tuple_binders <> List.length tuple_values then
        runtime_error "Tuple arity mismatch in let-tuple";
      let env' = bind_many tuple_binders tuple_values state.env in
      finish_current { state with current_comp = cont; env = env' }
    | Case { term; branch1 = ((binder1, _), comp1); branch2 = ((binder2, _), comp2) } ->
      begin
        match get_node (force_value state.env term) with
        | Inl value ->
          let env' = VarMap.add (Var.of_binder binder1) (runtime_of_ir state.env value) state.env in
          finish_current { state with current_comp = comp1; env = env' }
        | Inr value ->
          let env' = VarMap.add (Var.of_binder binder2) (runtime_of_ir state.env value) state.env in
          finish_current { state with current_comp = comp2; env = env' }
        | _ ->
        runtime_error
          (Format.asprintf "Expected sum value for case analysis, got: %a" pp_value (force_value state.env term))
      end
    | CaseL { term; ty = _; nil; cons = ((binder1, binder2), comp) } ->
      begin
        match get_node (force_value state.env term) with
        | Nil ->
          finish_current { state with current_comp = nil }
        | Cons (head, tail) ->
          let env' =
            state.env
            |> VarMap.add (Var.of_binder binder1) (runtime_of_ir state.env head)
            |> VarMap.add (Var.of_binder binder2) (runtime_of_ir state.env tail)
          in
          finish_current { state with current_comp = comp; env = env' }
        | _ ->
        runtime_error
          (Format.asprintf "Expected list value for case-list analysis, got: %a" pp_value (force_value state.env term))
      end
    | Dup vars ->
      let names = lookup_runtime_names state.env vars in
      Runtime.dup runtime names;
      return_unit state
    | Drop { vars; names } ->
      let var_names = lookup_runtime_names state.env vars in
      Runtime.drop runtime (var_names @ names);
      return_unit state
    | New _ -> return state (WithIrMetadata.make <| Ir.Name (Runtime.new_mailbox runtime))
    | Send { target; message = (tag, payloads); iname = _ } ->
      let mb_name = runtime_name_of_value state.env target in
      let runtime_message = (tag, List.map (RuntimeValue.of_ir state.env) payloads) in
      Runtime.send runtime mb_name runtime_message;
      return_unit state
    | Guard { target; guards; _ } ->
      let mb_name = runtime_name_of_value state.env target in
      let tags = List.concat_map (fun g ->
        match get_node g with
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
              |> bind recv_guard.mailbox_binder (WithIrMetadata.make (Name mb_name))
            in
            finish_current { state with env = env'; current_comp = recv_guard.cont } 
        | Freed ->
            let (bnd, cont) = find_empty_guard guards in
            let env' = bind bnd (WithIrMetadata.make (Name mb_name)) state.env in
            finish_current { state with env = env'; current_comp = cont } 
      end
    | Free (target, _iname) ->
      let rt_name = runtime_name_of_value state.env target in
      Runtime.free_mailbox runtime rt_name;
      return_unit state
    | Spawn comp ->
      Runtime.spawn runtime
        (fun () -> 
          let st = { program = state.program; current_comp = comp;
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