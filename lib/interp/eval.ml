open Common
open Common_types
open Util.Utility
open Ir
open Runtime_common
open Eio

let max_steps_before_yield = 20

module VarMap = Runtime_common.VarMap
module RuntimeNameMap = Map.Make(RuntimeName)

let get_node = WithIrMetadata.node
let get_fvs = WithIrMetadata.fvs
let with_val_fvs value = WithIrMetadata.make ~fvs:(get_fvs value)

let unit_value = WithIrMetadata.make (Tuple [])
let return_unit_value =
	WithIrMetadata.make (Return (WithIrMetadata.make (Tuple [])))
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
  current_comp: comp;
  env: environment;
  stack: computation_frame list
}

let pp_mailbox_entry ppf (refcount, messages) =
  let pp_message ppf (tag, payloads) =
    Format.fprintf ppf "%s(%a)" tag
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ") pp_value)
      payloads
  in
  Format.fprintf ppf "(refcount=%d, messages=[%a])" refcount
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") pp_message)
    messages

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
      | Some bound -> force_value env (ir_of_runtime bound)
      | None -> value
    end
  | _ -> value

let rec runtime_name_of_value value =
  match value with
  | RuntimeValue.VAnnotate (v, _) -> runtime_name_of_value v
  | RuntimeValue.Name runtime_name -> runtime_name
  | _ ->
    runtime_error
      (Format.asprintf "Expected a mailbox runtime name value, got: %a" pp_value (ir_of_runtime value))

let variable_name_from_target target =
  match get_node target with
  | Variable (var, _) -> var
  | _ ->
    runtime_error
      (Format.asprintf "Expected target to be a variable, got: %a" pp_value target)

let remove_first_tagged_message tag messages =
  let rec aux prefix = function
    | [] -> None
    | ((msg_tag, payloads) as msg) :: rest ->
      if String.equal msg_tag tag then
        Some (payloads, List.rev_append prefix rest)
      else
        aux (msg :: prefix) rest
  in
  aux [] messages

let decl_map program =
  List.fold_left
    (fun acc decl ->
      let var = Var.of_binder decl.decl_name in
      VarMap.add var decl acc)
    VarMap.empty
    program.prog_decls


let install_seq_frame saved_env next_comp current =
  { current with stack = SeqFrame { saved_env; next_comp } :: current.stack }

let install_let_frame binder saved_env next_comp current =
  { current with stack = LetFrame { binder; saved_env; next_comp } :: current.stack }

(* Handles a Return given the stack. Binds a value in a LetFrame, not in a SeqFrame.*)
  (*
let pop_frame_with_value value current =
  match current.stack with
  | [] -> None
  | frame :: rest ->
    begin
      match frame with
      | SeqFrame { saved_env; next_comp } ->
        Some { current_comp = next_comp; env = saved_env; stack = rest }
      | LetFrame { binder; saved_env; next_comp } ->
        (* If we're returning a function or constructor, we need to generate a new 
           function runtime name, store in the reference counted heap,
           and return this instead of the lambda binding. *)
        begin
          match get_node value with
            | Lam blah ->

            | _ ->
              let env' = VarMap.add binder value saved_env in
              Some { current_comp = next_comp; env = env'; stack = rest }
        end
    end
  *)

let handle_return value (current, rest) state =
  (* We can only store a closed runtime value in the environment, so we need to substitute any FVs. *)
  let forced = force_value current.env value in
  let irv = runtime_of_ir current.env value in
  let update_computation comp = inc_step { state with computations = comp :: rest } in
  match (get_node forced, current.stack) with
    | (_, []) -> 
      (* Nothing to return; thread terminated *)
      inc_step { state with computations = rest }
    | (_, SeqFrame { saved_env; next_comp } :: other_frames) ->
      update_computation { current_comp = next_comp; env = saved_env; stack = other_frames }
    | (Lam _, LetFrame { binder; saved_env; next_comp } :: other_frames) ->
      (* If we're returning a function or constructor, we need to generate a new 
          function runtime name, store in the reference counted heap,
          and return this instead of the lambda binding. *)
      let new_ref = RuntimeName.make_value () in
      let refc_val_map =
        RuntimeNameMap.add new_ref (1, irv) state.reference_counted_values
      in
      let env' =
        VarMap.add binder (RuntimeValue.Name new_ref) saved_env
      in
      let new_comp_state = { current_comp = next_comp; env = env'; stack = other_frames } in
      inc_step { state with computations = new_comp_state :: rest; reference_counted_values = refc_val_map }
    | (_, LetFrame { binder; saved_env; next_comp } :: other_frames) ->
      let env' = VarMap.add binder irv saved_env in
      update_computation { current_comp = next_comp; env = env'; stack = other_frames }

let rec bind_many env binders values =
  match binders, values with
  | [], [] -> env
  | binder :: binders, value :: values ->
    bind_many (VarMap.add (Var.of_binder binder) (runtime_of_ir env value) env) binders values
  | _ -> runtime_error "Arity mismatch while binding values"

let rec find_empty_guard guards =
  match guards with
  | [] -> None
  | guard :: rest ->
    begin
      match get_node guard with
      | Empty (mailbox_binder, cont) -> Some (mailbox_binder, cont)
      | _ -> find_empty_guard rest
    end

let rec find_receive_guard guards messages =
  match guards with
  | [] -> None
  | guard :: rest ->
    begin
      match get_node guard with
      | Receive recv_guard ->
        begin
          match remove_first_tagged_message recv_guard.tag messages with
          | None -> find_receive_guard rest messages
          | Some (payloads, remaining_messages) ->
            Some (recv_guard, payloads, remaining_messages)
        end
      | _ -> find_receive_guard rest messages
    end

let evaluate_guard runtime_name env guards mailbox =
  let (count, messages) = mailbox in
  match messages with
  | [] ->
    (* If there aren't any messages then we'll need to check whether the reference count is 1. 
       If so we can evaluate the empty guard; if not then we'll need to block *)
    begin
      match (count, find_empty_guard guards) with
      | (1, Some (mailbox_binder, cont)) ->
        let mailbox_value = mk_name runtime_name in
        let next_env = VarMap.add (Var.of_binder mailbox_binder) (runtime_of_ir env mailbox_value) env in
        Some (next_env, cont, messages) 
      | _ -> None
    end
  | _ ->
    begin
      match find_receive_guard guards messages with
      | None -> None
      | Some (recv_guard, payloads, remaining_messages) ->
        if List.length recv_guard.payload_binders <> List.length payloads then
          runtime_error "Receive payload arity mismatch";
        let mailbox_value = mk_name runtime_name in
        let next_env =
          bind_many env recv_guard.payload_binders payloads
          |> VarMap.add (Var.of_binder recv_guard.mailbox_binder) (runtime_of_ir env mailbox_value)
        in
        Some (next_env, recv_guard.cont, remaining_messages) 
    end

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

let apply_primitive prim env args =
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
    (* Intentionally a no-op for now *)
    unit_value
  | "intToString" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] -> string_const (string_of_int (int_of_value env x))
      | _ -> assert false
    end
  | _ ->
    runtime_error (Printf.sprintf "Unknown primitive '%s'" prim)

let lookup_lambda name refcount_map =
  match RuntimeNameMap.find_opt name refcount_map with
    | Some (_, runtime_value) ->
      begin
        match runtime_value with
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
                  RuntimeName.pp name Ir.pp_value (ir_of_runtime bad))
      end
    | None -> runtime_error
      (Format.asprintf "Looking up lambda in RC map: name %a unbound" RuntimeName.pp name)

let rec step_current runtime state =
  let return comp_state value : unit =
    Runtime.yield runtime (fun () ->
      step_current runtime 
        { comp_state with current_comp = WithIrMetadata.make (Ir.Return value) }
    )
  in
  match state.computations with
  | [] ->
    (* If there aren't any computations, and also nothing is blocked, then program has 
      terminated normally. *)
    if RuntimeNameMap.is_empty state.blocked then
      None
    else
    (* If things are blocked, we have a deadlock. *)
      runtime_error "No runnable computations remain (deadlock or blocked system)"
  | current :: rest ->
    let finish_current next_current =
      Some (inc_step { state with computations = next_current :: rest })
    in
    let finish_current_with_mailboxes next_current mailboxes =
      Some (inc_step { state with computations = next_current :: rest; mailboxes })
    in
    begin
      match get_node current.current_comp with
      | Annotate (comp, _) ->
        finish_current { current with current_comp = comp }
      (* Seq: install frame for comp2, evaluate comp1 *)
      | Seq (comp1, comp2) ->
        let next_current =
          { current with current_comp = comp1 }
          |> install_seq_frame current.env comp2
        in
        finish_current next_current
      (* Let: install frame for env/binder/cont, evaluate subject *)
      | Let { binder; term; cont } ->
        let next_current =
          { current with current_comp = term }
          |> install_let_frame (Var.of_binder binder) current.env cont
        in
        finish_current next_current
      (* Return: subcomputation has finished. Inspect stack; if there's a continuation
          then evaluate that, otherwise the thread's finished. *)
      | Return value -> Some (handle_return value (current, rest) state)
      (* App: Check whether applying a primitive or variable. If a primitive, handle separately.
         If a variable, looks up in declarations; if a primitive, handles directly *)
      | App { func; args } ->
        let func = normalise_function_value current.env func in
        let args = List.map (force_value current.env) args in
        begin
          match get_node func with
          | Primitive prim ->
            let result = apply_primitive prim current.env args in
            finish_current { current with current_comp = with_val_fvs result (Return result) }
          | Variable (var, _) ->
            let decls = decl_map state.program in
            begin
              match VarMap.find_opt var decls with
              | None -> runtime_error "Attempted to call unknown declaration"
              | Some decl ->
                let binders = List.map fst decl.decl_parameters in
                let call_env = bind_many VarMap.empty binders args in
                finish_current { current with current_comp = decl.decl_body; env = call_env }
            end
          (* Applying a function literal. We don't need to heap-allocate this, or do anything
             special with closures, as it can't be re-called. *)
          | Lam lambda ->
              let binders = List.map fst lambda.parameters in
              let extended_env = bind_many current.env binders args in
              finish_current { current with current_comp = lambda.body; env = extended_env  }
          (* We've previously bound the function. Need to dup its FVs, drop a
            ref, extend the env with param -> arg mappings, and eval body *) 
          | Name name ->
            let (lambda, fvs, closure_env) = lookup_lambda name state.reference_counted_values in
            let dup_cmd = WithIrMetadata.make (Ir.Dup (List.map (fun n -> (n, 1)) (VarSet.elements fvs))) in
            let drop_cmd = WithIrMetadata.make (Ir.Drop { vars = []; names = [ (name, 1) ] }) in
            let extended_env = bind_many closure_env (List.map fst lambda.parameters) args in
            let new_stack =
              SeqFrame { saved_env = current.env; next_comp = drop_cmd }
              :: SeqFrame { saved_env = extended_env; next_comp = lambda.body }
              :: current.stack
            in
            finish_current { current with current_comp = dup_cmd; stack = new_stack }
          | other ->
            runtime_error
              (Format.asprintf
                "Function position must be a declaration, lambda, or primitive, but got %a"
                Ir.pp_value_node other)
        end
      | If { test; then_expr; else_expr } ->
        if bool_of_value current.env test then
          finish_current { current with current_comp = then_expr }
        else
          finish_current { current with current_comp = else_expr }
      | LetTuple { binders; tuple; cont } ->
        let tuple_values = tuple_values_of_value current.env tuple in
        let tuple_binders = List.map fst binders in
        if List.length tuple_binders <> List.length tuple_values then
          runtime_error "Tuple arity mismatch in let-tuple";
        let env' = bind_many current.env tuple_binders tuple_values in
        finish_current { current with current_comp = cont; env = env' }
      | Case { term; branch1 = ((binder1, _), comp1); branch2 = ((binder2, _), comp2) } ->
        begin
          match get_node (force_value current.env term) with
          | Inl value ->
            let env' = VarMap.add (Var.of_binder binder1) (runtime_of_ir current.env value) current.env in
            finish_current { current with current_comp = comp1; env = env' }
          | Inr value ->
            let env' = VarMap.add (Var.of_binder binder2) (runtime_of_ir current.env value) current.env in
            finish_current { current with current_comp = comp2; env = env' }
          | _ ->
          runtime_error
            (Format.asprintf "Expected sum value for case analysis, got: %a" pp_value (force_value current.env term))
        end
      | CaseL { term; ty = _; nil; cons = ((binder1, binder2), comp) } ->
        begin
          match get_node (force_value current.env term) with
          | Nil ->
            finish_current { current with current_comp = nil }
          | Cons (head, tail) ->
            let env' =
              current.env
              |> VarMap.add (Var.of_binder binder1) (runtime_of_ir current.env head)
              |> VarMap.add (Var.of_binder binder2) (runtime_of_ir current.env tail)
            in
            finish_current { current with current_comp = comp; env = env' }
          | _ ->
          runtime_error
            (Format.asprintf "Expected list value for case-list analysis, got: %a" pp_value (force_value current.env term))
        end
      | Dup vars ->
        let (mailboxes, _) = apply_refcount_delta current.env state.mailboxes vars [] 1 in
        finish_current_with_mailboxes { current with current_comp = return_unit_value } mailboxes
      | Drop { vars; names } ->
        (* After doing the reference updates, we might have some blocked processes that we can awake,
           due to Empty references becoming fireable *)
        let (mailboxes, to_wake) = apply_refcount_delta current.env state.mailboxes vars names (-1) in
        let (blocked, computations) = enqueue_unblocked_many state.blocked rest to_wake in
        let current' = { current with current_comp = return_unit_value } in
        Some (inc_step { state with computations = current' :: computations; blocked; mailboxes } )
      | New _ ->
        return (Runtime.new_mailbox runtime)
        (*
        let runtime_name = RuntimeName.make_mailbox () in
        let mailboxes = RuntimeNameMap.add runtime_name (1, []) state.mailboxes in
        let return_name = mk_name runtime_name in
        finish_current_with_mailboxes { current with current_comp =
        WithIrMetadata.make (Return return_name) } mailboxes
        *)
      | Send { target; message; iname = _ } ->
        let target_var = variable_name_from_target target in
        let runtime_name = runtime_name_of_value (lookup_env current.env target_var) in
        let message = (fst message, List.map (force_value current.env) (snd message)) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
            | None ->
              runtime_error
                (Format.asprintf "Send target mailbox %a does not exist" RuntimeName.pp runtime_name)
            | Some (refcount, messages) ->
              let next_refcount = refcount - 1 in
              if next_refcount < 0 then
                runtime_error
                  (Format.asprintf "Mailbox %a reference count became negative after send: %a"
                    RuntimeName.pp runtime_name pp_mailbox_entry (refcount, messages));
                let mailboxes =
                  RuntimeNameMap.add runtime_name (next_refcount, messages @ [message]) state.mailboxes
                in
                let blocked, computations_tail = enqueue_unblocked state.blocked rest runtime_name in
                let current' = { current with current_comp = return_unit_value } in
                Some (inc_step { state with computations = current' :: computations_tail; blocked; mailboxes })
        end
      | Guard { target; pattern = _; guards; iname = _ } ->
        let target_var = variable_name_from_target target in
        let runtime_name = runtime_name_of_value (lookup_env current.env target_var) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
          | None ->
            runtime_error
              (Format.asprintf "Guard target mailbox %a does not exist" RuntimeName.pp runtime_name)
          | Some ((refcount, _) as mailbox) ->
            begin
              match evaluate_guard runtime_name current.env guards mailbox with
              | Some (next_env, next_comp, remaining_messages) ->
                let mailboxes =
                  RuntimeNameMap.add runtime_name (refcount, remaining_messages) state.mailboxes
                in
                let current' = { current with current_comp = next_comp; env = next_env } in
                Some (inc_step { state with computations = current' :: rest; mailboxes })
              | None ->
                let blocked = RuntimeNameMap.add runtime_name current state.blocked in
                Some { state with computations = rest; blocked; step_count = 0 }
            end
        end
      | Free (target, _iname) ->
        let target_var =
          match get_node target with
          | Variable (var, _) -> var
          | _ -> runtime_error "Free expects a variable mailbox target"
        in
        let runtime_name = runtime_name_of_value (lookup_env current.env target_var) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
          | Some (1, []) ->
            let mailboxes = RuntimeNameMap.remove runtime_name state.mailboxes in
            finish_current_with_mailboxes { current with current_comp = return_unit_value } mailboxes
          | Some (refcount, _) when refcount > 1 ->
            let blocked = RuntimeNameMap.add runtime_name current state.blocked in
            Some { state with computations = rest; blocked; step_count = 0 }
          | Some entry ->
            runtime_error
              (Format.asprintf "Free requires mailbox %a to have state (1, empty), got %a"
                RuntimeName.pp runtime_name pp_mailbox_entry entry)
          | None ->
            runtime_error
              (Format.asprintf "Free target mailbox %a does not exist" RuntimeName.pp runtime_name)
        end
      | Spawn comp ->
        let spawned = { current_comp = comp; env = current.env; stack = [] } in
        let current' = { current with current_comp = return_unit_value } in
        Some (inc_step { state with computations = current' :: (rest @ [spawned]) })
    end

let step state =
  if is_finished state then
    Finished
  else
    let state =
      if state.step_count > max_steps_before_yield then
        { state with step_count = 0; computations = rotate_computations state.computations }
      else state
    in
    match step_current state with
    | None -> Finished
    | Some stepped -> Stepped stepped

let initial_state program =
  let computations =
    match program.prog_body with
    | None -> []
    | Some comp -> [{ current_comp = comp; env = VarMap.empty; stack = [] }]
  in
  { program; step_count = 0; computations;
	blocked = RuntimeNameMap.empty; mailboxes = RuntimeNameMap.empty;
  reference_counted_values = RuntimeNameMap.empty }

let rec run_until_finished state =
  match step state with
  | Finished -> state
  | Stepped state' -> run_until_finished state'

let run_to_completion program =
  Random.self_init ();
  run_until_finished (initial_state program)

