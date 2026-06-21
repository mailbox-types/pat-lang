open Common
open Source_code
open Util.Utility

let max_steps_before_yield = 20

module VarOrd = struct
  type t = Ir.Var.t

  let compare = Ir.Var.compare
end

module VarMap = Map.Make(VarOrd)
module RuntimeNameMap = Map.Make(Ir.RuntimeName)

(* Placeholder runtime values for the CEK machine skeleton. *)
type value = Ir.value

type environment = value VarMap.t

type computation_frame =
  | SeqFrame of {
    saved_env: environment;
    next_comp: Ir.comp;
  }
  | LetFrame of {
    binder: Ir.Var.t;
    saved_env: environment;
    next_comp: Ir.comp;
  }

type computation_state = {
  current_comp: Ir.comp;
  env: environment;
  stack: computation_frame list;
}

type mailbox_entry = int * Ir.message list

type blocked_state = computation_state RuntimeNameMap.t
type mailbox_state = mailbox_entry RuntimeNameMap.t

type machine_state = {
    program: Ir.program;
  step_count: int;
  computations: computation_state list;
  blocked: blocked_state;
  mailboxes: mailbox_state;
}

type step_result =
  | Stepped of machine_state
  | Finished

let is_finished state =
  state.computations = [] && RuntimeNameMap.is_empty state.blocked

let rotate_computations = function
  | [] -> []
  | comp :: rest -> rest @ [comp]

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

let pp_mailbox_entry ppf (refcount, messages) =
  let pp_message ppf (tag, payloads) =
    Format.fprintf ppf "%s(%a)" tag
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ") Ir.pp_value)
      payloads
  in
  Format.fprintf ppf "(refcount=%d, messages=[%a])" refcount
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") pp_message)
    messages

let mk_value ?(pos = Position.dummy) node =
  WithPos.make ~pos node

let mk_comp ?(pos = Position.dummy) node =
  WithPos.make ~pos node

let unit_value ?(pos = Position.dummy) () =
  mk_value ~pos (Ir.Tuple [])

let lookup_env env var =
  match VarMap.find_opt var env with
  | Some value -> value
  | None ->
    runtime_error (Format.asprintf "Unbound runtime variable %a" Ir.Var.pp var)

let rec force_value env value =
  match WithPos.node value with
  | Ir.VAnnotate (v, _) -> force_value env v
  | Ir.Variable (var, _) -> force_value env (lookup_env env var)
  | _ -> value

let rec normalise_function_value env value =
  match WithPos.node value with
  | Ir.VAnnotate (v, _) -> normalise_function_value env v
  | Ir.Variable (var, _) ->
    begin
      match VarMap.find_opt var env with
      | Some bound -> force_value env bound
      | None -> value
    end
  | _ -> value

let runtime_name_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Name runtime_name -> runtime_name
  | _ ->
    runtime_error
      (Format.asprintf "Expected a mailbox runtime name value, got: %a" Ir.pp_value forced)

let variable_name_from_target target =
  match WithPos.node target with
  | Ir.Variable (var, _) -> var
  | _ ->
    runtime_error
      (Format.asprintf "Expected target to be a variable, got: %a" Ir.pp_value target)

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
    (fun acc decl_with_pos ->
      let decl = WithPos.node decl_with_pos in
      let var = Ir.Var.of_binder decl.Ir.decl_name in
      VarMap.add var decl acc)
    VarMap.empty
    program.Ir.prog_decls

let apply_refcount_delta env mailboxes vars sign =
  List.fold_left
    (fun (mailboxes_acc, to_wake) (var, count) ->
      if count < 0 then runtime_error "Negative reference-count adjustment is invalid";
            match WithPos.node (lookup_env env var) with
            | Ir.Name mb ->
                begin
                    match RuntimeNameMap.find_opt mb mailboxes_acc with
                    | None ->
                        runtime_error
                            (Format.asprintf "Mailbox %a missing during reference-count update" Ir.RuntimeName.pp mb)
                    | Some (refcount, messages) ->
                        let next_refcount = refcount + (sign * count) in
                        let next_acc = RuntimeNameMap.add mb (next_refcount, messages) mailboxes_acc in
                        if next_refcount <= 0 then
                            runtime_error
                                (Format.asprintf "Mailbox %a reference count became below-zero: %a"
                                    Ir.RuntimeName.pp mb pp_mailbox_entry (refcount, messages))
                        (* If the next reference count is 1, then we will need to wake any threads blocked
                           waiting for this mailbox. *)
                        else if next_refcount = 1 then
                          (next_acc, mb :: to_wake)
                        else
                          (next_acc, to_wake)
                end
            | _ -> (mailboxes_acc, to_wake) (* Reference counting for other things is a no-op at present. *)
        )
    (mailboxes, [])
    vars

let enqueue_unblocked blocked computations runtime_name =
  match RuntimeNameMap.find_opt runtime_name blocked with
  | None -> (blocked, computations)
  | Some blocked_comp ->
    (RuntimeNameMap.remove runtime_name blocked, computations @ [blocked_comp])

let enqueue_unblocked_many blocked computations =
  List.fold_left (uncurry enqueue_unblocked) (blocked, computations)

let install_seq_frame saved_env next_comp current =
  { current with stack = SeqFrame { saved_env; next_comp } :: current.stack }

let install_let_frame binder saved_env next_comp current =
  { current with stack = LetFrame { binder; saved_env; next_comp } :: current.stack }

(* Handles a Return given the stack. Binds a value in a LetFrame, not in a SeqFrame *)
let pop_frame_with_value value current =
  match current.stack with
  | [] -> None
  | frame :: rest ->
    begin
      match frame with
      | SeqFrame { saved_env; next_comp } ->
        Some { current_comp = next_comp; env = saved_env; stack = rest }
      | LetFrame { binder; saved_env; next_comp } ->
        let env' = VarMap.add binder value saved_env in
        Some { current_comp = next_comp; env = env'; stack = rest }
    end

let inc_step state =
  { state with step_count = state.step_count + 1 }

let rec bind_many env binders values =
  match binders, values with
  | [], [] -> env
  | binder :: binders, value :: values ->
    bind_many (VarMap.add (Ir.Var.of_binder binder) value env) binders values
  | _ -> runtime_error "Arity mismatch while binding values"

type guard_transition = {
  next_env: environment;
  next_comp: Ir.comp;
  remaining_messages: Ir.message list;
}

type receive_guard_match = {
  payload_binders: Ir.Binder.t list;
  payloads: value list;
  mailbox_binder: Ir.Binder.t;
  cont: Ir.comp;
  remaining_messages: Ir.message list;
}

let rec find_empty_guard guards =
  match guards with
  | [] -> None
  | guard :: rest ->
    begin
      match WithPos.node guard with
      | Ir.Empty (mailbox_binder, cont) -> Some (mailbox_binder, cont)
      | _ -> find_empty_guard rest
    end

let rec find_receive_guard guards messages =
  match guards with
  | [] -> None
  | guard :: rest ->
    begin
      match WithPos.node guard with
      | Ir.Receive { tag; payload_binders; mailbox_binder; strategy = _; cont } ->
        begin
          match remove_first_tagged_message tag messages with
          | None -> find_receive_guard rest messages
          | Some (payloads, remaining_messages) ->
            Some { payload_binders; payloads; mailbox_binder; cont; remaining_messages }
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
        let mailbox_value = mk_value (Ir.Name runtime_name) in
        let next_env = VarMap.add (Ir.Var.of_binder mailbox_binder) mailbox_value env in
        Some { next_env; next_comp = cont; remaining_messages = messages }
      | _ -> None
    end
  | _ ->
    begin
      match find_receive_guard guards messages with
      | None -> None
      | Some { payload_binders; payloads; mailbox_binder; cont; remaining_messages } ->
        if List.length payload_binders <> List.length payloads then
          runtime_error "Receive payload arity mismatch";
        let mailbox_value = mk_value (Ir.Name runtime_name) in
        let next_env =
          bind_many env payload_binders payloads
          |> VarMap.add (Ir.Var.of_binder mailbox_binder) mailbox_value
        in
        Some { next_env; next_comp = cont; remaining_messages }
    end

let bool_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Constant (Common_types.Constant.Bool b) -> b
  | _ ->
    runtime_error
      (Format.asprintf "Expected boolean test value, got: %a" Ir.pp_value forced)

let tuple_values_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Tuple values -> values
  | _ ->
    runtime_error
      (Format.asprintf "Expected tuple value, got: %a" Ir.pp_value forced)

let int_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Constant (Common_types.Constant.Int i) -> i
  | _ ->
    runtime_error
      (Format.asprintf "Expected integer value, got: %a" Ir.pp_value forced)

let string_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Constant (Common_types.Constant.String s) -> s
  | _ ->
    runtime_error
      (Format.asprintf "Expected string value, got: %a" Ir.pp_value forced)

let bool_runtime_of_value env value =
  let forced = force_value env value in
  match WithPos.node forced with
  | Ir.Constant (Common_types.Constant.Bool b) -> b
  | _ ->
    runtime_error
      (Format.asprintf "Expected boolean value, got: %a" Ir.pp_value forced)

let expect_arity prim expected args =
  let actual = List.length args in
  if actual <> expected then
    runtime_error
      (Printf.sprintf "Primitive '%s' expected %d arguments but got %d" prim expected actual)

let int_const ?(pos = Position.dummy) i =
  mk_value ~pos (Ir.Constant (Common_types.Constant.Int i))

let bool_const ?(pos = Position.dummy) b =
  mk_value ~pos (Ir.Constant (Common_types.Constant.Bool b))

let string_const ?(pos = Position.dummy) s =
  mk_value ~pos (Ir.Constant (Common_types.Constant.String s))

let apply_primitive prim env args pos =
  match prim with
  | "+" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const ~pos (int_of_value env x + int_of_value env y)
      | _ -> assert false
    end
  | "-" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const ~pos (int_of_value env x - int_of_value env y)
      | _ -> assert false
    end
  | "*" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> int_const ~pos (int_of_value env x * int_of_value env y)
      | _ -> assert false
    end
  | "/" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] ->
        let denom = int_of_value env y in
        if denom = 0 then runtime_error "Division by zero in primitive '/'";
        int_const ~pos (int_of_value env x / denom)
      | _ -> assert false
    end
  | "<" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x < int_of_value env y)
      | _ -> assert false
    end
  | "<=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x <= int_of_value env y)
      | _ -> assert false
    end
  | ">" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x > int_of_value env y)
      | _ -> assert false
    end
  | ">=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x >= int_of_value env y)
      | _ -> assert false
    end
  | "==" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x = int_of_value env y)
      | _ -> assert false
    end
  | "!=" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (int_of_value env x <> int_of_value env y)
      | _ -> assert false
    end
  | "&&" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (bool_runtime_of_value env x && bool_runtime_of_value env y)
      | _ -> assert false
    end
  | "||" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> bool_const ~pos (bool_runtime_of_value env x || bool_runtime_of_value env y)
      | _ -> assert false
    end
  | "print" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        print_endline (string_of_value env x);
        unit_value ~pos ()
      | _ -> assert false
    end
  | "concat" ->
    expect_arity prim 2 args;
    begin
      match args with
      | [x; y] -> string_const ~pos (string_of_value env x ^ string_of_value env y)
      | _ -> assert false
    end
  | "rand" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] ->
        let bound = int_of_value env x in
        if bound <= 0 then runtime_error "Primitive 'rand' expects a positive integer bound";
        int_const ~pos (Random.int bound)
      | _ -> assert false
    end
  | "randBool" ->
    expect_arity prim 0 args;
    bool_const ~pos (Random.bool ())
  | "sleep" ->
    expect_arity prim 1 args;
    (* Intentionally a no-op for now *)
    unit_value ~pos ()
  | "intToString" ->
    expect_arity prim 1 args;
    begin
      match args with
      | [x] -> string_const ~pos (string_of_int (int_of_value env x))
      | _ -> assert false
    end
  | _ ->
    runtime_error (Printf.sprintf "Unknown primitive '%s'" prim)

let step_current state =
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
    let pos = WithPos.pos current.current_comp in
    let finish_current next_current =
      Some (inc_step { state with computations = next_current :: rest })
    in
    let finish_current_with_mailboxes next_current mailboxes =
      Some (inc_step { state with computations = next_current :: rest; mailboxes })
    in
    begin
      match WithPos.node current.current_comp with
      | Ir.Annotate (comp, _) ->
        finish_current { current with current_comp = comp }
      (* Seq: install frame for comp2, evaluate comp1 *)
      | Ir.Seq (comp1, comp2) ->
        let next_current =
          { current with current_comp = comp1 }
          |> install_seq_frame current.env comp2
        in
        finish_current next_current
      (* Let: install frame for env/binder/cont, evaluate subject *)
      | Ir.Let { binder; term; cont } ->
        let next_current =
          { current with current_comp = term }
          |> install_let_frame (Ir.Var.of_binder binder) current.env cont
        in
        finish_current next_current
      (* Return: subcomputation has finished. Inspect stack; if there's a continuation
          then evaluate that, otherwise the thread's finished. *)
      | Ir.Return value ->
        let forced = force_value current.env value in
        begin
          match pop_frame_with_value forced current with
          | Some resumed -> finish_current resumed
          | None -> Some (inc_step { state with computations = rest })
        end
      (* App: Check whether applying a primitive or variable. If a primitive, handle separately.
         If a variable, looks up in declarations; if a primitive, handles directly *)
      | Ir.App { func; args } ->
        let func = normalise_function_value current.env func in
        let args = List.map (force_value current.env) args in
        begin
          match WithPos.node func with
          | Ir.Primitive prim ->
            let result = apply_primitive prim current.env args pos in
            finish_current { current with current_comp = mk_comp ~pos (Ir.Return result) }
          | Ir.Variable (var, _) ->
            let decls = decl_map state.program in
            begin
              match VarMap.find_opt var decls with
              | None -> runtime_error "Attempted to call unknown declaration"
              | Some decl ->
                let binders = List.map fst decl.decl_parameters in
                let call_env = bind_many VarMap.empty binders args in
                finish_current { current with current_comp = decl.decl_body; env = call_env }
            end
          | _ -> runtime_error "Function position must be a declaration variable or primitive"
        end
      | Ir.If { test; then_expr; else_expr } ->
        if bool_of_value current.env test then
          finish_current { current with current_comp = then_expr }
        else
          finish_current { current with current_comp = else_expr }
      | Ir.LetTuple { binders; tuple; cont } ->
        let tuple_values = tuple_values_of_value current.env tuple in
        let tuple_binders = List.map fst binders in
        if List.length tuple_binders <> List.length tuple_values then
          runtime_error "Tuple arity mismatch in let-tuple";
        let env' = bind_many current.env tuple_binders tuple_values in
        finish_current { current with current_comp = cont; env = env' }
      | Ir.Case { term; branch1 = ((binder1, _), comp1); branch2 = ((binder2, _), comp2) } ->
        begin
          match WithPos.node (force_value current.env term) with
          | Ir.Inl value ->
            let env' = VarMap.add (Ir.Var.of_binder binder1) value current.env in
            finish_current { current with current_comp = comp1; env = env' }
          | Ir.Inr value ->
            let env' = VarMap.add (Ir.Var.of_binder binder2) value current.env in
            finish_current { current with current_comp = comp2; env = env' }
          | _ ->
          runtime_error
            (Format.asprintf "Expected sum value for case analysis, got: %a" Ir.pp_value (force_value current.env term))
        end
      | Ir.CaseL { term; ty = _; nil; cons = ((binder1, binder2), comp) } ->
        begin
          match WithPos.node (force_value current.env term) with
          | Ir.Nil ->
            finish_current { current with current_comp = nil }
          | Ir.Cons (head, tail) ->
            let env' =
              current.env
              |> VarMap.add (Ir.Var.of_binder binder1) head
              |> VarMap.add (Ir.Var.of_binder binder2) tail
            in
            finish_current { current with current_comp = comp; env = env' }
          | _ ->
          runtime_error
            (Format.asprintf "Expected list value for case-list analysis, got: %a" Ir.pp_value (force_value current.env term))
        end
      | Ir.Dup vars ->
        let (mailboxes, _) = apply_refcount_delta current.env state.mailboxes vars 1 in
        finish_current_with_mailboxes { current with current_comp =
          mk_comp ~pos (Ir.Return (unit_value ~pos ())) } mailboxes
      | Ir.Drop vars ->
        (* After doing the reference updates, we might have some blocked processes that we can awake,
           due to Empty references becoming fireable *)
        let (mailboxes, to_wake) = apply_refcount_delta current.env state.mailboxes vars (-1) in
        let (blocked, computations) = enqueue_unblocked_many state.blocked rest to_wake in
        let current' = { current with current_comp = mk_comp ~pos (Ir.Return (unit_value ~pos ())) } in
        Some (inc_step { state with computations = current' :: computations; blocked; mailboxes } )
      | Ir.New _ ->
        let runtime_name = Ir.RuntimeName.make () in
        let mailboxes = RuntimeNameMap.add runtime_name (1, []) state.mailboxes in
        let return_name = mk_value ~pos (Ir.Name runtime_name) in
        finish_current_with_mailboxes { current with current_comp =
          mk_comp ~pos (Ir.Return return_name) } mailboxes
      | Ir.Send { target; message; iname = _ } ->
        let target_var = variable_name_from_target target in
        let runtime_name = runtime_name_of_value current.env (lookup_env current.env target_var) in
        let message = (fst message, List.map (force_value current.env) (snd message)) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
            | None ->
              runtime_error
                (Format.asprintf "Send target mailbox %a does not exist" Ir.RuntimeName.pp runtime_name)
            | Some (refcount, messages) ->
              let next_refcount = refcount - 1 in
              if next_refcount < 0 then
                runtime_error
                  (Format.asprintf "Mailbox %a reference count became negative after send: %a"
                    Ir.RuntimeName.pp runtime_name pp_mailbox_entry (refcount, messages));
                let mailboxes =
                  RuntimeNameMap.add runtime_name (next_refcount, messages @ [message]) state.mailboxes
                in
                let blocked, computations_tail = enqueue_unblocked state.blocked rest runtime_name in
                let current' = { current with current_comp = mk_comp ~pos (Ir.Return (unit_value ~pos ())) } in
                Some (inc_step { state with computations = current' :: computations_tail; blocked; mailboxes })
        end
      | Ir.Guard { target; pattern = _; guards; iname = _ } ->
        let target_var = variable_name_from_target target in
        let runtime_name = runtime_name_of_value current.env (lookup_env current.env target_var) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
          | None ->
            runtime_error
              (Format.asprintf "Guard target mailbox %a does not exist" Ir.RuntimeName.pp runtime_name)
          | Some ((refcount, _) as mailbox) ->
            begin
              match evaluate_guard runtime_name current.env guards mailbox with
              | Some { next_env; next_comp; remaining_messages } ->
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
      | Ir.Free (target, _iname) ->
        let target_var =
          match WithPos.node target with
          | Ir.Variable (var, _) -> var
          | _ -> runtime_error "Free expects a variable mailbox target"
        in
        let runtime_name = runtime_name_of_value current.env (lookup_env current.env target_var) in
        begin
          match RuntimeNameMap.find_opt runtime_name state.mailboxes with
          | Some (1, []) ->
            let mailboxes = RuntimeNameMap.remove runtime_name state.mailboxes in
            finish_current_with_mailboxes { current with current_comp = mk_comp ~pos (Ir.Return (unit_value ~pos ())) } mailboxes
        | Some entry ->
          runtime_error
            (Format.asprintf "Free requires mailbox %a to have state (1, empty), got %a"
              Ir.RuntimeName.pp runtime_name pp_mailbox_entry entry)
        | None ->
          runtime_error
            (Format.asprintf "Free target mailbox %a does not exist" Ir.RuntimeName.pp runtime_name)
        end
      | Ir.Spawn comp ->
        let spawned = { current_comp = comp; env = current.env; stack = [] } in
        let current' = { current with current_comp = mk_comp ~pos (Ir.Return (unit_value ~pos ())) } in
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
    match program.Ir.prog_body with
    | None -> []
    | Some comp -> [{ current_comp = comp; env = VarMap.empty; stack = [] }]
  in
  { program; step_count = 0; computations; blocked = RuntimeNameMap.empty;
    mailboxes = RuntimeNameMap.empty }

let rec run_until_finished state =
  match step state with
  | Finished -> state
  | Stepped state' -> run_until_finished state'

let run_to_completion program =
  Random.self_init ();
  run_until_finished (initial_state program)

