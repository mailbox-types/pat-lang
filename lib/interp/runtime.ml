open Common
open Runtime_common
open Eio
open Ir


(*
let update_mailbox_refcount mailboxes_acc to_wake mb count sign =
  match RuntimeNameMap.find_opt mb mailboxes_acc with
  | None ->
    runtime_error
      (Format.asprintf "Mailbox %a missing during reference-count update" RuntimeName.pp mb)
  | Some (refcount, messages) ->
    let next_refcount = refcount + (sign * count) in
    let next_acc = RuntimeNameMap.add mb (next_refcount, messages) mailboxes_acc in
    if next_refcount <= 0 then
      runtime_error
        (Format.asprintf "Mailbox %a reference count became below-zero: %a"
          RuntimeName.pp mb pp_mailbox_entry (refcount, messages))
    else if next_refcount = 1 then
      (next_acc, mb :: to_wake)
    else
      (next_acc, to_wake)

let apply_refcount_delta env mailboxes vars names sign =
  let open RuntimeName in
  let (mailboxes_after_vars, to_wake_after_vars) =
  List.fold_left
    (fun (mailboxes_acc, to_wake) (var, count) ->
      if count < 0 then runtime_error "Negative reference-count adjustment is invalid";
        match get_node (ir_of_runtime (lookup_env env var)) with
          | Name ((MailboxName _) as mb) ->
            update_mailbox_refcount mailboxes_acc to_wake mb count sign
          | Name (ValueName _) ->
            (mailboxes_acc, to_wake)
          | _ -> (mailboxes_acc, to_wake) (* Reference counting for other things is a no-op at present. *)
        )
    (mailboxes, [])
    vars
  in
  List.fold_left
    (fun (mailboxes_acc, to_wake) (name, count) ->
      if count < 0 then runtime_error "Negative reference-count adjustment is invalid";
      match name with
      | RuntimeName.MailboxName _ -> update_mailbox_refcount mailboxes_acc to_wake name count sign
      | RuntimeName.ValueName _ -> (mailboxes_acc, to_wake))
    (mailboxes_after_vars, to_wake_after_vars)
    names
*)

type runtime_message = (message_tag * RuntimeValue.t list)
type mailbox = int * runtime_message list

(* Pairs a runtime name with a promise resolver to trigger a recheck of the mailbox. 
An optimisation may be to only wake up when we know a given message will make the mailbox,
but that comes later.
*)
type blocked_state = (RuntimeName.t, unit Promise.u) Hashtbl.t
type mailbox_state = (RuntimeName.t, mailbox) Hashtbl.t
type reference_counting_state = (RuntimeName.t, (int * RuntimeValue.t)) Hashtbl.t

type t = {
  program: program;
  switch: Eio.Switch.t;
  blocked: blocked_state;
  mailboxes: mailbox_state;
  reference_counted_values: (RuntimeName.t, (int * RuntimeValue.t)) Hashtbl.t;
  step_count: int ref
}

let max_step_count = 20

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

let update_hashtable : ('a, 'b) Hashtbl.t -> ('b option -> 'b) -> 'a -> unit =
  fun tbl updt key ->
    let new_val = updt (Hashtbl.find_opt tbl key) in
    Hashtbl.replace tbl key new_val

let pp_mailbox_entry ppf (refcount, messages) =
  let pp_message ppf (tag, payloads) =
    Format.fprintf ppf "%s(%a)" tag
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ") RuntimeValue.pp)
      payloads
  in
  Format.fprintf ppf "(refcount=%d, messages=[%a])" refcount
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") pp_message)
    messages

let update_mailbox_refcount runtime to_wake mb count sign =
  if count < 0 then runtime_error "Negative reference-count adjustment is invalid";
  match Hashtbl.find_opt runtime.mailboxes mb with
  | None ->
    runtime_error
      (Format.asprintf "Mailbox %a missing during reference-count update" RuntimeName.pp mb)
  | Some (refcount, messages) ->
    let next_refcount = refcount + (sign * count) in
    if next_refcount <= 0 then
      runtime_error
        (Format.asprintf "Mailbox %a reference count became below-zero: %a"
          RuntimeName.pp mb pp_mailbox_entry (refcount, messages));
    Hashtbl.replace runtime.mailboxes mb (next_refcount, messages);
    if next_refcount = 1 then mb :: to_wake else to_wake

let update_value_refcount runtime name count sign =
  if count < 0 then runtime_error "Negative reference-count adjustment is invalid";
  match Hashtbl.find_opt runtime.reference_counted_values name with
  | None ->
    runtime_error
      (Format.asprintf "Value reference %a missing during reference-count update" RuntimeName.pp name)
  | Some (refcount, value) ->
    let next_refcount = refcount + (sign * count) in
    if next_refcount < 0 then
      runtime_error
        (Format.asprintf "Value reference %a reference count became below-zero: %d" RuntimeName.pp name next_refcount)
    else if next_refcount = 0 then
      Hashtbl.remove runtime.reference_counted_values name
    else
      Hashtbl.replace runtime.reference_counted_values name (next_refcount, value)

let apply_refcount_delta runtime names sign =
  List.fold_left
    (fun to_wake (name, count) ->
      match name with
      | RuntimeName.MailboxName _ -> update_mailbox_refcount runtime to_wake name count sign
      | RuntimeName.ValueName _ ->
        update_value_refcount runtime name count sign;
        to_wake)
    []
    names

let wake_blocked_many runtime to_wake =
  List.iter
    (fun runtime_name ->
      match Hashtbl.find_opt runtime.blocked runtime_name with
      | None -> ()
      | Some wakeup ->
        Hashtbl.remove runtime.blocked runtime_name;
        Promise.resolve wakeup ())
    to_wake

let run (program : program) (callback: t -> unit) : unit = 
  Eio_main.run (fun _env ->
    let final_blocked =
      Eio.Switch.run (fun sw ->
        let state = {
          program;
          switch = sw;
          blocked = Hashtbl.create 128;
          mailboxes = Hashtbl.create 128;
          reference_counted_values = Hashtbl.create 128;
          step_count = ref 0
        } in
        Random.self_init ();
        Fiber.fork ~sw (fun () -> callback state);
        state.blocked
      )
    in
    (* Switch will block until everything has finished.
       We now just need to check to see whether any threads 
       remain blocked (this would be a deadlock) *)
    if (not (Hashtbl.length final_blocked = 0)) then
      runtime_error "No runnable computations remain (deadlock or blocked system)"
  )

let spawn (runtime : t) (callback: t -> unit) : unit =
  Eio.Fiber.fork ~sw:runtime.switch (fun () -> callback runtime)

let new_mailbox (runtime : t) : RuntimeName.t =
  let mailbox_name = RuntimeName.make_mailbox () in
  Hashtbl.add runtime.mailboxes mailbox_name (1, []);
  mailbox_name
let free_mailbox (_runtime : t) (_mailbox : RuntimeName.t) : unit = failwith "TODO"
let await_message (_runtime : t) (_tags : message_tag list) : message option = failwith "TODO"
let send (runtime : t) (runtime_name : RuntimeName.t) (message : Runtime_common.runtime_message) : unit =
  match Hashtbl.find_opt runtime.mailboxes runtime_name with
  | None ->
    runtime_error
      (Format.asprintf "Send target mailbox %a does not exist" RuntimeName.pp runtime_name)
  | Some (refcount, messages) ->
    let next_refcount = refcount - 1 in
    if next_refcount < 0 then
      runtime_error
        (Format.asprintf "Mailbox %a reference count became negative after send: %a"
          RuntimeName.pp runtime_name pp_mailbox_entry (refcount, messages));
    Hashtbl.replace runtime.mailboxes runtime_name (next_refcount, messages @ [message]);
    begin
      match Hashtbl.find_opt runtime.blocked runtime_name with
      | None -> ()
      | Some wakeup ->
        Hashtbl.remove runtime.blocked runtime_name;
        Promise.resolve wakeup ()
    end

let sleep (_runtime : t) (_duration : int) : unit = failwith "TODO"
(* Called after each computation step. May potentially yield to another thread. *)
let yield (runtime : t) (callback: unit -> unit) =
  let cur_steps = !(runtime.step_count) in
  if cur_steps > max_step_count then
    let () = runtime.step_count := 0 in
    Eio.Fiber.yield ()
  else
    runtime.step_count := cur_steps + 1;
    callback ()

let dup (runtime : t) (counts : (RuntimeName.t * int) list) : unit =
  let to_wake = apply_refcount_delta runtime counts 1 in
  wake_blocked_many runtime to_wake

let drop (runtime : t) (counts : (RuntimeName.t * int) list) : unit =
  let to_wake = apply_refcount_delta runtime counts (-1) in
  wake_blocked_many runtime to_wake

let lookup_lambda runtime name =
  match Hashtbl.find_opt runtime.reference_counted_values name with
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
                  RuntimeName.pp name Ir.pp_value (RuntimeValue.to_ir bad))
      end
    | None -> runtime_error
      (Format.asprintf "Looking up lambda in RC map: name %a unbound" RuntimeName.pp name)

let record_value runtime rt_val =
  let new_ref = RuntimeName.make_value () in
  Hashtbl.add runtime.reference_counted_values new_ref (1, rt_val);
  new_ref