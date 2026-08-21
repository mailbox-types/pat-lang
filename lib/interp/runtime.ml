open Common
open Runtime_common
open Eio
open Evaluation_ir

(* A mailbox is represented internally as a pair of a reference count, and a
list of runtime messages. *)
type mailbox = int * runtime_message list

(* The result of guarding on a mailbox. *)
type await_result =
   | Received of Runtime_common.runtime_message
   | Freed

(* Pairs a runtime name with a promise resolver to trigger a recheck of the mailbox. *)
type blocked_state = (RuntimeName.t, unit Promise.u) Hashtbl.t
type mailbox_state = (RuntimeName.t, mailbox) Hashtbl.t
type reference_counting_state = (RuntimeName.t, (int * RuntimeValue.t)) Hashtbl.t

(* The overall runtime state, recording required EIO metadata; all blocked threads; mailboxes;
   reference counting state; and the thread and step counts. 
   Convenient to make this mutable such that it is accessible across threads; this is safe
   due to co-operative concurrency. Accesses will need synchronisation if we decide to move
   to parallel execution. *)
type t = {
  program: program;
  switch: Eio.Switch.t;
  env: Eio_unix.Stdenv.base;
  blocked: blocked_state;
  mailboxes: mailbox_state;
  reference_counted_values: reference_counting_state;
  thread_count: int ref;
  step_count: int ref
}

let block_thread runtime mailbox_name =
  let len_plus_1 = Hashtbl.length runtime.blocked + 1 in
  let thread_count = !(runtime.thread_count) in
  if len_plus_1 >= thread_count then
    runtime_error "Deadlock! All running threads are blocked."
  else
    let (wait_for_retry, wakeup) = Promise.create () in
    let () = Hashtbl.replace runtime.blocked mailbox_name wakeup in
    Promise.await wait_for_retry
let max_step_count = 20

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

let pp_mailbox_entry ppf (refcount, messages) =
  let pp_message ppf (tag, payloads) =
    Format.fprintf ppf "%s(%a)" tag
      (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf ", ") RuntimeValue.pp)
      payloads
  in
  Format.fprintf ppf "(refcount=%d, messages=[%a])" refcount
    (Format.pp_print_list ~pp_sep:(fun ppf () -> Format.pp_print_string ppf "; ") pp_message)
    messages

let wake_blocked_many runtime to_wake =
  List.iter
    (fun runtime_name ->
      match Hashtbl.find_opt runtime.blocked runtime_name with
      | None -> ()
      | Some wakeup ->
        Hashtbl.remove runtime.blocked runtime_name;
        Promise.resolve wakeup ())
    to_wake

let rec apply_refcount_delta runtime names sign =
  List.fold_left
    (fun to_wake (name, count) ->
      match name with
      | RuntimeName.MailboxName _ ->
        update_mailbox_refcount runtime to_wake name count sign
      | RuntimeName.ValueName _ ->
        update_value_refcount runtime name count sign;
        to_wake)
    []
    names
and update_mailbox_refcount runtime to_wake mb count sign =
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

and update_value_refcount runtime name count sign =
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
      let () = Hashtbl.remove runtime.reference_counted_values name in
      begin
        match value with
        | RuntimeValue.Closure { lambda; value_env } ->
          let fv_runtime_names =
            lambda.fvs
            |> VarSet.elements
            |> List.filter_map (fun fv ->
                match VarMap.find_opt fv value_env with
                | Some (RuntimeValue.Name runtime_name) -> Some (runtime_name, 1)
                | _ -> None)
          in
          let to_wake = apply_refcount_delta runtime fv_runtime_names (-1) in
          wake_blocked_many runtime to_wake
        | _ -> ()
      end
    else
      Hashtbl.replace runtime.reference_counted_values name (next_refcount, value)

let run (program : program) (callback: t -> unit) : unit = 
  Eio_main.run (fun env ->
      Eio.Switch.run (fun switch ->
        let state = {
          program;
          switch;
          env;
          blocked = Hashtbl.create 128;
          mailboxes = Hashtbl.create 128;
          reference_counted_values = Hashtbl.create 128;
          thread_count = ref 1;
          step_count = ref 0
        } in
        Random.self_init ();
        Fiber.fork ~sw:switch (fun () -> callback state)
      )
  )

let spawn (runtime : t) (callback: unit -> unit) : unit =
  incr runtime.thread_count;
  Eio.Fiber.fork ~sw:runtime.switch (fun () -> callback ())

let new_mailbox (runtime : t) : RuntimeName.t =
  let mailbox_name = RuntimeName.make_mailbox () in
  Hashtbl.add runtime.mailboxes mailbox_name (1, []);
  mailbox_name

let rec free_mailbox (runtime : t) (mailbox : RuntimeName.t) : unit =
  match Hashtbl.find_opt runtime.mailboxes mailbox with
  | None ->
    runtime_error
      (Format.asprintf "Free target mailbox %a does not exist" RuntimeName.pp mailbox)
  | Some (1, []) ->
    Hashtbl.remove runtime.mailboxes mailbox
  | Some (refcount, _) when refcount > 1 ->
    block_thread runtime mailbox;
    free_mailbox runtime mailbox
  | Some entry ->
    runtime_error
      (Format.asprintf "Free requires mailbox %a to have state (1, empty), got %a"
        RuntimeName.pp mailbox pp_mailbox_entry entry)

let rec await_message (runtime : t) (name: RuntimeName.t) (tags : message_tag list) : await_result =
  match Hashtbl.find_opt runtime.mailboxes name with
  | None ->
    runtime_error
      (Format.asprintf "Guard target mailbox %a does not exist" RuntimeName.pp name)
  (* If the mailbox is empty and has refcount 1, then we can trigger an empty guard. *)
  | Some (refcount, messages) when refcount = 1 && List.is_empty messages ->
    Freed
  | Some (refcount, messages) ->
    (* Otherwise we need to check whether any messages in the mailbox are contained in the tag list *)
    begin
      match find_first_matching_message tags messages with
        (* If so, update mailbox and return *)
        | Some (msg, updated_mb) ->
          let () = Hashtbl.replace runtime.mailboxes name (refcount, updated_mb) in
          Received msg
        (* If not, we need to block and re-check *)
        | None ->
          block_thread runtime name;
          await_message runtime name tags
    end

let send (runtime : t) (runtime_name : RuntimeName.t) (message : Runtime_common.runtime_message) : unit =
  match Hashtbl.find_opt runtime.mailboxes runtime_name with
  | None ->
    runtime_error
      (Format.asprintf "Send target mailbox %a does not exist" RuntimeName.pp runtime_name)
  | Some (refcount, messages) ->
    let next_refcount = refcount - 1 in
    let () =
      if next_refcount < 1 then
        runtime_error
          (Format.asprintf "Mailbox %a reference count became < 1 after send: %a"
            RuntimeName.pp runtime_name pp_mailbox_entry (refcount, messages))
    in
    Hashtbl.replace runtime.mailboxes runtime_name (next_refcount, messages @ [message]);
    begin
      match Hashtbl.find_opt runtime.blocked runtime_name with
      | None -> ()
      | Some wakeup ->
        Hashtbl.remove runtime.blocked runtime_name;
        Promise.resolve wakeup ()
    end

let sleep (runtime : t) (duration : int) : unit =
  let duration_float = (float_of_int duration) /. 1000.0 in
  Eio.Time.sleep (Eio.Stdenv.clock runtime.env) duration_float

(* Called after each computation step. May potentially yield to another thread. *)
let yield (runtime : t) (callback: unit -> unit) =
  let cur_steps = !(runtime.step_count) in
  if cur_steps > max_step_count then
    begin
      runtime.step_count := 0;
      Eio.Fiber.yield ();
      callback ()
    end
  else 
    begin
      runtime.step_count := cur_steps + 1;
      callback ()
    end

let dup (runtime : t) (counts : (RuntimeName.t * int) list) : unit =
  let to_wake = apply_refcount_delta runtime counts 1 in
  wake_blocked_many runtime to_wake

let drop (runtime : t) (counts : (RuntimeName.t * int) list) : unit =
  let to_wake = apply_refcount_delta runtime counts (-1) in
  wake_blocked_many runtime to_wake

let lookup_tracked_value (runtime : t) (name : RuntimeName.t) : RuntimeValue.t =
  match Hashtbl.find_opt runtime.reference_counted_values name with
    | Some (_, runtime_value) -> runtime_value
    | None -> runtime_error
      (Format.asprintf "Looking up tracked value in RC map: name %a unbound" RuntimeName.pp name)

let record_value runtime rt_val =
  let new_ref = RuntimeName.make_value () in
  Hashtbl.add runtime.reference_counted_values new_ref (1, rt_val);
  new_ref

let finish_thread runtime =
  decr runtime.thread_count;
  if Hashtbl.length runtime.blocked > 0 && 
    !(runtime.thread_count) = Hashtbl.length runtime.blocked then
    runtime_error "Deadlock! All running threads are blocked."
