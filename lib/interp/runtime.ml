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
  reference_counted_values: ((int * RuntimeValue.t), RuntimeName.t) Hashtbl.t;
  step_count: int
}

let runtime_error message =
  raise (Errors.internal_error "eval.ml" message)

let update_hashtable : ('a, 'b) Hashtbl.t -> ('b option -> 'b) -> 'a -> unit =
  fun tbl updt key ->
    let new_val = updt (Hashtbl.find_opt tbl key) in
    Hashtbl.replace tbl key new_val

let run (program : program) (callback: t -> unit) : unit = 
  Eio_main.run (fun _env ->
    Eio.Switch.run (fun sw ->
      let state = {
        program;
        switch = sw;
        blocked = Hashtbl.create 128;
        mailboxes = Hashtbl.create 128;
        reference_counted_values = Hashtbl.create 128;
        step_count = 0
      } in
      Fiber.fork ~sw (fun () -> callback state)
    )
  )

let spawn (runtime : t) (callback: t -> unit) : unit =
  Eio.Fiber.fork ~sw:runtime.switch (fun () -> callback runtime)

let new_mailbox (runtime : t) : RuntimeName.t =
  let mailbox_name = RuntimeName.make_mailbox () in
  Hashtbl.add runtime.mailboxes mailbox_name (1, []);
  mailbox_name
let free_mailbox (_runtime : t) (_mailbox : RuntimeName.t) : unit = failwith "TODO"
let await_message (_runtime : t) (_tags : message_tag list) : message option = failwith "TODO"
let send (_runtime : t) (_message : Runtime_common.runtime_message) (_target : RuntimeName.t) : unit = failwith "TODO"
let sleep (_runtime : t) (_duration : int) : unit = failwith "TODO"
(* Called after each computation step. May potentially yield to another thread. *)
let yield (_runtime : t) (callback: unit -> unit) = failwith "TODO"
let dup (_runtime : t) (_counts : (RuntimeName.t * int) list) : unit = failwith "TODO"
let drop (_runtime : t) (_counts : (RuntimeName.t * int) list) : unit = failwith "TODO"