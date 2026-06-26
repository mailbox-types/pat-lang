
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