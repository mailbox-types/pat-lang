(* Interface for the runtime system. *)
open Runtime_common

type t

(* Result of guarding on a mailbox: either a message has been received,
   or no more messages will ever be received and the mailbox should be freed.
*)
type await_result =
   | Received of Runtime_common.runtime_message
   | Freed

(* Runs a program. The continuation is a callback invoked with the
   freshly-created runtime that should evaluate the main thread. 
   We require the callback in order to avoid a circular depdenency
   between the runtime and the evaluator.
*)
val run : Evaluation_ir.program -> (t -> unit) -> unit
(* Spawns a new thread on the given runtime.
   The thunk should evaluate the body of the spawned process. *)
val spawn : t -> (unit -> unit) -> unit
(* Creates a fresh mailbox and returns its new runtime name. *)
val new_mailbox : t -> Evaluation_ir.RuntimeName.t
(* Frees the mailbox with the given runtime name. Raises an error if the
   reference count of the mailbox is not exactly 1. *)
val free_mailbox : t -> Evaluation_ir.RuntimeName.t -> unit
(* Blocks awaiting a message. Returns an await_result. *)
val await_message : t -> Evaluation_ir.RuntimeName.t -> Evaluation_ir.message_tag list -> await_result
(* Sends a message to the given mailbox. *)
val send :  t -> Evaluation_ir.RuntimeName.t -> Runtime_common.runtime_message  -> unit
(* Sleeps the current thread for the given number of milliseconds. Will yield. *)
val sleep : t -> int -> unit
(* Called after each computation step. May potentially yield to another thread. *)
val yield : t -> (unit -> unit) -> unit
(* Given a list [(a, n)], increments the reference count of each a_i by n_i *)
val dup : t -> (Evaluation_ir.RuntimeName.t * int) list -> unit
(* Given a list [(a, n)], decrements the reference count of each a_i by n_i *)
val drop : t -> (Evaluation_ir.RuntimeName.t * int) list -> unit

(* Looks up the tracked runtime value for a given reference-counted name. *)
val lookup_tracked_value : t -> Evaluation_ir.RuntimeName.t -> RuntimeValue.t
(* Records a value for reference counting, returning a runtime name *)
val record_value : t -> RuntimeValue.t -> Evaluation_ir.RuntimeName.t
(* Called when a thread has finished evaluating. *)
val finish_thread : t -> unit