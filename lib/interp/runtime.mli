(* Interface for the runtime system. *)
open Common
open Runtime_common

type t

val run : Ir.program -> (t -> unit) -> unit
val spawn : t -> (unit -> unit) -> unit
val new_mailbox : t -> Ir.RuntimeName.t
val free_mailbox : t -> Ir.RuntimeName.t -> unit
(* Blocks awaiting a message. Returns Some (Ir.message) when a message arrives.
   Returns None if there are no messages and the reference count has dropped to the point that
    a free guard should be invoked.
   TODO: Maybe implement an isomorphic type to make this clearer.
*)
val await_message : t -> Ir.RuntimeName.t -> Ir.message_tag list -> Runtime_common.runtime_message option
val send :  t -> Ir.RuntimeName.t -> Runtime_common.runtime_message  -> unit
val sleep : t -> int -> unit
(* Called after each computation step. May potentially yield to another thread. *)
val yield : t -> (unit -> unit) -> unit
val dup : t -> (Ir.RuntimeName.t * int) list -> unit
val drop : t -> (Ir.RuntimeName.t * int) list -> unit

val lookup_lambda : t -> Ir.RuntimeName.t -> (Ir.lambda * Ir.VarSet.t * value_env)
(* Records a value for reference counting, returning a runtime name *)
val record_value : t -> RuntimeValue.t -> Ir.RuntimeName.t