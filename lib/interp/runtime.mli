(* Interface for the runtime system. *)
open Common

type t
val init : Ir.program -> t
val spawn : t -> (unit -> unit) -> unit
val new_mailbox : t -> Ir.RuntimeName.t
val free_mailbox : t -> Ir.RuntimeName.t -> unit
(* Blocks awaiting a message. Returns Some (Ir.message) when a message arrives.
   Returns None if there are no messages and the reference count has dropped to the point that
    a free guard should be invoked.
   TODO: Maybe implement an isomorphic type to make this clearer.
*)
val await_message : t -> Ir.message_tag list -> Ir.message option
val send :  t -> Runtime_common.runtime_message -> Ir.RuntimeName.t -> unit
val sleep : t -> int -> unit
(* Called after each computation step. May potentially yield to another thread. *)
val yield : t -> (unit -> unit) -> unit
val dup : t -> (Ir.RuntimeName.t * int) list -> unit
val drop : t -> (Ir.RuntimeName.t * int) list -> unit