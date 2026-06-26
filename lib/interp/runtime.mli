type t
val init : Ir.program -> t
val spawn : Ir.comp -> unit
(* Blocks awaiting a message. Returns Some (Ir.message) when a message arrives.
   Returns None if there are no messages and the reference count has dropped to the point that
    a free guard should be invoked.
   TODO: Maybe implement an isomorphic type to make this clearer.
*)
val await_message : t -> Ir.message_tag list -> Ir.message option
val send :  t -> Runtime_common.runtime_message -> RuntimeName.t -> unit
val sleep : t -> int -> unit
(* Called after each computation step. May potentially yield to another thread. *)
val yield : t -> (unit -> unit) -> unit