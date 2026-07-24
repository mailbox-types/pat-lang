type 'a setting


module ReceiveTypingStrategy : sig
    type t = Strict | Interface | Nothing
    val enum : (string * t) list
end

val verbose : bool setting
val debug : bool setting
val benchmark : int setting
val receive_typing_strategy : ReceiveTypingStrategy.t setting
val disable_quasilinearity : bool setting
val join_not_combine : bool setting
val liberal_datatypes  : bool setting
val show_ir : bool setting
val show_ref_counting : bool setting
val eval : bool setting

val set : 'a setting -> 'a -> unit
val get : 'a setting -> 'a

val if_verbose : (unit -> unit) -> unit
val if_debug : (unit -> unit) -> unit
