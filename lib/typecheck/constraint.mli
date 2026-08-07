open Common

type t

(** Constructs a constraint from two patterns *)
val make : Type.Pattern.t -> Type.Pattern.t -> t

(** Gets left-hand-side of the constraint *)
val lhs : t -> Type.Pattern.t

(** Gets right-hand-side of the constraint *)
val rhs : t -> Type.Pattern.t

(** Returns 'true' if the constraint is an upper bound
    (i.e., is of the form `pat1 <= pat2` where pat2 contains no pattern variables) *)
val is_upper_bound : t -> bool

(** Returns 'true' if the constraint is a lower bound
    (i.e., is of the form `pat1 <= pvar`) *)
val is_lower_bound : t -> bool

(** Compares two constraints *)
val compare : t -> t -> int

(** Pretty-print *)
val pp : Format.formatter -> t -> unit
