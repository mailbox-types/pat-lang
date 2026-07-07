(* A constraint is a language inclusion relation between two patterns. *)
open Common
open Type

type t = (Pattern.t * Pattern.t)

let make p1 p2 = p1, p2

let lhs = fst
let rhs = snd

let is_upper_bound =
    let open Pattern in
    function
        | (_, PatVar _) -> true
        | _ -> false

let is_lower_bound (_, p2) = Pattern.defined p2

(* Use default comparison function to allow set equality *)
let compare = compare

let pp ppf (p1, p2) =
    Format.(fprintf ppf "%a ⊑ %a"
        Pattern.pp p1
        Pattern.pp p2)
