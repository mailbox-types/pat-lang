(* Random stuff that's useful everywhere *)

(* Maps *)

module type STRINGMAP = (Map.S with type key = string)
module StringMap = Map.Make(String)
type 'a stringmap = 'a StringMap.t

module type STRINGSET = (Set.S with type elt = string)
module StringSet = Set.Make(String)
type stringset = StringSet.t

module Multiset = struct
    module Make (Ord : Map.OrderedType) = struct
        module Map = Map.Make(Ord)

        type elt = Ord.t
        type t = int Map.t

        let empty = Map.empty

        let singleton x = Map.singleton x 1

        let multiplicity x xs =
            Map.find_opt x xs
            |> Option.value ~default:0

        let add ?(count=1) x xs =
            if count <= 0 then
                xs
            else
                Map.update x
                    (function
                        | None -> Some count
                        | Some n -> Some (n + count))
                    xs

        let of_list xs =
            List.fold_left (fun acc x -> add x acc) empty xs

        let combine xs ys =
            Map.merge
                (fun _ left right ->
                    match left, right with
                        | None, None -> None
                        | Some n, None | None, Some n -> Some n
                        | Some n1, Some n2 -> Some (n1 + n2))
                xs ys

        let combine_many xss =
            List.fold_left combine empty xss

        let bindings = Map.bindings
    end
end



(* Pipelining and composition *)

(* Options *)
let sequence_options xs =
  List.fold_right
    (fun x acc ->
       match x, acc with
       | Some v, Some vs -> Some (v :: vs)
       | _ -> None)
    xs
    (Some [])

(* Reverse function application (nicer and more uniform than `@@`) *)
let (<|) f x = f x

(* Function composition (left) *)
let (<<) f g x = f(g(x))

(* Function composition (right) *)
let (>>) f g x = g(f(x))

let flip f = fun x y -> f y x

(* Chars *)

let is_uppercase c =
    let code = Char.code c in
    code >= Char.code 'A' && code <= Char.code 'Z'

(* Lists *)

module ListUtils = struct

let intersect xs ys =
  List.filter (fun x -> List.mem x ys) xs

let rec split3 : ('a * 'b * 'c) list -> 'a list * 'b list * 'c list = function
    | [] -> ([], [], [])
    | (x, y, z) :: rest ->
        let (xs, ys, zs) = split3 rest in
        x :: xs, y :: ys, z :: zs

let rec combine3 : 'a list -> 'b list -> 'c list -> ('a * 'b * 'c) list =
    fun xs ys zs ->
        match (xs, ys, zs) with
            | ([], [], []) -> []
            | (x :: xs, y :: ys, z :: zs) ->
                let rest = combine3 xs ys zs in
                (x, y, z) :: rest
            | _, _, _ ->
                raise (Invalid_argument "mismatching lengths to combine3")
end

let find_char (s : bytes) (c : char) : int list =
    let rec aux offset occurrences =
      try let index = Bytes.index_from s offset c in
            aux (index + 1) (index :: occurrences)
      with Not_found -> occurrences
    in List.rev (aux 0 [])

(* Pretty-printing *)
open Format
let pp_comma ppf () =
    pp_print_string ppf ", "

let pp_print_comma_list ppf =
    pp_print_list ~pp_sep:(pp_comma) ppf

let pp_print_newline_list ppf =
    pp_print_list ~pp_sep:(pp_force_newline) ppf

let pp_double_newline ppf () =
    pp_force_newline ppf ();
    pp_force_newline ppf ()

let pp_print_double_newline_list ppf =
    pp_print_list ~pp_sep:(pp_double_newline) ppf

(* Prints an error *)
let print_error ?(note="ERROR") err =
    Format.fprintf err_formatter "[\027[31m%s\027[0m] %s\n" note err

let print_debug err =
    Format.fprintf std_formatter "[\027[34mDEBUG\027[0m] %s\n" err


(* f: a, b -> c ==> f: (a, b) -> c *)
let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

let rec split3 = function
    | [] -> ([], [], [])
    | (x, y, z) :: rest ->
        let (xs, ys, zs) = split3 rest in
        (x :: xs, y :: ys, z :: zs)
