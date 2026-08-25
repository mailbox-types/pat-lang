(* Common types used over multiple files *)

module Base = struct
    type t =
        | Atom
        | Int
        | Bool
        | String
    [@@deriving show]

    let pp ppf =
        let ps = Format.pp_print_string ppf in
        function
           | Atom -> ps "Atom"
           | Int -> ps "Int"
           | Bool -> ps "Bool"
           | String -> ps "String"
end

type interface_name = string
    [@@name "string"]
    [@@deriving show]

type tag = string
    [@@name "string"]
    [@@deriving show]

(* Boxed constants *)
module Constant = struct
    type t =
        | Int of int
        | String of string
        | Bool of bool

    let type_of = function
        | Int _ -> Base.Int
        | Bool _ -> Base.Bool
        | String _ -> Base.String

    let pp ppf = function
        | Int i -> Format.pp_print_int ppf i
        | String s -> Format.fprintf ppf "\"%s\"" s
        | Bool b -> Format.pp_print_bool ppf b

    let wrap_int i = Int i
    let wrap_string s = String s
    let wrap_bool b = Bool b

    let unwrap_int pos_list = function
        | Int i -> i
        | _ -> raise (Errors.type_error "unwrap_int on non-int" pos_list)

    let unwrap_string pos_list = function
        | String s -> s
        | _ -> raise (Errors.type_error "unwrap_string on non-string" pos_list)

    let unwrap_bool pos_list = function
        | Bool b -> b
        | _ -> raise (Errors.type_error "unwrap_bool on non-bool" pos_list)
end

(* Utility functions *)
let list_type_name = "List"
let sum_type_name = "Sum"