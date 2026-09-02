(* FGCBV IR *)
open Common_types
open Format
open Util.Utility

module Binder = struct
    type t = { id: int; name: string }
    [@@name "binder"]
    [@@deriving visitors { variety = "map"; data = false }]

    (* Accessors *)
    let id x = x.id
    let name x = x.name

    let source = ref 0

    let gen () =
        let res = !source in
        incr source;
        res

    let make ?(name="") () =
        { id = gen (); name = name }

    (* Display *)
    let pp ppf x =
        let prefix =
            if x.name = "" then "_" else x.name in
        Format.pp_print_string ppf (prefix ^ (string_of_int x.id))
end

module RuntimeName = struct
    type t =
        | MailboxName of int
        | ValueName of int
    [@@name "runtime_name"]
    [@@deriving visitors { variety = "map"; data = false }]

    (* Accessors *)
    let id = function
        | MailboxName i
        | ValueName i -> i

    let compare x1 x2 =
        match (x1, x2) with
        | (MailboxName i1, MailboxName i2)
        | (ValueName i1, ValueName i2) -> Int.compare i1 i2
        | (MailboxName _, ValueName _) -> -1
        | (ValueName _, MailboxName _) -> 1

    let source = ref 0

    let gen () =
        let res = !source in
        incr source;
        res

    let make_mailbox () =
        MailboxName (gen ())

    let make_value () =
        ValueName (gen ())

    (* Display *)
    let pp ppf x =
        match x with
        | MailboxName i -> Format.pp_print_string ppf ("m_" ^ string_of_int i)
        | ValueName i -> Format.pp_print_string ppf ("v_" ^ string_of_int i)
end

module Var = struct
    type t = { id: int; name: string }
    [@@name "var"]
    [@@deriving visitors { variety = "map"; data = false }]

    (* Accessors *)
    let id x = x.id
    let name x = x.name

    (* Display *)
    let pp ppf x =
        let prefix =
            if x.name = "" then "_" else x.name in
        Format.pp_print_string ppf (prefix ^ (string_of_int x.id))

    let pp_name ppf x =
        Format.pp_print_string ppf x.name

    let unique_name =
        Format.asprintf "%a" pp

    let of_binder : Binder.t -> t = fun x ->
        { id = Binder.id x; name = Binder.name x }

    let compare x1 x2 =
        compare (unique_name x1) (unique_name x2)
end

(*
module type VarSet = (Set.S with type elt = Var.t)
*)
module VarSet = struct
    include Set.Make(Var) 
    let union_many vs = List.fold_left (union) empty vs
    let remove_many set vs = diff set (of_list vs)
    let pp ppf varset =
        Format.fprintf ppf "{%a}" (pp_print_comma_list Var.pp) (elements varset)
end 
type varset = VarSet.t

(* It is useful to keep track of metadata associated with each IR node.
This includes both source positions (for diagnostics) and free variables
(for reference counting and eventually cancellation). *)
module WithIrMetadata = struct
  type 'a t = { node : 'a
              ; pos  : (Source_code.Position.t[@opaque])
              ; fvs  : (varset[@opaque])
              } 
            [@@name "withIR"]
            [@@deriving visitors { variety = "map"; polymorphic = true}]
            
    let make ?(pos = Source_code.Position.dummy) ?(fvs = VarSet.empty) node = { node; pos; fvs }
  let node t = t.node
  let pos t = t.pos
  let fvs t = t.fvs

    let pp pp_node ppf { node; pos; fvs } =
        Format.fprintf ppf "%a @ %a with FVs ({%a})" pp_node node Source_code.Position.pp pos VarSet.pp fvs

end


type program = {
    prog_interfaces: (Interface.t[@name "interface"]) list;
    prog_decls: decl list;
    prog_body: comp option
}
and decl = {
    decl_name: (Binder.t[@name "binder"]);
    decl_parameters: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) list;
    decl_return_type: (Type.t[@name "ty"]);
    decl_body: comp
}
and comp = (comp_node WithIrMetadata.t [@name "withIR"])
and comp_node =
    | Annotate of comp * (Type.t[@name "ty"])
    | Let of {
        binder: (Binder.t[@name "binder"]);
        term: comp;
        cont: comp
      }
    | Seq of (comp * comp)
    | Return of value
    | App of {
        func: value;
        args: value list
      }
    | If of { test: value; then_expr: comp; else_expr: comp }
    | LetTuple of {
        (* By annotating with inferred pretypes, we can always use a checking rule
           during inference, irrespective of whether both of the binders are used. *)
        binders: ((Binder.t[@name "binder"]) * (Pretype.t[@name "pretype"]) option) list;
        tuple: value;
        cont: comp
    }
    | Case of {
        term: value;
        prety: ((Pretype.t[@name "pretype"]) option);
        branches: (((Binder.t[@name "binder"]) list) * comp * string) list
    }
    | New of string
    | Spawn of comp
    | Send of {
        target: value;
        message: (message[@name "msg"]);
        iname: string option
      }
    | Free of (value * string option)
    | Fail of (value * string option)
    | Guard of {
        target: value;
        pattern: (Type.Pattern.t[@name "pattern"]);
        guards: guard list;
        iname: string option
      }
and value = (value_node WithIrMetadata.t [@name "withIR"])
and lambda = {
    linear: bool;
    parameters: ((Binder.t[@name "binder"]) * (Type.t[@name "ty"])) list;
    result_type: (Type.t[@name "ty"]);
    body: comp
}
and value_node =
    | VAnnotate of value * (Type.t[@name "ty"])
    | Atom of atom_name
    | Constant of constant
    | Primitive of primitive_name
    | Variable of (Var.t[@name "var"]) * (Pretype.t[@name "pretype"]) option
    | Name of (RuntimeName.t[@name "runtime_name"])
    | Tuple of value list
    | Inject of string * value list
    | Lam of lambda
and message_tag = string
and message = (message_tag * value list)
    [@@name "msg"]
and primitive_name = string
and atom_name = string
and constant =
    [%import: Common_types.Constant.t]
and guard = (guard_node WithIrMetadata.t [@name "withIR"])
and receive_guard = {
        tag: string;
        payload_binders: (Binder.t[@name "binder"]) list;
        mailbox_binder: (Binder.t[@name "binder"]);
        strategy: Settings.ReceiveTypingStrategy.t option;
        cont: comp
    }
and guard_node =
    | Receive of receive_guard
    | Empty of ((Binder.t[@name "binder"]) * comp)
    [@@deriving visitors {
        variety = "map";
        ancestors = [
            "Type.map"; "Pretype.map"; "Binder.map";
            "RuntimeName.map"; "Interface.map"; "Var.map"; "WithIrMetadata.map"];
        data = false }]

let normalise_seq comp =
    let right_nest_seq c =
        let rec mk_right_nested left right =
            match WithIrMetadata.node left with
            | Seq (a, b) ->
                let right' = WithIrMetadata.make ~fvs:(WithIrMetadata.fvs right) (Seq (b, right)) in
                mk_right_nested a right'
            | _ ->
                WithIrMetadata.make ~fvs:(WithIrMetadata.fvs c) (Seq (left, right))
        in
        match WithIrMetadata.node c with
        | Seq (c1, c2) -> mk_right_nested c1 c2
        | _ -> c
    in
    let visitor =
        object
            inherit [_] map as super

            method! visit_comp env c =
                let c' = super#visit_comp env c in
                right_nest_seq c'

            method visit_t _env x = x
        end
    in
    visitor#visit_comp () comp

(* Pretty-printing of the AST *)
(* Programs *)
let rec pp_program ppf { prog_interfaces; prog_decls; prog_body } =
    fprintf ppf "%a@.%a@.@.%a"
        (pp_print_newline_list pp_interface) prog_interfaces
        (pp_print_double_newline_list pp_decl) prog_decls
        (pp_print_option pp_comp) prog_body
(* Interfaces *)
and pp_interface ppf iface =
    let pp_msg_ty ppf (tag, tys) =
        fprintf ppf "%s(%a)" tag
        (pp_print_comma_list Type.pp) tys
    in
    let xs = Interface.bindings iface in
    fprintf ppf "interface %s { %a }"
        (Interface.name iface)
        (pp_print_comma_list pp_msg_ty) xs
(* Declarations *)
and pp_decl ppf { decl_name; decl_parameters; decl_return_type; decl_body } =
    fprintf ppf "def %a(%a): %a {@,@[<v 2>  %a@]@,}"
        Binder.pp decl_name
        (pp_print_comma_list pp_param) decl_parameters
        Type.pp decl_return_type
        pp_comp decl_body
(* Messages *)
and pp_message ppf (tag, vs) =
    fprintf ppf "%s(%a)"
        tag
        (pp_print_comma_list pp_value) vs
(* Parameters *)
and pp_param ppf (param, ty) = fprintf ppf "%a: %a" Binder.pp param Type.pp ty
and pp_branch name ppf (bnds, c, _) =
    fprintf ppf "%s(%a) -> @[<v>%a@]"
        name
        (pp_print_comma_list Binder.pp) bnds
        pp_comp c
and pp_nil name ppf c =
  fprintf ppf "%s([]) -> @[<v>%a@]"
    name
    pp_comp c
and pp_cons name ppf ((bnd1, bnd2), c) =
    fprintf ppf "%s(%a :: %a) -> @[<v>%a@]"
        name
        Binder.pp bnd1
        Binder.pp bnd2
        pp_comp c
(* Expressions *)
and pp_comp ppf comp_with_pos =
    let comp_node = WithIrMetadata.node comp_with_pos in
    match comp_node with
    | Annotate (c, ty) ->
        fprintf ppf "(%a : %a)" pp_comp c Type.pp ty
    | Seq (c1, c2) ->
        fprintf ppf "(%a;@,%a)" pp_comp c1 pp_comp c2
    | Let { binder; term; cont } ->
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            Binder.pp binder
            pp_comp term
            pp_comp cont
    | Return v -> pp_value ppf v
    | Free (v, _) ->
            fprintf ppf "free(%a)" pp_value v
    | Fail (v, _) ->
            fprintf ppf "fail(%a)" pp_value v
    | If { test; then_expr; else_expr } ->
            fprintf ppf "if (%a) {@[<v>%a@]} else {@[<v>%a@]}}"
            pp_value test
            pp_comp then_expr
            pp_comp else_expr
    | App { func; args } ->
        fprintf ppf "%a(%a)"
            pp_value func
            (pp_print_comma_list pp_value) args
    | New iname -> fprintf ppf "new[%s]" iname
    | Spawn e -> fprintf ppf "spawn {@[<v>@,%a@]@,}" pp_comp e
    | Send { target; message; _ (* iname *) } ->
        (* Special-case the common case of sending to a variable.
           Bracket the rest for readability. *)
        begin
            match WithIrMetadata.node target with
                | Variable _ ->
                    fprintf ppf "%a ! %a"
                        pp_value target
                        pp_message message
                | _ ->
                    fprintf ppf "(@[<v 2>%a@]) ! %a"
                        pp_value target
                        pp_message message
        end
    | LetTuple { binders = bs; tuple; cont } ->
        let bs = List.map fst bs in
        fprintf ppf "let %a = @[<v>%a@] in@,%a"
            (pp_print_comma_list Binder.pp) bs
            pp_value tuple
            pp_comp cont
    | Case { term; prety; branches } ->
        fprintf ppf
            "case %a : %a of {@[<v>%a@]}"
            pp_value term
            (pp_print_option ~none:(fun ppf () -> fprintf ppf "<no pretype>") Pretype.pp) prety
            (pp_print_list ~pp_sep:(fun ppf () -> fprintf ppf "@,")
                (fun ppf (bnds, c, name) -> pp_branch name ppf (bnds, c, name))) branches
    | Guard { target; pattern; guards; _ } ->
        fprintf ppf
            "guard %a : %a {@,@[<v 2>  %a@]@,}"
            pp_value target
            Type.Pattern.pp pattern
            (pp_print_newline_list pp_guard) guards
and pp_value ppf v =
    pp_value_node ppf (WithIrMetadata.node v)
and pp_value_node ppf value =
    match value with
    (* Might want, at some stage, to print out pretype info *)
    | VAnnotate (value, ty) ->
        fprintf ppf "(%a : %a)" pp_value value Type.pp ty
    | Atom name -> Format.pp_print_string ppf (":" ^ name)
    | Primitive prim -> Format.pp_print_string ppf prim
    | Variable (var, _) -> Var.pp ppf var
    | Name runtime_name -> RuntimeName.pp ppf runtime_name
    | Constant c -> Constant.pp ppf c
    | Tuple vs ->
        fprintf ppf "%a" (pp_print_comma_list pp_value) vs
    | Inject (name, vs) ->
        fprintf ppf "%s(%a)" name (pp_print_comma_list pp_value) vs
    | Lam { linear; parameters; result_type; body } ->
        let lin = if linear then "linfun" else "fun" in
        fprintf ppf "%s(%a): %a {@,  @[<v>%a@]@,}"
            lin
            (pp_print_comma_list pp_param) parameters
            Type.pp result_type
            pp_comp body
and pp_guard ppf guard_with_pos =
    let guard_node = WithIrMetadata.node guard_with_pos in
    match guard_node with
    | Receive { tag; payload_binders; mailbox_binder; strategy; cont } ->
            let receive_keyword = match strategy with
                | Some Nothing -> "receive*"
                | _ -> "receive"
            in
            fprintf ppf "%s %s(%a) from %a ->@,@[<v 2>  %a@]"
            receive_keyword
            tag
            (pp_print_comma_list Binder.pp) payload_binders
            Binder.pp mailbox_binder
            pp_comp cont
    | Empty (x, e) ->
        fprintf ppf "empty(%a) ->@,  @[<v>%a@]" Binder.pp x pp_comp e

let unit = Tuple []

let is_receive_guard = function
    | Receive _ -> true
    | _ -> false

let is_free_guard = function
    | Free _ -> true
    | _ -> false

(* Substitutes a pattern solution through the program *)
let substitute_solution sol =
    let visitor =
        object
            inherit [_] map

            method! visit_PatVar _env x =
                match StringMap.find_opt x sol with
                    | Some ty -> ty
                    | None -> Type.Pattern.PatVar x
            
            method visit_Settings_ReceiveTypingStrategy_t _env x = x
            
            method visit_t _env x = x
        end
    in
    visitor#visit_program ()
