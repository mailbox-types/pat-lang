open Common_types
open Util.Utility

module Capability = struct
    type t = In | Out
    [@@name "capability"]
    [@@deriving visitors { variety = "map"; nude = true }]

    let pp ppf =
        let open Format in
        function
        | In -> pp_print_string ppf "?"
        | Out -> pp_print_string ppf "!"
end

module Quasilinearity = struct
    type t = Usable | Returnable
    [@@name "quasilinearity"]
    [@@deriving visitors { variety = "map"; nude = true }]

    let is_returnable x = (x = Returnable)

    (* If we've got a type which is returnable, we can treat it
       as a type which is only usable.

       Conversely, we can't 'promote' a type which is only usable
       to be returnable.
     *)
    let is_sub x1 x2 =
        (Settings.(get disable_quasilinearity)) ||
            match x1, x2 with
                | Returnable, Usable -> true
                | x1, x2 -> x1 = x2

    let max ql1 ql2 =
        if ql1 = Returnable || ql2 = Returnable then
            Returnable
        else
            Usable

    (* The |> operator in the calculus.
       Idea: can have many Usable aliases but only one Returnable.
       Returnable use must be the last-used alias in the frame stack,
       preventing use-after-free errors and other nastiness.
     *)
    let sequence x1 x2 =
        if (Settings.(get disable_quasilinearity)) then
            Some (max x1 x2)
        else
            match x1, x2 with
                | Usable, Usable -> Some Usable
                | Usable, Returnable -> Some Returnable
                | _, _ -> None

    let pp ppf =
        let open Format in
        function
            | Usable -> pp_print_string ppf "Usable"
            | Returnable -> pp_print_string ppf "Returnable"
end

module PatternVar = struct
    type t = string
    [@@name "pattern_var"]
    [@@deriving
        visitors { variety = "map" },
        visitors { variety = "reduce" }
    ]

    let source = ref 0

    let fresh ?(prefix="p") () =
        let res = !source in
        incr source;
        prefix ^ (string_of_int res)

    let pp = Format.pp_print_string
end

module Pattern = struct
    type t =
        | PatVar of (PatternVar.t [@name "pattern_var"])
        | One
        | Zero
        (* Note: We do not need the payloads here, since they will be
           declared in the interface. *)
        | Message of string (* tag name *)
        | Plus of t * t
        | Concat of t * t
        | Many of t
    [@@name "pattern"]
    [@@deriving
        visitors {
            variety = "map";
            ancestors = ["PatternVar.map"]
        },
        visitors {
            variety = "reduce";
            ancestors = ["PatternVar.reduce"]
        }
    ]

    (** Creates a pattern consisting of a fresh pattern variable. *)
    let fresh () = PatVar (PatternVar.fresh ())

    (* Common visitor for derivatives *)
    class virtual ['self] deriv_visitor =
        object(self: 'self)
            inherit [_] map

            method! visit_Concat env p1 p2 =
                let lhs = Concat (self#visit_pattern env p1, p2) in
                let rhs = Concat (p1, self#visit_pattern env p2) in
                Plus (lhs, rhs)

            method! visit_Many env p =
                Concat (self#visit_pattern env p, Many p)

            method! visit_One _env = Zero
        end

    (** Calculates the pattern derivative wrt. a message tag. *)
    let tag_derivative tag =
        let visitor =
            object
                inherit [_] deriv_visitor
                method! visit_Message _ m = if m = tag then One else Zero
            end
        in
        visitor#visit_pattern ()

    let var_derivative var =
        let visitor =
            object
                inherit [_] deriv_visitor
                (* Variable derivative of a message is also Zero. *)
                method! visit_Message _ _ = Zero
                method! visit_PatVar _ v2 = if var = v2 then One else Zero
            end
        in
        visitor#visit_pattern ()

    let subst pat to_subst var =
        let visitor =
            object
                inherit [_] map
                method! visit_PatVar _ pv =
                    if pv = var then to_subst else PatVar pv
            end
        in
        visitor#visit_pattern () pat

    (* Given a Variable |-> Pattern map,
       substitutes all occurrences of a variable within the pattern
       with its associated pattern. *)
    let subst_all pat map =
        StringMap.fold (fun var pat acc ->
            subst acc pat var
        ) map pat

    (** Computes the Hopkins-Kozen closed-form solution of a pattern wrt. a
        pattern variable. *)
    let hopkins_kozen_solution var pat =
        let inner =
            Concat (Many (subst (var_derivative var pat) pat var), pat)
        in
        subst inner Zero var

    let simplify =
        let visitor =
            object(self)
                inherit [_] map

                (* Zero is the unit for Plus. *)
                method! visit_Plus env p1 p2 =
                    let (p1, p2) =
                        (self#visit_pattern env p1, self#visit_pattern env p2) in
                    if p1 = p2 then p1 else
                    match p1, p2 with
                        | (Zero, p)
                        | (p, Zero) -> p
                        | _, _ -> Plus (p1, p2)

                (* One is the unit for Concat. Zero is the eliminator. *)
                method! visit_Concat env p1 p2 =
                    let (p1, p2) =
                        (self#visit_pattern env p1, self#visit_pattern env p2) in
                    match p1, p2 with
                        | (Zero, _) | (_, Zero) -> Zero
                        | (One, p)  | (p, One) -> p
                        | _, _ -> Concat (p1, p2)

                method! visit_Many env p =
                    match self#visit_pattern env p with
                        (* Note: counterintuitively (but crucially), simplify(0* ) = 1.
                           This is due to the semantic interpretation of P* being grounded at 1. *)
                        | Zero
                        | One -> One
                        | p -> Many p
            end
        in
        visitor#visit_pattern ()

    let variables =
        let o =
            object
                inherit [_] reduce
                method zero = StringSet.empty
                method plus = StringSet.union
                method! visit_PatVar _ = StringSet.singleton
            end
        in
        o#visit_pattern ()

    let tags =
        let o =
            object
                inherit [_] reduce
                method zero = StringSet.empty
                method plus = StringSet.union
                method! visit_Message _ = StringSet.singleton
            end
        in
        o#visit_pattern ()


    let defined p = variables p |> StringSet.is_empty

    let is_zero p =
        match simplify p with
            | Zero -> true
            | _ -> false

    let rec pp ppf : t -> unit =
      let open Format in
      let ps = pp_print_string ppf in
      function
        | PatVar x -> PatternVar.pp ppf x
        | One -> ps "1"
        | Zero -> ps "0"
        | Message tag -> ps tag
        | Plus (p1, p2) ->
            fprintf ppf "(%a + %a)" pp p1 pp p2
        | Concat (p1, p2) ->
            fprintf ppf "(%a . %a)" pp p1 pp p2
        | Many p ->
            fprintf ppf "(%a)*" pp p

    let show = Format.asprintf "%a" pp
end

type t =
    | Base of base
    | Fun of { linear: bool; args: t list; result: t }
    | Tuple of t list
    | Rec of (string * t list)
    (* User-written mailbox type. May not have specified QL and pattern.
       This will be desugared before IR conversion. *)
    | UserMailbox of {
        umb_capability: (Capability.t [@name "capability"]);
        umb_interface: string;
        umb_quasilinearity: (Quasilinearity.t [@name "quasilinearity"]) option;
        umb_pattern: (Pattern.t [@name "pattern"]) option

    }
    (* Mailbox type after desugaring, or produced during TC *)
    | Mailbox of {
        capability: (Capability.t [@name "capability"]);
        interface: string;
        (* A mailbox type can either be returnable or usable.
           A returnable mailbox name can be used for all purposes (can be
           returned from subexpressions, can be sent upon, can be received
           upon).

           A usable mailbox can only be used for sending.

           The purpose of this is to restrict aliasing to a sensible
           level: we don't want to introduce 'bad' send aliasing and then
           circumvent syntactic checks.
         *)
        quasilinearity: (Quasilinearity.t [@name "quasilinearity"]);
        pattern: (Pattern.t [@name "pattern"])
    }
    [@@name "ty"]
and base = [%import: Common_types.Base.t]
    [@@deriving visitors {
        variety = "map";
        ancestors = ["Capability.map"; "Pattern.map"; "Quasilinearity.map"];
        data = false }
    ]

let is_mailbox_type = function
    | Mailbox _ -> true
    | _ -> false

let rec contains_mailbox_type = function
    | Mailbox _ -> true
    | Tuple ts -> List.exists contains_mailbox_type ts
    | Rec (_, ts) -> List.exists contains_mailbox_type ts
    | _ -> false

(* Easy constructors *)
let int_type = Base Base.Int
let string_type = Base Base.String
let bool_type = Base Base.Bool
let unit_type = Tuple []
let atom = Base Base.Atom
let function_type linear args result =
    Fun { linear; args; result }

let mailbox_send_unit interface quasilinearity =
    Mailbox {
        capability = Capability.Out;
        interface;
        pattern = Pattern.One;
        quasilinearity
    }

let rec pp ppf =
  let open Format in
  function
    | Base b -> Base.pp ppf b
    | Fun { linear; args; result } ->
        let arrow = if linear then "-o" else "->" in
        fprintf ppf "(%a) %s %a"
            (pp_print_comma_list pp) args
            arrow
            pp result
    | Tuple ts ->
        let pp_star ppf () = pp_print_string ppf " * " in
        fprintf ppf "(%a)"
            (pp_print_list ~pp_sep:(pp_star) pp) ts
    | Rec ("Sum", [t1; t2]) ->
        fprintf ppf "(%a + %a)"
            pp t1
            pp t2
    | Rec (s, ts) ->
        let pp_comma ppf () = pp_print_string ppf ", " in
        fprintf ppf "%s(%a)"
        s
        (pp_print_list ~pp_sep:(pp_comma) pp) ts
    | Mailbox { capability; interface; pattern; quasilinearity } ->
        let ql =
            match quasilinearity with
                | Quasilinearity.Returnable -> "R"
                | Quasilinearity.Usable -> "U"
        in
        let cap =
            match capability with
                | Capability.In -> "?"
                | Capability.Out -> "!"
        in
        fprintf ppf "%s%s(%a)[%s]"
            interface
            cap
            pp_pattern pattern
            ql
    | UserMailbox { umb_capability; umb_interface;
            umb_pattern; umb_quasilinearity } ->
        let ql =
            match umb_quasilinearity with
                | Some (Quasilinearity.Returnable) -> "[R]"
                | Some (Quasilinearity.Usable) -> "[U]"
                | None -> ""
        in
        let cap =
            match umb_capability with
                | Capability.In -> "?"
                | Capability.Out -> "!"
        in
        fprintf ppf "%s%s(%a)%s"
            umb_interface
            cap
            (pp_print_option pp_pattern) umb_pattern
            ql
and pp_capability = Capability.pp
and pp_base = Base.pp
and pp_pattern = Pattern.pp
and pp_pattern_var = PatternVar.pp

let show t =
  let open Format in
  pp str_formatter t;
  flush_str_formatter ()

let rec is_lin = function
    | Base _ -> false
    | Fun { linear; _ } -> linear
    (* !1 is unrestricted... *)
    | Mailbox { capability = Out; pattern = One; _ } -> false
    | Tuple ts -> List.exists is_lin ts
    | Rec (_, ts) -> List.exists is_lin ts
    (* ...but otherwise a mailbox type must be used linearly. *)
    | Mailbox _ -> true
    | UserMailbox _ -> assert false

let is_input_mailbox = function
    | Mailbox { capability = In; _ } -> true
    | _ -> false

let is_output_mailbox = function
    | Mailbox { capability = Out; _ } -> true
    | UserMailbox { umb_capability = Out; _ } -> true
    | _ -> false

let rec contains_output_mailbox = function
    | Mailbox { capability = Out; _} -> true
    | UserMailbox { umb_capability = Out; _} -> true
    | Tuple ts
    | Rec (_, ts) -> List.exists contains_output_mailbox ts
    | _ -> false

let is_tuple = function
    | Tuple _ -> true
    | _ -> false

let get_pattern = function
    | Mailbox { pattern = pat; _ } -> pat
    | UserMailbox { umb_pattern = Some pat; _ } -> pat
    | _ -> raise (Errors.internal_error "type.ml" "attempted to get pattern of non-mailbox type")

let get_interface = function
    | Mailbox { interface = iface; _ }
    | UserMailbox { umb_interface = iface; _ } -> iface
    | _ -> raise (Errors.internal_error "type.ml" "attempted to get interface of non-mailbox type")


let get_quasilinearity = function
    | Mailbox { quasilinearity; _ } -> quasilinearity
    | UserMailbox { umb_quasilinearity = Some ql; _ } -> ql
    | _ -> raise (Errors.internal_error "type.ml" "attempted to get quasilinearity of non-mailbox type")

(* make_usable always defined on datatypes in order to ensure spawn masking works *)
let rec make_usable = function
    | Mailbox m -> Mailbox { m with quasilinearity = Quasilinearity.Usable }
    | Tuple ts -> Tuple (List.map make_usable ts)
    | Rec (s, ts) -> Rec (s, (List.map make_usable ts))
    | t -> t

(* make_returnable propagates returnability to datatype components
   if liberal datatypes is off; otherwise it leaves them untouched *)
let rec make_returnable = function
    | Mailbox m -> Mailbox { m with quasilinearity = Quasilinearity.Returnable }
    | ty ->
        begin
            if not <| Settings.(get liberal_datatypes) then
                match ty with
                    | Tuple ts -> Tuple (List.map make_returnable ts)
                    | Rec (s, ts) -> Rec (s, List.map make_returnable ts)
                    | _ -> ty
            else ty
        end
    

let is_unr = is_lin >> not

let is_returnable = function
    | Mailbox { quasilinearity = ql; _ } ->
        ql = Quasilinearity.Returnable
    | _ -> true

let make_function_type linear args result =
    Fun { linear; args; result }

let make_tuple_type tys =
    if Settings.(get liberal_datatypes) then
        Tuple tys
    else
        Tuple (List.map make_returnable tys)

let make_sum_type ty1 ty2 =
    if Settings.(get liberal_datatypes) then
        Rec (sum_type_name, [ty1; ty2])
    else
        Rec (sum_type_name, [make_returnable ty1; make_returnable ty2])

let is_list = function
    | Rec (s, _) -> String.equal s list_type_name
    | _ -> false

let make_list_type ty = Rec (list_type_name, [ty])
