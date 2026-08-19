%{
open Common
open Sugar_ast
open Common_types
open Source_code
open SourceCodeManager

module type Pos = sig
    (* Type of positions. *)
    type t
    val with_pos : t -> 'a -> 'a WithPos.t
end

module ParserPosition
    : Pos with type t = (Lexpos.t * Lexpos.t) = struct
    (* parser position produced by Menhir *)
    type t = Lexpos.t * Lexpos.t
    (* Convert position produced by a parser to SourceCode position *)
    let pos (start, finish) =
        let code = get_instance () in
        Position.make ~start ~finish ~code:code
    (* Wrapper around SourceCode.WithPos.make.  Accepts parser positions. *)
    let with_pos (start, finish) v = WithPos.make ~pos:(pos (start, finish)) v
end

let get_start_pos e = Position.start (WithPos.pos e)
let get_end_pos e = Position.finish (WithPos.pos e)

(* Helper function to create an expression/interface/decl with a position *)
let with_pos_from_positions p1 p2 newE = ParserPosition.with_pos (p1, p2) newE

let parse_error x pos_list = Errors.Parse_error (x,pos_list)

let binary_op op_name x1 x2 = App { func = ParserPosition.with_pos ((get_start_pos x1),(get_end_pos x2)) (Primitive op_name); args = [x1; x2] }

(* Data declaration field descriptions *)
type data_field_desc =
    | DVar of string
    | DApp of string * data_field_desc list
    | DBase of string   (* bare constructor name: base type or 0-param self-ref *)

(* Map a base type name to a Type.t, or None if unknown *)
let base_type_of_name = function
    | "Int"    -> Some (Type.Base Base.Int)
    | "Bool"   -> Some (Type.Base Base.Bool)
    | "String" -> Some (Type.Base Base.String)
    | "Atom"   -> Some (Type.Base Base.Atom)
    | "Unit"   -> Some (Type.Tuple [])
    | _        -> None

(* Interpret a data field as a binder_source *)
let interpret_data_field type_name params field pos =
    let find_param_index v =
        let rec go i = function
            | [] -> None
            | p :: _ when p = v -> Some i
            | _ :: rest -> go (i + 1) rest
        in go 0 params
    in
    match field with
    | DVar v ->
        begin match find_param_index v with
        | Some i -> Recursive_types.Param i
        | None ->
            raise (parse_error
                (Format.sprintf "Unknown type variable '%s' in data declaration" v)
                [pos])
        end
    | DBase name when name = type_name && params = [] ->
        (* Bare self-reference for a 0-parameter type, e.g., Expr in Add Expr Expr *)
        Recursive_types.Self
    | DBase name ->
        begin match base_type_of_name name with
        | Some ty -> Recursive_types.Fixed ty
        | None ->
            raise (parse_error
                (Format.sprintf
                    "Unknown type '%s' in data declaration field \
                     (expected a base type like Int, Bool, String, or a self-reference)" name)
                [pos])
        end
    | DApp (name, args) when name = type_name ->
        (* Check that args match the type parameters exactly *)
        let matches =
            List.length args = List.length params &&
            List.for_all2 (fun arg param ->
                match arg with DVar v -> v = param | _ -> false
            ) args params
        in
        if matches then Recursive_types.Self
        else
            raise (parse_error
                (Format.sprintf
                    "Recursive reference to '%s' must use the same type parameters" type_name)
                [pos])
    | DApp (name, _) ->
        raise (parse_error
            (Format.sprintf
                "Unsupported field type '%s' in data declaration \
                 (only base types, type parameters, and self-references are supported)" name)
            [pos])


%}
(* Tokens *)
%token <int> INT
%token <bool> BOOL
%token <string> STRING
%token <string> VARIABLE
%token <string> CONSTRUCTOR
%token <string> ATOM

(* %token NULL *)
%token LEFT_BRACE RIGHT_BRACE
%token LEFT_BRACK RIGHT_BRACK
%token LEFT_PAREN RIGHT_PAREN
%token SEMICOLON
%token COLON
%token COMMA
(*
These will be added in later
%token <string> CONSTRUCTOR
%token <float> FLOAT
*)
%token BANG
%token QUERY
%token DOT
%token STAR
%token EQ
%token EOF
%token RIGHTARROW
%token LOLLI
%token PLUS
%token DIV

(* Keyword tokens *)
%token LET
%token SPAWN
%token NEW
%token GUARD
%token RECEIVE
%token RECEIVESTAR
%token FREE
%token FAIL
%token EMPTY
%token IN
%token FUN
%token LINFUN
%token FROM
%token INTERFACE
%token DEF
%token IF
%token ELSE
%token MINUS
%token GEQ
%token LT
%token GT
%token LEQ
%token EQQ
%token NEQ
%token AND
%token OR
%token CASE
%token CASEL
%token <string> CTOR_KW
%token CONS
%token OF
%token PIPE
%token DATA

(* Precedence *)
%left AND OR
%left LT GT GEQ LEQ EQQ NEQ
%left PLUS MINUS
%left STAR DIV

(* Resolves the shift/reduce conflict between continuing a data constructor's
   field list (data_field_list below) and ending it so that whatever follows
   the data declarations (typically a top-level expr) can begin. *)
%nonassoc END_DATA_FIELDS
%nonassoc VARIABLE CONSTRUCTOR LEFT_PAREN

(* Start parsing *)
%start <expr> expr_main
%start <program * source_code > program

%%

(* Any constructor name: covers both registered CTOR_KW and unregistered CONSTRUCTOR *)
any_constructor:
    | CONSTRUCTOR { $1 }
    | CTOR_KW { $1 }

(* Data declaration field: a type variable, a bare constructor (base type or 0-param self),
   or a parenthesized type application for parameterized types.
   A parenthesized constructor with no inner fields, e.g. (Nothing), is treated as DBase
   (a 0-param self-reference or base type). *)
data_field:
    | VARIABLE { DVar $1 }
    | CONSTRUCTOR { DBase $1 }
    | LEFT_PAREN any_constructor RIGHT_PAREN { DBase $2 }
    | LEFT_PAREN any_constructor data_field+ RIGHT_PAREN { DApp ($2, $3) }

(* Zero or more data fields, written out explicitly (rather than via the
   data_field* combinator) so the empty-list production can carry the
   %prec annotation that resolves the shift/reduce conflict described above. *)
data_field_list:
    | (* empty *) %prec END_DATA_FIELDS { [] }
    | data_field data_field_list { $1 :: $2 }

(* A single data constructor: name followed by zero or more fields *)
data_ctor:
    | any_constructor data_field_list { ($1, $2) }

(* Data type declaration with side-effecting registration *)
data_decl:
    | DATA CONSTRUCTOR VARIABLE* EQ separated_nonempty_list(PIPE, data_ctor) {
        let type_name = $2 in
        let params = $3 in
        let param_count = List.length params in
        let pos = Position.make ~start:$startpos ~finish:$endpos
            ~code:!source_code_instance in
        let constructors = List.map (fun (ctor_name, fields) ->
            let binder_sources = List.map
                (fun f -> interpret_data_field type_name params f pos)
                fields
            in
            Recursive_types.{ ctor_name; binder_sources }
        ) $5 in
        let def = Recursive_types.{ type_name; param_count; constructors } in
        Recursive_types.register def [pos]
    }

(* Constructor name: either a built-in CTOR_KW or a user-defined CONSTRUCTOR *)
ctor_name:
    | CTOR_KW { $1 }
    | CONSTRUCTOR { $1 }

message:
    | CONSTRUCTOR LEFT_PAREN separated_list(COMMA, expr) RIGHT_PAREN { ($1, $3) }

message_binder:
    | CONSTRUCTOR LEFT_PAREN separated_list(COMMA, VARIABLE) RIGHT_PAREN { ($1, $3) }

type_annot:
    | COLON ty { $2 }

branch:
    | ctor_name LEFT_PAREN separated_list(COMMA, VARIABLE) RIGHT_PAREN RIGHTARROW expr { ($3, $6, $1) }
    | ctor_name RIGHTARROW expr { ([], $3, $1) }
    | LEFT_PAREN VARIABLE CONS VARIABLE RIGHT_PAREN RIGHTARROW expr { ([$2; $4], $7, "Cons") }

expr:
    (* Let *)
    | LET VARIABLE type_annot? EQ expr IN expr
        { with_pos_from_positions $startpos $endpos (Let { binder = $2; annot = $3; term = $5; body = $7 }) }
    | LET LEFT_PAREN separated_list(COMMA, VARIABLE) RIGHT_PAREN COLON tuple_annotation EQ basic_expr IN expr
        { with_pos_from_positions $startpos $endpos (LetTuple { binders = $3; term = $8; annot = Some $6; cont = $10 }) }
    | LET LEFT_PAREN separated_list(COMMA, VARIABLE) RIGHT_PAREN EQ basic_expr IN expr
        { with_pos_from_positions $startpos $endpos (LetTuple { binders = $3; term = $6; annot = None; cont = $8 }) }
    | basic_expr SEMICOLON expr { with_pos_from_positions $startpos $endpos (Seq ($1, $3)) }
    | basic_expr COLON ty { with_pos_from_positions $startpos $endpos (Annotate ($1, $3)) }
    | basic_expr { $1 }

expr_list:
    | separated_list(COMMA, expr) { $1 }

tuple_exprs:
    | LEFT_PAREN expr COMMA separated_nonempty_list(COMMA, expr) RIGHT_PAREN { $2 :: $4 }

linearity:
    | FUN    { false }
    | LINFUN { true }

basic_expr:
    | ctor_name LEFT_PAREN separated_list(COMMA, expr) RIGHT_PAREN { with_pos_from_positions $startpos $endpos ( Inject ($1, $3) )}
    | ctor_name { with_pos_from_positions $startpos $endpos ( Inject ($1, []) )}
    | CASE basic_expr type_annot OF LEFT_BRACE separated_list(PIPE, branch) RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos ( Case { term = $2; ty = $3; branches = $6 } )}
    (* SJF TODO: Update example files to use Case instead of CaseL and delete this parse form *)
    | CASEL basic_expr type_annot OF LEFT_BRACE branch PIPE branch RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos ( Case { term = $2; ty = $3; branches = [$6; $8] } )}
    (* New *)
    | NEW LEFT_BRACK interface_name RIGHT_BRACK { with_pos_from_positions $startpos $endpos ( New $3 )}
    (* Spawn *)
    | SPAWN LEFT_BRACE expr RIGHT_BRACE { with_pos_from_positions $startpos $endpos ( Spawn $3 )}
    (* Free *)
    | FREE LEFT_PAREN expr RIGHT_PAREN { with_pos_from_positions $startpos $endpos ( Free $3 )}
    (* Sugared Fail forms *)
    | FAIL LEFT_PAREN expr RIGHT_PAREN LEFT_BRACK ty RIGHT_BRACK { with_pos_from_positions $startpos $endpos ( SugarFail ($3, $6))}
    | tuple_exprs { with_pos_from_positions $startpos $endpos ( Tuple $1 ) }
    | LEFT_PAREN expr CONS expr RIGHT_PAREN { with_pos_from_positions $startpos $endpos ( Inject ("Cons", [$2; $4]) ) }
    (* App *)
    | fact LEFT_PAREN expr_list RIGHT_PAREN
        { with_pos_from_positions $startpos $endpos (
            App {   func = with_pos_from_positions $startpos $endpos ($1);
                    args = $3 }
        )}
    (* Lam *)
    | linearity LEFT_PAREN annotated_var_list RIGHT_PAREN COLON ty LEFT_BRACE expr RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos ( Lam { linear = $1; parameters = $3; result_type = $6; body = $8 } )}
    (* Send *)
    | fact BANG message
        { with_pos_from_positions $startpos $endpos(
            Send {  target = with_pos_from_positions $startpos $endpos ($1);
                    message = $3;
                    iname = None
            }
        )}
    (* If-Then-Else *)
    | IF LEFT_PAREN expr RIGHT_PAREN LEFT_BRACE expr RIGHT_BRACE ELSE LEFT_BRACE expr RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos ( If { test = $3; then_expr = $6; else_expr = $10 } )}
    (* Guard *)
    | GUARD basic_expr COLON pat LEFT_BRACE guard+ RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos (
            Guard {
                target = $2;
                pattern = $4;
                guards = $6;
                iname = None
            }
        )}
    | op { with_pos_from_positions $startpos $endpos ( $1 )}

op:
    | basic_expr AND basic_expr { binary_op "&&" $1 $3 }
    | basic_expr OR basic_expr { binary_op "||" $1 $3 }
    | basic_expr EQQ basic_expr { binary_op "==" $1 $3 }
    | basic_expr NEQ basic_expr { binary_op "!=" $1 $3 }
    | basic_expr LT basic_expr { binary_op "<" $1 $3 }
    | basic_expr GT basic_expr { binary_op ">" $1 $3 }
    | basic_expr LEQ basic_expr { binary_op "<=" $1 $3 }
    | basic_expr GEQ basic_expr { binary_op ">=" $1 $3 }
    | basic_expr PLUS basic_expr { binary_op "+" $1 $3 }
    | basic_expr MINUS basic_expr { binary_op "-" $1 $3 }
    | basic_expr STAR basic_expr { binary_op "*" $1 $3 }
    | basic_expr DIV basic_expr { binary_op "/" $1 $3 }
    | fact { $1 }

fact:
    (* Unit *)
    | LEFT_PAREN RIGHT_PAREN { Tuple [] }
    | ATOM { Atom (String.(sub $1 1 (length $1 - 1))) }
    | BOOL   { Constant (Constant.wrap_bool $1) }
    (* Var *)
    | VARIABLE {
        if List.mem_assoc $1 (Lib_types.signatures) then
            Primitive $1
        else
            Var $1
    }
    (* Constant *)
    | INT    { Constant (Constant.wrap_int $1) }
    | STRING { Constant (Constant.wrap_string $1) }
    | LEFT_PAREN expr RIGHT_PAREN { WithPos.node $2 }


guard:
    | FAIL COLON ty { with_pos_from_positions $startpos $endpos ( Fail $3) }
    | EMPTY LEFT_PAREN VARIABLE RIGHT_PAREN RIGHTARROW expr { with_pos_from_positions $startpos $endpos (Empty ($3, $6)) }
    | FREE RIGHTARROW expr { with_pos_from_positions $startpos $endpos (GFree $3) }
    | RECEIVE message_binder FROM VARIABLE RIGHTARROW expr
            { with_pos_from_positions $startpos $endpos (
              let (tag, bnds) = $2 in
              Receive { tag; payload_binders = bnds;
                        mailbox_binder = $4; strategy = None; cont = $6 })
            }
    | RECEIVESTAR message_binder FROM VARIABLE RIGHTARROW expr
            { with_pos_from_positions $startpos $endpos (
              let (tag, bnds) = $2 in
              Receive { tag; payload_binders = bnds;
                        mailbox_binder = $4; strategy = Some Nothing; cont = $6 })
            }

(* Type parser *)

ty_list:
    | separated_nonempty_list(COMMA, ty) { $1 }

(* Note: don't parse a 1-tuple, which doesn't make sense *)
tuple_annotation:
    | LEFT_PAREN ty STAR separated_nonempty_list(STAR, ty) RIGHT_PAREN { $2 :: $4 }

parenthesised_datatypes:
    | LEFT_PAREN RIGHT_PAREN { [] }
    | LEFT_PAREN ty_list RIGHT_PAREN { $2 }

ty:
    | parenthesised_datatypes RIGHTARROW simple_ty  { Type.Fun { linear = false; args = $1; result = $3} }
    | parenthesised_datatypes LOLLI simple_ty       { Type.Fun { linear = true;  args = $1; result = $3} }
    | LEFT_PAREN simple_ty PLUS simple_ty RIGHT_PAREN { Type.make_sum_type $2 $4 }
    | tuple_annotation { Type.make_tuple_type $1 }
    | CONSTRUCTOR LEFT_PAREN separated_list(COMMA, ty) RIGHT_PAREN {
        let name = $1 in
        let args = $3 in
        match Recursive_types.find_type name with
        | Some def when List.length args = def.param_count ->
            Type.Rec (name, args)
        | Some def ->
            raise (parse_error
                (Format.sprintf "%s expects %d type argument(s), got %d"
                    name def.param_count (List.length args))
                [Position.make ~start:$startpos ~finish:$endpos ~code:!source_code_instance])
        | None ->
            raise (parse_error
                (Format.sprintf "Unknown type constructor: %s" name)
                [Position.make ~start:$startpos ~finish:$endpos ~code:!source_code_instance])
    }
    | simple_ty { $1 }

interface_name:
    | CONSTRUCTOR { $1 }

pat:
    | star_pat PLUS pat { Type.Pattern.Plus ($1, $3) }
    | star_pat DOT pat  { Type.Pattern.Concat ($1, $3) }
    | star_pat          { $1 }

star_pat:
    | simple_pat STAR   { Type.Pattern.Many $1 }
    | simple_pat        { $1 }

simple_pat:
    | CONSTRUCTOR { Type.Pattern.Message $1 }
    | INT {
            match $1 with
                | 0 -> Type.Pattern.Zero
                | 1 -> Type.Pattern.One
                | _ -> raise (parse_error "Invalid pattern: expected 0 or 1."
                                [Position.make ~start:$startpos ~finish:$endpos ~code:!source_code_instance])
        }
    | LEFT_PAREN pat RIGHT_PAREN { $2 }

ql:
    | LEFT_BRACK CONSTRUCTOR RIGHT_BRACK {
        match $2 with
            | "R" -> Type.Quasilinearity.Returnable
            | "U" -> Type.Quasilinearity.Usable
            | _ -> raise (parse_error "Invalid usage: expected U or R."
                            [Position.make ~start:$startpos ~finish:$endpos ~code:!source_code_instance])
    }

mailbox_ty:
    | CONSTRUCTOR BANG simple_pat? ql? {
        Type.(UserMailbox {
            umb_capability = Capability.Out;
            umb_interface = $1;
            umb_pattern = $3;
            umb_quasilinearity = $4
        })
    }
    | CONSTRUCTOR QUERY simple_pat? ql? {
        Type.(UserMailbox {
            umb_capability = Capability.In;
            umb_interface = $1;
            umb_pattern = $3;
            umb_quasilinearity = $4
        })
    }

simple_ty:
    | mailbox_ty { $1 }
    | base_ty { $1 }

base_ty:
    | CONSTRUCTOR {
        let pos = Position.make ~start:$startpos ~finish:$endpos ~code:!source_code_instance in
        match $1 with
            | "Atom"   -> Type.Base Base.Atom
            | "Unit"   -> Type.Tuple []
            | "Int"    -> Type.Base Base.Int
            | "Bool"   -> Type.Base Base.Bool
            | "String" -> Type.Base Base.String
            | name ->
                (* Check if it's a 0-param user-defined recursive type *)
                match Recursive_types.find_type name with
                | Some def when def.param_count = 0 -> Type.Rec (name, [])
                | Some def ->
                    raise (parse_error
                        (Format.sprintf "%s expects %d type argument(s), got 0"
                            name def.param_count)
                        [pos])
                | None ->
                    raise (parse_error
                        (Format.sprintf "Unknown type '%s': expected Int, Bool, String, Atom, Unit, or a defined type" name)
                        [pos])
    }

message_ty:
    | CONSTRUCTOR LEFT_PAREN separated_list(COMMA, ty) RIGHT_PAREN { ($1, $3) }

message_list:
    | separated_list(COMMA, message_ty) { $1 }

annotated_var:
    | VARIABLE COLON ty { ($1, $3) }

annotated_var_list:
    | separated_list(COMMA, annotated_var)  { $1 }

interface:
    | INTERFACE interface_name LEFT_BRACE message_list RIGHT_BRACE
        { with_pos_from_positions $startpos $endpos ( Interface.make $2 $4)  }

decl:
    | DEF VARIABLE LEFT_PAREN annotated_var_list RIGHT_PAREN COLON ty LEFT_BRACE expr
    RIGHT_BRACE {
        with_pos_from_positions $startpos $endpos (
        {
          decl_name = $2;
          decl_parameters = $4;
          decl_return_type = $7;
          decl_body = $9
        })
    }

expr_main:
    | expr EOF { $1 }

program:
    | data_decl* interface* decl* expr? EOF { ({ prog_interfaces = $2; prog_decls = $3; prog_body = $4 }, !source_code_instance) }
