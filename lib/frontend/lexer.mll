{
(* Preamble *)
open Lexing
open Parser
open Util
open Common.Source_code

exception SyntaxError of string

(* Increments internal lexer metadata *)
let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
        { pos with pos_bol = pos.Lexing.pos_cnum;
                   pos_lnum = pos.pos_lnum + 1
        }
(* Adds a lexeme along with its position to the source code memory,
   enabling accurate error reporting later. *)
let add_to_source_code lexbuf =
    let lexeme = Lexing.lexeme lexbuf in
    let source_code = SourceCodeManager.get_instance () in
    let _ = source_code#parse_into (fun buffer _ ->
        let len = String.length lexeme in
        String.blit lexeme 0 buffer 0 len;
        len) (Bytes.of_string lexeme) (String.length lexeme) in
    ()


(* Keywords *)
let keywords = [
    "let", LET;
    "spawn", SPAWN;
    "new", NEW;
    "guard", GUARD;
    "receive", RECEIVE;
    "free", FREE;
    "empty", EMPTY;
    "fail", FAIL;
    "in", IN;
    "linfun", LINFUN;
    "fun", FUN;
    "from", FROM;
    "interface", INTERFACE;
    "def", DEF;
    "if", IF;
    "else", ELSE;
    "case", CASE;
    "of", OF;
    "data", DATA
]
}

(* Regular expressions (mostly taken from Links) *)
let def_id = (['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*)
let def_atom = (':' ['a'-'z' 'A'-'Z'] ['a'-'z' 'A'-'Z' '_' '0'-'9' '\'']*)
let def_white = [' ' '\t']+
let def_newline = '\r' | '\n' | "\r\n"
let def_integer = (['1'-'9'] ['0'-'9']* | '0')
let def_float = (def_integer '.' ['0'-'9']+ ('e' ('-')? def_integer)?)
let op_char = [ '.' '!' '$' '&' '*' '+' '/' '<' '=' '>' '@' '\\' '^' '-' '|' ]

(* Lexing rules *)

rule read =
    parse
    | def_white  { add_to_source_code lexbuf; read lexbuf }
    | def_newline { add_to_source_code lexbuf; next_line lexbuf; read lexbuf }
    | def_integer { add_to_source_code lexbuf; INT (int_of_string (Lexing.lexeme lexbuf)) }
    | '#' ([^ '\n'] *) { add_to_source_code lexbuf; read lexbuf } (* Comment *)
    (* | def_float { add_to_source_code lexbuf; FLOAT (float_of_string (Lexing.lexeme lexbuf)) }  *)
    | "true"   { add_to_source_code lexbuf; BOOL true }
    | "false"  { add_to_source_code lexbuf; BOOL false }
    | "receive*" { add_to_source_code lexbuf; RECEIVESTAR }
    | def_id as var { add_to_source_code lexbuf;
                      try List.assoc var keywords
                      with Not_found ->
                      (* Check if it's a registered constructor keyword *)
                      match Common.Recursive_types.find_constructor_keyword var with
                      | Some name -> CTOR_KW name
                      | None ->
                          if Utility.is_uppercase var.[0] then
                              CONSTRUCTOR var
                          else
                              VARIABLE var }
    | def_atom as atom { add_to_source_code lexbuf; ATOM atom }
    | '"'      { add_to_source_code lexbuf; read_string (Buffer.create 17) lexbuf }
    | '{'      { add_to_source_code lexbuf; LEFT_BRACE }
    | '}'      { add_to_source_code lexbuf; RIGHT_BRACE }
    | '['      { add_to_source_code lexbuf; LEFT_BRACK }
    | ']'      { add_to_source_code lexbuf; RIGHT_BRACK }
    | '('      { add_to_source_code lexbuf; LEFT_PAREN }
    | ')'      { add_to_source_code lexbuf; RIGHT_PAREN }
    | ';'      { add_to_source_code lexbuf; SEMICOLON }
    | ':'      { add_to_source_code lexbuf; COLON }
    | ','      { add_to_source_code lexbuf; COMMA }
    | '='      { add_to_source_code lexbuf; EQ }
    | '!'      { add_to_source_code lexbuf; BANG }
    | '?'      { add_to_source_code lexbuf; QUERY }
    | '.'      { add_to_source_code lexbuf; DOT }
    | '*'      { add_to_source_code lexbuf; STAR }
    | '/'      { add_to_source_code lexbuf; DIV }
    | '+'      { add_to_source_code lexbuf; PLUS }
    | '-'      { add_to_source_code lexbuf; MINUS }
    | '|'      { add_to_source_code lexbuf; PIPE }
    | "&&"     { add_to_source_code lexbuf; AND }
    | "||"     { add_to_source_code lexbuf; OR }
    | ">="     { add_to_source_code lexbuf; GEQ }
    | "<"      { add_to_source_code lexbuf; LT }
    | ">"      { add_to_source_code lexbuf; GT }
    | "<="     { add_to_source_code lexbuf; LEQ }
    | "=="     { add_to_source_code lexbuf; EQQ }
    | "!="     { add_to_source_code lexbuf; NEQ }
    | "->"     { add_to_source_code lexbuf; RIGHTARROW }
    | "-o"     { add_to_source_code lexbuf; LOLLI }
    | "::"     { add_to_source_code lexbuf; CONS }
    | _ { raise (SyntaxError ("Unexpected char: " ^ Lexing.lexeme lexbuf)) }
    | eof      { EOF }
and read_string buf =
    parse
    | '"'       { add_to_source_code lexbuf; STRING (Buffer.contents buf) }
    | '\\' '/'  { add_to_source_code lexbuf; Buffer.add_char buf '/'; read_string buf lexbuf }
    | '\\' '\\' { add_to_source_code lexbuf; Buffer.add_char buf '\\'; read_string buf lexbuf }
    | '\\' 'b'  { add_to_source_code lexbuf; Buffer.add_char buf '\b'; read_string buf lexbuf }
    | '\\' 'f'  { add_to_source_code lexbuf; Buffer.add_char buf '\012'; read_string buf lexbuf }
    | '\\' 'n'  { add_to_source_code lexbuf; Buffer.add_char buf '\n'; read_string buf lexbuf }
    | '\\' 'r'  { add_to_source_code lexbuf; Buffer.add_char buf '\r'; read_string buf lexbuf }
    | '\\' 't'  { add_to_source_code lexbuf; Buffer.add_char buf '\t'; read_string buf lexbuf }
    | [^ '"' '\\']+
      { add_to_source_code lexbuf; Buffer.add_string buf (Lexing.lexeme lexbuf);
        read_string buf lexbuf
      }
    | _ { raise (SyntaxError ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
    | eof { raise (SyntaxError ("String is not terminated")) }
