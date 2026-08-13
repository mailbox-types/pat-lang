open Common
open Lexer
open Lexing
open Source_code

let pos lexbuf = Position.make 
                    ~start:
                        { lexbuf.lex_start_p with
                          Lexing.pos_lnum = 
                            if lexbuf.lex_start_p.pos_lnum > 1 then
                              lexbuf.lex_start_p.pos_lnum - 2
                            else
                              lexbuf.lex_start_p.pos_lnum
                        }
                    ~finish:lexbuf.lex_curr_p
                    ~code:(SourceCodeManager.get_instance ())

let parse_with_error lexbuf =
  try Parser.program Lexer.read lexbuf with
  | SyntaxError msg ->
    let msg = Format.asprintf "%s" msg in
    raise (Errors.parse_error msg [pos lexbuf])
  | Parser.Error ->
    let msg = Format.asprintf "syntax error" in
    raise (Errors.parse_error msg [pos lexbuf])

let parse_and_print lexbuf =
  let (program, _) = parse_with_error lexbuf in
  Settings.if_verbose (fun () ->
      Format.printf "=== Parsed Program ===\n%a\n\n" Sugar_ast.pp_program program);
  program

let parse_file filename () =
  (* Reset the recursive type registry to built-ins for each new file *)
  Common.Recursive_types.reset ();
  let inx = In_channel.open_text filename in
  let lexbuf = Lexing.from_channel inx in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = filename };
  let expr = parse_and_print lexbuf in
  In_channel.close inx;
  expr

let parse_string x () =
  Common.Recursive_types.reset ();
  let lexbuf = Lexing.from_string x in
  lexbuf.lex_curr_p <- { lexbuf.lex_curr_p with pos_fname = "<string>" };
  let expr = parse_and_print lexbuf in
  expr
