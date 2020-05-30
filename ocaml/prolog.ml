open Fitch_system

let main () =
  let f = open_in Sys.argv.(1) in
  let buf = Lexing.from_channel f in
  try
    let c = Prolog_parser.main Prolog_lexer.token buf in
    Printf.printf "%b\n" (valid_claim_dec0 c);
    close_in f
  with
  | Prolog_lexer.Error msg ->
      Printf.eprintf "%s%!" msg
  | Prolog_parser.Error ->
      Printf.eprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buf)

let _ = main ()
