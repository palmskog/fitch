open Util
open Fitch_system
open FitchProgramMap
open FitchPI

let main () =
  let f = open_in Sys.argv.(1) in
  let buf = Lexing.from_channel f in
  try
    let c = Parser.main Lexer.token buf in
    Printf.printf "%b\n" (valid_claim_dec0 c);
    close_in f
  with
  | Lexer.Error msg ->
      Printf.eprintf "%s%!" msg
  | Parser.Error ->
      Printf.eprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buf)

let _ = main ()
