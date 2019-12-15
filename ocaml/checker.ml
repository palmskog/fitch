open Util
open Fitch_system
open FitchProgramMap
open FitchPI

let rec string_of_prop = function
| Coq_prop_cont -> "_|_"
| Coq_prop_neg p -> "~ " ^ string_of_prop p
| Coq_prop_and (p1, p2) -> (string_of_prop p1) ^ " /\\ " ^ (string_of_prop p2)
| Coq_prop_or (p1, p2) -> (string_of_prop p1) ^ " \\/ " ^ (string_of_prop p2)
| Coq_prop_imp (p1, p2) -> (string_of_prop p1) ^ " -> " ^ (string_of_prop p2)
| Coq_prop_p p -> string_of_char_list p

let rec string_of_claim = function
| Coq_claim_judgment_proof (Coq_judgment_follows (pl, p), _) ->
  String.concat ", " (List.map string_of_prop pl) ^ " |- " ^ (string_of_prop p)

let main () =
  let f = open_in Sys.argv.(1) in
  let buf = Lexing.from_channel f in
  try
    let c = Parser.main Lexer.token buf in
    (*Printf.printf "%s\n" (string_of_claim c);*)
    Printf.printf "%b\n" (valid_claim_dec0 c);
    close_in f
  with
  | Lexer.Error msg ->
      Printf.eprintf "%s%!" msg
  | Parser.Error ->
      Printf.eprintf "At offset %d: syntax error.\n%!" (Lexing.lexeme_start buf)

let _ = main ()
