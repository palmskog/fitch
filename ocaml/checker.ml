open Util
open Fitch_system
open FitchProgramMap
open FitchPI

let rec string_of_prop = function
| Coq_prop_cont -> "cont"
| Coq_prop_neg p -> "(" ^ "~ " ^ string_of_prop p ^ ")"
| Coq_prop_and (p1, p2) -> "(" ^ (string_of_prop p1) ^ " /\\ " ^ (string_of_prop p2) ^ ")"
| Coq_prop_or (p1, p2) -> "(" ^ (string_of_prop p1) ^ " \\/ " ^ (string_of_prop p2) ^ ")"
| Coq_prop_imp (p1, p2) -> "(" ^ (string_of_prop p1) ^ " -> " ^ (string_of_prop p2) ^ ")"
| Coq_prop_p p -> string_of_char_list p

let string_of_justification = function
| Coq_justification_premise -> "premise"
| Coq_justification_lem -> "lem"
| Coq_justification_copy i -> "copy" ^ " " ^ string_of_int i
| Coq_justification_andi (i1, i2) -> "andi" ^ " " ^ (string_of_int i1) ^ "," ^ (string_of_int i2)
| Coq_justification_ande1 i -> "ande1" ^ " " ^ string_of_int i
| Coq_justification_ande2 i -> "ande2" ^ " " ^ string_of_int i
| Coq_justification_ori1 i -> "ori1" ^ " " ^ string_of_int i
| Coq_justification_ori2 i -> "ori2" ^ " " ^ string_of_int i
| Coq_justification_impe (i1, i2) -> "impe" ^ " " ^ (string_of_int i1) ^ "," ^ (string_of_int i2)
| Coq_justification_nege (i1, i2) -> "nege" ^ " " ^ (string_of_int i1) ^ "," ^ (string_of_int i2)
| Coq_justification_conte i -> "conte" ^ " " ^ string_of_int i
| Coq_justification_negnegi i -> "negnegi" ^ " " ^ string_of_int i
| Coq_justification_negnege i -> "negnege" ^ " " ^ string_of_int i
| Coq_justification_mt (i1, i2) -> "mt" ^ " " ^ (string_of_int i1) ^ "," ^ (string_of_int i2)
| Coq_justification_impi (i1, i2) -> "impi" ^ " " ^ (string_of_int i1) ^ "-" ^ (string_of_int i2)
| Coq_justification_negi (i1, i2) -> "negi" ^ " " ^ (string_of_int i1) ^ "-" ^ (string_of_int i2)
| Coq_justification_ore (i1, i2, i3, i4, i5) -> "ore" ^ " " ^ (string_of_int i1) ^ "," ^ (string_of_int i2) ^ "-" ^ (string_of_int i3) ^ "," ^ (string_of_int i4) ^ "-" ^ (string_of_int i5)
| Coq_justification_pbc (i1, i2) -> "pbc" ^ " " ^ (string_of_int i1) ^ "-" ^ (string_of_int i2)

let string_of_reason = function
| Coq_reason_assumption -> "assumption"
| Coq_reason_justification j -> string_of_justification j

let string_of_derivation = function
| Coq_derivation_deriv (i, p, r) -> (string_of_int i) ^ " " ^ (string_of_prop p) ^ " " ^ (string_of_reason r)

let rec string_of_entry = function
| Coq_entry_derivation d -> string_of_derivation d
| Coq_entry_box (Coq_proof_entries el) -> "[" ^ "\n" ^ String.concat "\n" (List.map string_of_entry el) ^ "\n" ^ "]"
| Coq_entry_invalid -> ""

let rec string_of_claim = function
| Coq_claim_judgment_proof (Coq_judgment_follows (pl, p), Coq_proof_entries el) ->
  String.concat ", " (List.map string_of_prop pl) ^ " |- " ^ (string_of_prop p) ^ "\n" ^
  String.concat "\n" (List.map string_of_entry el)

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
