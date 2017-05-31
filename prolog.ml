open Camlp4.PreCast
open Util
open Fitch
open FitchProgramMap
open FitchPI

module Gram = MakeGram(Lexer)

let claim = Gram.Entry.mk "claim"
let judgment = Gram.Entry.mk "judgment"
let prop = Gram.Entry.mk "prop"
let proof = Gram.Entry.mk "proof"
let entry = Gram.Entry.mk "entry"
let derivation = Gram.Entry.mk "derivation"
let reason = Gram.Entry.mk "reason"
let justification = Gram.Entry.mk "justification"

  EXTEND Gram
  claim:
  [[
    j = judgment; "["; p = proof; "]"; "." -> Coq_claim_judgment_proof (j, p)
  ]];
  judgment:
  [[
    "["; ls = LIST0 prop SEP ","; "]"; "."; p = prop; "." -> Coq_judgment_follows (ls, p)
  ]];
  prop: 
  [[ 
    "cont" -> Coq_prop_cont
  | "neg"; "("; p = prop; ")" -> Coq_prop_neg p
  | p = LIDENT -> Coq_prop_p (char_list_of_string p)
  | "and"; "("; p1 = prop; ","; p2 = prop; ")" -> Coq_prop_and (p1, p2)
  | "or"; "("; p1 = prop; ","; p2 = prop; ")" -> Coq_prop_or (p1, p2)
  | "imp"; "("; p1 = prop; ","; p2 = prop; ")" -> Coq_prop_imp (p1, p2)
  ]];
  proof:
  [[
    ls = LIST0 entry SEP "," -> Coq_proof_entries ls
  ]];    
  entry:
  [[
    "["; d = derivation; "]" -> Coq_entry_derivation d
  | "["; p = proof; "]" -> Coq_entry_box p 
  ]];
  derivation:
  [[
    i = INT; ","; p = prop; ","; r = reason -> Coq_derivation_deriv (int_of_string i, p, r)
  ]];
  reason:
  [[
    "assumption" -> Coq_reason_assumption
  | j = justification -> Coq_reason_justification j
  ]];
  justification:
  [[
    "premise" -> Coq_justification_premise
  | "lem" -> Coq_justification_lem
  | "copy"; "("; i = INT; ")" -> Coq_justification_copy (int_of_string i)
  | "andint"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_andi (int_of_string i1, int_of_string i2)
  | "andel1"; "("; i = INT; ")" -> Coq_justification_ande1 (int_of_string i)
  | "andel2"; "("; i = INT; ")" -> Coq_justification_ande2 (int_of_string i)
  | "orint1"; "("; i = INT; ")" -> Coq_justification_ori1 (int_of_string i)
  | "orint2"; "("; i = INT; ")" -> Coq_justification_ori2 (int_of_string i)
  | "impel"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_impe (int_of_string i1, int_of_string i2)
  | "negel"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_nege (int_of_string i1, int_of_string i2)
  | "contel"; "("; i = INT; ")" -> Coq_justification_conte (int_of_string i)
  | "negnegint"; "("; i = INT; ")" -> Coq_justification_negnegi (int_of_string i)
  | "negnegel"; "("; i = INT; ")" -> Coq_justification_negnege (int_of_string i)
  | "mt"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_mt (int_of_string i1, int_of_string i2)
  | "impint"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_impi (int_of_string i1, int_of_string i2)
  | "negint"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_negi (int_of_string i1, int_of_string i2)
  | "orel"; "("; i1 = INT; ","; i2 = INT; ","; i3 = INT; ","; i4 = INT; ","; i5 = INT; ")" -> Coq_justification_ore (int_of_string i1, int_of_string i2, int_of_string i3, int_of_string i4, int_of_string i5)
  | "pbc"; "("; i1 = INT; ","; i2 = INT; ")" -> Coq_justification_pbc (int_of_string i1, int_of_string i2)
  ]];
  END
;;

try 
  let f = open_in Sys.argv.(1) in
  let fs = Stream.of_channel f in
  let c = (Gram.parse claim Loc.ghost fs) in
  Printf.printf "%b\n" (valid_claim_dec c);
  (*Printf.printf "%s" (texize_claim c);*)
  close_in f
with Loc.Exc_located (_, x) -> raise x 
