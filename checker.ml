open Camlp4.PreCast
open Fitch
open FitchString
open Util

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
    j = judgment; p = proof -> Coq_claim_judgment_proof (j, p)
  ]];
  judgment:
  [[
    ls = LIST0 prop SEP ","; "|-"; p = prop -> Coq_judgment_follows (ls, p)
  ]];
  prop: 
  [[ 
    "cont" -> Coq_prop_cont
  | "~"; p = prop -> Coq_prop_neg p
  | p = LIDENT -> Coq_prop_p (char_list_of_string p)
  | p1 = prop; "/\\"; p2 = prop -> Coq_prop_and (p1, p2)
  | p1 = prop; "\\/"; p2 = prop -> Coq_prop_or (p1, p2)
  | p1 = prop; "->"; p2 = prop -> Coq_prop_imp (p1, p2)
  | "("; p = prop; ")" -> p
  ]]; 
  proof:
  [[
    ls = LIST0 entry -> Coq_proof_entries ls
  ]];    
  entry:
  [[
    d = derivation -> Coq_entry_derivation d
  | "["; p = proof; "]" -> Coq_entry_box p 
  ]];
  derivation:
  [[
    i = INT; p = prop; r = reason -> Coq_derivation_deriv (int_of_string i, p, r)
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
  | "copy"; i = INT -> Coq_justification_copy (int_of_string i)
  | "andi"; i1 = INT; ","; i2 = INT -> Coq_justification_andi (int_of_string i1, int_of_string i2)
  | "ande1"; i = INT -> Coq_justification_ande1 (int_of_string i)
  | "ande2"; i = INT -> Coq_justification_ande2 (int_of_string i)
  | "ori1"; i = INT -> Coq_justification_ori1 (int_of_string i)
  | "ori2"; i = INT -> Coq_justification_ori2 (int_of_string i)
  | "impe"; i1 = INT; ","; i2 = INT -> Coq_justification_impe (int_of_string i1, int_of_string i2)
  | "nege"; i1 = INT; ","; i2 = INT -> Coq_justification_nege (int_of_string i1, int_of_string i2)
  | "conte"; i = INT -> Coq_justification_conte (int_of_string i)
  | "negnegi"; i = INT -> Coq_justification_negnegi (int_of_string i)
  | "negnege"; i = INT -> Coq_justification_negnege (int_of_string i)
  | "mt"; i1 = INT; ","; i2 = INT -> Coq_justification_mt (int_of_string i1, int_of_string i2)
  | "impi"; i1 = INT; "-"; i2 = INT -> Coq_justification_impi (int_of_string i1, int_of_string i2)
  | "negi"; i1 = INT; "-"; i2 = INT -> Coq_justification_negi (int_of_string i1, int_of_string i2)
  | "ore"; i1 = INT; ","; i2 = INT; "-"; i3 = INT; ","; i4 = INT; "-"; i5 = INT -> Coq_justification_ore (int_of_string i1, int_of_string i2, int_of_string i3, int_of_string i4, int_of_string i5)
  | "pbc"; i1 = INT; "-"; i2 = INT -> Coq_justification_pbc (int_of_string i1, int_of_string i2)
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
