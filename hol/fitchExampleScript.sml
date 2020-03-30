open HolKernel boolLib Parse bossLib
 relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory
 ottTheory ottLib fitchTheory;

val _ = new_theory "fitchExample";

Definition example_premises:
  example_premises = [prop_p "p"; prop_p "q"]
End

Definition example_proof:
 example_proof = 
  [entry_derivation (derivation_deriv 1 (prop_p "p") (reason_justification justification_premise));
  entry_derivation (derivation_deriv 2 (prop_p "q") (reason_justification justification_premise));
  entry_derivation (derivation_deriv 3 (prop_and (prop_p "p") (prop_p "q")) (reason_justification (justification_andi 1 2)))]
End

Definition example_claim:
 example_claim = 
  claim_judgment_proof
   (judgment_follows example_premises (prop_and (prop_p "p") (prop_p "q"))) example_proof
End

Theorem example_valid_claim:
  valid_claim example_claim
Proof
 rw [example_claim,example_premises,example_proof] >>
 once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def,LAST_DEFAULT] >>
 once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def] >-
 (once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def]) >>
 once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def] >-
 (once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def]) >>
 once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def] >-
 (once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def] >-
 fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM, FDOM_FUPDATE] >>
 fs [FLOOKUP_DEF,FAPPLY_FUPDATE_THM, FDOM_FUPDATE]) >>
 once_rewrite_tac [valid_claim_cases] >> rw [clause_name_def]
QED

val _ = export_theory();
