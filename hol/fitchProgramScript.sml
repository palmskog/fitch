open HolKernel boolLib Parse bossLib;
open relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory;
open ottTheory ottLib fitchTheory;

val _ = new_theory "fitchProgram";

Definition valid_derivation_deriv_premise:
 valid_derivation_deriv_premise (G:G) pl (l:l) p = MEM p pl
End

Theorem valid_derivation_deriv_premise_sound:
 !G pl l p. valid_derivation_deriv_premise G pl l p <=>
 valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_premise] >> EQ_TAC
 >- ( `clause_name "vd_premise"` by RW_TAC bool_ss [clause_name_def] >>
      METIS_TAC [valid_claim_rules] )
 >- ( FULL_SIMP_TAC list_ss [valid_claim_cases] >> RW_TAC list_ss [] )
QED

Definition valid_derivation_deriv_lem:
 valid_derivation_deriv_lem (G:G) (pl: prop list) (l:l) p =
  case p of
  | prop_or p1 (prop_neg p2) => p1 = p2
  | _ => F
End

Theorem valid_derivation_deriv_lem_sound:
 !G pl l p. valid_derivation_deriv_lem G pl l p <=>
 valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_lem] >>
 Cases_on `p` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `p0` >> RW_TAC bool_ss [valid_claim_cases, clause_name_def] >>
 EQ_TAC >> RW_TAC bool_ss []
QED

val _ = export_theory();
