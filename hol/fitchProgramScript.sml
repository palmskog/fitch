open HolKernel boolLib Parse bossLib;
open relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory;
open ottTheory ottLib fitchTheory;

val _ = new_theory "fitchProgram";

val valid_derivation_deriv_premise_def = Define
`valid_derivation_deriv_premise (G:G) pl (l:l) p =
  MEM p pl`;

val valid_derivation_deriv_premise_sound_thm = Q.store_thm("valid_derivation_deriv_premise_sound",
`!G pl l p. valid_derivation_deriv_premise G pl l p <=>
 valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise))`,
RW_TAC bool_ss [valid_derivation_deriv_premise_def] THEN
EQ_TAC THEN1
(`clause_name "vd_premise"` by RW_TAC bool_ss [clause_name_def] THEN
METIS_TAC [valid_claim_rules]) THEN
FULL_SIMP_TAC list_ss [valid_claim_cases] THEN RW_TAC list_ss []);

val valid_derivation_deriv_lem_def = Define
`valid_derivation_deriv_lem (G:G) (pl: prop list) (l:l) p =
  case p of
  | prop_or p1 (prop_neg p2) => p1 = p2
  | _ => F`;

val valid_derivation_deriv_lem_sound_thm = Q.store_thm("valid_derivation_deriv_lem_sound",
`!G pl l p. valid_derivation_deriv_lem G pl l p <=>
 valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem))`,
RW_TAC bool_ss [valid_derivation_deriv_lem_def] THEN
Cases_on `p` THEN RW_TAC bool_ss [valid_claim_cases] THEN
Cases_on `p0` THEN RW_TAC bool_ss [valid_claim_cases, clause_name_def] THEN
EQ_TAC THEN RW_TAC bool_ss []);

val _ = export_theory();
