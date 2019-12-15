open HolKernel boolLib Parse bossLib;
open relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory;
open ottTheory ottLib fitchTheory;

val _ = new_theory "fitchProgram";

Definition valid_derivation_deriv_premise:
 valid_derivation_deriv_premise pl p = MEM p pl
End

Theorem valid_derivation_deriv_premise_sound:
 !G pl l p. valid_derivation_deriv_premise pl p <=>
  valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_premise] >> EQ_TAC
 >- ( `clause_name "vd_premise"` by RW_TAC bool_ss [clause_name_def] >>
      METIS_TAC [valid_claim_rules] )
 >- ( FULL_SIMP_TAC list_ss [valid_claim_cases] >> RW_TAC list_ss [] )
QED

Definition valid_derivation_deriv_lem:
 valid_derivation_deriv_lem p =
  case p of
  | prop_or p1 (prop_neg p2) => p1 = p2
  | _ => F
End

Theorem valid_derivation_deriv_lem_sound:
 !G pl l p. valid_derivation_deriv_lem p <=>
  valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_lem] >>
 Cases_on `p` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `p0` >> RW_TAC bool_ss [valid_claim_cases, clause_name_def] >>
 EQ_TAC >> RW_TAC bool_ss []
QED

Definition valid_derivation_deriv_copy:
 valid_derivation_deriv_copy G l p =
  case FLOOKUP G (INL l) of
  | SOME (INL p')  => p = p'
  | _ => F
End

Theorem valid_derivation_deriv_copy_sound:
 !G pl l p l'. valid_derivation_deriv_copy G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_copy l)))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_copy] >>
 Cases_on `FLOOKUP G (INL l)` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `x` >> RW_TAC bool_ss [clause_name_def] >>
 EQ_TAC >> RW_TAC bool_ss []
QED

Definition valid_derivation_deriv_andi:
 valid_derivation_deriv_andi G l1 l2 p =
   case FLOOKUP G (INL l1) of
   | SOME (INL p1) =>
     (case FLOOKUP G (INL l2) of
     | SOME (INL p2) => p = prop_and p1 p2
     | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_andi_sound:
 !G pl l p l1 l2. valid_derivation_deriv_andi G l1 l2 p <=>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_andi l1 l2)))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_andi] >>
 Cases_on `FLOOKUP G (INL l1)` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `x` >> RW_TAC bool_ss [clause_name_def] >>
 Cases_on `FLOOKUP G (INL l2)` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `x` >> RW_TAC bool_ss [clause_name_def]
QED

Definition valid_derivation_deriv_ande1:
 valid_derivation_deriv_ande1 G l p =
   case FLOOKUP G (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p1
   | _ => F
End

Theorem valid_derivation_deriv_ande1_sound:
 !G pl l l' p. valid_derivation_deriv_ande1 G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_ande1 l)))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_ande1] >>
 Cases_on `FLOOKUP G (INL l)` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `x` >> RW_TAC bool_ss [clause_name_def] >>
 Cases_on `x'` >> RW_TAC bool_ss [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_ande2:
 valid_derivation_deriv_ande2 G l p =
   case FLOOKUP G (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p2
   | _ => F
End

Theorem valid_derivation_deriv_ande2_sound:
 !G pl l l' p. valid_derivation_deriv_ande2 G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_ande2 l)))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_ande2] >>
 Cases_on `FLOOKUP G (INL l)` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `x` >> RW_TAC bool_ss [clause_name_def] >>
 Cases_on `x'` >> RW_TAC bool_ss [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_ori1:
 valid_derivation_deriv_ori1 G l p =
  case p of
  | prop_or p1 p2 =>
    (case FLOOKUP G (INL l) of
     | SOME (INL p') => p1 = p'
     | _ => F)
  | _ => F
End

Theorem valid_derivation_deriv_ori1_sound:
 !G pl l l' p. valid_derivation_deriv_ori1 G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_ori1 l)))
Proof
 RW_TAC bool_ss [valid_derivation_deriv_ori1] >>
 Cases_on `p` >> RW_TAC bool_ss [valid_claim_cases] >>
 Cases_on `FLOOKUP G (INL l)` >> RW_TAC bool_ss [clause_name_def] >>
 Cases_on `x` >> RW_TAC bool_ss [] >> METIS_TAC []
QED

Inductive valid_entry:
(!G pl l p j. (valid_derivation G pl (derivation_deriv l p (reason_justification j))) ==>
 (valid_entry G pl (entry_derivation (derivation_deriv l p (reason_justification j)))))
/\
(!G pl pr l p. valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
 (valid_entry G pl (entry_box (proof_entries (entry_derivation (derivation_deriv l p reason_assumption) :: (proof_list_entry pr))))))
End

val _ = export_theory();
