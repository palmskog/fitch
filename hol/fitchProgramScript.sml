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

Definition valid_derivation_deriv_ori2:
 valid_derivation_deriv_ori2 G l p =
   case p of
   | prop_or p1 p2 => 
     (case FLOOKUP G (INL l) of
       | SOME (INL p') => p2 = p'	 
       | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_ori2_sound:
 !G pl l l' p. valid_derivation_deriv_ori2 G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_ori2 l)))
Proof
 rw [valid_derivation_deriv_ori2] >>
 Cases_on `p` >> rw [valid_claim_cases] >>
 Cases_on `FLOOKUP G (INL l)` >> rw [clause_name_def] >>
 Cases_on `x` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_impe:
 valid_derivation_deriv_impe G l1 l2 p =
   case FLOOKUP G (INL l1) of
   | SOME (INL p1) => 
     (case FLOOKUP G (INL l2) of
      | SOME (INL (prop_imp p2 p3)) => p1 = p2 /\ p = p3
      | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_impe_sound:
 !G pl l1 l2 l' p. valid_derivation_deriv_impe G l1 l2 p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_impe l1 l2)))
Proof
 rw [valid_derivation_deriv_impe] >>
 Cases_on `FLOOKUP G (INL l1)` >> rw [valid_claim_cases] >>
 Cases_on `x` >> rw [] >>
 Cases_on `FLOOKUP G (INL l2)` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `x''` >> rw [] >>
 rw [clause_name_def] >> METIS_TAC []
QED

Definition valid_derivation_deriv_nege:
  valid_derivation_deriv_nege G l1 l2 p =
     case p of 
     | prop_cont => 
       (case FLOOKUP G (INL l1) of
	| SOME (INL p1) =>
	  (case FLOOKUP G (INL l2) of
	   | SOME (INL (prop_neg p2)) => p1 = p2
	   | _ => F)
	| _ => F)
     | _ => F
End

Theorem valid_derivation_deriv_nege_sound:
 !G pl l1 l2 l' p. valid_derivation_deriv_nege G l1 l2 p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_nege l1 l2)))
Proof
 rw [valid_derivation_deriv_nege] >>
 Cases_on `p` >> rw [valid_claim_cases,clause_name_def] >>
 Cases_on `FLOOKUP G (INL l1)` >> rw [] >>
 Cases_on `x` >> rw [] >>
 Cases_on `FLOOKUP G (INL l2)` >> rw [] >>
 Cases_on `x` >> rw [] >>
 Cases_on `x''` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_conte:
 valid_derivation_deriv_conte G l =
   case FLOOKUP G (INL l) of
   | SOME (INL prop_cont)  => T     
   | _ => F
End

Theorem valid_derivation_deriv_conte_sound:
 !G pl l l' p. valid_derivation_deriv_conte G l <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_conte l)))
Proof
 rw [valid_derivation_deriv_conte] >>
 Cases_on `FLOOKUP G (INL l)` >> rw [valid_claim_cases,clause_name_def] >>
 Cases_on `x` >> rw [] >>
 Cases_on `x'` >> rw []
QED

Definition valid_derivation_deriv_negnegi:
  valid_derivation_deriv_nenegi G l p =
    case p of
    | prop_neg (prop_neg p1) => 
      (case FLOOKUP G (INL l) of
	| SOME (INL p2) => p1 = p2
	| _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_negnegi_sound:
 !G pl l l' p. valid_derivation_deriv_nenegi G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_negnegi l)))
Proof
 rw [valid_derivation_deriv_negnegi] >>
 Cases_on `p` >> rw [valid_claim_cases,clause_name_def] >>
 Cases_on `p'` >> rw [] >>
 Cases_on `FLOOKUP G (INL l)` >> rw [] >>
 Cases_on `x` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_negnege:
 valid_derivation_deriv_negnege G l p =
  case FLOOKUP G (INL l) of
  | SOME (INL (prop_neg (prop_neg p'))) => p' = p
  | _ => F
End

Theorem valid_derivation_deriv_negnege_sound:
 !G pl l l' p. valid_derivation_deriv_negnege G l p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_negnege l)))
Proof
 rw [valid_derivation_deriv_negnege] >>
 Cases_on `FLOOKUP G (INL l)` >> rw [valid_claim_cases,clause_name_def] >>
 Cases_on `x` >> rw [] >> Cases_on `x'` >> rw [] >>
 Cases_on `p'` >> rw []
QED

Definition valid_derivation_deriv_mt:
  valid_derivation_deriv_mt G l1 l2 p =
    case p of
    | prop_neg p' =>
      (case FLOOKUP G (INL l1) of
       | SOME (INL (prop_imp p1 p2)) =>
	 if p' = p1 then
	     (case FLOOKUP G (INL l2) of
	     | SOME (INL (prop_neg p3)) => p2 = p3
	     | _ => F)
	 else F
       | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_mt_sound:
 !G pl l1 l2 l' p. valid_derivation_deriv_mt G l1 l2 p <=>
    valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_mt l1 l2)))
Proof
 rw [valid_derivation_deriv_mt] >>
 Cases_on `p` >> rw [valid_claim_cases,clause_name_def] >>
 Cases_on `FLOOKUP G (INL l1)` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `x'` >> rw [] >>
 Cases_on `FLOOKUP G (INL l2)` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `x'` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_impi:
  valid_derivation_deriv_impi G l1 l2 p =
    case p of
    | prop_imp p1 p2 => 
      (case FLOOKUP G (INR (l1, l2)) of
      | SOME (INR (p3, p4)) => p1 = p3 /\ p2 = p4
      | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_impi_sound:
  !G pl l1 l2 l' p. valid_derivation_deriv_impi G l1 l2 p <=>
    valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_impi l1 l2)))
Proof
 rw [valid_derivation_deriv_impi] >>
 Cases_on `p` >> rw[valid_claim_cases,clause_name_def] >>
 Cases_on `FLOOKUP G (INR (l1,l2))` >> rw [] >>
 Cases_on `x` >> rw [] >>
 Cases_on `y` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_negi:
 valid_derivation_deriv_negi G l1 l2 p =
   case p of
   | prop_neg p1 => 
     (case FLOOKUP G (INR (l1,l2)) of
      | SOME (INR (p2,prop_cont)) => p1 = p2	
      | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_negi_sound:
  !G pl l1 l2 l' p. valid_derivation_deriv_negi G l1 l2 p <=>
  valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_negi l1 l2)))
Proof
 rw [valid_derivation_deriv_negi] >>
 Cases_on `p` >> rw[valid_claim_cases,clause_name_def] >>
 Cases_on `FLOOKUP G (INR (l1,l2))` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `y` >> rw [] >>
 Cases_on `r` >> rw [] >> METIS_TAC []
QED

Definition valid_derivation_deriv_ore:
  valid_derivation_deriv_ore G l1 l2 l3 l4 l5 p =
    case FLOOKUP G (INL l1) of
    | SOME (INL (prop_or p1 p2)) => 
      (case FLOOKUP G (INR (l2, l3)) of
       | SOME (INR (p3, p4)) => 
	 if p1 = p3 /\ p = p4 then
	     (case FLOOKUP G (INR (l4,l5)) of
              | SOME (INR (p5, p6)) =>
		p2 = p5 /\ p = p6
	      | _ => F)
	 else F	     
       | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_ore_sound:
!G pl l1 l2 l3 l4 l5 l' p. valid_derivation_deriv_ore G l1 l2 l3 l4 l5 p <=>
    valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_ore l1 l2 l3 l4 l5)))
Proof
 rw [valid_derivation_deriv_ore] >>
 Cases_on `FLOOKUP G (INL l1)` >> rw[valid_claim_cases,clause_name_def] >>
 Cases_on `x` >> rw [] >> Cases_on `x'` >> rw [] >>
 Cases_on `FLOOKUP G (INR (l2,l3))` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `y` >> rw [] >>
 Cases_on `FLOOKUP G (INR (l4,l5))` >> rw [] >>
 Cases_on `x` >> rw [] >> Cases_on `y` >> rw [] >>
 METIS_TAC []
QED

Definition valid_derivation_deriv_pbc:
  valid_derivation_deriv_pbc G l1 l2 p =
   case FLOOKUP G (INR (l1,l2)) of
   | SOME (INR (prop_neg p', prop_cont)) =>
     p' = p
   | _ => F
End

Theorem valid_derivation_deriv_pbc_sound:
  !G pl l1 l2 l' p. valid_derivation_deriv_pbc G l1 l2 p <=>
    valid_derivation G pl (derivation_deriv l' p (reason_justification (justification_pbc l1 l2)))
Proof
 rw [valid_derivation_deriv_pbc] >>
 Cases_on `FLOOKUP G (INR (l1,l2))` >> rw[valid_claim_cases,clause_name_def] >>
 Cases_on `x` >> rw [] >> Cases_on `y` >> rw [] >>
 Cases_on `q` >> rw [] >> Cases_on `r` >> rw []
QED

Definition valid_derivation_deriv_dec:
  valid_derivation_deriv_dec G pl p r =
    case r of
    | reason_assumption => F
    | reason_justification j => 
      case j of
      | justification_premise =>  valid_derivation_deriv_premise pl p
      | justification_lem => valid_derivation_deriv_lem p
      | justification_copy l => valid_derivation_deriv_copy G l p
      | justification_andi l1 l2  => valid_derivation_deriv_andi G l1 l2 p
      | justification_ande1 l => valid_derivation_deriv_ande1 G l p
      | justification_ande2 l => valid_derivation_deriv_ande2 G l p
      | justification_ori1 l => valid_derivation_deriv_ori1 G l p
      | justification_ori2 l => valid_derivation_deriv_ori2 G l p
      | justification_impe l1 l2 => valid_derivation_deriv_impe G l1 l2 p
      | justification_nege l1 l2 => valid_derivation_deriv_nege G l1 l2 p
      | justification_conte l => valid_derivation_deriv_conte G l
      | justification_negnegi l => valid_derivation_deriv_nenegi G l p
      | justification_negnege l => valid_derivation_deriv_negnege G l p
      | justification_mt l1 l2 => valid_derivation_deriv_mt G l1 l2 p
      | justification_impi l1 l2 => valid_derivation_deriv_impi G l1 l2 p
      | justification_negi l1 l2 => valid_derivation_deriv_negi G l1 l2 p
      | justification_ore l1 l2 l3 l4 l5 => valid_derivation_deriv_ore G l1 l2 l3 l4 l5 p
      | justification_pbc l1 l2 => valid_derivation_deriv_pbc G l1 l2 p
End

Theorem valid_derivation_deriv_dec_sound:
  !G pl l p r. valid_derivation_deriv_dec G pl p r <=>
     valid_derivation G pl (derivation_deriv l p r)
Proof
  rw [valid_derivation_deriv_dec] >>
  Cases_on `r` >> rw [] >- rw [valid_claim_cases] >>  
  Cases_on `j` >> rw [] >| [
    PROVE_TAC [valid_derivation_deriv_premise_sound],
    PROVE_TAC [valid_derivation_deriv_lem_sound],
    PROVE_TAC [valid_derivation_deriv_copy_sound],
    PROVE_TAC [valid_derivation_deriv_andi_sound],
    PROVE_TAC [valid_derivation_deriv_ande1_sound],
    PROVE_TAC [valid_derivation_deriv_ande2_sound],
    PROVE_TAC [valid_derivation_deriv_ori1_sound],
    PROVE_TAC [valid_derivation_deriv_ori2_sound],
    PROVE_TAC [valid_derivation_deriv_impe_sound],
    PROVE_TAC [valid_derivation_deriv_nege_sound],
    PROVE_TAC [valid_derivation_deriv_conte_sound],
    PROVE_TAC [valid_derivation_deriv_negnegi_sound],
    PROVE_TAC [valid_derivation_deriv_negnege_sound],
    PROVE_TAC [valid_derivation_deriv_mt_sound],
    PROVE_TAC [valid_derivation_deriv_impi_sound],
    PROVE_TAC [valid_derivation_deriv_negi_sound],
    PROVE_TAC [valid_derivation_deriv_ore_sound],
    PROVE_TAC [valid_derivation_deriv_pbc_sound]
  ]
QED

Inductive valid_entry:
(!G pl l p j. (valid_derivation G pl (derivation_deriv l p (reason_justification j))) ==>
 (valid_entry G pl (entry_derivation (derivation_deriv l p (reason_justification j)))))
/\
(!G pl pr l p. valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
 (valid_entry G pl (entry_box (proof_entries (entry_derivation (derivation_deriv l p reason_assumption) :: (proof_list_entry pr))))))
End

val _ = export_theory();
