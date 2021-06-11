open HolKernel boolLib Parse bossLib pairTheory optionTheory stringTheory relationTheory listTheory rich_listTheory finite_mapTheory pred_setTheory ottTheory ottLib fitchTheory;

val _ = new_theory "fitchMeta";

(* key semantic definitions *)

Definition prop_sem:
 (prop_sem (prop_p x) a = a x) /\
 (prop_sem (prop_neg p) a = ~(prop_sem p a)) /\
 (prop_sem (prop_and p1 p2) a = ((prop_sem p1 a) /\ (prop_sem p2 a))) /\
 (prop_sem (prop_or p1 p2) a = ((prop_sem p1 a) \/ (prop_sem p2 a))) /\
 (prop_sem (prop_imp p1 p2) a = ((prop_sem p1 a) ==> (prop_sem p2 a))) /\
 (prop_sem prop_cont a = F)
End

Definition premises_admitted:
 premises_admitted pl a =
  (!p. MEM p pl ==> prop_sem p a)
End

Definition map_line_admitted:
 map_line_admitted (G:G) a =
  (!l p. FLOOKUP G (INL l) = SOME (INL p) ==> prop_sem p a)
End

Definition map_box_admitted:
 map_box_admitted (G:G) a =
  (!l1 l2 p1 p2. FLOOKUP G (INR (l1, l2)) = SOME (INR (p1, p2)) ==>
  (prop_sem p1 a ==> prop_sem p2 a))
End

(* useful induction principle *)

Theorem valid_proof_ind:
 !P. ((!G pl. P G pl [])
 /\
 (!G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) /\
 valid_proof (FUPDATE G (INL l, INL p)) pl pr /\
 P (FUPDATE G (INL l, INL p)) pl pr ==>
 P G pl (((entry_derivation (derivation_deriv l p (reason_justification j))) :: pr)))
 /\
 (!G pl l p pr pr' l' p' r.
 LAST_DEFAULT (entry_derivation (derivation_deriv l p reason_assumption) :: pr) entry_invalid =
   entry_derivation (derivation_deriv l' p' r) /\
  valid_proof (FUPDATE G (INL l, INL p)) pl pr /\
  P (FUPDATE G (INL l, INL p)) pl pr /\
  valid_proof (FUPDATE G (INR (l,l'),INR (p,p'))) pl pr' /\
  P (FUPDATE G (INR (l,l'),INR (p,p'))) pl pr' ==>
  P G pl (entry_box ((entry_derivation (derivation_deriv l p reason_assumption) :: pr)) :: pr'))) ==>
 (!(G:G) pl pr. valid_proof G pl pr ==> P G pl pr)
Proof
 GEN_TAC >> STRIP_TAC >>
 `((!c. valid_claim c ==> (\_. T) c) /\
  (!G pl pr. valid_proof G pl pr ==> (\G0 pl0 pr0. P G0 pl0 pr0 /\ valid_proof G0 pl0 pr0) G pl pr) /\
  (!G pl d. valid_derivation G pl d ==> valid_derivation G pl d))` suffices_by METIS_TAC [] >>
 MATCH_MP_TAC valid_claim_ind >> RW_TAC list_ss [valid_claim_rules]
QED

(* soundness of line rules *)

Theorem soundness_premise:
 !G pl p a l. premises_admitted pl a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise)) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [premises_admitted, valid_claim_cases]
QED

Theorem soundness_lem:
 !G pl p a l. valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem)) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem]
QED

Theorem soundness_andi:
 !G pl p a l l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_andi l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_copy:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_copy l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_ande1:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_ande2:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande2 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_ori1:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_ori2:
 !G pl p a l l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori2 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_impe:
 !G pl p a l l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impe l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_nege:
 !G pl p a l l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_nege l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_conte:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_conte l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_negnegi:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnegi l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_negnege:
 !G pl p a l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnege l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_mt:
 !G pl p a l l1 l2. map_line_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_mt l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_line_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_impi:
 !G pl p a l l1 l2. map_box_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impi l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_box_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC []
QED

Theorem soundness_negi:
 !G pl p a l l1 l2. map_box_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_negi l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_box_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >>
 Cases_on `prop` >> METIS_TAC [prop_sem]
QED

Theorem soundness_pbc:
 !G pl p a l l1 l2. map_box_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_pbc l1 l2))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_box_admitted, valid_claim_cases] >>
 FULL_SIMP_TAC list_ss [prop_sem, FLOOKUP_DEF] >> METIS_TAC [prop_sem]
QED

Theorem soundness_ore:
 !G pl p a l l1 l2 l3 l4 l5. map_line_admitted G a ==> map_box_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification (justification_ore l1 l2 l3 l4 l5))) ==>
  prop_sem p a
Proof
 RW_TAC list_ss [map_box_admitted, map_line_admitted, valid_claim_cases] >>
 `(prop_sem prop a) \/ (prop_sem prop' a)` by METIS_TAC [prop_sem, FLOOKUP_DEF] >>
 METIS_TAC [prop_sem, FLOOKUP_DEF]
QED

Theorem soundness_derivations:
 !G pl p a l j. premises_admitted pl a ==> map_line_admitted G a ==> map_box_admitted G a ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  prop_sem p a
Proof
 Cases_on `j` >| [
  PROVE_TAC [soundness_premise],
  PROVE_TAC [soundness_lem],
  PROVE_TAC [soundness_copy],
  PROVE_TAC [soundness_andi],
  PROVE_TAC [soundness_ande1],
  PROVE_TAC [soundness_ande2],
  PROVE_TAC [soundness_ori1],
  PROVE_TAC [soundness_ori2],
  PROVE_TAC [soundness_impe],
  PROVE_TAC [soundness_nege],
  PROVE_TAC [soundness_conte],
  PROVE_TAC [soundness_negnegi],
  PROVE_TAC [soundness_negnege],
  PROVE_TAC [soundness_mt],
  PROVE_TAC [soundness_impi],
  PROVE_TAC [soundness_negi],
  PROVE_TAC [soundness_ore],
  PROVE_TAC [soundness_pbc]
 ]
QED

(* soundness of system  *)

Theorem justification_valid_in:
 !G pl pr. valid_proof G pl pr ==>
  !l p r. MEM (entry_derivation (derivation_deriv l p r)) pr ==> r <> reason_assumption
Proof
 HO_MATCH_MP_TAC valid_proof_ind >> RW_TAC list_ss []
QED

Definition soundness_prop:
 soundness_prop (G:G) pl pr =
  !a. premises_admitted pl a ==>
  !l j. map_line_admitted G a ==> map_box_admitted G a ==>
  !p. MEM (entry_derivation (derivation_deriv l p (reason_justification j))) pr ==>
  prop_sem p a
End

Theorem soundness_empty:
 !G pl. soundness_prop G pl []
Proof
 RW_TAC list_ss [soundness_prop]
QED

Theorem soundness_derivation:
 !G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop G pl (entry_derivation (derivation_deriv l p (reason_justification j)) :: pr)
Proof
 RW_TAC list_ss [soundness_prop] >- METIS_TAC [soundness_derivations] >>
 SUBGOAL_THEN ``map_line_admitted (FUPDATE (G:G) (INL l, INL p)) a`` ASSUME_TAC >> RW_TAC list_ss [map_line_admitted]
 >- ( Cases_on `l = l''` >> RW_TAC list_ss [map_line_admitted] >>
      FULL_SIMP_TAC list_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE]
      >- METIS_TAC [soundness_derivations]
      >- METIS_TAC [map_line_admitted, FLOOKUP_DEF] )
 >- ( SUBGOAL_THEN ``map_box_admitted (FUPDATE (G:G) (INL l, INL p)) a`` ASSUME_TAC
     >- ( FULL_SIMP_TAC list_ss [map_box_admitted, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, FLOOKUP_DEF] >>
          METIS_TAC [map_box_admitted] )
     >- METIS_TAC [] )
QED

Theorem soundness_box:
 !G pl l1 l2 p1 p2 pr1 pr2 r.
   LAST_DEFAULT (entry_derivation (derivation_deriv l1 p1 reason_assumption) :: pr1) entry_invalid = entry_derivation (derivation_deriv l2 p2 r) ==>
  valid_proof (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
  soundness_prop (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
  valid_proof (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
  soundness_prop (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
  soundness_prop G pl ((entry_box (entry_derivation (derivation_deriv l1 p1 reason_assumption) :: pr1)) :: pr2)
Proof
rw [soundness_prop] >>
`map_line_admitted (G |+ (INR (l1,l2),INR (p1,p2))) a /\ map_box_admitted (G |+ (INR (l1,l2),INR (p1,p2))) a` suffices_by METIS_TAC [] >>
rw [] >-
 (fs [map_line_admitted] >>
  rw [FLOOKUP_DEF] >>
  `FLOOKUP G (INL l') = SOME (INL p')` suffices_by METIS_TAC [] >>
  fs [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE]) >>
once_rewrite_tac [map_box_admitted] >> rw [] >>
Cases_on `pr1` >> rw [] >-
 (fs [LAST_DEFAULT, LAST_DEF] >> rw [] >>
  Cases_on `(l1,l1) = (l1',l2')` >> rw [] >-
  (fs [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE] >> rw []) >>
  fs [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] >>
  METIS_TAC [FLOOKUP_DEF,map_box_admitted]) >>
`LAST_DEFAULT (h::t) entry_invalid = entry_derivation (derivation_deriv l2 p2 r)` by fs [LAST_DEFAULT, LAST_DEF] >>
`MEM (entry_derivation (derivation_deriv l2 p2 r)) (h::t)` by METIS_TAC [LAST_DEFAULT, MEM_LAST] >>
`r <> reason_assumption` by METIS_TAC [justification_valid_in] >>
Cases_on `r` >- rw [] >>
Cases_on `(l1',l2') <> (l1,l2)` >-
 (fs [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] >>
  rw [] >> fs [] >> METIS_TAC [FLOOKUP_DEF,map_box_admitted]) >>
FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] >> rw [] >>
`map_line_admitted (G |+ (INL l1,INL p1)) a /\ map_box_admitted (G |+ (INL l1,INL p1)) a` suffices_by METIS_TAC [map_box_admitted] >>
CONJ_TAC >-
 (RW_TAC bool_ss [map_line_admitted] >>
  Cases_on `l1 = l'` >> FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] >>
  `FLOOKUP G (INL l') = SOME (INL p')` suffices_by METIS_TAC [map_line_admitted] >>
  RW_TAC bool_ss [FLOOKUP_DEF]) >>
RW_TAC bool_ss [map_box_admitted] >>
FULL_SIMP_TAC std_ss [FLOOKUP_DEF, FAPPLY_FUPDATE_THM, FDOM_FUPDATE, IN_INSERT] >>
`FLOOKUP G (INR (l1',l2')) = SOME (INR (p1',p2'))` suffices_by METIS_TAC [map_box_admitted] >>
RW_TAC bool_ss [FLOOKUP_DEF]
QED

Theorem soundness_proof:
 !G pl pr. valid_proof G pl pr ==> soundness_prop G pl pr
Proof
 HO_MATCH_MP_TAC valid_proof_ind >> rw [] >| [
  PROVE_TAC [soundness_empty],
  PROVE_TAC [soundness_derivation],
  PROVE_TAC [soundness_box]
 ]
QED

Theorem soundness_claim:
 !p pl pr a. premises_admitted pl a ==>
 valid_claim (claim_judgment_proof (judgment_follows pl p) pr) ==>
 prop_sem p a
Proof
 SUBGOAL_THEN ``(!a0. valid_claim a0 <=>
  ?proplist prop proof l j. a0 = claim_judgment_proof (judgment_follows proplist prop) proof /\
  clause_name "vc_claim" /\
  LAST_DEFAULT proof entry_invalid =
   entry_derivation (derivation_deriv l prop (reason_justification j)) /\
  valid_proof FEMPTY proplist proof)`` ASSUME_TAC >- METIS_TAC [valid_claim_cases] >>
 RW_TAC list_ss [] >>
 SUBGOAL_THEN ``map_line_admitted (FEMPTY:num + num # num |-> prop + prop # prop) a`` ASSUME_TAC >-
 RW_TAC list_ss [map_line_admitted, FLOOKUP_DEF, FDOM_FEMPTY] >>
 SUBGOAL_THEN ``map_box_admitted (FEMPTY:num + num # num |-> prop + prop # prop) a`` ASSUME_TAC >-
 RW_TAC list_ss [map_box_admitted, FLOOKUP_DEF, FDOM_FEMPTY] >>

 Cases_on `pr` >-
 (FULL_SIMP_TAC list_ss [LAST_DEFAULT] >>
  `entry_invalid <> entry_derivation (derivation_deriv l p (reason_justification j))` by RW_TAC list_ss [fetch "fitch" "entry_distinct"] >>
 RW_TAC list_ss []) >>
 
 RW_TAC list_ss [] >> FULL_SIMP_TAC list_ss [LAST_DEFAULT] >>
 SUBGOAL_THEN ``MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (h::t)`` ASSUME_TAC >-
 (RW_TAC bool_ss [] >> METIS_TAC [MEM_LAST]) >>
 METIS_TAC [soundness_proof,soundness_prop]
QED

val _ = export_theory ();
