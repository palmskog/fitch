open HolKernel boolLib Parse bossLib pairTheory optionTheory stringTheory;
open relationTheory listTheory rich_listTheory finite_mapTheory;
open IndDefLib IndDefRules ottTheory ottLib fitchTheory;

val _ = new_theory "fitchMeta";

val prop_of_def = Define
`(prop_of (prop_p b) = b) /\
 (prop_of (prop_neg p) = ~(prop_of p)) /\
 (prop_of (prop_and p1 p2) = ((prop_of p1) /\ (prop_of p2))) /\
 (prop_of (prop_or p1 p2) = ((prop_of p1) \/ (prop_of p2))) /\
 (prop_of (prop_imp p1 p2) = ((prop_of p1) ==> (prop_of p2))) /\
 (prop_of prop_cont = F)`;

val premises_admitted_def = Define
`!pl. premises_admitted pl = (!p. MEM p pl ==> prop_of p)`;

val map_line_admitted_def = Define
`!G. map_line_admitted G = (!l p. FAPPLY G (INL l) = (INL p) ==> prop_of p)`;

val map_box_admitted_def = Define
`!G. map_box_admitted G = 
 (!l1 l2 p1 p2. FAPPLY G (INR (l1, l2)) = (INR (p1, p2)) ==>
 (prop_of p1 ==> prop_of p2))`;

(* soundness of line rules *)

val soundness_premise_thm = Q.store_thm("soundness_premise",
`!G pl p l. premises_admitted pl ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise)) ==>
 prop_of p`,
RW_TAC list_ss [premises_admitted_def, valid_claim_cases]);

val soundness_lem_thm = Q.store_thm("soundness_lem",
`!G pl p l. valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem)) ==>
 prop_of p`,
RW_TAC list_ss [valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def]);

val soundness_andi_thm = Q.store_thm("soundness_andi",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_andi l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [])

val soundness_copy_thm = Q.store_thm("soundness_copy",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_copy l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC []);

val soundness_ande1_thm = Q.store_thm("soundness_ande1",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_ande2_thm = Q.store_thm("soundness_ande2",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande2 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_ori1_thm = Q.store_thm("soundness_ori1",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC []);

val soundness_ori2_thm = Q.store_thm("soundness_ori2",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori2 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC []);

val soundness_impe_thm = Q.store_thm("soundness_impe",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impe l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_nege_thm = Q.store_thm("soundness_nege",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_nege l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_conte_thm = Q.store_thm("soundness_conte",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_conte l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_negnegi_thm = Q.store_thm("soundness_negnegi",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnegi l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC []);

val soundness_negnege_thm = Q.store_thm("soundness_negnege",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnege l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_mt_thm = Q.store_thm("soundness_mt",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_mt l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_line_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_impi_thm = Q.store_thm("soundness_impi",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impi l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_box_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC []);

val soundness_negi_thm = Q.store_thm("soundness_negi",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_negi l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_box_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN
Cases_on `prop` THEN METIS_TAC [prop_of_def]);

val soundness_pbc_thm = Q.store_thm("soundness_pbc",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_pbc l1 l2))) ==>
 prop_of p`,
RW_TAC list_ss [map_box_admitted_def, valid_claim_cases] THEN
FULL_SIMP_TAC list_ss [prop_of_def] THEN METIS_TAC [prop_of_def]);

val soundness_ore_thm = Q.store_thm("soundness_ore",
`!G pl p l l1 l2 l3 l4 l5. map_line_admitted G ==> map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_ore l1 l2 l3 l4 l5))) ==>
 prop_of p`,
RW_TAC list_ss [map_box_admitted_def, map_line_admitted_def, valid_claim_cases] THEN
SUBGOAL_THEN ``((prop_of prop) \/ (prop_of prop'))`` ASSUME_TAC THEN1 METIS_TAC [prop_of_def] THEN
METIS_TAC [prop_of_def]);

val soundness_derivations_thm = Q.store_thm("soundness_derivations",
`!G pl p l j. premises_admitted pl ==> map_line_admitted G ==> map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
 prop_of p`,
Cases_on `j` THENL [
 PROVE_TAC [soundness_premise_thm],
 PROVE_TAC [soundness_lem_thm],
 PROVE_TAC [soundness_copy_thm],
 PROVE_TAC [soundness_andi_thm],
 PROVE_TAC [soundness_ande1_thm],
 PROVE_TAC [soundness_ande2_thm],
 PROVE_TAC [soundness_ori1_thm],
 PROVE_TAC [soundness_ori2_thm],
 PROVE_TAC [soundness_impe_thm],
 PROVE_TAC [soundness_nege_thm],
 PROVE_TAC [soundness_conte_thm],
 PROVE_TAC [soundness_negnegi_thm],
 PROVE_TAC [soundness_negnege_thm],
 PROVE_TAC [soundness_mt_thm],
 PROVE_TAC [soundness_impi_thm],
 PROVE_TAC [soundness_negi_thm],
 PROVE_TAC [soundness_ore_thm],
 PROVE_TAC [soundness_pbc_thm]
]);

(* absence of assumptions from proofs *)

val justification_prop_def = Define
`!G pl pr. justification_prop G pl pr =
  !l p r. valid_proof G pl pr ==>
  MEM (entry_derivation (derivation_deriv l p r)) (proof_list_entry pr) ==>
  r <> reason_assumption`;

val justification_empty_thm = Q.store_thm("justification_empty",
`!G pl. justification_prop G pl (proof_entries [])`,
RW_TAC list_ss [justification_prop_def, proof_list_entry_def]);

val justification_derivation_thm = Q.store_thm("justification_derivation",
`!G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
  justification_prop (FUPDATE G (INL l, INL p)) pl pr ==>
  justification_prop G pl (proof_entries (entry_derivation
   (derivation_deriv l p (reason_justification j)) :: proof_list_entry pr))`,
RW_TAC list_ss [justification_prop_def, proof_list_entry_def]);

val justification_box_thm = Q.store_thm("justification_box",
`!G pl l1 l2 p1 p2 pr1 pr2 r. LAST (proof_list_entry (proof_entries (entry_derivation
  (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1))) =
  entry_derivation (derivation_deriv l2 p2 r) ==>
 valid_proof (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
 justification_prop (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
 valid_proof (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
 justification_prop (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
 justification_prop G pl (proof_entries (entry_box (proof_entries (entry_derivation
  (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1)) :: proof_list_entry pr2))`,
RW_TAC list_ss [justification_prop_def, proof_list_entry_def]);

(* soundness of system  *)

val soundness_prop_def = Define
`soundness_prop (G:G) pl pr =
 !l j p. premises_admitted pl ==>
  map_line_admitted G ==>
  map_box_admitted G ==>
  MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr) ==>
  prop_of p`;

val soundness_empty_thm = Q.store_thm("soundness_empty",
`!G pl. soundness_prop G pl (proof_entries [])`,
RW_TAC list_ss [soundness_prop_def, proof_list_entry_def]
);

val soundness_derivation_thm = Q.store_thm("soundness_derivation",
`!G pl l p j pr. valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
  valid_proof (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop (FUPDATE G (INL l, INL p)) pl pr ==>
  soundness_prop G pl (proof_entries (entry_derivation
   (derivation_deriv l p (reason_justification j)) :: proof_list_entry pr))`,
RW_TAC list_ss [soundness_prop_def,proof_list_entry_def] THEN1 METIS_TAC [soundness_derivations_thm] THEN
SUBGOAL_THEN ``map_line_admitted (FUPDATE (G:G) (INL l, INL p))`` ASSUME_TAC THEN RW_TAC list_ss [map_line_admitted_def] THEN1
( Cases_on `l = l''` THEN RW_TAC list_ss [map_line_admitted_def] THEN FULL_SIMP_TAC list_ss [FAPPLY_FUPDATE_THM]
  THENL [ METIS_TAC [soundness_derivations_thm], METIS_TAC [map_line_admitted_def] ] ) THEN
SUBGOAL_THEN ``map_box_admitted (FUPDATE (G:G) (INL l, INL p))`` ASSUME_TAC THEN1
( RW_TAC list_ss [map_box_admitted_def, FAPPLY_FUPDATE_THM] THEN METIS_TAC [map_box_admitted_def] ) THEN
METIS_TAC []);

val justification_valid_in_thm = Q.store_thm("justification_valid_in",
`!G pl pr l p r. valid_proof G pl pr ==>
 MEM (entry_derivation (derivation_deriv l p r)) (proof_list_entry pr) ==>
 r <> reason_assumption`,
cheat);

val soundness_box_thm = Q.store_thm("soundness_box",
`!G pl l1 l2 p1 p2 pr1 pr2 r. LAST (proof_list_entry (proof_entries (entry_derivation
  (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1))) =
  entry_derivation (derivation_deriv l2 p2 r) ==>
 valid_proof (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
 soundness_prop (FUPDATE G (INL l1, INL p1)) pl pr1 ==>
 valid_proof (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
 soundness_prop (FUPDATE G (INR (l1, l2), INR (p1, p2))) pl pr2 ==>
 soundness_prop G pl (proof_entries (entry_box (proof_entries (entry_derivation
  (derivation_deriv l1 p1 reason_assumption) :: proof_list_entry pr1)) :: proof_list_entry pr2))`,
cheat);

val soundness_proof_thm = Q.store_thm("soundness_proof",
`!G pl pr p l j. premises_admitted pl ==>
  map_line_admitted G ==>
  map_box_admitted G ==>
  valid_proof G pl pr ==>
  MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr) ==>
  prop_of p`,
cheat);

val FAPPLY_FEMPTY_not_eq_thm = Q.store_thm("FAPPLY_FEMPTY_not_eq",
`!a b. FAPPLY FEMPTY a <> b`,
cheat);

val soundness_claim_thm = Q.store_thm("soundness_claim",
`!p pl pr. premises_admitted pl ==>
 valid_claim (claim_judgment_proof (judgment_follows pl p) pr) ==>
 prop_of p`,
SUBGOAL_THEN ``(!a0.valid_claim a0 ⇔
          ?proplist prop proof l j.
              a0 = claim_judgment_proof (judgment_follows proplist prop) proof ∧
              clause_name "vc_claim" ∧
              LAST (proof_list_entry proof) =
              entry_derivation
                (derivation_deriv l prop (reason_justification j)) ∧
              valid_proof FEMPTY proplist proof)`` ASSUME_TAC THEN1 METIS_TAC [valid_claim_cases] THEN
RW_TAC list_ss [] THEN
SUBGOAL_THEN ``map_line_admitted (FEMPTY:num + num # num |-> prop + prop # prop)`` ASSUME_TAC THEN1
(RW_TAC list_ss [map_line_admitted_def] THEN FULL_SIMP_TAC list_ss [FAPPLY_FEMPTY_not_eq_thm]) THEN
SUBGOAL_THEN ``map_box_admitted (FEMPTY:num + num # num |-> prop + prop # prop)`` ASSUME_TAC THEN1
(RW_TAC list_ss [map_box_admitted_def] THEN FULL_SIMP_TAC list_ss [FAPPLY_FEMPTY_not_eq_thm]) THEN
SUBGOAL_THEN ``?e el. proof_list_entry pr = e::el`` ASSUME_TAC THEN1
(Cases_on `pr` THEN RW_TAC list_ss [] THEN Cases_on `l'` THEN RW_TAC list_ss [] THEN
 FULL_SIMP_TAC list_ss [proof_list_entry_def] THEN cheat) THEN
RW_TAC list_ss [] THEN
SUBGOAL_THEN ``MEM (entry_derivation (derivation_deriv l p (reason_justification j))) (proof_list_entry pr)`` ASSUME_TAC THEN1
(ASM_REWRITE_TAC [] THEN METIS_TAC [MEM_LAST]) THEN
METIS_TAC [soundness_proof_thm]);

val _ = export_theory();

(*
valid_proof_ind
     : forall P : G -> proplist -> proof -> Prop,
       (forall (G5 : G) (proplist5 : proplist),
        P G5 proplist5 (proof_entries [])) ->
       (forall (G5 : G) (proplist5 : proplist) 
          (l5 : l) (prop5 : FitchProp.prop)
          (justification5 : justification) 
          (proof5 : proof),
        valid_derivation G5 proplist5
          (derivation_deriv l5 prop5
             (reason_justification justification5)) ->
        valid_proof (Map.add (inl l5) (inl prop5) G5) proplist5
          proof5 ->
        P (Map.add (inl l5) (inl prop5) G5) proplist5 proof5 ->
        P G5 proplist5
          (proof_entries
             (entry_derivation
                (derivation_deriv l5 prop5
                   (reason_justification justification5))
              :: proof_list_entry proof5))) ->
       (forall (G5 : G) (proplist5 : proplist) 
          (l5 : l) (prop5 : FitchProp.prop)
          (proof5 proof' : proof) (l' : l)
          (prop' : FitchProp.prop) (reason5 : reason),
        last
          (proof_list_entry
             (proof_entries
                (entry_derivation
                   (derivation_deriv l5 prop5 reason_assumption)
                 :: proof_list_entry proof5))) entry_invalid =
        entry_derivation (derivation_deriv l' prop' reason5) ->
        valid_proof (Map.add (inl l5) (inl prop5) G5) proplist5
          proof5 ->
        P (Map.add (inl l5) (inl prop5) G5) proplist5 proof5 ->
        valid_proof
          (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
          proplist5 proof' ->
        P (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
          proplist5 proof' ->
        P G5 proplist5
          (proof_entries
             (entry_box
                (proof_entries
                   (entry_derivation
                      (derivation_deriv l5 prop5
                         reason_assumption)
                    :: proof_list_entry proof5))
              :: proof_list_entry proof'))) ->
       forall (g : G) (p : proplist) (p0 : proof),
       valid_proof g p p0 -> P g p p0
*)
