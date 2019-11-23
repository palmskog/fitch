open HolKernel boolLib Parse bossLib pairTheory optionTheory stringTheory;
open relationTheory listTheory finite_mapTheory;
open ottTheory ottLib IndDefLib IndDefRules fitchTheory;

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

(* fun RI thm = RULE_INDUCT_THEN thm STRIP_ASSUME_TAC STRIP_ASSUME_TAC; *)

val soundness_premise_thm = Q.store_thm("soundness_premise",
`!G pl p l. premises_admitted pl ==>
  valid_derivation G pl (derivation_deriv l p (reason_justification justification_premise)) ==>
  prop_of p`,
RW_TAC list_ss [premises_admitted_def]);

val soundness_lem_thm = Q.store_thm("soundness_lem",
`!G pl p l. valid_derivation G pl (derivation_deriv l p (reason_justification justification_lem)) ==> prop_of p`,
ID_TAC);

val soundness_andi_thm = Q.store_thm("soundness_andi",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_andi l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_copy_thm = Q.store_thm("soundness_copy",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_copy l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_ande1_thm = Q.store_thm("soundness_ande1",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_ande2_thm = Q.store_thm("soundness_ande2",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ande2 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_ori1_thm = Q.store_thm("soundness_ori1",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_ori2_thm = Q.store_thm("soundness_ori2",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_ori2 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_impe_thm = Q.store_thm("soundness_impe",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impe l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_nege_thm = Q.store_thm("soundness_nege",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_nege l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_conte_thm = Q.store_thm("soundness_conte",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_conte l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_conte_negnegi_thm = Q.store_thm("soundness_negnegi",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnegi l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_conte_negnege_thm = Q.store_thm("soundness_negnege",
`!G pl p l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l1 p (reason_justification (justification_negnege l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_mt_thm = Q.store_thm("soundness_mt",
`!G pl p l l1 l2. map_line_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_mt l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_impi_thm = Q.store_thm("soundness_impi",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_impi l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_negi_thm = Q.store_thm("soundness_negi",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_negi l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_ore_thm = Q.store_thm("soundness_ore",
`!G pl p l l1 l2 l3 l4 l5. map_line_admitted G ==> map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_ore l1 l2 l3 l4 l5))) ==>
 prop_of p`,
ID_TAC);

val soundness_pbc_thm = Q.store_thm("soundness_pbc",
`!G pl p l l1 l2. map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification (justification_pbc l1 l2))) ==>
 prop_of p`,
ID_TAC);

val soundness_derivations_thm = Q.store_thm("soundness_derivations",
`!G pl p l j. premises_admitted pl ==> map_line_admitted G ==> map_box_admitted G ==>
 valid_derivation G pl (derivation_deriv l p (reason_justification j)) ==>
 prop_of p`,
ID_TAC);

val justification_prop_def = Define
`!G pl pr. justification_prop G pl pr =
!l p r. valid_proof G pl pr ==>
MEM (entry_derivation (derivation_deriv l p r)) (proof_list_entry pr) ==>
r <> reason_assumption`;

val justification_empty_thm = Q.store_thm("justification_empty",
`!G pl. justification_prop G pl (proof_entries [])`,
ID_TAC);

val _ = export_theory();
