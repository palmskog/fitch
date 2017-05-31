Require Import FMapList.
Require Import dyadicnat.
Require Import fitch.
Require Import fitch_metatheory.
Require Import mathcomp.ssreflect.ssreflect.

Module SpecMapList 
 (ST : SpecType) (SUOT : SpecUsualOrderedType ST)
 (DST : DyadicSpecType ST) (SUOTD : SpecUsualOrderedType DST) <: FMapInterface.S with Module E := SUOTD :=
FMapList.Make SUOTD.

Module NatSpecType <: SpecType. Definition t := nat. End NatSpecType.
Module NatSpecUsualOrderedType <: SpecUsualOrderedType NatSpecType := Nat_as_OT.
Module NatDyadicSpec <: DyadicSpecType NatSpecType := DyadicSpec NatSpecType.
Module NatDyadicSpecUsualOrderedType <: SpecUsualOrderedType NatDyadicSpec :=
 SpecDyadicUsualOrderedType NatSpecType NatSpecUsualOrderedType NatDyadicSpec.
Module MapList :=
 SpecMapList NatSpecType NatSpecUsualOrderedType NatDyadicSpec NatDyadicSpecUsualOrderedType.

Module FitchPropMetatheoryListMap :=
 FitchPropMetatheory 
   NatSpecType NatSpecUsualOrderedType
   NatDyadicSpec NatDyadicSpecUsualOrderedType
   MapList.
Import FitchPropMetatheoryListMap.

Section TestFitch.

Variable P : Prop.
Variable Q : Prop.

Hypothesis H_q : Q.
Hypothesis H_p : P.

Definition pp  := prop_p P.
Definition pq := prop_p Q.

Definition prems := pp :: pq :: nil.

Lemma pm_pq : prop_mapping (prop_and pp pq) (P /\ Q).
Proof. by apply pm_and; apply pm_p. Qed.

Definition proof_pq : proof :=
  (proof_entries     
      ((entry_derivation (derivation_deriv 1 pp (reason_justification justification_premise))) ::
      (entry_derivation (derivation_deriv 2 pq (reason_justification justification_premise))) ::
      (entry_derivation (derivation_deriv 3 (prop_and pp pq) (reason_justification (justification_andi 1 2)))) :: nil)).

Definition claim_pq : claim := 
  claim_judgment_proof 
  (judgment_follows prems (prop_and pp pq))
  proof_pq.

Lemma valid_claim_p_q : valid_claim claim_pq.
Proof.
apply vc_claim with (l5 := 3) (justification5 := justification_andi 1 2); first by [].
rewrite /proof_pq.
set derivs := (entry_derivation (derivation_deriv 2 pq (reason_justification justification_premise))) :: (entry_derivation (derivation_deriv 3 (prop_and pp pq) (reason_justification (justification_andi 1 2))) :: nil).
have ->: derivs = proof_list_entry (proof_entries derivs) by [].
apply vp_derivation; first by apply vd_premise; left.
rewrite /derivs {derivs}.
set derivs := entry_derivation (derivation_deriv 3 (prop_and pp pq) (reason_justification (justification_andi 1 2))) :: nil.
have ->: derivs = proof_list_entry (proof_entries derivs) by [].
apply vp_derivation; first by apply vd_premise; right; left.
rewrite /derivs {derivs}.
have ->: nil = proof_list_entry (proof_entries nil) by [].
apply vp_derivation; last by apply vp_empty.
by apply vd_andi.
Qed.

Lemma premises_admitted_pq : premises_admitted prems.
Proof.
rewrite /premises_admitted.
move => prop6 P6 H_P6 H_in.
case: H_in => H_eq.
  rewrite -H_eq in H_P6.
  have H_pm: prop_mapping pp P by apply pm_p.
  by rewrite -(prop_mapping_eq pp P P6 H_pm H_P6).
case: H_eq => H_eq; last by [].
rewrite -H_eq in H_P6.
have H_pm: prop_mapping pq Q by apply pm_p.
by rewrite -(prop_mapping_eq pq Q P6 H_pm H_P6).
Qed.

Theorem p_q : P /\ Q.
exact (soundness_claim (prop_and pp pq) (P /\ Q) prems proof_pq premises_admitted_pq pm_pq valid_claim_p_q).
Qed.

End TestFitch.
