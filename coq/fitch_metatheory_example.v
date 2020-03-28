Require Import FMapList.
Require Import Fitch.fitch.
Require Import Fitch.fitch_metatheory.
Require Import Fitch.ssrexport.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.

Module Import FitchPropMetatheoryListMap := FitchPropMetatheory Nat_as_OT Nat_as_DUOT Map.

Section TestFitch.

Variable P : Prop.
Variable Q : Prop.

Hypothesis H_q : Q.
Hypothesis H_p : P.

Definition pp  := prop_p P.
Definition pq := prop_p Q.

Definition prems := pp :: pq :: nil.

Definition proof_pq : proof :=
  (((entry_derivation (derivation_deriv 1 pp (reason_justification justification_premise))) ::
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
apply vp_derivation; first by apply vd_premise; left.
rewrite /derivs {derivs}.
set derivs := entry_derivation (derivation_deriv 3 (prop_and pp pq) (reason_justification (justification_andi 1 2))) :: nil.
apply vp_derivation; first by apply vd_premise; right; left.
rewrite /derivs {derivs}.
apply vp_derivation; last by apply vp_empty.
by apply vd_andi.
Qed.

Lemma premises_admitted_pq : premises_admitted prems.
Proof.
rewrite /premises_admitted.
move => prop6 H_in.
case: H_in => H_eq; first by rewrite -H_eq.
case: H_eq => H_eq; last by [].
by rewrite -H_eq.
Qed.

Theorem p_q : P /\ Q.
exact (soundness_claim (prop_and pp pq) prems proof_pq premises_admitted_pq valid_claim_p_q).
Qed.

End TestFitch.
