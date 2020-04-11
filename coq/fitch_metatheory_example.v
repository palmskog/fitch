Require Import FMapList.
Require Import Fitch.fitch.
Require Import Fitch.fitch_metatheory.
Require Import Fitch.ssrexport.
Require Import String.
Import ListNotations.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.
Module Import FitchMetatheoryNat := FitchPropMetatheory Nat_as_OT Nat_as_DUOT Map.

Definition p_prop  := prop_p 0.
Definition q_prop := prop_p 1.

Definition prems_1 := [p_prop; q_prop].
Definition proof_1 : proof :=
  [entry_derivation (derivation_deriv 1 p_prop (reason_justification justification_premise));
   entry_derivation (derivation_deriv 2 q_prop (reason_justification justification_premise));
   entry_derivation (derivation_deriv 3 (prop_and p_prop q_prop) (reason_justification (justification_andi 1 2)))].
Definition claim_1 : claim := 
  claim_judgment_proof (judgment_follows prems_1 (prop_and p_prop q_prop)) proof_1.

Lemma valid_claim_p_q : valid_claim claim_1.
Proof.
apply vc_claim with (l5 := 3) (justification5 := justification_andi 1 2); first by [].
rewrite /proof_1.
set derivs := (entry_derivation (derivation_deriv 2 p_prop (reason_justification justification_premise))) :: (entry_derivation (derivation_deriv 3 (prop_and p_prop q_prop) (reason_justification (justification_andi 1 2))) :: nil).
apply vp_derivation; first by apply vd_premise; left.
rewrite /derivs {derivs}.
set derivs := entry_derivation (derivation_deriv 3 (prop_and p_prop q_prop) (reason_justification (justification_andi 1 2))) :: nil.
apply vp_derivation; first by apply vd_premise; right; left.
rewrite /derivs {derivs}.
apply vp_derivation; last by apply vp_empty.
by apply vd_andi.
Qed.

Section TestFitch.

Variable P : Prop.
Variable Q : Prop.

Hypothesis H_p : P.
Hypothesis H_q : Q.

Definition pq_sem (n : nat) :=
  match n with
  | 0 => P
  | 1 => Q
  | _ => False
  end.

Lemma premises_admitted_pq : premises_admitted prems_1 pq_sem.
Proof.
rewrite /premises_admitted.
move => prop6 H_in.
case: H_in => H_eq; first by rewrite -H_eq.
case: H_eq => H_eq; last by [].
by rewrite -H_eq.
Qed.

Theorem p_q : P /\ Q.
exact (soundness_claim (prop_and p_prop q_prop) prems_1 proof_1 pq_sem premises_admitted_pq valid_claim_p_q).
Qed.

End TestFitch.
