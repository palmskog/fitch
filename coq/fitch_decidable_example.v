Require Import FMapList.
Require Import Fitch.fitch.
Require Import Fitch.fitch_decidable.
Require Import Fitch.fitch_metatheory.
Require Import String.
Require Import Fitch.ssrexport.
Import ListNotations.

Definition partialOut {P : Prop} (x : option P) :=
  match x return (match x with
                    | Some _ => P
                    | None => True
                  end) with
    | Some pf => pf
    | None => I
  end.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.
Module Import FitchDecidableNat := FitchDecidable Nat_as_OT Nat_as_DUOT Map.

Definition p_prop  := prop_p "p"%string.
Definition q_prop := prop_p "q"%string.

Definition prems_1 := [p_prop].
Definition proof_1 := [entry_derivation (derivation_deriv 1 p_prop (reason_justification justification_premise))].
Definition claim_1 := claim_judgment_proof (judgment_follows prems_1 p_prop) proof_1.

Lemma claim_1_valid : valid_claim claim_1.
Proof.
exact
  (partialOut (match valid_claim_dec string_dec claim_1 with
   | left H => Some H
   | right _ => None
   end)).
Qed.

Definition prems_2 := [prop_or p_prop (prop_and p_prop q_prop)].
Definition proof_2 :=
  [entry_derivation (derivation_deriv 1 (prop_or p_prop (prop_and p_prop q_prop)) (reason_justification justification_premise));
   entry_box
    [entry_derivation (derivation_deriv 2 p_prop reason_assumption);
     entry_derivation (derivation_deriv 3 p_prop (reason_justification (justification_copy 2)))];
   entry_box
    [entry_derivation (derivation_deriv 4 (prop_and p_prop q_prop) reason_assumption);
     entry_derivation (derivation_deriv 5 p_prop (reason_justification (justification_ande1 4)))];
   entry_derivation (derivation_deriv 6 p_prop (reason_justification (justification_ore 1 2 3 4 5)))].
Definition claim_2 := claim_judgment_proof (judgment_follows prems_2 p_prop) proof_2.

Lemma claim_2_valid : valid_claim claim_2.
Proof.
exact
  (partialOut (match valid_claim_dec string_dec claim_2 with
   | left H => Some H
   | right _ => None
   end)).
Qed.
