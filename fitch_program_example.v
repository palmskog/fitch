Require Import FMapList.
Require Import fitch.
Require Import fitch_program.
Require Import String.
Require Import mathcomp.ssreflect.ssreflect.

Module PIString <: PropInterpretation.
Definition A := string.
End PIString.

Module DPIString <: DecidablePropInterpretation PIString.
Definition A_eq_dec := string_dec.
End DPIString.

Module NatSpecType <: SpecType. Definition t := nat. End NatSpecType.
Module NatSpecUsualOrderedType <: SpecUsualOrderedType NatSpecType := Nat_as_OT.
Module NatDyadicSpec := DyadicSpec NatSpecType.
Module NatDyadicSpecUsualOrderedType := SpecDyadicUsualOrderedType NatSpecType NatSpecUsualOrderedType NatDyadicSpec.
Module Map := FMapList.Make NatDyadicSpecUsualOrderedType.

Module FitchProgramMap :=
 FitchProgram
   PIString DPIString
   NatSpecType NatSpecUsualOrderedType
   NatDyadicSpec NatDyadicSpecUsualOrderedType
   Map.
Import FitchProgramMap.

Definition test_claim_1 : claim := 
  (claim_judgment_proof 
    (judgment_follows (cons (prop_p "p"%string) nil) (prop_p "p"%string)) 
    (proof_entries (cons (entry_derivation (derivation_deriv 1 (prop_p "p"%string) (reason_justification justification_premise))) nil))).

Definition test_claim_2 : claim :=
  (claim_judgment_proof (judgment_follows (cons (prop_or (prop_p "p"%string)  (prop_and (prop_p "p"%string) (prop_p "q"%string)) ) nil) (prop_p "p"%string)) (proof_entries ((app (cons (entry_derivation (derivation_deriv 1 (prop_or (prop_p "p"%string)  (prop_and (prop_p "p"%string) (prop_p "q"%string)) ) (reason_justification justification_premise))) nil) (app (cons (entry_box (proof_entries ((app (cons (entry_derivation (derivation_deriv 2 (prop_p "p"%string) reason_assumption)) nil) (app (cons (entry_derivation (derivation_deriv 3 (prop_p "p"%string) (reason_justification (justification_copy 2)))) nil) nil))))) nil) (app (cons (entry_box (proof_entries ((app (cons (entry_derivation (derivation_deriv 4 (prop_and (prop_p "p"%string) (prop_p "q"%string)) reason_assumption)) nil) (app (cons (entry_derivation (derivation_deriv 5 (prop_p "p"%string) (reason_justification (justification_ande1 4)))) nil) nil))))) nil) (app (cons (entry_derivation (derivation_deriv 6 (prop_p "p"%string) (reason_justification (justification_ore 1 2 3 4 5)))) nil) nil))))))).

Lemma test_claim_1_true : validate_claim test_claim_1 = true.
Proof. by []. Qed.

Lemma test_claim_2_true : validate_claim test_claim_2 = true.
Proof. by []. Qed.
