Require Import FMapList.
Require Import Fitch.fitch.
Require Import Fitch.fitch_program.
Require Import String.
Require Import Fitch.ssrexport.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.

Module Import FitchProgramMap := FitchProgram Nat_as_OT Nat_as_DUOT Map.

Definition test_claim_1 : claim := 
  (claim_judgment_proof 
    (judgment_follows (cons (prop_p "p"%string) nil) (prop_p "p"%string)) 
    (proof_entries (cons (entry_derivation (derivation_deriv 1 (prop_p "p"%string) (reason_justification justification_premise))) nil))).

Definition test_claim_2 : claim :=
  (claim_judgment_proof (judgment_follows (cons (prop_or (prop_p "p"%string)  (prop_and (prop_p "p"%string) (prop_p "q"%string)) ) nil) (prop_p "p"%string)) (proof_entries ((app (cons (entry_derivation (derivation_deriv 1 (prop_or (prop_p "p"%string)  (prop_and (prop_p "p"%string) (prop_p "q"%string)) ) (reason_justification justification_premise))) nil) (app (cons (entry_box (proof_entries ((app (cons (entry_derivation (derivation_deriv 2 (prop_p "p"%string) reason_assumption)) nil) (app (cons (entry_derivation (derivation_deriv 3 (prop_p "p"%string) (reason_justification (justification_copy 2)))) nil) nil))))) nil) (app (cons (entry_box (proof_entries ((app (cons (entry_derivation (derivation_deriv 4 (prop_and (prop_p "p"%string) (prop_p "q"%string)) reason_assumption)) nil) (app (cons (entry_derivation (derivation_deriv 5 (prop_p "p"%string) (reason_justification (justification_ande1 4)))) nil) nil))))) nil) (app (cons (entry_derivation (derivation_deriv 6 (prop_p "p"%string) (reason_justification (justification_ore 1 2 3 4 5)))) nil) nil))))))).

Lemma test_claim_1_true : validate_claim string_dec test_claim_1 = true.
Proof. by []. Qed.

Lemma test_claim_2_true : validate_claim string_dec test_claim_2 = true.
Proof. by []. Qed.
