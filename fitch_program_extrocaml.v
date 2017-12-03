Require Import String.
Require Import FMapList.

Require Import Fitch.fitch.
Require Import Fitch.fitch_program.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Module PIString <: PropInterpretation.
Definition A := string.
End PIString.

Module DPIString <: DecidablePropInterpretation PIString.
Definition A_eq_dec := string_dec.
End DPIString.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.

Module FitchProgramMap :=
 FitchProgram
   PIString DPIString
   Nat_as_OT Nat_as_DUOT
   Map.
Import FitchProgramMap.

Extraction "fitch.ml" valid_claim_dec.
