Require Import String.
Require Import FMapList.

Require Import Fitch.fitch.
Require Import Fitch.fitch_program.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

Module Nat_as_DUOT <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := Nat_as_DUOT := FMapList.Make Nat_as_DUOT.

Module FitchProgramMap := FitchProgram Nat_as_OT Nat_as_DUOT Map.

Definition valid_claim_dec := @FitchProgramMap.valid_claim_dec string string_dec.

Extraction "ocaml/fitch_system.ml" valid_claim_dec.
