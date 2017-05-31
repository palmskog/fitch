Require Import String.
Require Import FMapList.

Require Import fitch.
Require Import fitch_program.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Require Import ExtrOcamlString.

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

Extraction "fitch.ml" valid_claim_dec.
