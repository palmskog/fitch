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

Module FitchProgramMap :=
 FitchProgram
   PIString DPIString
   NatSpecType NatSpecUsualOrderedType
   NatDyadicSpec NatDyadicSpecUsualOrderedType
   MapList.
Import FitchProgramMap.

Extraction "fitch.ml" valid_claim_dec.
