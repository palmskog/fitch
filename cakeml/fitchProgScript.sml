open preamble
     ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory
     ListProgTheory MapProgTheory mlmapTheory
     fitchProgramTheory astPP basisFunctionsLib;

val _ = new_theory "fitchProg";

val _ = translation_extends "MapProg";

val _ = ml_prog_update (open_module "fitchProg");

val _ = ml_prog_update open_local_block;

(*val res = translate MEMBER_def;*)

Definition valid_derivation_deriv_premise_cake:
 valid_derivation_deriv_premise_cake pl p = MEMBER p pl
End

Theorem valid_derivation_deriv_premise_eq:
 !pl p. valid_derivation_deriv_premise_cake pl p = valid_derivation_deriv_premise pl p
Proof
 rw [valid_derivation_deriv_premise_cake,valid_derivation_deriv_premise,MEMBER_INTRO]
QED

val res = translate valid_derivation_deriv_premise_cake;

Definition valid_derivation_deriv_lem_cake:
 valid_derivation_deriv_lem_cake p =
  case p of
  | prop_or p1 (prop_neg p2) => p1 = p2
  | _ => F
End

Theorem valid_derivation_deriv_lem_eq:
 !p. valid_derivation_deriv_lem_cake p = valid_derivation_deriv_lem p
Proof
 rw [valid_derivation_deriv_lem_cake,valid_derivation_deriv_lem]
QED

val res = translate valid_derivation_deriv_lem_cake;

(*val res = translate lookup_def;*)

Definition valid_derivation_deriv_copy_cake:
 valid_derivation_deriv_copy_cake t l p =
  case lookup t (INL l) of
  | SOME (INL p')  => p = p'
  | _ => F
End

Theorem valid_derivation_deriv_copy_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_copy_cake t l p = 
   valid_derivation_deriv_copy (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_copy_cake,valid_derivation_deriv_copy] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_copy_cake;

(*
fun get_current_prog() =
let
  val state = get_ml_prog_state()
  val state_thm =
    state |> ml_progLib.remove_snocs
          |> ml_progLib.clean_state
          |> get_thm
  val current_prog =
    state_thm
    |> concl
    |> strip_comb |> #2
    |> el 2
in current_prog end;

val _ = astPP.enable_astPP();

val _ = print_term (get_current_prog());
*)

val _ = ml_prog_update close_local_block;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
