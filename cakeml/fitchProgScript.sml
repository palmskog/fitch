open preamble ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory astPP MapProgTheory comparisonTheory basisFunctionsLib dyadicCmpTheory fitchTheory fitchExampleTheory fitchDecidableTheory fitchCakeTheory;

val _ = new_theory "fitchProg";

fun get_current_prog () =
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

val _ = translation_extends "MapProg";

val _ = (use_full_type_names := false);
val _ = register_type ``:fitch$justification``;
val _ = register_type ``:fitch$reason``;
val _ = register_type ``:fitch$prop``;
val _ = register_type ``:fitch$derivation``;
val _ = register_type ``:fitch$entry``;
val _ = register_type ``:fitch$judgment``;
val _ = register_type ``:fitch$claim``;
val _ = (use_full_type_names := true);

val _ = ml_prog_update (open_module "Fitch");

val _ = ml_prog_update open_local_block;

val _ = next_ml_names := ["valid_derivation_deriv_premise"];
val _ = translate valid_derivation_deriv_premise_cake;

val _ = next_ml_names := ["valid_derivation_deriv_lem"];
val _ = translate valid_derivation_deriv_lem_cake;

val _ = next_ml_names := ["valid_derivation_deriv_copy"];
val _ = translate valid_derivation_deriv_copy_cake;

val _ = next_ml_names := ["valid_derivation_deriv_andi"];
val _ = translate valid_derivation_deriv_andi_cake;

val _ = next_ml_names := ["valid_derivation_deriv_ande1"];
val _ = translate valid_derivation_deriv_ande1_cake;

val _ = next_ml_names := ["valid_derivation_deriv_ande2"];
val _ = translate valid_derivation_deriv_ande2_cake;

val _ = next_ml_names := ["valid_derivation_deriv_ori1"];
val _ = translate valid_derivation_deriv_ori1_cake;

val _ = next_ml_names := ["valid_derivation_deriv_ori2"];
val _ = translate valid_derivation_deriv_ori2_cake;

val _ = next_ml_names := ["valid_derivation_deriv_impe"];
val _ = translate valid_derivation_deriv_impe_cake;

val _ = next_ml_names := ["valid_derivation_deriv_nege"];
val _ = translate valid_derivation_deriv_nege_cake;

val _ = next_ml_names := ["valid_derivation_deriv_conte"];
val _ = translate valid_derivation_deriv_conte_cake;

val _ = next_ml_names := ["valid_derivation_deriv_negnegi"];
val _ = translate valid_derivation_deriv_negnegi_cake;

val _ = next_ml_names := ["valid_derivation_deriv_negnege"];
val _ = translate valid_derivation_deriv_negnege_cake;

val _ = next_ml_names := ["valid_derivation_deriv_mt"];
val _ = translate valid_derivation_deriv_mt_cake;

val _ = next_ml_names := ["valid_derivation_deriv_impi"];
val _ = translate valid_derivation_deriv_impi_cake;

val _ = next_ml_names := ["valid_derivation_deriv_negi"];
val _ = translate valid_derivation_deriv_negi_cake;

val _ = next_ml_names := ["valid_derivation_deriv_ore"];
val _ = translate valid_derivation_deriv_ore_cake;

val _ = next_ml_names := ["valid_derivation_deriv_pbc"];
val _ = translate valid_derivation_deriv_pbc_cake;

val _ = next_ml_names := ["valid_derivation_deriv"];
val _ = translate valid_derivation_deriv_cake;

val _ = translate LAST_DEFAULT;

val _ = next_ml_names := ["valid_proof_entry_list"];
val _ = translate valid_proof_entry_list_cake;

val _ = next_ml_names := ["valid_proof"];
val _ = translate valid_proof_dec_cake;

val _ = next_ml_names := ["valid_claim_cmp"];
val _ = translate valid_claim_dec_cmp_cake;

val _ = translate dyadic_cmp;
val _ = translate num_cmp_def;
val _ = translate dyadic_cmp_num;

val _ = ml_prog_update open_local_in_block;

val _ = next_ml_names := ["valid_claim"];
val _ = translate valid_claim_dec_cake;

val _ = translate example_premises;
val _ = translate example_proof;
val _ = translate example_claim;

val _ = ml_prog_update close_local_block;

val _ = ml_prog_update (close_module NONE);

val _ = astPP.enable_astPP ();
val _ = Globals.max_print_depth := 100;
val _ = print_term (get_current_prog ());
val _ = Globals.max_print_depth := 20;
val _ = astPP.disable_astPP ();

val _ = export_theory ();
