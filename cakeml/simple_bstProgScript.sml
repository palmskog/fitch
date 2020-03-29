(*
  Using the CakeML translator to produce a verified deep embedding of the
  simple BST implementation.
*)

open preamble
     ml_progLib ml_translatorLib ml_translatorTheory astPP
     simple_bstTheory ListProgTheory;

val _ = new_theory "simple_bstProg";

(*val _ = translation_extends "ListProg";*)

(*
  To translate a HOL function to CakeML, call translate on its definition. For
  example, let us start by translating the singleton function from
  simple_bstTheory.

  The necessary datatypes (('a,'b) btree in this case) will be automatically
  translated first.

  The result is a certificate theorem indicating that the CakeML value
  (singleton_v) that results from running the generated code for declaring the
  CakeML version of the singleton function refines the HOL function singleton.
*)

(*val prog_tm =
  get_ml_prog_state() |> remove_snocs |> clean_state |> get_thm
  |> concl |> strip_comb |> #2 |> el 2*)

(*
  The translator maintains state, containing the entire current translated program.
  For each top-level declaration in this program, the translator also defines a
  constant representing the state of the CakeML semantics after this
  As a side effect of calling translate, the program is appended to the state.

  Let us look at the code in the current program.
*)

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

val res = translate singleton_def;

(*print_term (get_current_prog());*)

val res = translate insert_def;

(*print_term (get_current_prog());*)

val res = translate lookup_def;

(*val res = translate valid_derivation_deriv_premise;*)

val _ = astPP.enable_astPP();
(*val () = Globals.max_print_depth := 20;*)

val _ = print_term (get_current_prog());

val _ = astPP.disable_astPP();

(*
val res = translate member_def;
*)

(* TODO: use of certificate theorem to show something about the generated code? *)

val _ = export_theory();
