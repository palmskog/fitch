open preamble
     ml_translatorLib ml_translatorTheory ml_progLib ml_progTheory
     ListProgTheory MapProgTheory mlmapTheory
     fitchProgramTheory astPP basisFunctionsLib;

val _ = new_theory "fitchProg";

val _ = translation_extends "MapProg";

val _ = ml_prog_update (open_module "FitchProg");

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

Definition valid_derivation_deriv_andi_cake:
 valid_derivation_deriv_andi_cake t l1 l2 p =
   case lookup t (INL l1) of
   | SOME (INL p1) =>
     (case lookup t (INL l2) of
     | SOME (INL p2) => p = prop_and p1 p2
     | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_andi_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_andi_cake t l1 l2 p = 
   valid_derivation_deriv_andi (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_andi_cake,valid_derivation_deriv_andi] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_andi_cake;

Definition valid_derivation_deriv_ande1_cake:
 valid_derivation_deriv_ande1_cake t l p =
   case lookup t (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p1
   | _ => F
End

Theorem valid_derivation_deriv_ande1_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_ande1_cake t l p = 
   valid_derivation_deriv_ande1 (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_ande1_cake,valid_derivation_deriv_ande1] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_ande1_cake;

Definition valid_derivation_deriv_ande2_cake:
 valid_derivation_deriv_ande2_cake t l p =
   case lookup t (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p2
   | _ => F
End

Theorem valid_derivation_deriv_ande2_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_ande2_cake t l p = 
   valid_derivation_deriv_ande2 (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_ande2_cake,valid_derivation_deriv_ande2] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_ande2_cake;

Definition valid_derivation_deriv_ori1_cake:
 valid_derivation_deriv_ori1_cake t l p =
  case p of
  | prop_or p1 p2 =>
    (case lookup t (INL l) of
     | SOME (INL p') => p1 = p'
     | _ => F)
  | _ => F
End

Theorem valid_derivation_deriv_ori1_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_ori1_cake t l p = 
   valid_derivation_deriv_ori1 (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_ori1_cake,valid_derivation_deriv_ori1] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_ori1_cake;

Definition valid_derivation_deriv_ori2_cake:
 valid_derivation_deriv_ori2_cake t l p =
   case p of
   | prop_or p1 p2 => 
     (case lookup t (INL l) of
       | SOME (INL p') => p2 = p'	 
       | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_ori2_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_ori2_cake t l p = 
   valid_derivation_deriv_ori2 (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_ori2_cake,valid_derivation_deriv_ori2] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_ori2_cake;

Definition valid_derivation_deriv_impe_cake:
 valid_derivation_deriv_impe_cake t l1 l2 p =
   case lookup t (INL l1) of
   | SOME (INL p1) => 
     (case lookup t (INL l2) of
      | SOME (INL (prop_imp p2 p3)) => p1 = p2 /\ p = p3
      | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_impe_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_impe_cake t l1 l2 p = 
   valid_derivation_deriv_impe (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_impe_cake,valid_derivation_deriv_impe] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_impe_cake;

Definition valid_derivation_deriv_nege_cake:
  valid_derivation_deriv_nege_cake t l1 l2 p =
     case p of 
     | prop_cont => 
       (case lookup t (INL l1) of
	| SOME (INL p1) =>
	  (case lookup t (INL l2) of
	   | SOME (INL (prop_neg p2)) => p1 = p2
	   | _ => F)
	| _ => F)
     | _ => F
End

Theorem valid_derivation_deriv_nege_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_nege_cake t l1 l2 p = 
   valid_derivation_deriv_nege (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_nege_cake,valid_derivation_deriv_nege] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_nege_cake;

Definition valid_derivation_deriv_conte_cake:
 valid_derivation_deriv_conte_cake t l =
   case lookup t (INL l) of
   | SOME (INL prop_cont)  => T     
   | _ => F
End

Theorem valid_derivation_deriv_conte_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_conte_cake t l = 
   valid_derivation_deriv_conte (to_fmap t) l
Proof
 rw [valid_derivation_deriv_conte_cake,valid_derivation_deriv_conte] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_conte_cake;

Definition valid_derivation_deriv_negnegi_cake:
  valid_derivation_deriv_negnegi_cake t l p =
    case p of
    | prop_neg (prop_neg p1) => 
      (case lookup t (INL l) of
	| SOME (INL p2) => p1 = p2
	| _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_negnegi_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_negnegi_cake t l p = 
   valid_derivation_deriv_negnegi (to_fmap t) l p
Proof
 rw [valid_derivation_deriv_negnegi_cake,valid_derivation_deriv_negnegi] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_negnegi_cake;

Definition valid_derivation_deriv_negnege_cake:
 valid_derivation_deriv_negnege_cake t l p =
  case lookup t (INL l) of
  | SOME (INL (prop_neg (prop_neg p'))) => p' = p
  | _ => F
End

Theorem valid_derivation_deriv_negnege_eq:
 !t l p. map_ok t ==>
  valid_derivation_deriv_negnege_cake t l p =   
   valid_derivation_deriv_negnege (to_fmap t) l p   
Proof
 rw [valid_derivation_deriv_negnege_cake,valid_derivation_deriv_negnege] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_negnege_cake;

Definition valid_derivation_deriv_mt_cake:
  valid_derivation_deriv_mt_cake t l1 l2 p =
    case p of
    | prop_neg p' =>
      (case lookup t (INL l1) of
       | SOME (INL (prop_imp p1 p2)) =>
	 if p' = p1 then
	     (case lookup t (INL l2) of
	     | SOME (INL (prop_neg p3)) => p2 = p3
	     | _ => F)
	 else F
       | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_mt_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_mt_cake t l1 l2 p = 
   valid_derivation_deriv_mt (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_mt_cake,valid_derivation_deriv_mt] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_mt_cake;

Definition valid_derivation_deriv_impi_cake:
  valid_derivation_deriv_impi_cake t l1 l2 p =
    case p of
    | prop_imp p1 p2 => 
      (case lookup t (INR (l1, l2)) of
      | SOME (INR (p3, p4)) => p1 = p3 /\ p2 = p4
      | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_impi_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_impi_cake t l1 l2 p = 
   valid_derivation_deriv_impi (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_impi_cake,valid_derivation_deriv_impi] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_impi_cake;

Definition valid_derivation_deriv_negi_cake:
 valid_derivation_deriv_negi_cake t l1 l2 p =
   case p of
   | prop_neg p1 => 
     (case lookup t (INR (l1,l2)) of
      | SOME (INR (p2,prop_cont)) => p1 = p2	
      | _ => F)
   | _ => F
End

Theorem valid_derivation_deriv_negi_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_negi_cake t l1 l2 p = 
   valid_derivation_deriv_negi (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_negi_cake,valid_derivation_deriv_negi] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_negi_cake;

Definition valid_derivation_deriv_ore_cake:
  valid_derivation_deriv_ore_cake t l1 l2 l3 l4 l5 p =
    case lookup t (INL l1) of
    | SOME (INL (prop_or p1 p2)) => 
      (case lookup t (INR (l2, l3)) of
       | SOME (INR (p3, p4)) => 
	 if p1 = p3 /\ p = p4 then
	     (case lookup t (INR (l4,l5)) of
              | SOME (INR (p5, p6)) =>
		p2 = p5 /\ p = p6
	      | _ => F)
	 else F	     
       | _ => F)
    | _ => F
End

Theorem valid_derivation_deriv_ore_eq:
 !t l1 l2 l3 l4 l5 p. map_ok t ==>
  valid_derivation_deriv_ore_cake t l1 l2 l3 l4 l5 p = 
   valid_derivation_deriv_ore (to_fmap t) l1 l2 l3 l4 l5 p
Proof
 rw [valid_derivation_deriv_ore_cake,valid_derivation_deriv_ore] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_ore_cake;

Definition valid_derivation_deriv_pbc_cake:
  valid_derivation_deriv_pbc_cake t l1 l2 p =
   case lookup t (INR (l1,l2)) of
   | SOME (INR (prop_neg p', prop_cont)) =>
     p' = p
   | _ => F
End

Theorem valid_derivation_deriv_pbc_eq:
 !t l1 l2 p. map_ok t ==>
  valid_derivation_deriv_pbc_cake t l1 l2 p = 
   valid_derivation_deriv_pbc (to_fmap t) l1 l2 p
Proof
 rw [valid_derivation_deriv_pbc_cake,valid_derivation_deriv_pbc] \\
 rw [lookup_thm]
QED

val res = translate valid_derivation_deriv_pbc_cake;

Definition valid_derivation_deriv_cake:
  valid_derivation_deriv_cake t pl p r =
    case r of
    | reason_assumption => F
    | reason_justification j => 
      case j of
      | justification_premise =>  valid_derivation_deriv_premise_cake pl p
      | justification_lem => valid_derivation_deriv_lem_cake p
      | justification_copy l => valid_derivation_deriv_copy_cake t l p
      | justification_andi l1 l2  => valid_derivation_deriv_andi_cake t l1 l2 p
      | justification_ande1 l => valid_derivation_deriv_ande1_cake t l p
      | justification_ande2 l => valid_derivation_deriv_ande2_cake t l p
      | justification_ori1 l => valid_derivation_deriv_ori1_cake t l p
      | justification_ori2 l => valid_derivation_deriv_ori2_cake t l p
      | justification_impe l1 l2 => valid_derivation_deriv_impe_cake t l1 l2 p
      | justification_nege l1 l2 => valid_derivation_deriv_nege_cake t l1 l2 p
      | justification_conte l => valid_derivation_deriv_conte_cake t l
      | justification_negnegi l => valid_derivation_deriv_negnegi_cake t l p
      | justification_negnege l => valid_derivation_deriv_negnege_cake t l p
      | justification_mt l1 l2 => valid_derivation_deriv_mt_cake t l1 l2 p
      | justification_impi l1 l2 => valid_derivation_deriv_impi_cake t l1 l2 p
      | justification_negi l1 l2 => valid_derivation_deriv_negi_cake t l1 l2 p
      | justification_ore l1 l2 l3 l4 l5 => valid_derivation_deriv_ore_cake t l1 l2 l3 l4 l5 p
      | justification_pbc l1 l2 => valid_derivation_deriv_pbc_cake t l1 l2 p
End

Theorem valid_derivation_deriv_eq:
  !t pl l p r. map_ok t ==> 
  valid_derivation_deriv_cake t pl p r = valid_derivation_deriv (to_fmap t) pl p r
Proof
  rw [valid_derivation_deriv_cake,valid_derivation_deriv] \\
  rw [valid_derivation_deriv_premise_eq] \\
  rw [valid_derivation_deriv_lem_eq] \\
  rw [valid_derivation_deriv_copy_eq] \\
  rw [valid_derivation_deriv_andi_eq] \\
  rw [valid_derivation_deriv_ande1_eq] \\
  rw [valid_derivation_deriv_ande2_eq] \\
  rw [valid_derivation_deriv_ori1_eq] \\
  rw [valid_derivation_deriv_ori2_eq] \\
  rw [valid_derivation_deriv_impe_eq] \\
  rw [valid_derivation_deriv_nege_eq] \\
  rw [valid_derivation_deriv_conte_eq] \\
  rw [valid_derivation_deriv_negnegi_eq] \\
  rw [valid_derivation_deriv_negnege_eq] \\
  rw [valid_derivation_deriv_mt_eq] \\
  rw [valid_derivation_deriv_impi_eq] \\
  rw [valid_derivation_deriv_negi_eq] \\
  rw [valid_derivation_deriv_ore_eq] \\
  rw [valid_derivation_deriv_pbc_eq] \\
  Cases_on `r` \\ rw [] \\ Cases_on `j` \\ rw []
QED

val res = translate valid_derivation_deriv_cake;

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

val _ = ml_prog_update (close_module NONE);

val _ = export_theory();
