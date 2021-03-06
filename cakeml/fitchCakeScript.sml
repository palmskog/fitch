open preamble basisFunctionsLib ml_translatorLib ml_translatorTheory mlmapTheory dyadicCmpTheory fitchTheory fitchExampleTheory fitchDecidableTheory;

val _ = new_theory "fitchCake";

Definition valid_derivation_deriv_premise_cake:
 valid_derivation_deriv_premise_cake pl p = MEMBER p pl
End

Definition valid_derivation_deriv_copy_cake:
 valid_derivation_deriv_copy_cake t l p =
  case lookup t (INL l) of
  | SOME (INL p')  => p = p'
  | _ => F
End

Definition valid_derivation_deriv_andi_cake:
 valid_derivation_deriv_andi_cake t l1 l2 p =
   case lookup t (INL l1) of
   | SOME (INL p1) =>
     (case lookup t (INL l2) of
     | SOME (INL p2) => p = prop_and p1 p2
     | _ => F)
   | _ => F
End

Definition valid_derivation_deriv_ande1_cake:
 valid_derivation_deriv_ande1_cake t l p =
   case lookup t (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p1
   | _ => F
End

Definition valid_derivation_deriv_ande2_cake:
 valid_derivation_deriv_ande2_cake t l p =
   case lookup t (INL l) of
   | SOME (INL (prop_and p1 p2)) => p = p2
   | _ => F
End

Definition valid_derivation_deriv_ori1_cake:
 valid_derivation_deriv_ori1_cake t l p =
  case p of
  | prop_or p1 p2 =>
    (case lookup t (INL l) of
     | SOME (INL p') => p1 = p'
     | _ => F)
  | _ => F
End

Definition valid_derivation_deriv_ori2_cake:
 valid_derivation_deriv_ori2_cake t l p =
   case p of
   | prop_or p1 p2 => 
     (case lookup t (INL l) of
       | SOME (INL p') => p2 = p'	 
       | _ => F)
   | _ => F
End

Definition valid_derivation_deriv_impe_cake:
 valid_derivation_deriv_impe_cake t l1 l2 p =
   case lookup t (INL l1) of
   | SOME (INL p1) => 
     (case lookup t (INL l2) of
      | SOME (INL (prop_imp p2 p3)) => p1 = p2 /\ p = p3
      | _ => F)
   | _ => F
End

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

Definition valid_derivation_deriv_conte_cake:
 valid_derivation_deriv_conte_cake t l =
   case lookup t (INL l) of
   | SOME (INL prop_cont)  => T     
   | _ => F
End

Definition valid_derivation_deriv_negnegi_cake:
  valid_derivation_deriv_negnegi_cake t l p =
    case p of
    | prop_neg (prop_neg p1) => 
      (case lookup t (INL l) of
	| SOME (INL p2) => p1 = p2
	| _ => F)
    | _ => F
End

Definition valid_derivation_deriv_negnege_cake:
 valid_derivation_deriv_negnege_cake t l p =
  case lookup t (INL l) of
  | SOME (INL (prop_neg (prop_neg p'))) => p' = p
  | _ => F
End

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

Definition valid_derivation_deriv_impi_cake:
  valid_derivation_deriv_impi_cake t l1 l2 p =
    case p of
    | prop_imp p1 p2 => 
      (case lookup t (INR (l1, l2)) of
      | SOME (INR (p3, p4)) => p1 = p3 /\ p2 = p4
      | _ => F)
    | _ => F
End

Definition valid_derivation_deriv_negi_cake:
 valid_derivation_deriv_negi_cake t l1 l2 p =
   case p of
   | prop_neg p1 => 
     (case lookup t (INR (l1,l2)) of
      | SOME (INR (p2,prop_cont)) => p1 = p2	
      | _ => F)
   | _ => F
End

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

Definition valid_derivation_deriv_pbc_cake:
  valid_derivation_deriv_pbc_cake t l1 l2 p =
   case lookup t (INR (l1,l2)) of
   | SOME (INR (prop_neg p', prop_cont)) =>
     p' = p
   | _ => F
End

Definition valid_derivation_deriv_cake:
 valid_derivation_deriv_cake t pl p r =
   case r of
   | reason_assumption => F
   | reason_justification j => 
     case j of
     | justification_premise =>  valid_derivation_deriv_premise_cake pl p
     | justification_lem => valid_derivation_deriv_lem p
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

Definition valid_proof_entry_list_cake:
  (valid_proof_entry_list_cake el t pl =
    case el of
    | [] => T
    | e :: el' =>
      (case e of
      | entry_derivation (derivation_deriv l p reason_assumption) => F
      | entry_derivation (derivation_deriv l p (reason_justification j)) =>
	if valid_entry_dec_cake t pl e then 
	  valid_proof_entry_list_cake el' (insert t (INL l) (INL p)) pl
	else F
      | entry_box pr => 
	(case pr of 
        | []  => F
	| e' :: _ => 
	    (case e' of
	     | entry_derivation (derivation_deriv l p r) =>
	       (case r of
	       | reason_assumption =>
		 (case LAST_DEFAULT pr entry_invalid of
		  | entry_derivation (derivation_deriv l' p' r') =>
		    if valid_entry_dec_cake t pl e then
		      valid_proof_entry_list_cake el' (insert t (INR (l, l')) (INR (p, p'))) pl
		    else F
		  | _ => F)
	       | reason_justification j => F)
	     | _ => F))
      | entry_invalid => F))
  /\
  (valid_entry_dec_cake t pl e =
    case e of
    | entry_derivation (derivation_deriv l p r) => 
       (case r of 
	| reason_assumption => F
	| reason_justification j => valid_derivation_deriv_cake t pl p r)
     | entry_box [] => F
     | entry_box (e'::el') => 
       (case e' of 
	| entry_derivation (derivation_deriv l p reason_assumption) =>
	  valid_proof_entry_list_cake el' (insert t (INL l) (INL p)) pl
	| entry_derivation (derivation_deriv l p (reason_justification j)) => F
	| _ => F)
     | entry_invalid => F)
Termination
 WF_REL_TAC `measure (\x.
 case x of
 | INL (a,_,_) => entry1_size a
 | INR (_,_,b)  => entry_size b)`
End

Definition valid_proof_dec_cake:
 valid_proof_dec_cake t pl pr = valid_proof_entry_list_cake pr t pl
End

Definition valid_claim_dec_cmp_cake:
 valid_claim_dec_cmp_cake cmp c =
  case c of
  | claim_judgment_proof (judgment_follows pl p) pr =>
    case LAST_DEFAULT pr entry_invalid of
    | entry_derivation (derivation_deriv l p' reason_assumption) => F
    | entry_derivation (derivation_deriv l p' (reason_justification j)) =>
      if p = p' then valid_proof_dec_cake (empty cmp) pl pr else F
    | _ => F
End

Definition valid_claim_dec_cake:
  valid_claim_dec_cake c = valid_claim_dec_cmp_cake dyadic_cmp_num c
End

Definition valid_proof_entry_list_cake_soundness:
  valid_proof_entry_list_cake_soundness el t pl =
   (map_ok t ==> valid_proof_entry_list_cake el t pl = valid_proof_entry_list el (to_fmap t) pl)
End

Definition valid_entry_dec_cake_soundness:
  valid_entry_dec_cake_soundness t pl e =
   (map_ok t ==> valid_entry_dec_cake t pl e = valid_entry_dec (to_fmap t) pl e)
End

Theorem valid_derivation_deriv_premise_eq:
 !pl p. valid_derivation_deriv_premise_cake pl p <=> valid_derivation_deriv_premise pl p
Proof
 rw [valid_derivation_deriv_premise_cake,valid_derivation_deriv_premise,MEMBER_INTRO]
QED

Theorem valid_derivation_deriv_copy_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_copy_cake t l p <=>
   valid_derivation_deriv_copy (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_copy_cake,valid_derivation_deriv_copy] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_andi_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_andi_cake t l1 l2 p <=> 
   valid_derivation_deriv_andi (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_andi_cake,valid_derivation_deriv_andi] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_ande1_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_ande1_cake t l p <=>
   valid_derivation_deriv_ande1 (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_ande1_cake,valid_derivation_deriv_ande1] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_ande2_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_ande2_cake t l p <=>
   valid_derivation_deriv_ande2 (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_ande2_cake,valid_derivation_deriv_ande2] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_ori1_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_ori1_cake t l p <=>
   valid_derivation_deriv_ori1 (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_ori1_cake,valid_derivation_deriv_ori1] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_ori2_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_ori2_cake t l p <=>
   valid_derivation_deriv_ori2 (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_ori2_cake,valid_derivation_deriv_ori2] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_impe_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_impe_cake t l1 l2 p <=>
   valid_derivation_deriv_impe (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_impe_cake,valid_derivation_deriv_impe] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_nege_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_nege_cake t l1 l2 p <=>
   valid_derivation_deriv_nege (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_nege_cake,valid_derivation_deriv_nege] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_conte_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_conte_cake t l <=>
   valid_derivation_deriv_conte (to_fmap t) l)
Proof
 rw [valid_derivation_deriv_conte_cake,valid_derivation_deriv_conte] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_negnegi_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_negnegi_cake t l p <=>
   valid_derivation_deriv_negnegi (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_negnegi_cake,valid_derivation_deriv_negnegi] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_negnege_eq:
 !t l p. map_ok t ==>
  (valid_derivation_deriv_negnege_cake t l p <=>
   valid_derivation_deriv_negnege (to_fmap t) l p)
Proof
 rw [valid_derivation_deriv_negnege_cake,valid_derivation_deriv_negnege] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_mt_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_mt_cake t l1 l2 p <=>
   valid_derivation_deriv_mt (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_mt_cake,valid_derivation_deriv_mt] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_impi_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_impi_cake t l1 l2 p <=>
   valid_derivation_deriv_impi (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_impi_cake,valid_derivation_deriv_impi] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_negi_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_negi_cake t l1 l2 p <=>
   valid_derivation_deriv_negi (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_negi_cake,valid_derivation_deriv_negi] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_ore_eq:
 !t l1 l2 l3 l4 l5 p. map_ok t ==>
  (valid_derivation_deriv_ore_cake t l1 l2 l3 l4 l5 p <=>
   valid_derivation_deriv_ore (to_fmap t) l1 l2 l3 l4 l5 p)
Proof
 rw [valid_derivation_deriv_ore_cake,valid_derivation_deriv_ore] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_pbc_eq:
 !t l1 l2 p. map_ok t ==>
  (valid_derivation_deriv_pbc_cake t l1 l2 p <=>
   valid_derivation_deriv_pbc (to_fmap t) l1 l2 p)
Proof
 rw [valid_derivation_deriv_pbc_cake,valid_derivation_deriv_pbc] \\
 rw [lookup_thm]
QED

Theorem valid_derivation_deriv_eq:
  !t pl l p r. map_ok t ==> 
  (valid_derivation_deriv_cake t pl p r <=> valid_derivation_deriv (to_fmap t) pl p r)
Proof
  rw [valid_derivation_deriv_cake,valid_derivation_deriv] \\
  rw [valid_derivation_deriv_premise_eq] \\
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

Theorem valid_proof_entry_list_entry_cake_sound:
  (!el t pl. valid_proof_entry_list_cake_soundness el t pl) /\
  (!t pl e. valid_entry_dec_cake_soundness t pl e)
Proof
 MATCH_MP_TAC valid_proof_entry_list_cake_ind \\ rw [] >- 
  (rw [valid_proof_entry_list_cake_soundness] \\
   once_rewrite_tac [valid_proof_entry_list_cake,valid_proof_entry_list] \\
   Cases_on `el'` \\ rw [] \\
   Cases_on `h` \\ rw [] >-
    (Cases_on `d` \\ rw [] \\
     Cases_on `r` \\ rw [] \\
     fs [valid_entry_dec_cake_soundness] \\
     fs [valid_proof_entry_list_cake_soundness] \\
     EQ_TAC \\ rw [] >-
      (rw [GSYM insert_thm] \\
       `map_ok (insert t (INL n) (INL p))` by rw [insert_thm] \\
       METIS_TAC []) \\
     rw [insert_thm]) \\
   Cases_on `l` \\ rw [] \\
   Cases_on `h` \\ rw [] \\ Cases_on `d` \\ rw [] \\
   Cases_on `r` \\ rw [] \\ 
   Cases_on `LAST_DEFAULT (entry_derivation (derivation_deriv n p reason_assumption)::t'') entry_invalid` \\ rw [] \\
   Cases_on `d` \\ rw [] \\
   fs [valid_entry_dec_cake_soundness] \\ 
   fs [valid_proof_entry_list_cake_soundness] \\
   METIS_TAC [insert_thm]) \\
 rw [valid_entry_dec_cake_soundness] \\
 once_rewrite_tac [valid_proof_entry_list_cake,valid_proof_entry_list] \\
 Cases_on `e` \\ rw [] >- 
  (Cases_on `d` \\ rw [valid_derivation_deriv_eq]) \\
 Cases_on `l` \\ rw [] \\
 Cases_on `h` \\ rw [] \\ Cases_on `d` \\ rw [] \\
 Cases_on `r` \\ rw [] \\
 fs [valid_proof_entry_list_cake_soundness] \\
 rw [insert_thm]
QED

Theorem valid_proof_entry_list_eq:
 !el t pl. map_ok t ==> 
  (valid_proof_entry_list_cake el t pl <=> valid_proof_entry_list el (to_fmap t) pl)
Proof
 rw [] \\
 `valid_proof_entry_list_cake_soundness el' t pl` suffices_by rw [valid_proof_entry_list_cake_soundness] \\
 rw [valid_proof_entry_list_entry_cake_sound]
QED

Theorem valid_entry_dec_eq:
 !t pl e. map_ok t ==> 
  (valid_entry_dec_cake t pl e <=> valid_entry_dec (to_fmap t) pl e)
Proof
 rw [] \\
 `valid_entry_dec_cake_soundness t pl e` suffices_by rw [valid_entry_dec_cake_soundness] \\
 rw [valid_proof_entry_list_entry_cake_sound]
QED

Theorem valid_proof_dec_eq:
 !t pl pr. map_ok t ==> 
  (valid_proof_dec_cake t pl pr <=> valid_proof_dec (to_fmap t) pl pr)
Proof
 rw [] \\
 rw [valid_proof_dec_cake,valid_proof_dec,valid_proof_entry_list_eq]
QED

Theorem valid_claim_dec_cmp_eq:
  !cmp c. TotOrd cmp ==> (valid_claim_dec_cmp_cake cmp c <=> valid_claim_dec c)
Proof
 rw [] \\
 Cases_on `c` \\ Cases_on `j` \\
 rw [valid_claim_dec_cmp_cake,valid_claim_dec] \\
 Cases_on `LAST_DEFAULT l entry_invalid` \\ rw [] \\
 Cases_on `d` \\ rw [] \\
 Cases_on `r` \\ rw [] \\
 rw [empty_thm,valid_proof_dec_eq]
QED

Theorem valid_claim_dec_cmp_cake_sound:
 !cmp c. TotOrd cmp ==> (valid_claim_dec_cmp_cake cmp c <=> valid_claim c)
Proof
 rw [valid_claim_dec_cmp_eq,valid_claim_dec_sound]
QED

Theorem valid_claim_dec_eq:
  !c. (valid_claim_dec_cake c <=> valid_claim_dec c)
Proof
  rw [valid_claim_dec_cake] \\
  MATCH_MP_TAC valid_claim_dec_cmp_eq \\
  rw [TotOrd_num_cmp]
QED

Theorem valid_claim_dec_cake_sound:
 !c. (valid_claim_dec_cake c <=> valid_claim c)
Proof
 rw [valid_claim_dec_eq,valid_claim_dec_sound]
QED

val _ = export_theory ();
