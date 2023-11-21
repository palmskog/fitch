(* generated by Ott 0.33 from: ../ott/fitch.ott *)
(* to compile: Holmake fitchTheory.uo   *)
(* for interactive use:
  app load ["pred_setTheory","finite_mapTheory","stringTheory","containerTheory","ottLib"];
*)

open HolKernel boolLib Parse bossLib ottLib;
infix THEN THENC |-> ## ;
local open arithmeticTheory stringTheory containerTheory pred_setTheory listTheory 
  finite_mapTheory in end;

val _ = new_theory "fitch";


val _ = type_abbrev("p", ``:string``); (* atomic proposition *)
val _ = type_abbrev("l", ``:num``); (* proof entry label *)
val _ = type_abbrev("n", ``:num``); (* index variable (subscript) *)
val _ = Hol_datatype ` 
justification =  (* derivation justification *)
   justification_premise (* premise *)
 | justification_lem (* law of excluded middle *)
 | justification_copy of l (* copying *)
 | justification_andi of l => l (* conjunction introduction *)
 | justification_ande1 of l (* conjunction elimination *)
 | justification_ande2 of l (* conjunction elimination *)
 | justification_ori1 of l (* disjunction introduction *)
 | justification_ori2 of l (* disjunction introduction *)
 | justification_impe of l => l (* implication elimination *)
 | justification_nege of l => l (* negation elimination *)
 | justification_conte of l (* contradiction elimination *)
 | justification_negnegi of l (* double negation introduction *)
 | justification_negnege of l (* double negation elimination *)
 | justification_mt of l => l (* modus tollens *)
 | justification_impi of l => l (* implication introduction *)
 | justification_negi of l => l (* negation introduction *)
 | justification_ore of l => l => l => l => l (* disjunction elimination *)
 | justification_pbc of l => l (* proof by contraduction *)
`;
val _ = Hol_datatype ` 
reason = 
   reason_assumption
 | reason_justification of justification
`;
val _ = Hol_datatype ` 
prop =  (* proposition *)
   prop_p of p (* atomic *)
 | prop_neg of prop (* negation *)
 | prop_and of prop => prop (* conjunction *)
 | prop_or of prop => prop (* disjunction *)
 | prop_imp of prop => prop (* implication *)
 | prop_cont (* contradiction *)
`;
val _ = Hol_datatype ` 
derivation =  (* derivation in proof *)
   derivation_deriv of l => prop => reason
`;
val _ = Hol_datatype ` 
entry =  (* proof entry *)
   entry_derivation of derivation (* line *)
 | entry_box of entry list (* box *)
 | entry_invalid
`;
val _ = type_abbrev("proplist", ``:prop list``);
val _ = type_abbrev("proof", ``:entry list``);
val _ = Hol_datatype ` 
judgment =  (* judgment *)
   judgment_follows of proplist => prop
`;
val _ = Hol_datatype ` 
claim =  (* claim *)
   claim_judgment_proof of judgment => proof
`;
val _ = type_abbrev("G", ``:((num + (num # num)) |-> (prop + (prop # prop)))``);
val _ = type_abbrev("dyadicprop", ``:(prop + (prop # prop))``);
Definition LAST_DEFAULT:
 (LAST_DEFAULT [] default = default) /\
 (LAST_DEFAULT (e::el) default = LAST (e::el))
End

(** definitions *)
(* defns validity *)

val (validity_rules, validity_ind, validity_cases) = Hol_reln`
(* defn valid_claim *)

( (* vc_claim *) ! (proplist:proplist) (prop:prop) (proof:proof) (l:l) (justification:justification) . (clause_name "vc_claim") /\
((  (LAST_DEFAULT ( proof ) entry_invalid)   =  (entry_derivation (derivation_deriv l prop (reason_justification justification))) ) /\
( ( valid_proof  FEMPTY  proplist proof )))
 ==> 
( ( valid_claim (claim_judgment_proof (judgment_follows proplist prop) proof) )))

/\(* defn valid_proof *)

( (* vp_empty *) ! (G:G) (proplist:proplist) . (clause_name "vp_empty") ==> 
( ( valid_proof G proplist  []  )))

/\ ( (* vp_derivation *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (justification:justification) (proof:proof) . (clause_name "vp_derivation") /\
(( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification justification)) )) /\
( ( valid_proof  (FUPDATE  G  (INL  l , INL  prop ))  proplist proof )))
 ==> 
( ( valid_proof G proplist  ( (entry_derivation (derivation_deriv l prop (reason_justification justification)))  ::  proof )  )))

/\ ( (* vp_box *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (proof:proof) (proof':proof) (l':l) (prop':prop) (reason:reason) . (clause_name "vp_box") /\
((  (LAST_DEFAULT (  ( (entry_derivation (derivation_deriv l prop reason_assumption))  ::  proof )  ) entry_invalid)   =  (entry_derivation (derivation_deriv l' prop' reason)) ) /\
( ( valid_proof  (FUPDATE  G  (INL  l , INL  prop ))  proplist proof )) /\
( ( valid_proof  (FUPDATE  G  (INR ( l ,  l' ), INR ( prop ,  prop' )))  proplist proof' )))
 ==> 
( ( valid_proof G proplist  (  (entry_box   ( (entry_derivation (derivation_deriv l prop reason_assumption))  ::  proof )  )   ::  proof' )  )))

/\(* defn valid_derivation *)

( (* vd_premise *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) . (clause_name "vd_premise") /\
(( (MEM  prop   proplist ) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification justification_premise)) )))

/\ ( (* vd_lem *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) . (clause_name "vd_lem") ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_or prop (prop_neg prop)) (reason_justification justification_lem)) )))

/\ ( (* vd_copy *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) . (clause_name "vd_copy") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  prop )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_copy l'))) )))

/\ ( (* vd_conte *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) . (clause_name "vd_conte") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  prop_cont )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_conte l'))) )))

/\ ( (* vd_andi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l1:l) (l2:l) . (clause_name "vd_andi") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  prop )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  prop' )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_and prop prop') (reason_justification (justification_andi l1 l2))) )))

/\ ( (* vd_ande1 *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) (prop':prop) . (clause_name "vd_ande1") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  (prop_and prop prop') )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_ande1 l'))) )))

/\ ( (* vd_ande2 *) ! (G:G) (proplist:proplist) (l:l) (prop':prop) (l':l) (prop:prop) . (clause_name "vd_ande2") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  (prop_and prop prop') )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop' (reason_justification (justification_ande2 l'))) )))

/\ ( (* vd_ori1 *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l':l) . (clause_name "vd_ori1") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  prop )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_or prop prop') (reason_justification (justification_ori1 l'))) )))

/\ ( (* vd_ori2 *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l':l) . (clause_name "vd_ori2") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  prop' )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_or prop prop') (reason_justification (justification_ori2 l'))) )))

/\ ( (* vd_impe *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l1:l) (l2:l) (prop':prop) . (clause_name "vd_impe") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  prop' )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  (prop_imp prop' prop) )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_impe l1 l2))) )))

/\ ( (* vd_negnegi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) . (clause_name "vd_negnegi") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  prop )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_neg (prop_neg prop)) (reason_justification (justification_negnegi l'))) )))

/\ ( (* vd_negnege *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l':l) . (clause_name "vd_negnege") /\
(( (FLOOKUP  G  (INL  l' ) = SOME (INL  (prop_neg (prop_neg prop)) )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_negnege l'))) )))

/\ ( (* vd_mt *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l1:l) (l2:l) (prop':prop) . (clause_name "vd_mt") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  (prop_imp prop prop') )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  (prop_neg prop') )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_neg prop) (reason_justification (justification_mt l1 l2))) )))

/\ ( (* vd_nege *) ! (G:G) (proplist:proplist) (l:l) (l1:l) (l2:l) (prop:prop) . (clause_name "vd_nege") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  prop )) ) /\
( (FLOOKUP  G  (INL  l2 ) = SOME (INL  (prop_neg prop) )) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop_cont (reason_justification (justification_nege l1 l2))) )))

/\ ( (* vd_impi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (prop':prop) (l1:l) (l2:l) . (clause_name "vd_impi") /\
(( (FLOOKUP  G  (INR ( l1 ,  l2 )) = SOME (INR ( prop ,  prop' ))) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_imp prop prop') (reason_justification (justification_impi l1 l2))) )))

/\ ( (* vd_negi *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l1:l) (l2:l) . (clause_name "vd_negi") /\
(( (FLOOKUP  G  (INR ( l1 ,  l2 )) = SOME (INR ( prop ,  prop_cont ))) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l (prop_neg prop) (reason_justification (justification_negi l1 l2))) )))

/\ ( (* vd_ore *) ! (G:G) (proplist:proplist) (l:l) (prop'':prop) (l1:l) (l2:l) (l3:l) (l4:l) (l5:l) (prop:prop) (prop':prop) . (clause_name "vd_ore") /\
(( (FLOOKUP  G  (INL  l1 ) = SOME (INL  (prop_or prop prop') )) ) /\
( (FLOOKUP  G  (INR ( l2 ,  l3 )) = SOME (INR ( prop ,  prop'' ))) ) /\
( (FLOOKUP  G  (INR ( l4 ,  l5 )) = SOME (INR ( prop' ,  prop'' ))) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop'' (reason_justification (justification_ore l1 l2 l3 l4 l5))) )))

/\ ( (* vd_pbc *) ! (G:G) (proplist:proplist) (l:l) (prop:prop) (l1:l) (l2:l) . (clause_name "vd_pbc") /\
(( (FLOOKUP  G  (INR ( l1 ,  l2 )) = SOME (INR ( (prop_neg prop) ,  prop_cont ))) ))
 ==> 
( ( valid_derivation G proplist (derivation_deriv l prop (reason_justification (justification_pbc l1 l2))) )))

`;

val _ = export_theory ();


