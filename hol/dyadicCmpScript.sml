open HolKernel boolLib Parse bossLib
 totoTheory comparisonTheory;

val _ = new_theory "dyadicCmp";

Definition dyadic_cmp:
  dyadic_cmp (cmp: 'a comp) =
   \x y.
    case x, y of
    | INL l, INL j => 
      (case cmp l j of
      | LESS => LESS
      | EQUAL => EQUAL
      | GREATER => GREATER)
    | INL _, INR _ => LESS
    | INR _, INL _ => GREATER
    | INR (l, l'), INR (j, j') =>
      (case cmp l j of
       | LESS => LESS
       | EQUAL =>
	 (case cmp l' j' of
	  | LESS => LESS
	  | EQUAL => EQUAL
	  | GREATER => GREATER)   
       | GREATER => GREATER)
End

Theorem TotOrd_dyadic_cmp:
  !cmp. TotOrd cmp ==> TotOrd (dyadic_cmp cmp)
Proof
 rw [dyadic_cmp] >> once_rewrite_tac [TotOrd] >> rw [] >| [

  Cases_on `x` >> rw [] >-
   (Cases_on `y` >> rw [] >>
    Cases_on `cmp x' x` >> rw [] >>
    Cases_on `x' = x` >> fs[TotOrd,all_cpn_distinct] >>
    `cmp x x = EQUAL` by fs[TotOrd] >>
    fs [all_cpn_distinct] >> METIS_TAC []) >>  
  Cases_on `y` >> rw [] >> Cases_on `y''` >> rw [] >>
  Cases_on `y'` >> rw [] >>   Cases_on `cmp q' q` >> rw [] >>
  Cases_on `q' = q` >> fs[TotOrd] >>
  `cmp q q = EQUAL` by fs[TotOrd] >>
  fs [all_cpn_distinct] >-
   (Cases_on `cmp r' r` >> rw [] >>
    Cases_on `r' = r` >> fs[TotOrd] >>
    `cmp r r = EQUAL` by fs[TotOrd] >>
    fs [all_cpn_distinct] >> METIS_TAC []) >>
  Cases_on `q' = q` >> rw [] >>
  `cmp q q = EQUAL` by fs[TotOrd] >>
  fs [all_cpn_distinct] >> METIS_TAC [],

  Cases_on `x` >> rw [] >-
   (Cases_on `y` >> rw [] >>
    Cases_on `cmp x' x` >> rw [] >> Cases_on `cmp x x'` >> rw [] >>
    fs [TotOrd] >>
    METIS_TAC [all_cpn_distinct]) >>
  Cases_on `y` >> rw [] >>
  Cases_on `y''` >> rw [] >>
  Cases_on `y'` >> rw [] >>
  Cases_on `cmp q' q` >> rw [] >> Cases_on `cmp q q'` >> rw [] >>
  Cases_on `cmp r' r` >> rw [] >> Cases_on `cmp r r'` >> rw [] >>
  fs [TotOrd] >> METIS_TAC [all_cpn_distinct],

  Cases_on `x` >> rw [] >> Cases_on `y` >> rw [] >> Cases_on `z` >> fs [] >-
   (Cases_on `cmp x' x` >> Cases_on `cmp x x''` >> Cases_on `cmp x' x''` >> fs [TotOrd] >>
    METIS_TAC [all_cpn_distinct]) >>
  Cases_on `y` >> Cases_on `y'` >> fs [] >> Cases_on `y''` >> fs [] >>
  Cases_on `cmp q' q''` >> Cases_on `cmp q'' q` >> Cases_on `cmp q' q` >> 
  Cases_on `cmp r' r''` >> Cases_on `cmp r'' r` >> Cases_on `cmp r' r` >> fs [TotOrd] >>
  METIS_TAC [all_cpn_distinct]
 ]
QED

Definition dyadic_cmp_num:
  dyadic_cmp_num = dyadic_cmp num_cmp
End

Theorem TotOrd_num_cmp:
 TotOrd dyadic_cmp_num
Proof
 rw [dyadic_cmp_num] >>
 MATCH_MP_TAC TotOrd_dyadic_cmp >>
 rw [num_cmp_numOrd] >>
 rw [TO_numOrd]
QED

val _ = export_theory();
