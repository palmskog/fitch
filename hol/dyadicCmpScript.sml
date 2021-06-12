open HolKernel boolLib Parse bossLib totoTheory comparisonTheory;

val _ = new_theory "dyadicCmp";

Definition dyadic_cmp:
 dyadic_cmp (cmp:'a comp) (x:'a+'a#'a) (y:'a+'a#'a) =
  case x of
  | INL l =>
    (case y of
    | INL j => cmp l j
    | INR (l,l') => LESS)
  | INR (l,l') =>
    (case y of
    | INL j => GREATER      
    | INR (j,j') =>
      (case cmp l j of
       | LESS => LESS
       | EQUAL => cmp l' j'
       | GREATER => GREATER))
End

Theorem TotOrd_dyadic_cmp:
 !cmp. TotOrd cmp ==> TotOrd (dyadic_cmp cmp)
Proof
 rw [dyadic_cmp] >> once_rewrite_tac [TotOrd] >> rw [] >| [
  Cases_on `x` >> rw [dyadic_cmp] >-
   (Cases_on `y` >> rw [] >>
    Cases_on `cmp x' x` >> rw [] >>
    Cases_on `x' = x` >> fs[TotOrd,all_cpn_distinct] >>
    `cmp x x = EQUAL` by fs[TotOrd] >>
    fs [all_cpn_distinct] >> METIS_TAC []) >>
  Cases_on `y` >> rw [] >> Cases_on `y'` >> rw [] >>
  Cases_on `y''` >> rw [] >>   Cases_on `cmp q q'` >> rw [] >>
  Cases_on `q = q'` >> fs [TotOrd] >> rw [] >>
  `cmp q q = EQUAL` by fs [TotOrd] >>
  fs [all_cpn_distinct] >>
  METIS_TAC [],

  Cases_on `x` >> rw [dyadic_cmp] >-
   (Cases_on `y` >> rw [] >-
     (Cases_on `cmp x' x` >> rw [] >> Cases_on `cmp x x'` >> rw [] >>
      fs [TotOrd] >> METIS_TAC [all_cpn_distinct]) >>
    Cases_on `y'` >> fs []) >>
  Cases_on `y'` >> rw [] >>
  Cases_on `y` >> rw [] >>
  Cases_on `y'` >> rw [] >>
  Cases_on `cmp q q'` >> rw [] >> Cases_on `cmp q' q` >> rw [] >>
  fs [TotOrd] >> METIS_TAC [all_cpn_distinct],

  Cases_on `x` >> fs [dyadic_cmp] >>
  Cases_on `y` >> fs [] >>
  Cases_on `z` >> fs [] >- (fs [TotOrd] >> METIS_TAC []) >>
  Cases_on `y'` >> fs [] >> Cases_on `y''` >> fs [] >>
  Cases_on `y` >> fs [] >>
  Cases_on `cmp q q'` >>
  Cases_on `cmp q q''` >>
  Cases_on `cmp q' q''` >>
  fs [TotOrd] >>
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

val _ = export_theory ();
