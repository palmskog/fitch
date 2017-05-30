Require Export OrderedType.
Require Export OrderedTypeEx.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.

Inductive dyadicnat : Set :=
| dyadicnat_nat : nat -> dyadicnat
| dyadicnat_dyad : nat -> nat -> dyadicnat.

Definition dyadicnat_eq_dec : forall d d' : dyadicnat, { d = d' }+{ d <> d' }.
decide equality; auto with arith.
Defined.

Inductive dyadicnat_lt : dyadicnat -> dyadicnat -> Prop :=
| dyadicnat_lt_nat_nat : forall (l l' : nat), l < l' -> dyadicnat_lt (dyadicnat_nat l) (dyadicnat_nat l')
| dyadicnat_lt_nat_dyad : forall (l l1 l1': nat), dyadicnat_lt (dyadicnat_nat l) (dyadicnat_dyad l1 l1')
| dyadicnat_lt_dyad_lt : forall (l0 l0' l1 l1' : nat), l0 < l1 -> dyadicnat_lt (dyadicnat_dyad l0 l0') (dyadicnat_dyad l1 l1')
| dyadicnat_lt_dyad_eq : forall (l l0' l1' : nat), l0' < l1' -> dyadicnat_lt (dyadicnat_dyad l l0') (dyadicnat_dyad l l1').

Theorem dyadicnat_lt_trans : forall x y z, dyadicnat_lt x y -> dyadicnat_lt y z -> dyadicnat_lt x z.
Proof.
move => x y z H_xy H_yz.
inversion H_xy; subst.
- inversion H_yz; subst.
  * by apply dyadicnat_lt_nat_nat; apply lt_trans with (m := l').
  * by apply dyadicnat_lt_nat_dyad.
- inversion H_yz; subst.
  * by apply dyadicnat_lt_nat_dyad.
  * by apply dyadicnat_lt_nat_dyad.
- inversion H_yz; subst.
  * by apply dyadicnat_lt_dyad_lt; apply lt_trans with (m := l1).
  * by apply dyadicnat_lt_dyad_lt.
- inversion H_yz; subst.
  * by apply dyadicnat_lt_dyad_lt.
  * by apply dyadicnat_lt_dyad_eq; apply lt_trans with (m := l1').
Qed.

Theorem dyadicnat_lt_not_eq : forall x y, dyadicnat_lt x y -> x <> y.
Proof.
move => x y H_xy; inversion H_xy; subst => H_neq.
- injection H_neq => H_eq.
  by omega.
- by [].
- injection H_neq => H_eq1 H_eq2.
  by omega.
- injection H_neq => H_eq.
  by omega.
Qed.


Definition compare_dyadicnat (x y : dyadicnat) : Compare dyadicnat_lt eq x y.
refine
  (match x as x0, y as y0 return (x = x0 -> y = y0 -> _) with
   | dyadicnat_nat l0, dyadicnat_nat l1 => fun (H_eq : _) (H_eq' : _) => 
     match lt_eq_lt_dec l0 l1 with
     | inleft (left H_dec) => LT _
     | inleft (right H_dec) => EQ _
     | inright H_dec => GT _
     end
   | dyadicnat_nat l0, dyadicnat_dyad l1 l1' => fun (H_eq : _) (H_eq' : _) => LT _
   | dyadicnat_dyad l0 l0', dyadicnat_nat l1 => fun (H_eq : _) (H_eq' : _) => GT _
   | dyadicnat_dyad l0 l0', dyadicnat_dyad l1 l1' => fun (H_eq : _) (H_eq' : _) =>
     match lt_eq_lt_dec l0 l1 with
     | inleft (left H_dec) => LT _
     | inleft (right H_dec) => 
       match lt_eq_lt_dec l0' l1' with
       | inleft (left H_dec') => LT _
       | inleft (right H_dec') => EQ _
       | inright H_dec' => GT _
       end
     | inright H_dec => GT _
     end
   end (refl_equal _) (refl_equal _)); rewrite H_eq H_eq'.
- exact: dyadicnat_lt_nat_nat.
- by rewrite H_dec.
- exact: dyadicnat_lt_nat_nat.
- exact: dyadicnat_lt_nat_dyad.
- exact: dyadicnat_lt_nat_dyad.
- exact: dyadicnat_lt_dyad_lt.
- rewrite H_dec.
  exact: dyadicnat_lt_dyad_eq.
- by rewrite H_dec H_dec'.
- rewrite H_dec.
  exact: dyadicnat_lt_dyad_eq.
- exact: dyadicnat_lt_dyad_lt.
Defined.

Module dyadicnat_as_OT <: OrderedType.
Definition t := dyadicnat.
Definition eq := eq (A := dyadicnat).
Definition lt := dyadicnat_lt.
Definition eq_refl := @eq_refl dyadicnat.
Definition eq_sym := eq_sym (A := dyadicnat).
Definition eq_trans := eq_trans (A := dyadicnat).
Definition lt_trans := dyadicnat_lt_trans.
Definition lt_not_eq := dyadicnat_lt_not_eq.
Definition compare := compare_dyadicnat.
Definition eq_dec := dyadicnat_eq_dec.
End dyadicnat_as_OT.

(*
Require Import FMapList.
Module Map <: FMapInterface.S := FMapList.Make dyadicnat_as_OT.
Eval compute in Map.find (dyadicnat_dyad 5 3) (Map.add (dyadicnat_dyad 5 3) 2 (Map.empty nat)).
*)

