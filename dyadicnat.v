Require Export OrderedType.
Require Export Structures.OrderedTypeEx.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.

Inductive dyadic {A : Type} : Type :=
| dyadic_t : A -> dyadic
| dyadic_dyad : A -> A -> dyadic.

Inductive dyadic_lt {A : Type} {lt : A -> A -> Prop} : dyadic -> dyadic -> Prop :=
| dyadic_lt_t_t : forall (l l' : A), lt l l' -> dyadic_lt (dyadic_t l) (dyadic_t l')
| dyadic_lt_t_dyad : forall (l l1 l1': A), dyadic_lt (dyadic_t l) (dyadic_dyad l1 l1')
| dyadic_lt_dyad_lt : forall (l0 l0' l1 l1' : A), lt l0 l1 -> dyadic_lt (dyadic_dyad l0 l0') (dyadic_dyad l1 l1')
| dyadic_lt_dyad_eq : forall (l l0' l1' : A), lt l0' l1' -> dyadic_lt (dyadic_dyad l l0') (dyadic_dyad l l1').

Module Type SpecType.
  Parameter t : Type.
End SpecType.

Module Type SpecUsualOrderedType (ST : SpecType) <: UsualOrderedType.
  Definition t := ST.t.
  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Parameter lt : t -> t -> Prop.
  Parameter eq_dec : forall t0 t1 : t, {eq t0 t1}+{~ eq t0 t1}.
  Parameter lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y, lt x y -> x <> y.
  Parameter compare : forall x y, Compare lt eq x y.
End SpecUsualOrderedType.

Module Type DyadicSpecType (ST : SpecType) <: SpecType.
  Definition t := @dyadic ST.t.
End DyadicSpecType.

Module DyadicSpec (ST : SpecType) <: DyadicSpecType ST.
  Definition t := @dyadic ST.t.
End DyadicSpec.

Module SpecDyadicUsualOrderedType 
  (ST : SpecType) (SUOT : SpecUsualOrderedType ST)
  (DST : DyadicSpecType ST) <: SpecUsualOrderedType DST.
  Definition t := @dyadic SUOT.t.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec : forall t0 t1 : t, {t0 = t1}+{t0 <> t1}.
    decide equality; auto using SUOT.eq_dec.
  Defined.

  Definition lt := @dyadic_lt _ SUOT.lt.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
  move => x y z H_xy H_yz.
  inversion H_xy; subst.
  - inversion H_yz; subst.
    * by apply dyadic_lt_t_t; apply SUOT.lt_trans with (y := l').
    * by apply dyadic_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lt_t_dyad.
    * by apply dyadic_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lt_dyad_lt; apply SUOT.lt_trans with (y := l1).
    * by apply dyadic_lt_dyad_lt.
  - inversion H_yz; subst.
    * by apply dyadic_lt_dyad_lt.
    * by apply dyadic_lt_dyad_eq; apply SUOT.lt_trans with (y := l1').
  Qed.

  Theorem lt_not_eq : forall x y, lt x y -> x <> y.
  Proof.
  move => x y H_xy; inversion H_xy; subst => H_neq.
  - injection H_neq => H_eq.
    subst.
    apply SUOT.lt_not_eq in H.
    by unfold SUOT.eq in H.
  - by [].
  - injection H_neq => H_eq1 H_eq2.
    subst.
    apply SUOT.lt_not_eq in H.
    by unfold SUOT.eq in H.
  - injection H_neq => H_eq.
    subst.
    apply SUOT.lt_not_eq in H.
    by unfold SUOT.eq in H.
  Qed.

  Definition compare (x y : t) : Compare lt eq x y.
  refine
  (match x as x0, y as y0 return (x = x0 -> y = y0 -> _) with
   | dyadic_t l0, dyadic_t l1 => 
     fun (H_eq : _) (H_eq' : _) => 
     match SUOT.compare l0 l1 with
     | LT H_cmp => LT _
     | EQ H_cmp => EQ _
     | GT H_cmp => GT _
     end
   | dyadic_t l0, dyadic_dyad l1 l1' => fun (H_eq : _) (H_eq' : _) => LT _
   | dyadic_dyad l0 l0', dyadic_t l1 => fun (H_eq : _) (H_eq' : _) => GT _
   | dyadic_dyad l0 l0', dyadic_dyad l1 l1' => fun (H_eq : _) (H_eq' : _) =>
     match SUOT.compare l0 l1 with
     | LT H_cmp => LT _
     | EQ H_cmp =>
       match SUOT.compare l0' l1' with
       | LT H_cmp' => LT _
       | EQ H_cmp' => EQ _
       | GT H_cmp' => GT _
       end
     | GT H_cmp => GT _
     end
   end (refl_equal _) (refl_equal _)); rewrite H_eq H_eq'.
  - exact: dyadic_lt_t_t.
  - by rewrite H_cmp.
  - exact: dyadic_lt_t_t.
  - exact: dyadic_lt_t_dyad.
  - exact: dyadic_lt_t_dyad.
  - exact: dyadic_lt_dyad_lt.
  - rewrite H_cmp.
    exact: dyadic_lt_dyad_eq.
  - by rewrite H_cmp H_cmp'.
  - rewrite H_cmp.
    exact: dyadic_lt_dyad_eq.
  - exact: dyadic_lt_dyad_lt.
  Defined.
End SpecDyadicUsualOrderedType.

(*
Require Import FMapList.
Module NatSpecType <: SpecType. Definition t := nat. End NatSpecType.
Module NatSpecUsualOrderedType <: SpecUsualOrderedType NatSpecType := Nat_as_OT.
Module NatDyadicSpec := DyadicSpec NatSpecType.
Module NatDyadicSpecUsualOrderedType := SpecDyadicUsualOrderedType NatSpecType NatSpecUsualOrderedType NatDyadicSpec.
Module Map := FMapList.Make NatDyadicSpecUsualOrderedType.
Import Map.
Eval compute in Map.find (dyadic_dyad 5 3) (Map.add (dyadic_dyad 5 3) 2 (Map.empty nat)).
*)
