Require Export OrderedType.
Require Export Structures.OrderedTypeEx.
Require Import mathcomp.ssreflect.ssreflect.
Require Import Omega.

Definition dyadic {A : Type} : Type := A + (A * A).

Inductive dyadic_lt {A : Type} {lt : A -> A -> Prop} : dyadic -> dyadic -> Prop :=
| dyadic_lt_t_t : forall (l l' : A), lt l l' -> dyadic_lt (inl l) (inl l')
| dyadic_lt_t_dyad : forall (l l1 l1': A), dyadic_lt (inl l) (inr (l1, l1'))
| dyadic_lt_dyad_lt : forall (l0 l0' l1 l1' : A), lt l0 l1 -> dyadic_lt (inr (l0, l0')) (inr (l1, l1'))
| dyadic_lt_dyad_eq : forall (l l0' l1' : A), lt l0' l1' -> dyadic_lt (inr (l, l0')) (inr (l, l1')).

Module Type DyadicUsualOrderedType (UOT : UsualOrderedType) <: UsualOrderedType.
  Definition t := @dyadic UOT.t.
  Definition eq := @eq t.
  Parameter Inline lt : t -> t -> Prop.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.
  Parameter lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Parameter lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Parameter compare : forall x y : t, Compare lt eq x y.
  Parameter eq_dec : forall x y : t, { eq x y } + { ~ eq x y }.
End DyadicUsualOrderedType.

Module LexDyadicUsualOrderedType (UOT : UsualOrderedType) <: DyadicUsualOrderedType UOT.
  Definition t := @dyadic UOT.t.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec : forall t0 t1 : t, {t0 = t1}+{t0 <> t1}.
    decide equality; auto using UOT.eq_dec.
    destruct b, p.
    decide equality; auto using UOT.eq_dec.
  Defined.

  Definition lt := @dyadic_lt _ UOT.lt.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
  move => x y z H_xy H_yz.
  inversion H_xy; subst.
  - inversion H_yz; subst.
    * by apply dyadic_lt_t_t; apply UOT.lt_trans with (y := l').
    * by apply dyadic_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lt_t_dyad.
    * by apply dyadic_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lt_dyad_lt; apply UOT.lt_trans with (y := l1).
    * by apply dyadic_lt_dyad_lt.
  - inversion H_yz; subst.
    * by apply dyadic_lt_dyad_lt.
    * by apply dyadic_lt_dyad_eq; apply UOT.lt_trans with (y := l1').
  Qed.

  Theorem lt_not_eq : forall x y, lt x y -> x <> y.
  Proof.
  move => x y H_xy; inversion H_xy; subst => H_neq.
  - injection H_neq => H_eq.
    subst.
    apply UOT.lt_not_eq in H.
    by unfold UOT.eq in H.
  - by [].
  - injection H_neq => H_eq1 H_eq2.
    subst.
    apply UOT.lt_not_eq in H.
    by unfold UOT.eq in H.
  - injection H_neq => H_eq.
    subst.
    apply UOT.lt_not_eq in H.
    by unfold UOT.eq in H.
  Qed.

  Definition compare (x y : t) : Compare lt eq x y.
  refine
  (match x as x0, y as y0 return (x = x0 -> y = y0 -> _) with
   | inl l0, inl l1 =>
     fun (H_eq : _) (H_eq' : _) => 
     match UOT.compare l0 l1 with
     | LT H_cmp => LT _
     | EQ H_cmp => EQ _
     | GT H_cmp => GT _
     end
   | inl l0, inr (l1, l1') => fun (H_eq : _) (H_eq' : _) => LT _
   | inr (l0, l0'), inl l1 => fun (H_eq : _) (H_eq' : _) => GT _
   | inr (l0, l0'), inr (l1, l1') => fun (H_eq : _) (H_eq' : _) =>
     match UOT.compare l0 l1 with
     | LT H_cmp => LT _
     | EQ H_cmp =>
       match UOT.compare l0' l1' with
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
End LexDyadicUsualOrderedType.

(*
Require Import FMapList.
Module NatDyadicUsualOrderedType <: DyadicUsualOrderedType Nat_as_OT := LexDyadicUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := NatDyadicUsualOrderedType := FMapList.Make NatDyadicUsualOrderedType.
Eval compute in Map.find (inr (5, 3)) (Map.add (inr (5, 3)) 2 (Map.empty nat)).
*)
