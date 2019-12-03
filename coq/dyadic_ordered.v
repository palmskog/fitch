Require Export OrderedType.
Require Export Structures.OrderedTypeEx.
Require Import Fitch.ssrexport.

Definition dyadic {A : Type} : Type := A + (A * A).

Inductive dyadic_lex_lt {A : Type} {lt : A -> A -> Prop} : dyadic -> dyadic -> Prop :=
| dyadic_lex_lt_t_t : forall (l l' : A), lt l l' -> dyadic_lex_lt (inl l) (inl l')
| dyadic_lex_lt_t_dyad : forall (l l1 l1': A), dyadic_lex_lt (inl l) (inr (l1, l1'))
| dyadic_lex_lt_dyad_lt : forall (l0 l0' l1 l1' : A), lt l0 l1 -> dyadic_lex_lt (inr (l0, l0')) (inr (l1, l1'))
| dyadic_lex_lt_dyad_eq : forall (l l0' l1' : A), lt l0' l1' -> dyadic_lex_lt (inr (l, l0')) (inr (l, l1')).

Section DyadicFun.

Variable A : Type.
Variable A_eq_dec : forall (a a' : A), {a = a'}+{a <> a'}.
Variable A_lt : A -> A -> Prop.
Variable A_compare : forall x y : A, Compare A_lt eq x y.

Program Definition dyadic_eq_dec (d d' : @dyadic A) : {d = d'}+{d <> d'} :=
  match d, d' with
  | inl a, inl a' =>
    match A_eq_dec a a' with
    | left H_dec => left _
    | right H_dec => right _
    end
  | inl _, inr _ => right _
  | inr _, inl _ => right _
  | inr (a0, a1), inr (a'0, a'1) =>
    match A_eq_dec a0 a'0, A_eq_dec a1 a'1 with
    | left H_dec, left H_dec' => left _
    | left H_dec, right H_dec' => right _
    | right H_dec, left H_dec' => right _
    | right H_dec, right H_dec' => right _
    end
  end.

Program Definition dyadic_compare (x y : @dyadic A) : Compare (@dyadic_lex_lt A A_lt) eq x y :=
  match x, y with
  | inl l0, inl l1 =>
    match A_compare l0 l1 with
    | LT H_cmp => LT _
    | EQ H_cmp => EQ _
    | GT H_cmp => GT _
    end
  | inl l0, inr (l1, l1') => LT _
  | inr (l0, l0'), inl l1 => GT _
  | inr (l0, l0'), inr (l1, l1') =>
    match A_compare l0 l1 with
    | LT H_cmp => LT _
    | EQ H_cmp =>
      match A_compare l0' l1' with
      | LT H_cmp' => LT _
      | EQ H_cmp' => EQ _
      | GT H_cmp' => GT _
      end
    | GT H_cmp => GT _
    end
  end.
Next Obligation.
exact: dyadic_lex_lt_t_t.
Qed.
Next Obligation.
exact: dyadic_lex_lt_t_t.
Qed.
Next Obligation.
exact: dyadic_lex_lt_t_dyad.
Qed.
Next Obligation.
exact: dyadic_lex_lt_t_dyad.
Qed.
Next Obligation.
exact: dyadic_lex_lt_dyad_lt.
Qed.
Next Obligation.
exact: dyadic_lex_lt_dyad_eq.
Qed.
Next Obligation.
exact: dyadic_lex_lt_dyad_eq.
Qed.
Next Obligation.
exact: dyadic_lex_lt_dyad_lt.
Qed.

End DyadicFun.

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

Module DyadicLexLtUsualOrderedType (UOT : UsualOrderedType) <: DyadicUsualOrderedType UOT.
  Definition t := @dyadic UOT.t.

  Definition eq := @eq t.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Definition eq_dec := dyadic_eq_dec UOT.t UOT.eq_dec.

  Definition lt := @dyadic_lex_lt UOT.t UOT.lt.

  Theorem lt_trans : forall x y z, lt x y -> lt y z -> lt x z.
  Proof.
  move => x y z H_xy H_yz.
  inversion H_xy; subst.
  - inversion H_yz; subst.
    * by apply dyadic_lex_lt_t_t; apply UOT.lt_trans with (y := l').
    * by apply dyadic_lex_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lex_lt_t_dyad.
    * by apply dyadic_lex_lt_t_dyad.
  - inversion H_yz; subst.
    * by apply dyadic_lex_lt_dyad_lt; apply UOT.lt_trans with (y := l1).
    * by apply dyadic_lex_lt_dyad_lt.
  - inversion H_yz; subst.
    * by apply dyadic_lex_lt_dyad_lt.
    * by apply dyadic_lex_lt_dyad_eq; apply UOT.lt_trans with (y := l1').
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

  Definition compare := dyadic_compare UOT.t UOT.lt UOT.compare.
End DyadicLexLtUsualOrderedType.

(*
Require Import FMapList.
Module NatDyadicUsualOrderedType <: DyadicUsualOrderedType Nat_as_OT := DyadicLexLtUsualOrderedType Nat_as_OT.
Module Map <: FMapInterface.S with Module E := NatDyadicUsualOrderedType := FMapList.Make NatDyadicUsualOrderedType.
Eval compute in Map.find (inr (5, 3)) (Map.add (inr (5, 3)) 2 (Map.empty nat)).
*)
