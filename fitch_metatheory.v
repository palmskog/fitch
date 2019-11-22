Require Import Fitch.fitch.
Require Import List.
Require Import FMapFacts.
Require Import Classical.
Require Import mathcomp.ssreflect.ssreflect.

Module FitchPropMetatheory
 (UOT : UsualOrderedType) (DUOT : DyadicUsualOrderedType UOT)
 (Map : FMapInterface.S with Module E := DUOT).

Module PI <: PropInterpretation.
Definition A := Prop.
End PI.

Module FitchProp := Fitch PI UOT DUOT Map.
Export FitchProp.

Fixpoint prop_of (p : prop) : Prop :=
  match p with
  | prop_p P => P
  | prop_neg p' => ~ prop_of p'
  | prop_and p1 p2 => (prop_of p1) /\ (prop_of p2)
  | prop_or p1 p2 => (prop_of p1) \/ (prop_of p2)
  | prop_imp p1 p2 => (prop_of p1) -> (prop_of p2)
  | prop_cont => False
  end.

Module MapFacts := Facts Map.

Definition premises_admitted (proplist5 : proplist) : Prop :=
  forall (prop6 : prop), 
    In prop6 proplist5 -> 
    prop_of prop6.

Definition map_line_admitted (G5 : G) : Prop :=
  forall (l6 : l) (prop6 : prop), 
    Map.find (inl l6) G5 = Some (inl prop6) -> 
    prop_of prop6.

Definition map_box_admitted (G5 : G) : Prop :=
  forall (l6 l7 : l) (prop6 prop7 : prop), 
    Map.find (inr (l6, l7)) G5 = Some (inr (prop6, prop7)) -> 
    (prop_of prop6 -> prop_of prop7).

Section Derivations.

Variables (G5 : G) (proplist5 : proplist) (prop5 : prop).

Hypothesis H_prem : premises_admitted proplist5.
Hypothesis H_m : map_line_admitted G5.
Hypothesis H_mm : map_box_admitted G5.

Lemma soundness_premise : forall (l5 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_premise)) -> 
  prop_of prop5.
Proof.
move => l5 H_vd.
inversion H_vd; subst.
exact: (H_prem prop5).
Qed.

Lemma soundness_lem : forall (l5 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_lem)) -> 
  prop_of prop5.
Proof.
move => l5 H_vd.
inversion H_vd; subst.
exact: classic.
Qed.

Lemma soundness_andi : forall (l5 l6 l7: l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_andi l6 l7))) -> 
  prop_of prop5.
Proof.
case: prop5.
- by move => p5 l5 l6 l7 H_vd; inversion H_vd.
- by move => p5 l5 l6 l7 H_vd; inversion H_vd.
- move => prop6 prop7 l5 l6 l7 H_vd.
  inversion H_vd; subst.
  have H_m' := H_m.
  rewrite /map_line_admitted in H_m'; split.
    by apply H_m' in H3.
  by apply H_m' in H7.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => l5 l6 l7 H_vd; inversion H_vd.
Qed.

Lemma soundness_copy : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_copy l6))) ->   
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2.
Qed.

Lemma soundness_ande1 : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande1 l6))) ->
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2; first by case: H2.
Qed.

Lemma soundness_ande2 : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande2 l6))) ->   
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2; first by case: H2.
Qed.

Lemma soundness_ori1 : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori1 l6))) ->   
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2; first by left.
Qed.

Lemma soundness_ori2 : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori2 l6))) ->   
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2; first by right.
Qed.

Lemma soundness_impe : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impe l6 l7))) ->   
  prop_of prop5.
Proof.
move => l5 l6 l7 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
apply H_m' in H3.
apply H_m' in H6.
by apply H6.
Qed.

Lemma soundness_nege : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_nege l6 l7))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
apply H_m' in H3.
by apply H_m' in H6.
Qed.

Lemma soundness_conte : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_conte l6))) -> 
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2.
Qed.

Lemma soundness_negnegi : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnegi l6))) -> 
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2.
Qed.

Lemma soundness_negnege : forall (l5 l6 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnege l6))) -> 
  prop_of prop5.
Proof.
move => l5 l6 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
by apply H_m' in H2; first by apply NNPP in H2.
Qed.

Lemma soundness_mt : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_mt l6 l7))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
apply H_m' in H3.
apply H_m' in H6.
by move => H_c; apply H3 in H_c.
Qed.

Lemma soundness_impi : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impi l6 l7))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7.
move: l5 l6 l7.
case: prop5.
- by move => prop6 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- move => prop6 prop7 l5 l6 l7 H_vd.
  inversion H_vd; subst.
  by apply H_mm in H2.
- by move => l5 l6 l7 H_vd; inversion H_vd.
Qed.

Lemma soundness_negi : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negi l6 l7))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7.
move: l5 l6 l7.
case: prop5.
- by move => prop6 l5 l6 l7 H_vd; inversion H_vd.
- move => prop6 l5 l6 l7 H_vd; inversion H_vd; subst.
  have H_mm' := H_mm.
  rewrite /map_box_admitted in H_mm'.
  rewrite /= => Hp.  
  by apply H_mm' in H2.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => prop6 prop7 l5 l6 l7 H_vd; inversion H_vd.
- by move => l5 l6 l7 H_vd; inversion H_vd.
Qed.

Lemma soundness_ore : forall (l5 l6 l7 l8 l9 l10 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ore l6 l7 l8 l9 l10))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7 l8 l9 l10 H_vd.
inversion H_vd; subst.
have H_m' := H_m.
rewrite /map_line_admitted in H_m'.
apply H_m' in H4.
have H_mm' := H_mm.
case: H4 => H4; rewrite /map_box_admitted in H_mm'.
  by apply H_mm' in H9.
by apply H_mm' in H10.
Qed.

Lemma soundness_pbc : forall (l5 l6 l7 : l), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_pbc l6 l7))) -> 
  prop_of prop5.
Proof.
move => l5 l6 l7 H_vd.
inversion H_vd; subst.
apply: (NNPP (prop_of prop5)) => H_n.
have H_mm' := H_mm.
rewrite /map_box_admitted in H_mm'.
by apply H_mm' in H2.
Qed.

Lemma soundness_derivations : forall (l5 : l) (justification5: justification), 
  valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification5)) -> 
  prop_of prop5.
Proof.
move => l5; case.
- exact: soundness_premise.
- exact: soundness_lem.
- exact: soundness_copy.
- exact: soundness_andi.
- exact: soundness_ande1.
- exact: soundness_ande2.
- exact: soundness_ori1.
- exact: soundness_ori2.
- exact: soundness_impe.
- exact: soundness_nege.
- exact: soundness_conte.
- exact: soundness_negnegi.
- exact: soundness_negnege.
- exact: soundness_mt.
- exact: soundness_impi.
- exact: soundness_negi.
- exact: soundness_ore.
- exact: soundness_pbc.
Qed.

End Derivations.

Lemma not_in_map :
  forall (G5 : G) (l0 l6 : l) (prop0 prop6 : prop),
    l0 <> l6 ->
    Map.find (inl l6) (Map.add (inl l0) (inl prop0) G5) = Some (inl prop6) ->
    Map.find (inl l6) G5 = Some (inl prop6).
Proof.
move => G5 l0 l6 prop0 prop6 H_neq H_some.
apply MapFacts.find_mapsto_iff in H_some.
apply MapFacts.add_neq_mapsto_iff in H_some; last by move => H_eq; injection H_eq.
by apply  MapFacts.find_mapsto_iff.
Qed.

Lemma not_in_map_dyad :
  forall (G5 : G) (l0 l6 l7 : l) (prop0 prop6 prop7 : prop),
    Map.find (inr (l6, l7)) (Map.add (inl l0) (inl prop0) G5) = Some (inr (prop6, prop7)) ->
    Map.find (inr (l6, l7)) G5 = Some (inr (prop6, prop7)).
Proof.
move => G5 l0 l6 l7 prop0 prop6 prop7 H_some.
apply MapFacts.find_mapsto_iff in H_some.
apply MapFacts.add_neq_mapsto_iff in H_some => //.
by apply MapFacts.find_mapsto_iff.
Qed.

Lemma not_in_dyad_map :
  forall (G5 : G) (l6 l7 l8 : l) (prop6 prop7 prop8 : prop),  
    Map.find (inl l6) (Map.add (inr (l7, l8)) (inr (prop7, prop8)) G5) = Some (inl prop6) ->
    Map.find (inl l6) G5 = Some (inl prop6).
Proof.
move => G5 l6 l7 l8 prop6 prop7 prop8 H_some.
apply MapFacts.find_mapsto_iff in H_some.
apply MapFacts.add_neq_mapsto_iff in H_some => //.
by apply MapFacts.find_mapsto_iff.
Qed.

Lemma in_map :
  forall (G5 : G) (l0 l6 : l) (prop0 prop6 : prop),
    l0 = l6 ->
    Map.find (inl l6) (Map.add (inl l0) (inl prop0) G5) = Some (inl prop6) ->
    prop0 = prop6.
Proof.
move => G5 l0 l6 prop0 prop6 H_eq H_some.
rewrite MapFacts.add_eq_o in H_some; first by injection H_some.
by rewrite H_eq.
Qed.

Lemma map_find_add : 
  forall (G5 : G) (dn : dyadic) (dp dp' : dyadicprop), 
    Map.find dn (Map.add dn dp G5) = Some dp' ->
    dp = dp'.
Proof.
move => G5 dn dp dp' H_some.
by rewrite MapFacts.add_eq_o in H_some; first by injection H_some.
Qed.

Lemma not_in_map_dyad_neq : forall (G5 : G) (d d' : dyadic) (prop5 prop6 prop7 prop' : prop), 
  d <> d' -> 
  Map.find d (Map.add d' (inr (prop5, prop')) G5) = Some (inr (prop6, prop7)) ->
  Map.find d G5 = Some (inr (prop6, prop7)).
Proof.
move => G5 d d' prop6 prop7 prop8 prop' H_neq H_some.
apply MapFacts.find_mapsto_iff in H_some.
apply MapFacts.add_neq_mapsto_iff in H_some; last by move => H_c; rewrite H_c in H_neq.
by apply MapFacts.find_mapsto_iff.
Qed.

Definition justification_prop (G5 : G) (proplist5 : proplist) (proof5 : proof) : Prop := 
  forall (l5 : l) (prop5 : prop) (reason5 : reason), 
  valid_proof G5 proplist5 proof5 -> 
  In (entry_derivation (derivation_deriv l5 prop5 reason5)) (proof_list_entry proof5) ->
  reason5 <> reason_assumption.

Lemma justification_empty : (forall (G5 : G) (proplist5 : proplist),
   justification_prop G5 proplist5 (proof_entries nil)).
Proof. by intuition. Qed.

Lemma justification_derivation :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) 
         (prop5 : prop) (justification5 : justification) 
         (proof5 : proof),
       valid_derivation G5 proplist5
         (derivation_deriv l5 prop5 (reason_justification justification5)) ->
       valid_proof (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       justification_prop (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       justification_prop G5 proplist5
         (proof_entries
            (entry_derivation
               (derivation_deriv l5 prop5
                  (reason_justification justification5))
             :: proof_list_entry proof5)).
Proof.
rewrite /justification_prop.
move => G5 proplist0 l5 prop5 justification5 proof5 H_vd.
move => H_vp IH.
move => l0 prop0 reason5 H_vp' H_in.
case: H_in => H_in; last by apply (IH l0 prop0).
injection H_in => H_reason H_prop H_l.
move => H_neq.
by rewrite -H_reason in H_neq.
Qed.

Lemma justification_box : 
  forall (G5 : G) (proplist5 : proplist) (l5 : l) 
    (prop5 : prop) (proof5 proof' : proof) (l' : l) 
    (prop' : prop) (reason5 : reason),
       last
         (proof_list_entry
            (proof_entries
               (entry_derivation
                  (derivation_deriv l5 prop5 reason_assumption)
                :: proof_list_entry proof5))) entry_invalid =
       entry_derivation (derivation_deriv l' prop' reason5) ->
       valid_proof (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       justification_prop (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       valid_proof
         (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
         proplist5 proof' ->
       justification_prop
         (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
         proplist5 proof' ->
       justification_prop G5 proplist5
         (proof_entries
            (entry_box
               (proof_entries
                  (entry_derivation
                     (derivation_deriv l5 prop5 reason_assumption)
                   :: proof_list_entry proof5)) :: proof_list_entry proof')).
Proof.
rewrite /justification_prop.
move => G5 proplist0 l5 prop5 proof5 proof' l' prop' reason5.
move => H_last H_vp IH H_vp' IH' l0 prop0 reason0 H_vp'' H_in.
case: H_in => H_in; first by contradict H_in.
exact: (IH' l0 prop0).
Qed.

Lemma valid_in_justification: forall (G5 : G) (proplist0 : proplist) (proof5 : proof) (l5 : l) (prop5 : prop) (reason5 : reason), 
  valid_proof G5 proplist0 proof5 -> 
  In (entry_derivation (derivation_deriv l5 prop5 reason5)) (proof_list_entry proof5) ->
  reason5 <> reason_assumption.
Proof.
move => G5 proplist0 proof5 l5 prop5 reason5 H_vp.
exact: (valid_proof_ind justification_prop justification_empty justification_derivation justification_box _ _ _ H_vp).
Qed.

Definition soundness_prop (G5 : G) (proplist5 : proplist) (proof5 : proof) : Prop := 
  premises_admitted proplist5 ->
  forall (l5 : l) (j5 : justification),
    map_line_admitted G5 ->
    map_box_admitted G5 ->
    forall (prop5 : prop),
      In (entry_derivation (derivation_deriv l5 prop5 (reason_justification j5))) (proof_list_entry proof5) -> 
      prop_of prop5.

Lemma soundness_empty : (forall (G5 : G) (proplist5 : proplist),
       soundness_prop G5 proplist5 (proof_entries nil)).
Proof. by intuition. Qed.

Lemma soundness_derivation :
(forall (G5 : G) (proplist5 : proplist) (l5 : l) 
  (prop5 : prop)(justification5 : justification) (proof5 : proof),
       valid_derivation G5 proplist5
         (derivation_deriv l5 prop5 (reason_justification justification5)) ->
       valid_proof (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       soundness_prop (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       soundness_prop G5 proplist5
         (proof_entries
            (entry_derivation
               (derivation_deriv l5 prop5
                  (reason_justification justification5))
             :: proof_list_entry proof5))).
Proof.
move => G5 proplist0 l5 prop5 j5 proof5.
rewrite /soundness_prop.
move => H_vd H_vp IH H_prem.
move => l6 j6 H_m H_mm prop0 H_in.
case: H_in => H_in.
  injection H_in => H_j H_prop H_l.
  rewrite H_j H_prop H_l in H_vd.
  exact: (soundness_derivations G5 proplist0 prop0 _ _ _ l6 j6).
rewrite -/(In _ _) in H_in.
apply IH in H_in => //.
- move => l7 prop6 H_mp'.
  case (UOT.eq_dec l5 l7) => H_eq_l.
    rewrite -(in_map G5 l5 l7 _ _ H_eq_l H_mp').
    exact: (soundness_derivations G5 proplist0 prop5 _ _ _ l5 j5).
  apply not_in_map in H_mp' => //.
  by eapply H_m; eauto.
- move => l7 l8 prop6 prop7 H_mm' H_p.
  apply not_in_map_dyad in H_mm'.
  by eapply H_mm; eauto.
Qed.

Lemma soundness_box : (forall (G5 : G) (proplist5 : proplist) (l5 : l) 
  (prop5 : prop)(proof5 proof' : proof) (l' : l) (prop' : prop) (reason5 : reason),
       last
         (proof_list_entry
            (proof_entries
               (entry_derivation
                  (derivation_deriv l5 prop5 reason_assumption)
                :: proof_list_entry proof5))) entry_invalid =
       entry_derivation (derivation_deriv l' prop' reason5) ->
       valid_proof (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       soundness_prop (Map.add (inl l5) (inl prop5) G5)
         proplist5 proof5 ->
       valid_proof
         (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
         proplist5 proof' ->
       soundness_prop
         (Map.add (inr (l5, l')) (inr (prop5, prop')) G5)
         proplist5 proof' ->
       soundness_prop G5 proplist5
         (proof_entries
            (entry_box
               (proof_entries
                  (entry_derivation
                     (derivation_deriv l5 prop5 reason_assumption)
                   :: proof_list_entry proof5)) :: proof_list_entry proof'))).
Proof.
move => G5 proplist0 l5 prop5 proof5 proof' l' prop' reason5.
rewrite /soundness_prop.
move => H_last H_vp IH H_vp' IH' H_prem.
move => l0 j5 H_m H_mm prop0 H_in.
rewrite /In /= -/(In _ _) in H_in.
case: H_in => H_in //.
move: H_in; apply IH' => //.
  move => l6 prop6 H_add.
  apply H_m with (l6 := l6) (prop6 := prop6) => //.
  by apply (not_in_dyad_map G5 l6 l5 l' prop6 prop5 prop' H_add).
move => l6 l7 prop6 prop7 H_mm' H_prop6.
move: H_last.
case H_proof5: (proof_list_entry proof5) => [|e le] H_eq.
  injection H_eq => H_reason H_prop H_l.
  case (DUOT.eq_dec (inr (l6, l7)) (inr (l5, l'))) => H_dyad_eq.
    injection H_dyad_eq => H_eq_l6 H_eq_l7.
    rewrite H_eq_l6 H_eq_l7 in H_mm'.
    apply map_find_add in H_mm'.
    injection H_mm' => H_eq_prop7 H_eq_prop6 {H_mm'}.
    by subst.
  apply (not_in_map_dyad_neq _ _ _ _ _ _ _ H_dyad_eq) in H_mm'.
  by apply H_mm with (l6 := l6) (l7 := l7) (prop6 := prop6) (prop7 := prop7).
rewrite -H_proof5 /= in H_eq.
have H_proof5_entry: last (proof_list_entry proof5) entry_invalid = entry_derivation (derivation_deriv l' prop' reason5).
  move: H_eq.
  case H_eq : (proof_list_entry proof5); last by [].
  by rewrite H_eq in H_proof5; auto with datatypes.
have H_in_valid: In (entry_derivation (derivation_deriv l' prop' reason5)) (proof_list_entry proof5).
  have H_nnil: proof_list_entry proof5 <> nil by move => H_nil; rewrite H_nil in H_proof5; auto with datatypes.
  have H_removelast := (@app_removelast_last entry (proof_list_entry proof5) entry_invalid H_nnil).
  rewrite H_removelast.
  apply (@in_app_iff entry).
  by right; left.
have H_justification := H_in_valid.
apply (valid_in_justification _ _ _ _ _ _ H_vp) in H_justification.
case H_reason: reason5 => [|j6] => //.
rewrite H_reason in H_in_valid.
rewrite H_reason in H_proof5_entry.
case (DUOT.eq_dec (inr (l6, l7)) (inr (l5, l'))) => H_dyad_eq; first last.
  apply (not_in_map_dyad_neq _ _ _ _ _ _ _ H_dyad_eq) in H_mm'.
  by apply H_mm with (l6 := l6) (l7 := l7) (prop6 := prop6) (prop7 := prop7).
injection H_dyad_eq => H_eq_l6 H_eq_l7.
rewrite H_eq_l6 H_eq_l7 in H_mm'.
apply map_find_add in H_mm'.
injection H_mm' => H_eq_prop7 H_eq_prop6.
apply IH with (l6 := l7) (j5 := j6) (prop5 := prop7) => //; last by rewrite H_eq_l6 -H_eq_prop7.
  move => l1 prop1 H_m1 {H_eq}.
  case (UOT.eq_dec l1 l5) => H_eq.
    move: H_m1.
    rewrite H_eq => H_m1.
    apply in_map in H_m1; last by [].
    by subst.
  unfold UOT.eq in H_eq.
  apply not_in_map in H_m1 => [|H_c]; last by rewrite H_c in H_eq.
  rewrite /map_line_admitted in H_m.
  by apply H_m in H_m1.
move => l1 l2 prop1 prop2 H_mm12 H_prop1.
apply not_in_map_dyad in H_mm12.
rewrite /map_box_admitted in H_mm.
by apply H_mm with (l6 := l1) (l7 := l2) (prop6 := prop1) (prop7 := prop2) in H_mm12.
Qed.

Lemma soundness_proof : forall (proof5 : proof) (G5 : G) (proplist5 : proplist) (prop5 : prop) (l5 : l) (j5 : justification),
  premises_admitted proplist5 ->
  map_line_admitted G5 ->
  map_box_admitted G5 ->
  valid_proof G5 proplist5 proof5 ->
  In (entry_derivation (derivation_deriv l5 prop5 (reason_justification j5))) (proof_list_entry proof5) ->
  prop_of prop5.
Proof.
move => proof5 G5 proplist5 prop5 l5 j5 H_prem H_m H_mm H_vp.
move: H_prem l5 j5 H_m H_mm prop5.
exact: (valid_proof_ind soundness_prop soundness_empty soundness_derivation soundness_box G5 proplist5 proof5 H_vp).
Qed.

Theorem soundness_claim : forall (prop5 : prop) (proplist5 : proplist) (proof5 : proof),
  premises_admitted proplist5 ->
  valid_claim (claim_judgment_proof (judgment_follows proplist5 prop5) proof5) ->
  prop_of prop5.
Proof.
move => p5 proplist5 proof5 H_prem H_c.
inversion H_c; subst.
have H_snd := soundness_proof proof5 (Map.empty dyadicprop) proplist5 p5 l5 justification5.
apply H_snd => //.
- rewrite /map_line_admitted.
  move => l6 prop6 H_find.
  apply MapFacts.find_mapsto_iff in H_find.
  by apply MapFacts.empty_mapsto_iff in H_find.
- rewrite /map_box_admitted.
  move => l6 l7 prop6 prop7 H_find.
  apply MapFacts.find_mapsto_iff in H_find.
  by apply MapFacts.empty_mapsto_iff in H_find.
- have H_nil: (proof_list_entry proof5) <> nil by destruct (proof_list_entry proof5); first by inversion H3.
  have H_last := (@app_removelast_last entry (proof_list_entry proof5) entry_invalid H_nil).
  rewrite H_last H1.
  have H_app := (@in_app_iff entry (removelast (proof_list_entry proof5)) (entry_derivation (derivation_deriv l5 p5 (reason_justification justification5)) :: nil) (entry_derivation (derivation_deriv l5 p5 (reason_justification justification5)))).
  apply H_app.
  by right; left.
Qed.

End FitchPropMetatheory.
