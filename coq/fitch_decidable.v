Require Import Fitch.fitch.
Require Import Fitch.ssrexport.

Module FitchDecidable
  (UOT : UsualOrderedType) (DUOT : DyadicUsualOrderedType UOT)
  (Map : FMapInterface.S with Module E := DUOT).

Module Export FitchProp := Fitch UOT DUOT Map.

Section PropDecide.
Context {A : Type} (A_eq_dec : forall (a a' : A), {a = a'}+{a <> a'}).

Local Notation prop := (@prop A).

Definition prop_eq_dec : forall (prop5 prop' : prop), { prop5 = prop' }+{ prop5 <> prop' }.
decide equality; apply A_eq_dec.
Defined.

Program Definition valid_derivation_deriv_premise_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_premise)) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_premise)) } :=
match In_dec prop_eq_dec prop5 proplist5 with
| left H_in => left _ _
| right H_in => right _ _
end.
Next Obligation.
exact: vd_premise.
Defined.
Next Obligation.
by move => H_vd; inversion H_vd.
Defined.

Program Definition valid_derivation_deriv_lem_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_lem)) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_lem)) } :=
match prop5 with
| prop_or prop' (prop_neg prop7) =>
  match prop_eq_dec prop' prop7 with
  | left H_eq => left _ _
  | right H_eq => right _ _
  end
| _ => right _ _
end.
Next Obligation.
by apply vd_lem.
Defined.
Next Obligation.
by rewrite 1?H_eq; move => H_vd; inversion H_vd.
Defined.
Next Obligation.
move => H_vd; inversion H_vd; subst.
by congruence.
Defined.

Program Definition valid_derivation_deriv_copy_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_copy l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_copy l6))) } :=
match Map.find (inl l6) G5 with
| Some (inl prop') =>
  match prop_eq_dec prop5 prop' with
  | left H_eq_prop => left _ _
  | right H_eq_prop => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_copy.
Defined.
Next Obligation.
  move => H_vd; inversion H_vd; subst.
  rewrite H2 in Heq_anonymous0; injection Heq_anonymous0 => H_eq; clear Heq_anonymous Heq_anonymous0.
  by case: H_eq_prop.
Defined.
Next Obligation.
 move => H_vd; inversion H_vd; subst.
 by case (H prop5).
Defined.

Program Definition valid_derivation_deriv_andi_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_andi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_andi l6 l7))) } :=
match Map.find (inl l6) G5 with
| Some (inl prop6) =>
  match Map.find (inl l7) G5 with
  | Some (inl prop7) =>
    match prop_eq_dec prop5 (prop_and prop6 prop7) with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_andi.
Defined.
Next Obligation.
  move => H_vd; inversion H_vd; subst.
  rewrite -Heq_anonymous0 in H3; injection H3 => H_eq_prop6; clear Heq_anonymous0.
  rewrite -Heq_anonymous1 in H6; injection H6 => H_eq_prop7; clear Heq_anonymous1 Heq_anonymous.
  by contradict H_dec; rewrite H_eq_prop6 H_eq_prop7.
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  by case (H prop').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0).
Defined.

Program Definition valid_derivation_deriv_ande1_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande1 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande1 l6))) } :=
match Map.find (inl l6) G5 with
| Some (inl (prop_and prop6 prop7)) =>
  match prop_eq_dec prop5 prop6 with
  | left H_eq_dec => left _ _
  | right H_eq_dec => right _ _
  end      
| _ => right _ _
end.
Next Obligation.
 by apply vd_ande1 with (prop' := prop7).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H2 in Heq_anonymous0; injection Heq_anonymous0 => H_prop5 H_prop6.
 by case: H_eq_dec {Heq_anonymous}.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop5 prop').
Defined.

Program Definition valid_derivation_deriv_ande2_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande2 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande2 l6))) } :=
match Map.find (inl l6) G5 with
| Some (inl (prop_and prop6 prop7)) =>
  match prop_eq_dec prop5 prop7 with
  | left H_eq_dec => left _ _
  | right H_eq_dec => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 by apply vd_ande2 with (prop5 := prop6).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H2 in Heq_anonymous0; injection Heq_anonymous0 => H_prop5 H_prop6.
 by case: H_eq_dec {Heq_anonymous}.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop0 prop5).
Defined.

Program Definition valid_derivation_deriv_ori1_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori1 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori1 l6))) } :=
match prop5 with
| prop_or prop6 prop7 =>
  match Map.find (inl l6) G5 with
  | Some (inl prop') =>
    match prop_eq_dec prop6 prop' with
    | left H_eq_dec => left _ _
    | right H_eq_dec => right _ _
    end 
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
  exact: vd_ori1.
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst; rewrite H2 in Heq_anonymous0; injection Heq_anonymous0 => Heq.
  by case: H_eq_dec {Heq_anonymous}.
Defined.
Next Obligation.  
  subst; move => H_vp; inversion H_vp; subst.
  by case (H prop6).
Defined.
Next Obligation.  
  subst; move => H_vp; inversion H_vp; subst.
  by case (H prop0 prop').
Defined.

Program Definition valid_derivation_deriv_ori2_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori2 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori2 l6))) } :=
match prop5 with
| prop_or prop6 prop7 =>
  match Map.find (inl l6) G5 with
  | Some (inl prop') =>
    match prop_eq_dec prop7 prop' with
    | left H_eq_dec => left _ _
    | right H_eq_dec => right _ _
    end 
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_ori2.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst; rewrite H2 in Heq_anonymous0; injection Heq_anonymous0 => Heq.
 by case H_eq_dec.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst; rewrite H3 in H.
 by case (H prop7).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0 prop').
Defined.

Program Definition valid_derivation_deriv_impe_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impe l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impe l6 l7))) } :=
match Map.find (inl l6) G5 with
| Some (inl prop6) =>
  match Map.find (inl l7) G5 with
  | Some (inl (prop_imp prop7 prop8)) =>
    match prop_eq_dec prop6 prop7, prop_eq_dec prop5 prop8 with
    | left H_eq_dec, left H_eq_dec' => left _ _
    | _, _ => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
  by apply vd_impe with (prop' := prop7).
Defined.
Next Obligation.    
  move => H_vp; inversion H_vp; subst.
  rewrite H7 in Heq_anonymous1.
  injection Heq_anonymous1 => Heq1 Heq2.
  rewrite H4 in Heq_anonymous2.
  injection Heq_anonymous2 => Heq.
  subst.
  move: H.
  case (prop_eq_dec _ _) =>  Heq1 //.
  case (prop_eq_dec _ _) =>  Heq2 // Heq.
  by case (Heq Heq1 Heq2).
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  by case (H prop' prop5).
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  by case (H prop').
Defined.

Program Definition valid_derivation_deriv_nege_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_nege l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_nege l6 l7))) } :=
match prop5 with
| prop_cont =>
  match Map.find (inl l6) G5 with
  | Some (inl prop6) =>
    match Map.find (inl l7) G5 with
    | Some (inl (prop_neg prop7)) =>
      match prop_eq_dec prop6 prop7 with
      | left H_eq_dec => left _ _
      | right H_eq_dec => right _ _
      end
    | _ => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 by apply vd_nege with (prop5 := prop7).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in Heq_anonymous0.
 rewrite H5 in Heq_anonymous1.
 injection Heq_anonymous0 => H_eq.
 injection Heq_anonymous1 => H_eq'.
 by congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H6 in H.
 by case (H prop5).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H4 in H.
 by case (H prop5).
Defined.
Next Obligation.
  by move => H_vp; inversion H_vp; subst.
Defined.

Program Definition valid_derivation_deriv_conte_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_conte l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_conte l6))) } :=
match Map.find (inl l6) G5 with
| Some (inl prop_cont) => left _ _
| _ => right _ _
end.
Next Obligation.
 exact: vd_conte.
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  by rewrite H3 in H.
Defined.

Program Definition valid_derivation_deriv_negnegi_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnegi l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnegi l6))) } :=
match prop5 with
| prop_neg (prop_neg prop6) =>
  match Map.find (inl l6) G5 with
  | Some (inl prop7) =>
    match prop_eq_dec prop6 prop7 with
    | left H_eq_dec => left _ _
    | right H_eq_dec => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_negnegi.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H2 in Heq_anonymous0.
 by injection Heq_anonymous0; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop6).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0).
Defined.

Program Definition valid_derivation_deriv_negnege_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnege l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnege l6))) } := 
match Map.find (inl l6) G5 with
| Some (inl (prop_neg (prop_neg prop6))) =>
  match prop_eq_dec prop5 prop6 with
  | left H_eq_dec => left _ _
  | right H_eq_dec => right _ _
  end
| _ => right _ _
end.
Next Obligation.
  exact: vd_negnege.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H2 in Heq_anonymous0.
 by injection Heq_anonymous0; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop5).
Defined.

Program Definition valid_derivation_deriv_mt_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_mt l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_mt l6 l7))) } :=
match prop5 with
| prop_neg prop6 =>
  match Map.find (inl l6) G5 with
  | Some (inl (prop_imp prop7 prop8)) => 
    match prop_eq_dec prop6 prop7 with
    | left H_dec =>
      match Map.find (inl l7) G5 with
      | Some (inl (prop_neg prop9)) =>
        match prop_eq_dec prop8 prop9 with
        | left H_dec' => left _ _
        | right H_dec' => right _ _
        end
      | _ => right _ _
      end
    | right H_dec => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 by apply vd_mt with (prop' := prop9).
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  rewrite H3 in Heq_anonymous0.
  rewrite H6 in Heq_anonymous2.
  injection Heq_anonymous0 => Heq.
  injection Heq_anonymous2 => Heq'.
  by congruence.
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst.
  rewrite H7 in H.
  by case (H prop').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in Heq_anonymous0.
 by injection Heq_anonymous0; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop6 prop').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0).
Defined.

Program Definition valid_derivation_deriv_impi_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impi l6 l7))) } :=
match prop5 with
| prop_imp prop6 prop7 =>
  match Map.find (inr (l6, l7)) G5 with
  | Some (inr (prop8, prop9)) =>
    match prop_eq_dec prop6 prop8, prop_eq_dec prop7 prop9 with
    | left H_dec, left H_dec' => left _ _         
    | _ , _ => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_impi.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in Heq_anonymous1.
 injection Heq_anonymous1 => Heq Heq' {Heq_anonymous1 H3}; subst.
 move: H; case (prop_eq_dec _ _) => Heq //; case (prop_eq_dec _ _) => Heq' // H.
 by case (H Heq Heq').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop6 prop7).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0 prop').
Defined.

Program Definition valid_derivation_deriv_negi_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negi l6 l7))) } :=
match prop5 with
| prop_neg prop6 =>
  match Map.find (inr (l6, l7)) G5 with
  | Some (inr (prop7, prop_cont)) =>
    match prop_eq_dec prop6 prop7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_negi.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by rewrite H2 in Heq_anonymous0; injection Heq_anonymous0; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop6).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H prop0).
Defined.

Program Definition valid_derivation_deriv_ore_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 l8 l9 l10 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ore l6 l7 l8 l9 l10))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ore l6 l7 l8 l9 l10))) } :=
match Map.find (inl l6) G5 with
| Some (inl (prop_or prop6 prop7)) =>
  match Map.find (inr (l7, l8)) G5 with
  | Some (inr (prop8, prop9)) =>
    match prop_eq_dec prop6 prop8, prop_eq_dec prop5 prop9 with
    | left H_dec_fst, left H_dec_fst_or =>
      match Map.find (inr (l9, l10)) G5 with
      | Some (inr (prop10, prop11)) =>
        match prop_eq_dec prop7 prop10, prop_eq_dec prop5 prop11 with
        | left H_dec_snd, left H_dec_snd_or => left _ _
        | _ , _ => right _ _
        end
      | _ => right _ _
      end
    | _ , _ => right _ _
    end
  | _ => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 by apply vd_ore with (prop5 := prop8) (prop' := prop10).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H5 in Heq_anonymous2; injection Heq_anonymous2 => Heq1 Heq1'.
 rewrite H11 in Heq_anonymous4; injection Heq_anonymous4 => Heq2 Heq2'.
 subst; move: H.
 case (prop_eq_dec _ _) => Heq //; case (prop_eq_dec _ _) => Heq' // H.
 by case (H Heq Heq').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H11 in H.
 by case (H prop' prop9).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H10 in Heq_anonymous1; injection Heq_anonymous1 => Heq1 Heq1'.
 rewrite H5 in Heq_anonymous2; injection Heq_anonymous2 => Heq2 Heq2'.
 subst; move: H.
 case (prop_eq_dec _ _) => Heq //; case (prop_eq_dec _ _) => Heq' // H.
 by case (H Heq Heq').
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H10 in H.
 by case (H prop0 prop5).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H5 in H.
 by case: (H prop0 prop').
Defined.

Program Definition valid_derivation_deriv_pbc_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l) :
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_pbc l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_pbc l6 l7))) } :=
match Map.find (inr (l6, l7)) G5 with
| Some (inr ((prop_neg prop6), prop_cont)) =>
  match prop_eq_dec prop5 prop6 with
  | left H_dec => left _ _
  | right H_dec => right _ _
  end
| _ => right _ _
end.
Next Obligation.
 exact: vd_pbc.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H2 in Heq_anonymous0.
 by injection Heq_anonymous0; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H3 in H.
 by case (H prop5).
Defined.

Program Definition valid_derivation_deriv_dec (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (reason5 : reason) :
  { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 reason5) }+
  { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 reason5) } :=
match reason5 with
| reason_assumption => right _ _
| reason_justification justification5 =>
  match justification5 with
  | justification_premise =>
    match valid_derivation_deriv_premise_dec G5 proplist5 l5 prop5 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_lem =>
    match valid_derivation_deriv_lem_dec G5 proplist5 l5 prop5 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_copy l6 =>
    match valid_derivation_deriv_copy_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_andi l6 l7 =>
    match valid_derivation_deriv_andi_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_ande1 l6 =>
    match valid_derivation_deriv_ande1_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_ande2 l6 =>
    match valid_derivation_deriv_ande2_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_ori1 l6 =>
    match valid_derivation_deriv_ori1_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_ori2 l6 =>
    match valid_derivation_deriv_ori2_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_impe l6 l7 =>
    match valid_derivation_deriv_impe_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_nege l6 l7 =>
    match valid_derivation_deriv_nege_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_conte l6 =>
    match valid_derivation_deriv_conte_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_negnegi l6 =>
    match valid_derivation_deriv_negnegi_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_negnege l6 =>
    match valid_derivation_deriv_negnege_dec G5 proplist5 l5 prop5 l6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_mt l6 l7 =>
    match valid_derivation_deriv_mt_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_impi l6 l7 =>
    match valid_derivation_deriv_impi_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_negi l6 l7 =>
    match valid_derivation_deriv_negi_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_ore l6 l7 l8 l9 l10 =>
    match valid_derivation_deriv_ore_dec G5 proplist5 l5 prop5 l6 l7 l8 l9 l10 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | justification_pbc l6 l7 =>
    match valid_derivation_deriv_pbc_dec G5 proplist5 l5 prop5 l6 l7 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  end
end.
Next Obligation.
 by move => H_deriv; inversion H_deriv.
Defined.

Inductive valid_entry (G5 : G) (proplist5 : proplist) : entry -> Prop :=
| valid_entry_derivation : 
  forall (l5 : l) (prop5 : prop) (justification5 : justification),  
    valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification5)) -> 
    valid_entry G5 proplist5 (entry_derivation (derivation_deriv l5 prop5 (reason_justification justification5)))
| valid_entry_box :
  forall (proof5 : proof) (l5 : l) (prop5 : prop),
    valid_proof (Map.add (inl l5) (inl prop5) G5) proplist5 proof5 ->
    valid_entry G5 proplist5 (entry_box (entry_derivation (derivation_deriv l5 prop5 reason_assumption) :: proof5)).

(*
Program Definition valid_proof_entry_list_
  (valid_entry_dec : forall (G5 : G) (proplist5 : proplist) (e : entry), 
    { valid_entry G5 proplist5 e } + { ~ valid_entry G5 proplist5 e } )
  (ls : list entry) (G5 : G) (proplist5 : proplist) :
    { valid_proof G5 proplist5 ls } + { ~ @valid_proof A G5 proplist5 ls } :=
(fix valid_proof_entry_list (ls : list entry) (G5 : G) (proplist5 : proplist) : 
  { valid_proof G5 proplist5 ls }+{ ~ valid_proof G5 proplist5 ls } :=
match ls with 
| nil => left _ _
| cons e ls' => 
  match e with
  | entry_derivation (derivation_deriv l5 prop5 reason5) =>
    match reason5 with
    | reason_assumption => right _ _
    | reason_justification justification5 =>
      match valid_entry_dec G5 proplist5 e with
      | left H_dec =>
        match valid_proof_entry_list ls' (Map.add (inl l5) (inl prop5) G5) proplist5 with
        | left H_dec_l => left _ _
        | right H_dec_l => right _ _
        end
      | right H_dec => right _ _
      end
    end
  | entry_box proof5 =>
    match proof5 with
    | nil => right _ _
    | e' :: ls5' =>
      match e' with
      | entry_derivation (derivation_deriv l5 prop5 reason5) =>
        match reason5 with
        | reason_assumption =>
           match last proof5 entry_invalid with
           | entry_derivation (derivation_deriv l6 prop6 reason6) =>
             match valid_entry_dec G5 proplist5 e with
             | left H_dec => 
               match valid_proof_entry_list ls' (Map.add (inr (l5, l6)) (inr (prop5, prop6)) G5) proplist5 with
               | left H_dec' => left _ _
               | right H_dec' => right _ _
               end
             | right H_dec => right _ _
             end
           | _ => right _ _
           end
        | reason_justification justification5 => right _ _
        end
      | _ => right _ _
      end
    end
  | entry_invalid => right _ _
  end
end) ls G5 proplist5.
Next Obligation.
  exact: vp_empty.
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp; subst.
Defined.
Next Obligation.
 inversion H_dec; subst => //.
 by apply vp_derivation.
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp; subst.
Defined.
Next Obligation.
  move => H_vp; inversion H_vp; subst => //.
  case: H_dec {Heq_anonymous}.
  exact: valid_entry_derivation.
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp; subst.
Defined.
Next Obligation.
 inversion H_dec; subst.
 by apply vp_box with (l' := l6) (prop' := prop6) (reason5 := reason6).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 case: H_dec' {Heq_anonymous}.
 rewrite -Heq_anonymous0 in H4.
  injection H4 => Heq1 Heq2 Heq3.
  by subst.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 case: H_dec {Heq_anonymous}.
 exact: valid_entry_box.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 rewrite H5 in H.
 by case (H l' prop' reason5).
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp; subst.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H l5 prop5 reason_assumption).
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp; subst.
Defined.
*)

Definition valid_proof_entry_list_   
  (valid_entry_dec : forall (G5 : G) (proplist5 : proplist) (e : entry), 
    { valid_entry G5 proplist5 e } + { ~ valid_entry G5 proplist5 e } ) : 
  forall (ls : list entry) (G5 : G) (proplist5 : proplist), 
    { valid_proof G5 proplist5 ls } + { ~ @valid_proof A G5 proplist5 ls }.
refine 
  (fix valid_proof_entry_list (ls : list entry) (G5 : G) (proplist5 : proplist) : 
    { valid_proof G5 proplist5 ls }+{ ~ valid_proof G5 proplist5 ls } :=
  match ls with 
  | nil => left _ _
  | cons e ls' => 
    match e as e' return (e = e' -> _) with 
    | entry_derivation (derivation_deriv l5 prop5 reason5) => fun (H_eq_e : _) => 
      match reason5 as reason' return (reason5 = reason' -> _) with
      | reason_assumption => fun (H_eq_j : _) => right _ _
      | reason_justification justification5 => fun (H_eq_j : _) => 
        match valid_entry_dec G5 proplist5 e with
        | left H_dec =>
          match valid_proof_entry_list ls' (Map.add (inl l5) (inl prop5) G5) proplist5 with
          | left H_dec_l => left _ _
          | right H_dec_l => right _ _
          end
        | right H_dec => right _ _
        end
      end (refl_equal _)      
    | entry_box proof5 => fun (H_eq : _) =>
      match proof5 as ls' return (proof5 = ls' -> _) with
      | nil => fun (H_ls5 : _) => right _ _
      | e' :: ls5' => fun (H_ls5 : _) =>
        match e' as e'' return (e' = e'' -> _) with
        | entry_derivation (derivation_deriv l5 prop5 reason5) => fun (H_eq_e' : _) =>
          match reason5 as reason' return (reason5 = reason' -> _) with
          | reason_assumption => fun (H_eq_r : _) => 
             match last proof5 entry_invalid as e'' return (_ = e'' -> _) with
             | entry_derivation (derivation_deriv l6 prop6 reason6) => fun (H_eq_d' : _) => 
               match valid_entry_dec G5 proplist5 e with
               | left H_dec => 
                 match valid_proof_entry_list ls' (Map.add (inr (l5, l6)) (inr (prop5, prop6)) G5) proplist5 with
                 | left H_dec' => left _ _
                 | right H_dec' => right _ _
                 end
               | right H_dec => right _ _
               end
             | _ => fun (H_eq_d' : _) => right _ _
             end (refl_equal _)
          | reason_justification justification5 => fun (H_eq_r : _) => right _ _
          end (refl_equal _)
        | _ => fun (H_eq_e' : _) => right _ _
        end (refl_equal _)
      end (refl_equal _)
    | entry_invalid => fun (H_eq : _) => right _ _
    end (refl_equal _)
  end); try by move => H_vp; inversion H_vp; subst.
- exact: vp_empty.
- inversion H_dec; subst => //.
  injection H0 => H_l H_prop H_j.
  rewrite H_l H_prop H_j in H.  
  by subst; apply vp_derivation.
- move => H_vp; inversion H_vp; subst => //.
  case: H_dec.
  exact: valid_entry_derivation.
- inversion H_dec; first by congruence.
  subst.
  injection H0 => H_pr H_p H_l.
  subst.
  by apply vp_box with (l' := l6) (prop' := prop6) (reason5 := reason6).
- move => H_vp; inversion H_vp; subst.
  case: H_dec'.
  rewrite H_eq_d' in H4.
  injection H4 => Heq1 Heq2 Heq3.
  by subst.
- move => H_vp; inversion H_vp; subst.
  contradict H_dec.
  exact: valid_entry_box.
- move => H_vp; inversion H_vp; subst.
  by rewrite H_eq_d' in H4.
- move => H_vp; inversion H_vp; subst.  
  by rewrite H_eq_d' in H4.
Defined.

Program Fixpoint valid_entry_dec (G5 : G) (proplist5 : proplist) (e : entry) {struct e}  : 
  { valid_entry G5 proplist5 e }+{ ~ valid_entry G5 proplist5 e } :=
match e with
| entry_derivation derivation5 =>
  match derivation5 with
  | derivation_deriv l5 prop5 reason5 =>
    match reason5 with
    | reason_assumption => right _ _
    | reason_justification justification5 =>
      match valid_derivation_deriv_dec G5 proplist5 l5 prop5 (reason_justification justification5) with
      | left H_dec => left _ _
      | right H_dec => right _ _
      end
    end
  end
| entry_box nil => right _ _ 
| entry_box (e :: ls') =>
  match e with
  | entry_derivation (derivation_deriv l5 prop5 reason5) =>
    match reason5 with
    | reason_assumption =>
      match valid_proof_entry_list_ valid_entry_dec ls' (Map.add (inl l5) (inl prop5) G5) proplist5 with
      | left H_dec => left _ _
      | right H_dec => right _ _
      end
    | reason_justification justification5 => right _ _
    end
  | _ => right _ _
  end
| entry_invalid => right _ _
end.
Next Obligation.
 by move => H_vp; inversion H_vp.
Defined.
Next Obligation.
 exact: valid_entry_derivation.
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp. 
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp. 
Defined.
Next Obligation.
 exact: valid_entry_box.
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp. 
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp. 
Defined.
Next Obligation.
 move => H_vp; inversion H_vp; subst.
 by case (H l5 prop5 reason_assumption).
Defined.
Next Obligation.
 by move => H_vp; inversion H_vp. 
Defined.

Definition valid_proof_entry_list := valid_proof_entry_list_ valid_entry_dec.

Program Definition valid_proof_dec (G5 : G) (proplist5 : proplist) (proof5 : proof) :
  { valid_proof G5 proplist5 proof5 }+{ ~ valid_proof G5 proplist5 proof5 } :=
match valid_proof_entry_list proof5 G5 proplist5 with
| left H_dec => left _ _
| right H_dec => right _ _
end.

Program Definition valid_claim_dec (c : @claim A) : { valid_claim c }+{ ~ valid_claim c } := 
match c with
| claim_judgment_proof judgment5 proof5 =>
  match last proof5 entry_invalid with
  | entry_derivation (derivation_deriv l5 prop5 reason5) =>
    match reason5 with
    | reason_assumption => right _ _
    | reason_justification justification5 =>
      match judgment5 with
      | judgment_follows proplist5 prop' =>
        match prop_eq_dec prop5 prop' with
        | left H_dec =>
          match valid_proof_dec (Map.empty dyadicprop) proplist5 proof5 with
          | left H_dec' => left _ _
          | right H_dec' => right _ _
          end
        | right H_dec => right _ _
        end
      end
    end
  | _ => right _ _
  end
end.
Next Obligation.
 move => H_vp; inversion H_vp.
 subst.
 by rewrite H1 in Heq_anonymous; congruence.
Defined.
Next Obligation.
 by apply vc_claim with (l6 := l5) (justification6 := justification5).
Defined.
Next Obligation.
 move => H_vp; inversion H_vp.
 by subst; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp.
 by subst; congruence.
Defined.
Next Obligation.
 move => H_vp; inversion H_vp.
 by subst; congruence.
Defined.

End PropDecide.

End FitchDecidable.
