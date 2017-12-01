Require Import fitch.
Require Import mathcomp.ssreflect.ssreflect.

Module Type DecidablePropInterpretation (Import PI : PropInterpretation).
Parameter A_eq_dec : forall x y : A, {x = y}+{x <> y}.
End DecidablePropInterpretation.

Module FitchProgram
  (PI : PropInterpretation) (DPI : DecidablePropInterpretation PI)
  (UOT : UsualOrderedType) (DUOT : DyadicUsualOrderedType UOT)
  (Map : FMapInterface.S with Module E := DUOT).

Module FitchPI := Fitch PI UOT DUOT Map.
Export FitchPI.

Definition prop_eq_dec : forall (prop5 prop' : prop), { prop5 = prop' }+{ prop5 <> prop' }.
decide equality; apply DPI.A_eq_dec.
Defined.

Definition valid_derivation_deriv_premise_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop), 
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_premise)) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_premise)) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) => 
      match In_dec prop_eq_dec prop5 proplist5 with
      | left H_in => left _ _
      | right H_in => right _ _
      end); last by move => H_vd; inversion H_vd.
exact: vd_premise.
Defined.

Definition valid_derivation_deriv_lem_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_lem)) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification justification_lem)) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) => 
    match prop5 with
    | prop_or prop' (prop_neg prop7) =>       
      match prop_eq_dec prop' prop7 with
      | left H_eq => left _ _
      | right H_eq => right _ _
      end      
    | _ => right _ _
    end); try by rewrite 1?H_eq; move => H_vd; inversion H_vd.
by rewrite H_eq; apply vd_lem.
Defined.

Definition valid_derivation_deriv_copy_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_copy l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_copy l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
    | Some (inl prop') => fun (H_eq : _) =>       
      match prop_eq_dec prop5 prop' with
      | left H_eq_prop => left _ _
      | right H_eq_prop => right _ _
      end
    | _ => fun (H_eq : _) => right _ _
    end (refl_equal _)); 
  subst; try by move => H_vd; inversion H_vd; subst; rewrite H2 in H_eq.
- exact: vd_copy.
- by move => H_vd; inversion H_vd; subst; rewrite H2 in H_eq; injection H_eq.
Defined.

Definition valid_derivation_deriv_andi_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_andi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_andi l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
    match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
    | Some (inl prop6) => fun (H_eq : _) => 
      match Map.find (inl l7) G5 as dp' return (_ = dp' -> _) with
      | Some (inl prop7) => fun (H_eq' : _) =>           
        match prop_eq_dec prop5 (prop_and prop6 prop7) with
        | left H_dec => left _ _
        | right H_dec => right _ _
        end
      | _ => fun (H_eq' : _) => right _ _
      end (refl_equal _)
    | _ => fun (H_eq : _) => right _ _
    end (refl_equal _)); 
  subst;
    try (by move => H_vp; inversion H_vp; subst; rewrite H3 in H_eq);
    try (by move => H_vp; inversion H_vp; subst; rewrite H6 in H_eq').
- exact: vd_andi.
- move => H_vd; inversion H_vd; subst.
  rewrite H_eq in H3; injection H3 => H_eq_prop6.
  rewrite H_eq' in H6; injection H6 => H_eq_prop7.
  by contradict H_dec; rewrite H_eq_prop6 H_eq_prop7.
Defined.

Definition valid_derivation_deriv_ande1_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande1 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande1 l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
    | Some (inl (prop_and prop6 prop7)) => fun (H_eq : _) =>      
      match prop_eq_dec prop5 prop6 with
      | left H_eq_dec => left _ _
      | right H_eq_dec => right _ _
      end      
    | _ => fun (H_eq : _) => right _ _
    end (refl_equal _)); subst; 
  try by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq.
- by apply vd_ande1 with (prop' := prop7).
- move => H_vp; inversion H_vp; subst.
  by rewrite H2 in H_eq; injection H_eq => H_prop5 H_prop6.
Defined.

Definition valid_derivation_deriv_ande2_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande2 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ande2 l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
    | Some (inl (prop_and prop6 prop7)) => fun (H_eq : _) =>
      match prop_eq_dec prop5 prop7 with
      | left H_eq_dec => left _ _
      | right H_eq_dec => right _ _
      end
    | _ => fun (H_eq : _) => right _ _
    end (refl_equal _)); subst; 
  try by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq.
- by apply vd_ande2 with (prop5 := prop6).
- move => H_vp; inversion H_vp; subst.
  by rewrite H2 in H_eq; injection H_eq => H_prop5 H_prop6.
Defined.

Definition valid_derivation_deriv_ori1_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori1 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori1 l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match prop5 as prop' return (prop5 = prop' -> _) with
    | prop_or prop6 prop7 => fun (H_eq_prop : _) =>
      match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
      | Some (inl prop') => fun (H_eq : _) =>      
        match prop_eq_dec prop6 prop' with
        | left H_eq_dec => left _ _
        | right H_eq_dec => right _ _
        end 
      | _ => fun (H_eq : _) => right _ _
      end (refl_equal _)
    | _ => fun (H_eq_prop : _) => right _ _
    end (refl_equal _)); 
  subst; try by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq.
- exact: vd_ori1.
- by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq; injection H_eq.
Defined.

Definition valid_derivation_deriv_ori2_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori2 l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ori2 l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match prop5 as prop' return (prop5 = prop' -> _) with
    | prop_or prop6 prop7 => fun (H_eq_prop : _) =>
      match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
      | Some (inl prop') => fun (H_eq : _) =>      
        match prop_eq_dec prop7 prop' with
        | left H_eq_dec => left _ _
        | right H_eq_dec => right _ _
        end 
      | _ => fun (H_eq : _) => right _ _
      end (refl_equal _)
    | _ => fun (H_eq_prop : _) => right _ _
    end (refl_equal _)); 
  subst; try by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq.
- exact: vd_ori2.
- by move => H_vp; inversion H_vp; subst; rewrite H2 in H_eq; injection H_eq.
Defined.

Definition valid_derivation_deriv_impe_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impe l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impe l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
   match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
   | Some (inl prop6) => fun (H_eq : _) => 
     match Map.find (inl l7) G5 as dp' return (_ = dp' -> _) with
     | Some (inl (prop_imp prop7 prop8)) => fun (H_eq' : _) => 
       match prop_eq_dec prop6 prop7, prop_eq_dec prop5 prop8 with
       | left H_eq_dec, left H_eq_dec' => left _ _
       | _, _ => right _ _
       end
     | _ => fun (H_eq' : _) => right _ _
     end (refl_equal _)
   | _ => fun (H_eq : _) => right _ _
   end (refl_equal _)); 
  subst; 
    try (by move => H_vp; inversion H_vp; subst; rewrite H3 in H_eq);
    try (by move => H_vp; inversion H_vp; subst; rewrite H6 in H_eq').
- by apply vd_impe with (prop' := prop7).
- move => H_vp; inversion H_vp; subst; rewrite H6 in H_eq'. 
  by injection H_eq' => H_eq_eq; contradict n.
- move => H_vp; inversion H_vp; subst; rewrite H3 in H_eq; rewrite H6 in H_eq'.
  injection H_eq => H_eq_eq; injection H_eq' => H_eq_eq' H_eq_eq''.
  by contradict n; subst.
Defined.

Definition valid_derivation_deriv_nege_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_nege l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_nege l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
    match prop5 as prop' return (prop5 = prop' -> _) with
    | prop_cont => fun (H_eq_cont : _) => 
      match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
      | Some (inl prop6) => fun (H_eq : _) => 
        match Map.find (inl l7) G5 as dp' return (_ = dp' -> _) with
        | Some (inl (prop_neg prop7)) => fun (H_eq' : _) =>
          match prop_eq_dec prop6 prop7 with
          | left H_eq_dec => left _ _
          | right H_eq_dec => right _ _
          end
        | _ => fun (H_eq' : _) => right _ _
        end (refl_equal _)
      | _ => fun (H_eq : _) => right _ _
      end (refl_equal _)
    | _ => fun (H_eq_cont : _) => right _ _
    end (refl_equal _));
  subst; 
    try (by move => H_vp; inversion H_vp; subst; rewrite H3 in H_eq);
    try (by move => H_vp; inversion H_vp; subst; rewrite H5 in H_eq').
- by apply vd_nege with (prop5 := prop7).
- move => H_vp; inversion H_vp; subst.
  rewrite H3 in H_eq; rewrite H5 in H_eq'.
  injection H_eq => H_eq_neg; injection H_eq' => H_eq_neg'.
  by contradict H_eq_dec; subst.
Defined.

Definition valid_derivation_deriv_conte_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_conte l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_conte l6))) }.
refine  
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
    match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
    | Some (inl prop_cont) => fun (H_eq : _) => left _ _
    | _ => fun (H_eq : _) => right _ _
    end (refl_equal _)); 
  subst; try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
exact: vd_conte.
Defined.

Definition valid_derivation_deriv_negnegi_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnegi l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnegi l6))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
   match prop5 as prop' return (prop5 = prop' -> _) with
   | prop_neg (prop_neg prop6) => fun (H_eq_prop : _) =>
     match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
     | Some (inl prop7) => fun (H_eq : _) => 
       match prop_eq_dec prop6 prop7 with
       | left H_eq_dec => left _ _
       | right H_eq_dec => right _ _
       end
     | _ => fun (H_eq : _) => right _ _
     end (refl_equal _)
   | _ => fun (H_eq_prop : _) => right _ _
   end (refl_equal _)); 
  subst; try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
- exact: vd_negnegi.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; subst; injection H_eq; contradict H_eq_dec.
Defined.

Definition valid_derivation_deriv_negnege_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnege l6))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negnege l6))) }.
refine  
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 : l) => 
   match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
   | Some (inl (prop_neg (prop_neg prop6))) => fun (H_eq : _) =>    
     match prop_eq_dec prop5 prop6 with
     | left H_eq_dec => left _ _
     | right H_eq_dec => right _ _
     end
   | _ => fun (H_eq : _) => right _ _
   end (refl_equal _)
  ); subst; try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
- exact: vd_negnege.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; subst; injection H_eq; contradict H_eq_dec.
Defined.

Definition valid_derivation_deriv_mt_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_mt l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_mt l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
    match prop5 as prop' return (prop5 = prop' -> _) with
    | prop_neg prop6 => fun (H_eq_prop : _) => 
      match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
      | Some (inl (prop_imp prop7 prop8)) => fun (H_eq : _) => 
        match prop_eq_dec prop6 prop7 with
        | left H_dec => 
          match Map.find (inl l7) G5 as dp' return (_ = dp' -> _) with
          | Some (inl (prop_neg prop9)) => fun (H_eq' : _) =>           
            match prop_eq_dec prop8 prop9 with
            | left H_dec' => left _ _
            | right H_dec' => right _ _
            end
          | _ => fun (H_eq' : _) => right _ _
          end (refl_equal _)
        | right H_dec => right _ _        
        end
      | _ => fun (H_eq : _) => right _ _
      end (refl_equal _)
    | _ => fun (H_eq_prop : _) => right _ _
    end (refl_equal _));
  subst; 
    try (by move => H_vp; inversion H_vp; subst; rewrite H3 in H_eq);
    try (by move => H_vp; inversion H_vp; subst; rewrite H6 in H_eq').    
- by apply vd_mt with (prop' := prop9).
- move => H_vp; inversion H_vp; rewrite H3 in H_eq; rewrite H6 in H_eq'.
  by injection H_eq => H_fst; injection H_eq' => H_snd'; contradict H_dec'; rewrite -H_fst.
- move => H_vp; inversion H_vp; rewrite H3 in H_eq.
  by injection H_eq => H_fst; contradict H_dec.
Defined.

Definition valid_derivation_deriv_impi_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_impi l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
   match prop5 as prop' return (prop5 = prop' -> _) with
   | prop_imp prop6 prop7 => fun (H_eq_prop : _) =>
     match Map.find (inr (l6, l7)) G5 as dp' return (_ = dp' -> _) with
     | Some (inr (prop8, prop9)) => fun (H_eq : _) =>
       match prop_eq_dec prop6 prop8, prop_eq_dec prop7 prop9 with
       | left H_dec, left H_dec' => left _ _         
       | _ , _ => right _ _
       end
     | _ => fun (H_eq : _) => right _ _
     end (refl_equal _)
   | _ => fun (H_eq_prop : _) => right _ _
   end (refl_equal _)); subst;
   try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
- exact: vd_impi.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; injection H_eq => H_find; contradict n.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; injection H_eq => H_find; contradict n.
Defined.

Definition valid_derivation_deriv_negi_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negi l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_negi l6 l7))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
   match prop5 as prop' return (prop5 = prop' -> _) with
   | prop_neg prop6 => fun (H_eq_prop : _) =>
     match Map.find (inr (l6, l7)) G5 as dp' return (_ = dp' -> _) with
     | Some (inr (prop7, prop_cont)) => fun (H_eq : _) =>
       match prop_eq_dec prop6 prop7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | _ => fun (H_eq : _) => right _ _
     end (refl_equal _)
   | _ => fun (H_eq_prop : _) => right _ _
   end (refl_equal _)
  ); subst;
  try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
- exact: vd_negi.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; injection H_eq => H_find; contradict H_dec.
Defined.

Definition valid_derivation_deriv_ore_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 l8 l9 l10 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ore l6 l7 l8 l9 l10))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_ore l6 l7 l8 l9 l10))) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 l8 l9 l10: l) =>
   match Map.find (inl l6) G5 as dp' return (_ = dp' -> _) with
   | Some (inl (prop_or prop6 prop7)) => fun (H_eq_or : _) => 
     match Map.find (inr (l7, l8)) G5 as dp' return (_ = dp' -> _) with
     | Some (inr (prop8, prop9)) => fun (H_eq_fst : _) => 
       match prop_eq_dec prop6 prop8, prop_eq_dec prop5 prop9 with
       | left H_dec_fst, left H_dec_fst_or =>
         match Map.find (inr (l9, l10)) G5 as dp' return (_ = dp' -> _) with
         | Some (inr (prop10, prop11)) => fun (H_eq_snd : _) => 
           match prop_eq_dec prop7 prop10, prop_eq_dec prop5 prop11 with
           | left H_dec_snd, left H_dec_snd_or => left _ _
           | _ , _ => right _ _
           end
         | _ => fun (H_eq_snd : _) => right _ _
         end (refl_equal _)
       | _ , _ => right _ _
       end
     | _ => fun (H_eq_fst : _) => right _ _
     end (refl_equal _)
   | _ => fun (H_eq_or : _) => right _ _
   end (refl_equal _)); subst;
  try (by move => H_vp; inversion H_vp; rewrite H4 in H_eq_or);
  try (by move => H_vp; inversion H_vp; rewrite H9 in H_eq_fst);
  try (by move => H_vp; inversion H_vp; rewrite H10 in H_eq_snd).
- by subst; apply vd_ore with (prop5 := prop8) (prop' := prop10).
- move => H_vp; inversion H_vp; subst.
  rewrite H10 in H_eq_snd; injection H_eq_snd => H_find_snd.
  by contradict n.
- move => H_vp; inversion H_vp; subst.
  rewrite H4 in H_eq_or; injection H_eq_or => H_find_or.  
  rewrite H10 in H_eq_snd; injection H_eq_snd => H_find_snd H_find_snd' H_find_snd''.
  by subst; contradict n.
- move => H_vp; inversion H_vp; subst.
  rewrite H9 in H_eq_fst; injection H_eq_fst => H_find_fst H_find_fst'.
  by subst; contradict n.
- move => H_vp; inversion H_vp; subst.
  rewrite H4 in H_eq_or; injection H_eq_or => H_find_or H_find_or'.
  rewrite H9 in H_eq_fst; injection H_eq_fst => H_find_fst H_find_fst'.
  by subst; contradict n.
Defined.

Definition valid_derivation_deriv_pbc_dec :
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7 : l),
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_pbc l6 l7))) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 (reason_justification (justification_pbc l6 l7))) }.
refine
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (l6 l7: l) => 
  match Map.find (inr (l6, l7)) G5 as dp' return (_ = dp' -> _) with
  | Some (inr ((prop_neg prop6), prop_cont)) => fun (H_eq : _) =>
    match prop_eq_dec prop5 prop6 with
    | left H_dec => left _ _
    | right H_dec => right _ _
    end
  | _ => fun (H_eq : _) => right _ _
  end (refl_equal _)); subst;
  try by move => H_vp; inversion H_vp; rewrite H2 in H_eq.
- exact: vd_pbc.
- by move => H_vp; inversion H_vp; rewrite H2 in H_eq; injection H_eq => H_find; contradict H_dec.
Defined.

Definition valid_derivation_deriv_dec : 
  forall (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (reason5 : reason), 
    { valid_derivation G5 proplist5 (derivation_deriv l5 prop5 reason5) }+
    { ~ valid_derivation G5 proplist5 (derivation_deriv l5 prop5 reason5) }.
refine 
  (fun (G5 : G) (proplist5 : proplist) (l5 : l) (prop5 : prop) (reason5 : reason) => 
   match reason5 as reason6 return (reason5 = reason6 -> _) with
   | reason_assumption => fun (H_reason : _) => right _ _
   | reason_justification justification5 => fun (H_reason : _) => 
     match justification5 as justification' return (justification5 = justification' -> _) with
     | justification_premise => fun (H_eq : _) => 
       match valid_derivation_deriv_premise_dec G5 proplist5 l5 prop5 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_lem => fun (H_eq : _) => 
       match valid_derivation_deriv_lem_dec G5 proplist5 l5 prop5 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_copy l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_copy_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_andi l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_andi_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_ande1 l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_ande1_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_ande2 l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_ande2_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_ori1 l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_ori1_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_ori2 l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_ori2_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_impe l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_impe_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_nege l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_nege_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_conte l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_conte_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_negnegi l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_negnegi_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_negnege l6 => fun (H_eq : _) => 
       match valid_derivation_deriv_negnege_dec G5 proplist5 l5 prop5 l6 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_mt l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_mt_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_impi l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_impi_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_negi l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_negi_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_ore l6 l7 l8 l9 l10 => fun (H_eq : _) => 
       match valid_derivation_deriv_ore_dec G5 proplist5 l5 prop5 l6 l7 l8 l9 l10 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     | justification_pbc l6 l7 => fun (H_eq : _) => 
       match valid_derivation_deriv_pbc_dec G5 proplist5 l5 prop5 l6 l7 with
       | left H_dec => left _ _
       | right H_dec => right _ _
       end
     end (refl_equal _)
   end (refl_equal _)); subst => //.
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
    valid_entry G5 proplist5 (entry_box (proof_entries (entry_derivation (derivation_deriv l5 prop5 reason_assumption) :: (proof_list_entry proof5)))).

Definition valid_proof_entry_list_   
  (valid_entry_dec : forall (G5 : G) (proplist5 : proplist) (e : entry), 
    { valid_entry G5 proplist5 e } + { ~ valid_entry G5 proplist5 e } ) : 
  forall (ls : list entry) (G5 : G) (proplist5 : proplist), 
    { valid_proof G5 proplist5 (proof_entries ls) } + { ~ valid_proof G5 proplist5 (proof_entries ls) }.
refine 
  (fix valid_proof_entry_list (ls : list entry) (G5 : G) (proplist5 : proplist) : 
    { valid_proof G5 proplist5 (proof_entries ls) }+{ ~ valid_proof G5 proplist5 (proof_entries ls) } :=
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
      match proof5 as proof' return (proof5 = proof' -> _) with
      | proof_entries ls5 => fun (H_eq_l : _) =>
        match ls5 as ls' return (ls5 = ls' -> _) with
        | nil => fun (H_ls5 : _) => right _ _
        | e' :: ls5' => fun (H_ls5 : _) =>
          match e' as e'' return (e' = e'' -> _) with
          | entry_derivation (derivation_deriv l5 prop5 reason5) => fun (H_eq_e' : _) =>
            match reason5 as reason' return (reason5 = reason' -> _) with
            | reason_assumption => fun (H_eq_r : _) => 
              match last ls5 entry_invalid as e'' return (_ = e'' -> _) with
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
      end (refl_equal _)
    | entry_invalid => fun (H_eq : _) => right _ _
    end (refl_equal _)
  end); try by move => H_vp; inversion H_vp; subst.
- exact: vp_empty.
- inversion H_dec; subst => //.
  injection H0 => H_l H_prop H_j.
  rewrite H_l H_prop H_j in H.
  have ->: ls' = proof_list_entry (proof_entries ls') by [].
  by subst; apply vp_derivation.
- move => H_vp; inversion H_vp; subst; last by [].
  move: H_dec_l.
  have ->: (proof_entries (proof_list_entry proof5)) = proof5 by destruct proof5.
  move => H_vp'.
  by injection H => H_j H_p H_l; subst.
- move => H_vp; inversion H_vp; subst => //.
  injection H => H_j H_p H_l; subst.
  contradict H_dec.
  exact: valid_entry_derivation. 
- inversion H_dec; first by rewrite H_eq H_eq_l in H0.
  rewrite H_eq H_eq_l H_ls5 H_eq_e' in H0.
  injection H0 => H_b H_d H_r H_prop.
  rewrite H_b.
  have ->: ls5' = proof_list_entry (proof_entries ls5') by [].
  have ->: ls' = proof_list_entry (proof_entries ls') by [].
  apply vp_box with (l' := l6) (prop' := prop6) (reason5 := reason6); try by subst.
  rewrite -H_b.
  by have ->: proof_entries (proof_list_entry proof0) = proof0 by destruct proof0.
- move => H_vp; inversion H_vp; subst; first by contradict H.
  injection H => H_eq_pr H_eq_prop H_eq_l.
  have H_eq: (entry_derivation (derivation_deriv l5 prop5 reason_assumption) :: proof_list_entry proof0) = (proof_list_entry (proof_entries (entry_derivation (derivation_deriv l5 prop5 reason_assumption) :: proof_list_entry proof0))) by [].
  rewrite -H_eq_prop -H_eq_l in H_eq.
  rewrite H_eq /= in H1.
  rewrite -H_eq_pr -H_eq_prop -H_eq_l /= in H_eq_d'.
  rewrite H1 in H_eq_d'.
  injection H_eq_d' => H_reason H_l H_l'.
  contradict H_dec'.
  rewrite -H_l -H_l' -H_eq_l -H_eq_prop.
  by have ->: (proof_entries (proof_list_entry proof')) = proof' by destruct proof'.
- move => H_vp; inversion H_vp; subst; first by contradict H.
  contradict H_dec.
  injection H => H_eq_ls H_eq_l H_eq_prop.
  rewrite -H_eq_ls -H_eq_l -H_eq_prop.
  exact: valid_entry_box.
- move => H_vp; inversion H_vp; subst; first by contradict H.
  injection H => H_eq_ls H_eq_l H_eq_prop; subst.
  by rewrite H_eq_d' in H1.
- move => H_vp; inversion H_vp; subst; first by contradict H.
  injection H => H_eq_ls H_eq_l H_eq_prop; subst.
  by rewrite H_eq_d' in H1.
Defined.

Fixpoint valid_entry_dec (G5 : G) (proplist5 : proplist) (e : entry) : 
  { valid_entry G5 proplist5 e }+{ ~ valid_entry G5 proplist5 e }.
refine 
  (match e as e' return (e = e' -> _) with
   | entry_derivation derivation5 => fun (H_eq_e : _) =>
     match derivation5 as derivation' return (derivation5 = derivation' -> _) with
     | derivation_deriv l5 prop5 reason5 => fun (H_eq_deriv: _) =>
       match reason5 as reason' return (reason5 = reason' -> _) with
       | reason_assumption => fun (H_eq_reason : _) => right _ _
       | reason_justification justification5 => fun (H_eq_reason : _) =>
         match valid_derivation_deriv_dec G5 proplist5 l5 prop5 (reason_justification justification5) with
         | left H_dec => left _ _
         | right H_dec => right _ _
         end
       end (refl_equal _)
     end (refl_equal _)
   | entry_box proof5 => fun (H_eq: _) => 
     match proof5 as proof' return (proof5 = proof' -> _) with
     | proof_entries ls => fun (H_eq_pr : _) => 
       match ls as ls' return (ls = ls' -> _) with
       | nil => fun (H_eq_l : _) => right _ _
       | e :: ls' => fun (H_eq_l : _) =>
         match e as e' return (e = e' -> _) with
         | entry_derivation (derivation_deriv l5 prop5 reason5) => fun (H_eq_e : _) =>
           match reason5 as reason' return (reason5 = reason' -> _) with
           | reason_assumption => fun (H_eq_r : _) => 
             match valid_proof_entry_list_ valid_entry_dec ls' (Map.add (inl l5) (inl prop5) G5) proplist5 with
             | left H_dec => left _ _
             | right H_dec => right _ _
             end
           | reason_justification justification5 => fun (H_eq_r : _) => right _ _
           end (refl_equal _)
         | _ => fun (H_eq_e : _) => right _ _
         end (refl_equal _)
       end (refl_equal _)
     end (refl_equal _)
   | entry_invalid => fun (H_eq: _) => right _ _
   end (refl_equal _)); subst; try by move => H_vp; inversion H_vp.
- exact: valid_entry_derivation.
- have ->: ls' = proof_list_entry (proof_entries ls') by [].
  exact: valid_entry_box.
- move => H_vp; inversion H_vp; subst.
  contradict H_dec.
  by have ->: (proof_entries (match proof5 with proof_entries ls => ls end)) = proof5 by destruct proof5.
Defined.

Definition valid_proof_entry_list := valid_proof_entry_list_ valid_entry_dec.

Definition valid_proof_dec : forall (G5 : G) (proplist5 : proplist) (proof5 : proof),
  { valid_proof G5 proplist5 proof5 }+{ ~ valid_proof G5 proplist5 proof5 }.
by refine
  (fun (G5 : G) (proplist5 : proplist) (proof5 : proof) =>
    match proof5 with
    | proof_entries ls =>
      match valid_proof_entry_list ls G5 proplist5 with
      | left H_dec => left _ _
      | right H_dec => right _ _
      end
    end).
Defined.

Definition valid_claim_dec : forall (c : claim), 
  { valid_claim c }+{ ~ valid_claim c }.
refine 
  (fun (c : claim) => 
    match c with
    | claim_judgment_proof judgment5 proof5 =>
      match proof5 as proof6 return (proof5 = proof6 -> _) with
      | proof_entries ls => fun (H_eq_pr : _) =>
        match last ls entry_invalid as e return (_ = e -> _) with
        | entry_derivation (derivation_deriv l5 prop5 reason5) => fun (H_eq_last : _) =>
          match reason5 as reason' return (reason5 = reason' -> _) with
          | reason_assumption => fun (H_eq_reason : _) => right _ _
          | reason_justification justification5 => fun (H_eq_reason : _) =>
            match judgment5 as judgment6 return (judgment5 = judgment6 -> _) with 
            | judgment_follows proplist5 prop' => fun (H_eq_judgment : _) =>
              match prop_eq_dec prop5 prop' with
              | left H_dec =>
                match valid_proof_dec (Map.empty dyadicprop) proplist5 (proof_entries ls) with
                | left H_dec' => left _ _
                | right H_dec' => right _ _
                end
              | right H_dec => right _ _
              end
            end (refl_equal _)
          end (refl_equal _)
        | _ => fun (H_eq : _) => right _ _
        end (refl_equal _)
      end (refl_equal _)
    end).
- move => H_vp; inversion H_vp.
  have H_ls: proof_list_entry (proof_entries ls) = ls by [].
  rewrite -H_eq_pr in H_ls.
  by rewrite H_ls H_eq_last H_eq_reason in H1.
- rewrite H_eq_judgment -H_dec {H_eq_judgment H_dec prop'}.
  apply vc_claim with (l5 := l5) (justification5 := justification5); last by rewrite -H_eq_pr in H_dec'.
  by rewrite -H_eq_reason -H_eq_last H_eq_pr.
- move => H_vp; inversion H_vp.
  by subst; congruence.
- move => H_vp; inversion H_vp; subst.
  have H_ls: proof_list_entry (proof_entries ls) = ls by [].  
  rewrite H_ls H_eq_last in H1.
  injection H1 => H_eq_p H_eq_pl H_eq_l.
  injection H => H_eq_p' H_eq_pl'.
  by rewrite -H_eq_p' -H_eq_pl in H_dec.
- move => H_vc; inversion H_vc.
  have H_ls: proof_list_entry (proof_entries ls) = ls by [].
  by rewrite H_eq_pr H_ls H_eq in H1.
- move => H_vc; inversion H_vc.
  have H_ls: proof_list_entry (proof_entries ls) = ls by [].
  by rewrite H_eq_pr H_ls H_eq in H1.
Defined.

Definition validate_claim (c : claim) : bool :=
match valid_claim_dec c with 
| left _ => true
| right _ => false
end.

End FitchProgram.
