import PLF.Stlc

namespace StlcProp
open STLC

theorem canonical_forms_bool: forall {t},
  ty{ ∅ |- [t]: Bool } -> t.value -> t = .True ∨ t = .False
:= by
  intro t HT HVal
  cases HVal with
  | Abs =>
    cases HT
  | True =>
    cases HT
    left
    eq_refl
  | False =>
    cases HT
    right
    eq_refl


theorem canonical_forms_fun: forall {t A B},
  ty{ ∅ |- [t]: [A] -> [B] } -> t.value -> exists x b, t = .Abs x A b
:= by
  intro t A B HT HVal
  cases HVal with
  | Abs =>
    cases HT
    constructor
    constructor
    trivial
  | _ => cases HT


theorem progress: forall {t T},
  ty{ ∅ |- [t]: [T]} -> t.value ∨ exists t', t.step t'
:= by
  intros t T HT
  generalize E: Context.empty = G
  rewrite [E] at HT
  induction HT with (try (left; constructor))
  | Var HT =>
    rewrite [<-E] at HT
    simp at HT
  | App HT1 HT2 IHT1 IHT2 =>
    right
    specialize (IHT1 E)
    specialize (IHT2 E)
    subst E
    cases IHT2 with
    | inr IHT2 =>
      constructor
      apply Tm.step.App2
      apply IHT2.choose_spec
    | inl IHT2 =>
      cases IHT1 with
      | inl IHT1 =>
        let H := canonical_forms_fun HT1 IHT1
        let ⟨x, ⟨b, Ef⟩⟩ := H
        constructor
        subst Ef
        apply Tm.step.AppAbs
        exact IHT2
      | inr IHT1 =>
        constructor
        apply Tm.step.App1
        apply IHT1.choose_spec
  | If Hc Ht Hf IHc IHt IHf =>
    right
    specialize (IHc E)
    specialize (IHt E)
    specialize (IHf E)
    subst E
    cases IHc with
    | inr IHc =>
      constructor
      apply Tm.step.If
      apply IHc.choose_spec
    | inl IHc =>
      let Hc := canonical_forms_bool Hc IHc
      cases Hc with
      | inl Et =>
        subst Et
        constructor
        apply Tm.step.IfTrue
      | inr Ef =>
        subst Ef
        constructor
        apply Tm.step.IfFalse


theorem progress': forall {t T},
  ty{ ∅ |- [t]: [T]} -> t.value ∨ exists t', t.step t'
:= by
  intro t
  induction t with (intro T HT; (try trivial); (try left; constructor))
  | App f x IHf IHx =>
    right
    cases HT with | App Hf Hx =>
      specialize (IHf Hf)
      specialize (IHx Hx)
      cases IHx with
      | inr IHx =>
        constructor
        apply Tm.step.App2
        apply IHx.choose_spec
      | inl IHx =>
        cases IHf with
        | inr IHf =>
          constructor
          apply Tm.step.App1
          apply IHf.choose_spec
        | inl IHf =>
          let Hf := canonical_forms_fun Hf IHf
          constructor
          rewrite [Hf.choose_spec.choose_spec]
          apply Tm.step.AppAbs
          exact IHx
  | If c t f IHc IHt IHf =>
    right
    cases HT with | If Hc Ht Hf =>
    specialize (IHc Hc)
    specialize (IHt Ht)
    specialize (IHf Hf)
    cases IHc with
    | inr IHc =>
      constructor
      apply Tm.step.If
      apply IHc.choose_spec
    | inl IHc =>
      let H := canonical_forms_bool Hc IHc
      cases H with
      | inl Et =>
        constructor
        rewrite [Et]
        apply Tm.step.IfTrue
      | inr Ef =>
        constructor
        rewrite [Ef]
        apply Tm.step.IfFalse


theorem weakening: forall {Gamma Gamma': Context} {t T},
  Gamma.included_in Gamma' ->
  ty{ Gamma |- [t]: [T]} ->
  ty{ Gamma' |- [t]: [T]}
:= by
  intro Gamma Gamma' t T
  intro Hinc HT
  revert Gamma'
  induction HT with (
    intros Gamma' Hinc;
    constructor <;> solve_by_elim [PartialMap.included_in_update]
  )

theorem weakening_empty: forall {Gamma: Context} {t T},
  ty{ ∅ |- [t]: [T]} ->
  ty{ Gamma |- [t]: [T]}
:= by
  intros Gamma t T
  apply weakening
  simp


theorem substitution_preserves_typing: forall {Gamma x U t v T},
  ty{ Gamma.update x U |- [t]: [T]} ->
  ty{ ∅ |- [v]: [U]} ->
  ty{ Gamma |- [[x := v] t]: [T] }
:= by
  intros Gamma x U t v T
  intros HT Hv
  revert Gamma T
  induction t with (intros Gamma T HT)
  | Var y =>
    simp
    cases HT with | Var H =>
    simp at H
    cases x.decEq y with
    | isTrue E =>
      simp [E] at *
      rewrite [<-H]
      apply weakening_empty
      exact Hv
    | isFalse NE =>
      have NE2: ¬y = x := fun E => NE E.symm
      simp [NE, NE2] at *
      apply Tm.has_type.Var
      exact H
  | App f t IHf IHt =>
    cases HT with | App Hf Ht =>
    apply Tm.has_type.App
    . -- typing of f
      apply IHf Hf
    . apply IHt Ht
  | Abs s A b IHb =>
    simp
    cases x.decEq s with
    | isTrue E =>
      simp [E]
      rewrite [E] at HT
      cases HT with | Abs Hb =>
      constructor
      let H: (Gamma.update s U).update s A = Gamma.update s A := TotalMap.update_shadow
      rewrite [H] at Hb
      exact Hb
    | isFalse NE =>
      cases HT with | Abs Hb =>
        simp [NE]
        constructor
        apply IHb
        . let H:
            (Gamma.update s A).update x U = (Gamma.update x U).update s A
          := TotalMap.update_permute NE
          rewrite [H]
          exact Hb
  | True | False =>
    cases HT with | _ =>
    simp
    constructor
  | If c t f IHc IHt IHf =>
    cases HT with | If Hc Ht Hf =>
    simp
    constructor
    . /- c -/
      apply IHc Hc
    . /- t -/
      apply IHt Ht
    . /- f -/
      apply IHf Hf

theorem preservation: forall {t t': Tm} {T},
  ty{ ∅ |- [t] : [T] } ->
  t.step t' ->
  ty{ ∅ |- [t'] : [T] }
:= by
  intros t t' T H
  revert t'
  generalize E: Context.empty = Gamma
  rewrite [E] at H
  induction H with (intro t' Hs)
  | Var | Abs | True | False =>
    cases Hs
  | @App c a b A B Hf Hx IHf IHx =>
    cases Hs with
    | AppAbs Hv =>
      rewrite [<-E] at Hx
      cases Hf with | Abs H =>
      apply substitution_preserves_typing
      . apply H
      . exact Hx
    | App1 Hf =>
      specialize (IHf E Hf)
      constructor
      . exact IHf
      . exact Hx
    | App2 Hx =>
      specialize (IHx E Hx)
      constructor
      . exact Hf
      . exact IHx
  | If Hc Ht Hf IHc IHt IHf =>
    cases Hs with
    | If H =>
      specialize (IHc E H)
      solve_by_elim
    | IfTrue | IfFalse => assumption


theorem not_subject_expansion:
  exists (t t': Tm) (T: Ty),
    t.step t' ∧ ty{ ∅ |- [t']: [T] } ∧ ¬ ty{ ∅ |- [t]: [T]}
:= by
  exists [tm| if true then true else x], .True, .Bool
  constructor
  . apply Tm.step.IfTrue
  . constructor
    . apply Tm.has_type.True
    . intro contra
      cases contra with | If Hc Ht Hf =>
      cases Hf with | Var H =>
      simp at H

end StlcProp
