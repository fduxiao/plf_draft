import PLF.SmallStep


namespace tm

inductive tm : Type where
  | tru : tm
  | fls : tm
  | ite : tm -> tm -> tm -> tm
  | zro : tm
  | scc : tm -> tm
  | prd : tm -> tm
  | iszro : tm -> tm


inductive tm.bvalue : tm -> Prop where
  | true : bvalue .tru
  | false : bvalue .fls

inductive tm.nvalue : tm -> Prop where
  | zero : nvalue .zro
  | succ (t: tm) : t.nvalue -> t.scc.nvalue

@[simp]
def tm.value (t : tm) := t.bvalue \/ t.nvalue


inductive tm.step : tm -> tm -> Prop where
  | IfTrue {t1 t2: tm}: tm.step (.ite .tru t1 t2) t1
  | IfFalse {t1 t2: tm}: tm.step (.ite .fls t1 t2) t2
  | If {c c' t2 t3}: tm.step c c' -> tm.step (.ite c t2 t3) (.ite c' t2 t3)
  | Succ {t1 t2}: tm.step t1 t2 -> tm.step t1.scc t2.scc
  | Pred0: tm.step (.prd .zro) (.zro)
  | PredSucc {v: tm}: v.nvalue -> tm.step (.prd v.scc) v
  | Pred {t1 t2}: tm.step t1 t2 -> tm.step t1.prd t2.prd
  | Iszero0: tm.step (.iszro .zro) .tru
  | IszeroSucc {v: tm}: v.nvalue -> tm.step (.iszro v.scc) .fls
  | Iszero {t1 t2}: tm.step t1 t2 -> tm.step (.iszro t1) (.iszro t2)


@[simp]
abbrev tm.step_normal := Relation.Normal tm.step
@[simp]
abbrev tm.stuck (t: tm): Prop := t.step_normal ∧ ¬ t.value

example: exists (t: tm), t.stuck := by
  exists tm.fls.prd
  apply And.intro
  . simp [Relation.Normal]
    intros x H
    cases H with | Pred K =>
    cases K
  . simp
    apply And.intro <;> (intros contra; cases contra)


theorem tm.value.is_nf {t: tm}: t.value -> t.step_normal := by
  intros H
  cases H with
  | inl Hb =>
    cases Hb <;> (intros contra; cases contra.choose_spec)
  | inr Hn =>
    induction Hn with
    | zero =>
      intros contra
      cases contra.choose_spec
    | succ m V IHm =>
      intros contra
      let ⟨y, contra⟩ := contra
      cases contra
      solve_by_elim

theorem tm.bvalue.is_nf {t: tm}: t.bvalue -> t.step_normal := by
  intros H
  apply tm.value.is_nf
  left
  trivial

theorem tm.nvalue.is_nf {t: tm}: t.nvalue -> t.step_normal := by
  intros H
  apply tm.value.is_nf
  right
  trivial

theorem tm.step.deterministic {t1 t2 t3: tm}:
  t1.step t2 ->
  t1.step t3 ->
  t2 = t3
:= by
  intros H12
  revert t3
  induction H12 with (intros t3 H23)
  | IfTrue | IfFalse =>
    cases H23 with
    | If H23 => cases H23
    | _ => eq_refl
  | If Hc IH =>
    cases H23 with
    | IfTrue | IfFalse =>
      cases Hc
    | If H23 =>
      specialize (IH H23)
      rewrite [IH]
      eq_refl
  | Succ H12 IH =>
    cases H23 with | Succ H23 =>
    specialize (IH H23)
    rewrite [IH]
    eq_refl
  | Pred0 =>
    cases H23 with
    | Pred0 => eq_refl
    | Pred H => cases H
  | PredSucc V =>
    cases H23 with
    | Pred H23 =>
      cases H23
      exfalso
      apply V.is_nf
      solve_by_elim
    | PredSucc => eq_refl
  | Pred H12 IH =>
    cases H23 with
    | Pred0 => cases H12
    | PredSucc V =>
      cases H12
      exfalso
      apply V.is_nf
      solve_by_elim
    | Pred =>
      rewrite [IH] <;> trivial
  | Iszero0 =>
    cases H23 with
    | Iszero0 => eq_refl
    | Iszero H23 => cases H23
  | IszeroSucc V =>
    cases H23 with
    | Iszero H23 =>
      cases H23
      exfalso
      apply V.is_nf
      solve_by_elim
    | _ => eq_refl
  | Iszero H12 IH =>
    cases H23 with
    | Iszero H23 =>
      specialize (IH H23)
      solve_by_elim
    | Iszero0 => cases H12
    | IszeroSucc V =>
      cases H12
      exfalso
      apply V.is_nf
      solve_by_elim


inductive ty: Type where
  | B: ty
  | N: ty

inductive tm.has_type: tm -> ty -> Prop where
  | True: tm.has_type .tru .B
  | False: tm.has_type .fls .B
  | If {t1 t2 t3: tm} {T: ty}:
    t1.has_type .B ->
    t2.has_type T ->
    t3.has_type T ->
    tm.has_type (.ite t1 t2 t3) T
  | Zero: tm.has_type .zro .N
  | Succ {t: tm}: t.has_type .N -> t.scc.has_type .N
  | Pred {t: tm}: t.has_type .N -> t.prd.has_type .N
  | Iszero {t: tm}: t.has_type .N -> t.iszro.has_type .B


example: (tm.ite .fls .zro (.scc .zro)).has_type .N := by
  repeat constructor

example: ¬ (tm.ite .fls .zro .tru).has_type .B := by
  intros contra
  cases contra with | If H1 H2 H3 =>
  cases H2

example {t: tm}: t.scc.has_type .N -> t.has_type .N := by
  intros H
  cases H
  assumption


theorem tm.bvalue.has_type {t: tm}: t.bvalue -> t.has_type .B := by
  intros H
  cases H <;> constructor

theorem tm.nvalue.has_type {t: tm}: t.nvalue -> t.has_type .N := by
  intros H
  induction H
  case zero => constructor
  case succ IH =>
    constructor
    exact IH


theorem tm.value.b_canonical {t: tm}:
  t.has_type .B -> t.value -> t.bvalue
:= by
  intros Ht V
  cases V with
  | inl Vb => assumption
  | inr Vn =>
    cases Vn <;> cases Ht


theorem tm.value.n_canonical {t: tm}:
  t.has_type .N -> t.value -> t.nvalue
:= by
  intros Ht V
  cases V with
  | inl Vb =>
    cases Vb <;> cases Ht
  | inr Vn => assumption


theorem tm.has_type.progress {t: tm} T:
  t.has_type T -> t.value \/ exists t', t.step t'
:= by
  intros Ht
  induction Ht with
  | True | False | Zero =>
    left
    try (left; solve_by_elim)
    try (right; solve_by_elim)
  | @If t1 t2 t3 T H1 H2 H3 IH1 IH2 IH3 =>
    right
    cases IH1 with
    | inl V =>
      have V := V.b_canonical H1
      cases V <;> solve_by_elim
    | inr H =>
      constructor
      . constructor
        exact H.choose_spec
  | Succ Ht IH =>
    cases IH with
    | inl V =>
      have V := V.n_canonical Ht
      left; right
      constructor; assumption
    | inr H =>
      right
      constructor
      . constructor
        exact H.choose_spec
  | Pred Ht IH =>
    cases IH with
    | inl V =>
      have V := V.n_canonical Ht
      right
      cases V with
      | zero =>
        constructor
        . constructor
      | succ =>
        let V := V.n_canonical Ht
        constructor
        . constructor
          cases V
          . assumption
    | inr H =>
      right
      constructor
      . constructor
        exact H.choose_spec
  | Iszero Ht IH =>
    cases IH with
    | inl V =>
      have V := V.n_canonical Ht
      right
      cases V with
      | zero =>
        constructor
        . constructor
      | succ =>
        let V := V.n_canonical Ht
        constructor
        . constructor
          cases V
          . assumption
    | inr H =>
      right
      constructor
      . constructor
        exact H.choose_spec


theorem tm.has_type.preservation {t t': tm} {T}:
  t.has_type T ->
  t.step t' ->
  t'.has_type T
:= by
  intros Ht
  revert t'
  induction Ht with (intros t' Hs)
  | True | False | Zero =>
    cases Hs
  | @If t1 t2 t3 T H1 H2 H3 IH1 IH2 IH3 =>
    cases Hs <;> solve_by_elim
  | Succ Ht IH =>
    cases Hs
    constructor
    apply IH
    assumption
  | Pred Ht IH =>
    cases Hs with
    | Pred0 => constructor
    | PredSucc V =>
      cases Ht
      assumption
    | Pred Hs =>
      constructor
      apply IH
      apply Hs
  | Iszero Ht IH =>
    cases Hs with
    | Iszero =>
      constructor
      apply IH
      assumption
    | _ => constructor


abbrev tm.multistep := RTCl (tm.step)
theorem tm.has_type.soundness {t t': tm} {T}:
  t.has_type T ->
  t.multistep t' ->
  ¬t'.stuck
:= by
  intros Ht Hs
  induction Hs with
  | refl =>
    let Ht := Ht.progress
    intros contra
    cases Ht with
    | inl V =>
      apply contra.right
      assumption
    | inr Hs =>
      apply contra.left
      assumption
  | step H1 H2 IH =>
    apply IH
    apply Ht.preservation
    apply H1


theorem tm.subject_expansion: ¬(forall (t t': tm) (T),
  t.step t' -> t'.has_type T -> t.has_type T)
:= by
  intros contra
  let t: tm := .ite .tru .zro .fls
  let t': tm := .zro
  specialize (contra t t' .N)
  have H1: t.step t' := by
    constructor
  have H2: t'.has_type .N := by
    constructor
  specialize (contra H1 H2)
  unfold t at contra
  cases contra
  contradiction


-- inductive tm : Type where
--   | tru : tm
--   | fls : tm
--   | ite : tm -> tm -> tm -> tm
--   | zro : tm
--   | scc : tm -> tm
--   | prd : tm -> tm
--   | iszro : tm -> tm

inductive tm.big_step: Relation tm where
  | Value {t: tm}: t.value -> t.big_step t
  | IfTrue {t1 t2 t2' t3: tm}:
    t1.big_step .tru ->
    t2.big_step t2' ->
    tm.big_step (.ite t1 t2 t3) t2'
  | IfFalse {t1 t2 t3 t3': tm}:
    t1.big_step .fls ->
    t3.big_step t3' ->
    tm.big_step (.ite t1 t2 t3) t3'
  | Succ {t1 t2: tm}: t1.big_step t2 -> tm.big_step t1.scc t2.scc
  | Pred0 {t: tm}: t.big_step .zro -> tm.big_step (.prd t) .zro
  | PredSucc {t1 t2: tm}: t1.big_step t2.scc -> tm.big_step (.prd t1) t2
  | Iszero0 {t: tm}: t.big_step .zro -> tm.big_step (.iszro t) .tru
  | IszeroSucc {t1 t2: tm}: t1.big_step t2.scc -> tm.big_step (.iszro t1) .fls


theorem tm.big_step.nvalue_refl {t t': tm}:
  t.nvalue -> t.big_step t' -> t = t'
:= by
  intros V
  revert t'
  induction V with (intros t' Hs)
  | zero =>
    cases Hs
    eq_refl
  | succ n V IH =>
    cases Hs with
    | Value => eq_refl
    | Succ H =>
      specialize (IH H)
      rewrite [IH]
      eq_refl


theorem tm.big_step.deterministic {t1 t2 t3: tm}:
  t1.big_step t2 ->
  t1.big_step t3 ->
  t2 = t3
:= by
  intros H12
  revert t3
  induction H12 with (intro t3 H13)
  | Value H =>
    cases H with
    | inl H =>
      cases H <;> cases H13
      . eq_refl
      . eq_refl
    | inr H =>
      apply big_step.nvalue_refl
      . exact H
      . exact H13
  | IfTrue HT H2 IH IH2 =>
    cases H13 with
    | Value H =>
      cases H <;> contradiction
    | IfTrue =>
      apply IH2
      assumption
    | IfFalse HF =>
      specialize (IH HF)
      contradiction
  | IfFalse HF H3 IH IH3 =>
    cases H13 with
    | Value H => cases H <;> contradiction
    | IfFalse =>
      apply IH3
      assumption
    | IfTrue HT =>
      specialize (IH HT)
      contradiction
  | Succ Hs IH =>
    cases H13 with
    | Value H =>
      cases H with
      | inl H => cases H
      | inr H =>
        cases H with | succ _ V =>
        have Hs := Hs.nvalue_refl V
        rewrite [Hs]
        eq_refl
    | Succ H =>
      specialize (IH H)
      rewrite [IH]
      eq_refl
  | Pred0 Hs IH =>
    cases H13 with
    | Value H => cases H <;> contradiction
    | Pred0 => eq_refl
    | PredSucc H =>
      specialize (IH H)
      contradiction
  | PredSucc Hs IH =>
    cases H13 with
    | Value H => cases H <;> contradiction
    | Pred0 H =>
      specialize (IH H)
      contradiction
    | PredSucc H =>
      specialize (IH H)
      cases IH
      eq_refl
  | Iszero0 Hs IH =>
    cases H13 with
    | Value H => cases H <;> contradiction
    | Iszero0 => eq_refl
    | IszeroSucc H =>
      specialize (IH H)
      contradiction
  | IszeroSucc Hs IH =>
    cases H13 with
    | Value H => cases H <;> contradiction
    | Iszero0 H =>
      specialize (IH H)
      contradiction
    | IszeroSucc =>
      eq_refl


theorem tm.has_type.big_step_preservation {t t': tm} {T}:
  t.has_type T ->
  t.big_step t' ->
  t'.has_type T
:= by
  intros Ht
  revert t'
  induction Ht with (intros t' Hs)
  | True | False | Zero =>
    cases Hs
    constructor
  | If H1 H2 H3 IH1 IH2 IH3 =>
    cases Hs with
    | Value H =>
      cases H <;> contradiction
    | IfTrue _ Hs =>
      apply IH2
      assumption
    | IfFalse =>
      apply IH3
      assumption
  | Succ Ht IH =>
    cases Hs <;> solve_by_elim
  | Pred Ht IH =>
    cases Hs with
    | Value H => cases H <;> contradiction
    | Pred0 => constructor
    | PredSucc Hs =>
      specialize (IH Hs)
      cases IH
      assumption
  | Iszero Ht IH =>
    cases Hs with
    | Value H => cases H <;> contradiction
    | Iszero0 => constructor
    | IszeroSucc Hs => constructor


theorem tm.has_type.big_step_progress_lemma {t1 t2 t3 : tm} {T}:
  t1.has_type ty.B ->
  t2.has_type T ->
  t3.has_type T ->
  (t1.value ∨ ∃ t', t1.big_step t' ∧ t'.value) ->
  (t2.value ∨ ∃ t', t2.big_step t' ∧ t'.value) ->
  (t3.value ∨ ∃ t', t3.big_step t' ∧ t'.value) ->
  ∃ t', (t1.ite t2 t3).big_step t' ∧ t'.value
:= by
  intros H1 H2 H3 IH1 IH2 IH3
  cases IH1 with
  | inl V =>
    let V := V.b_canonical H1
    cases V with
    | true =>
      cases IH2 with
      | inl V2 =>
        exists t2
        apply And.intro
        . apply big_step.IfTrue
          . apply big_step.Value
            left
            exact V
          . apply big_step.Value
            exact V2
        . exact V2
      | inr H =>
        let ⟨t', ⟨Hs, V⟩⟩ := H
        exists t'
        apply And.intro
        . apply big_step.IfTrue
          . apply big_step.Value
            left
            apply bvalue.true
          . exact Hs
        . exact V
    | false =>
      cases IH3 with
      | inl V3 =>
        exists t3
        apply And.intro
        . apply big_step.IfFalse
          . apply big_step.Value
            left
            exact V
          . apply big_step.Value
            exact V3
        . exact V3
      | inr H =>
        let ⟨t', ⟨Hs, V⟩⟩ := H
        exists t'
        apply And.intro
        . apply big_step.IfFalse
          . apply big_step.Value
            left
            apply bvalue.false
          . exact Hs
        . exact V
  | inr H =>
    let ⟨t', ⟨Hst', V⟩⟩ := H
    let H1 := H1.big_step_preservation Hst'
    let V := V.b_canonical H1
    cases V with
    | true =>
      cases IH2 with
      | inl V2 =>
        exists t2
        apply And.intro
        . apply big_step.IfTrue
          . apply Hst'
          . apply big_step.Value
            exact V2
        . exact V2
      | inr H =>
        let ⟨t', ⟨Hs, V⟩⟩ := H
        exists t'
        apply And.intro
        . apply big_step.IfTrue
          . apply Hst'
          . exact Hs
        . exact V
    | false =>
      cases IH3 with
      | inl V3 =>
        exists t3
        apply And.intro
        . apply big_step.IfFalse
          . apply Hst'
          . apply big_step.Value
            exact V3
        . exact V3
      | inr H =>
        let ⟨t', ⟨Hs, V⟩⟩ := H
        exists t'
        apply And.intro
        . apply big_step.IfFalse
          . apply Hst'
          . exact Hs
        . exact V


theorem tm.has_type.big_step_progress {t: tm} T:
  t.has_type T -> t.value \/ exists t', (t.big_step t' ∧ t'.value)
:= by
  intros Ht
  induction Ht with
  | True =>
    left; left
    apply bvalue.true
  | False =>
    left; left
    apply bvalue.false
  | Zero =>
    left; right
    apply nvalue.zero
  | @If t1 t2 t3 T H1 H2 H3 IH1 IH2 IH3 =>
    right
    apply tm.has_type.big_step_progress_lemma <;> solve_by_elim
  | Succ Ht IH =>
    cases IH with
    | inl H =>
      left; right
      constructor
      apply H.n_canonical Ht
    | inr H =>
      let ⟨t', ⟨Hs, V⟩⟩ := H
      right
      exists t'.scc
      apply And.intro
      . apply big_step.Succ
        exact Hs
      . right
        constructor
        apply value.n_canonical
        apply Ht.big_step_preservation
        . exact Hs
        . exact V
  | Pred Ht IH =>
    right
    cases IH with
    | inl V =>
      have Ht := V.n_canonical Ht
      cases Ht with
      | zero =>
        exists tm.zro
        apply And.intro
        . apply big_step.Pred0
          apply big_step.Value
          exact V
        . apply V
      | succ n H =>
        exists n
        apply And.intro
        . apply big_step.PredSucc
          apply big_step.Value
          exact V
        . right
          apply H
    | inr H =>
      let ⟨t', ⟨H, V⟩⟩ := H
      let Ht := Ht.big_step_preservation H
      let V := V.n_canonical Ht
      cases V with
      | zero =>
        exists tm.zro
        solve_by_elim
      | succ t' =>
        exists t'
        apply And.intro
        . apply big_step.PredSucc
          exact H
        . right
          cases V
          assumption
  | Iszero Ht IH =>
    right
    cases IH with
    | inl V =>
      have Ht := V.n_canonical Ht
      cases Ht with
      | zero =>
        exists tm.tru
        apply And.intro
        . apply big_step.Iszero0
          apply big_step.Value
          exact V
        . left
          apply bvalue.true
      | succ n H =>
        exists tm.fls
        apply And.intro
        . apply big_step.IszeroSucc
          apply big_step.Value
          exact V
        . left
          apply bvalue.false
    | inr H =>
      let ⟨t', ⟨H, V⟩⟩ := H
      let Ht := Ht.big_step_preservation H
      let V := V.n_canonical Ht
      cases V with
      | zero =>
        exists tm.tru
        apply And.intro
        . apply big_step.Iszero0
          exact H
        . left
          apply bvalue.true
      | succ t' =>
        exists tm.fls
        apply And.intro
        . apply big_step.IszeroSucc
          exact H
        . left
          apply bvalue.false

end tm
