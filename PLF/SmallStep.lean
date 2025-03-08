import PLF.Relation
import PLF.Imp

inductive TM : Type where
  | C : Nat -> TM
  | P : TM -> TM -> TM


instance: Coe Nat TM where
  coe := .C


@[simp]
def TM.eval: TM -> Nat
  | C n => n
  | P a b => a.eval + b.eval


inductive TM.EvalTo: TM -> Nat -> Prop where
  | Const n: (TM.C n).EvalTo n
  | Plus (t1 t2: TM) n1 n2:
    t1.EvalTo n1 -> t2.EvalTo n2 -> (t1.P t2).EvalTo (n1 + n2)


inductive TM.value: TM -> Prop where
  | C n: (TM.C n).value


inductive TM.step: Relation TM where
  | PCC (n1 n2: Nat): ((TM.C n1).P (.C n2)).step (.C (n1 + n2))
  | P1 (t1 t1' t2: TM): t1.step t1' -> (t1.P t2).step (t1'.P t2)
  | P2 (v t2 t2': TM): v.value -> t2.step t2' -> (v.P t2).step (v.P t2')


theorem TM.step.deterministic {x y1 y2: TM}:
  x.step y1 ->
  x.step y2 ->
  y1 = y2
:= by
  intros Hy1
  revert y2
  induction Hy1 with
  | PCC n1 n2 =>
    intros y2 Hy2
    cases Hy2 with
    | PCC => eq_refl
    | P1 _ _ _ Hy2 => cases Hy2
    | P2 _ _ _ Hv Hy2 => cases Hy2
  | P1 t1 t1' t2 H1 IH =>
    intros y2 Hy2
    cases Hy2 with
    | PCC => cases H1
    | P1 _ _ _ Hy2 =>
      specialize (IH Hy2)
      solve_by_elim
    | P2 _ _ _ Hv Hy2 =>
      cases Hv
      cases H1
  | P2 n1 t2 t2' Hv H2 IH =>
    cases Hv
    intros y2 Hy2
    cases Hy2 with
    | PCC => cases H2
    | P1 _ _ _ Hy2 => cases Hy2
    | P2 _ _ _ _ Hy2 =>
      specialize (IH Hy2)
      solve_by_elim


def TM.strongProgress (t: TM): t.value \/ exists t', t.step t'
:= by
  induction t with
  | C n =>
    left
    constructor
  | P t1 t2 IH1 IH2 =>
    right
    cases IH1 with
    | inl Hv1 =>
      cases Hv1 with | C n1 =>
      cases IH2 with
      | inl Hv2 =>
        cases Hv2 with | C n2 =>
        exists (TM.C (n1 + n2))
        constructor
      | inr H =>
        let ⟨t2', Ht2'⟩ := H
        exists (TM.C n1).P t2'
        constructor
        . constructor
        . exact Ht2'
    | inr H =>
      let ⟨t1', Ht1'⟩ := H
      exists t1'.P t2
      constructor
      exact Ht1'


abbrev TM.normal (t: TM) := TM.step.Normal t

theorem TM.value.normal {t: TM}: t.value -> t.normal := by
  intros H
  cases H with | C n =>
  intros contra
  cases contra.choose_spec


theorem TM.normal.value {t: TM}: t.normal -> t.value := by
  cases t with
  | C n =>
    intros H
    constructor
  | P t1 t2 =>
    intros H
    cases (t1.P t2).strongProgress with
    | inl => assumption
    | inr K =>
      exfalso
      apply H
      exact K


abbrev TM.multistep := RTCl TM.step
theorem TM.multistep.congr1 {t1 t1' t2: TM}:
  t1.multistep t1' -> (t1.P t2).multistep (t1'.P t2)
:= by
  intros H
  apply TM.step.keep_cong (f := fun t => t.P t2)
  . intros a b
    apply TM.step.P1
  . apply H


theorem TM.multistep.congr2 {v t2 t2': TM}:
  v.value ->
  t2.multistep t2' -> (v.P t2).multistep (v.P t2')
:= by
  intros V H
  apply TM.step.keep_cong (f := fun t => v.P t)
  . intros a b
    apply TM.step.P2
    apply V
  . apply H


instance: Irreflexive TM.step where
  irrefl := by
    intros t H
    induction t with
    | C => cases H
    | P t1 t2 IHt1 IHt2 =>
      cases H with solve_by_elim


@[simp]
def TM.normalize: TM -> TM
  | .C n => .C n
  | .P t1 t2 => match (t1.normalize, t2.normalize) with
    | (.C n1, .C n2) => .C (n1 + n2)
    | (t1', t2') => t1'.P t2'


theorem TM.normalize_normal (t: TM): (t.normalize).normal := by
  induction t with
  | C n =>
    simp
    intros contra
    cases contra.choose_spec
  | P t1 t2 IH1 IH2 =>
    generalize E1: t1.normalize = c1
    generalize E2: t2.normalize = c2
    rewrite [E1] at IH1
    rewrite [E2] at IH2
    have H1 := IH1.value
    cases H1
    have H2 := IH2.value
    cases H2
    simp
    rewrite [E1, E2]
    simp
    intros contra
    cases contra.choose_spec


theorem TM.normalize_char (t: TM): exists n,
  t.normalize = .C n /\ t.multistep (.C n)
:= by
  induction t with
  | C n =>
    simp
    apply RTCl.refl
  | P t1 t2 IH1 IH2 =>
    let ⟨n1, ⟨E1, H1⟩⟩ := IH1
    let ⟨n2, ⟨E2, H2⟩⟩ := IH2
    exists (n1 + n2)
    apply And.intro
    . simp
      rewrite [E1, E2]
      simp
    . apply TM.multistep.trans
      . apply TM.multistep.congr1 H1
      . apply TM.multistep.trans
        . apply TM.multistep.congr2
          . constructor
          . apply H2
        . apply TM.step.super
          apply TM.step.PCC


theorem TM.multistep_normalize (t: TM): t.multistep t.normalize := by
  let ⟨n, ⟨E, H⟩⟩ := t.normalize_char
  rewrite [E]
  assumption


namespace TM

theorem eval_multistep {t: TM} n: t.EvalTo n -> t.multistep n := by
  intros H
  induction H with
  | Const n => apply multistep.refl
  | Plus t1 t2 n1 n2 H1 H2 IH1 IH2 =>
    have H: (t1.P t2).multistep ((TM.C n1).P t2) := by
      apply TM.multistep.congr1
      apply IH1
    apply TM.multistep.trans
    . apply TM.multistep.congr1
      apply IH1
    . apply TM.multistep.trans
      . apply TM.multistep.congr2
        . /- value -/ constructor
        . apply IH2
      . apply TM.step.super
        constructor


theorem step_EvalTo {t t': TM} {n}:
  t.step t' ->
  t'.EvalTo n ->
  t.EvalTo n
:= by
  intros Hs
  revert n
  induction Hs with
  | PCC n1 n2 =>
    intro n HE
    cases HE
    constructor
    . constructor
    . constructor
  | P1 t1 t1' t2 Hs IH =>
    intros n HE
    cases HE with | Plus _ _ n1 n2 H1 H2 =>
    specialize (IH H1)
    constructor <;> assumption
  | P2 t1 t2 t2' V Hs IH =>
    intros n HE
    cases HE with | Plus _ _ n1 n2 H1 H2 =>
    specialize (IH H2)
    constructor <;> assumption


theorem multistep_EvalTo_lemma {t: TM}:
  forall n, t.normalize = .C n -> t.EvalTo n
:= by
  induction t with
  | C m =>
    intros n
    simp
    intros H
    rewrite [H]
    constructor
  | P t1 t2 IH1 IH2 =>
    intros n
    let ⟨n1, ⟨E1, H1⟩⟩ := t1.normalize_char
    specialize (IH1 n1 E1)
    let ⟨n2, ⟨E2, H2⟩⟩ := t2.normalize_char
    specialize (IH2 n2 E2)
    simp
    rewrite [E1, E2]
    simp
    intros H
    rewrite [<-H]
    constructor <;> assumption


theorem multistep_EvalTo {t: TM}: exists n, t.normalize = .C n /\ t.EvalTo n
:= by
  let ⟨n, ⟨E, H⟩⟩ := t.normalize_char
  exists n
  solve_by_elim [multistep_EvalTo_lemma]


theorem eval_EvalTo {t: TM} {n: Nat}:
  t.eval = n <-> t.EvalTo n
:= by
  revert n
  induction t with
  | C m =>
    intros n
    simp
    apply Iff.intro
    . intros E
      rewrite [E]
      constructor
    . intros H
      cases H
      eq_refl
  | P t1 t2 IH1 IH2 =>
    intros n
    simp
    apply Iff.intro
    . intros E
      rewrite [<-E]
      constructor
      . apply IH1.mp
        eq_refl
      . apply IH2.mp
        eq_refl
    . intros H
      cases H with | Plus t1 t2 n1 n2 H1 H2 =>
      let E1 := IH1.mpr H1
      let E2 := IH2.mpr H2
      subst_eqs
      eq_refl


end TM


inductive AExp.value : AExp -> Prop where
  | Num n: AExp.value (.Num n)


inductive AExp.step (st : State) : Relation AExp where
  | Id {i: String}: (AExp.Var i).step st (st i)
  | Plus1 {a1 a1' a2: AExp}:
      a1.step st a1' ->
      <{A| [a1] + [a2] }>.step st <{A| [a1'] + [a2] }>
  | Plus2 {v1 a2 a2': AExp}:
      v1.value ->
      a2.step st a2' ->
      <{A| [v1] + [a2] }>.step st <{A| [v1] + [a2'] }>
  | Plus {v1 v2 : Nat}:
      <{A| [v1] + [v2] }>.step st (v1 + v2)
  | Minus1 {a1 a1' a2: AExp}:
      a1.step st a1' ->
      <{A| [a1] - [a2] }>.step st <{A| [a1'] - [a2] }>
  | Minus2 {v1 a2 a2': AExp}:
      v1.value ->
      a2.step st a2' ->
      <{A| [v1] - [a2] }>.step st <{A| [v1] - [a2'] }>
  | Minus {v1 v2 : Nat}:
      <{A| [v1] - [v2] }>.step st (v1 - v2)
  | Mult1 {a1 a1' a2: AExp}:
      a1.step st a1' ->
      <{A| [a1] * [a2] }>.step st <{A| [a1'] * [a2] }>
  | Mult2 {v1 a2 a2': AExp}:
      v1.value ->
      a2.step st a2' ->
      <{A| [v1] * [a2] }>.step st <{A| [v1] * [a2'] }>
  | Mult {v1 v2 : Nat}:
      <{A| [v1] * [v2] }>.step st (v1 * v2)

notation:60 a "/" st "a->" b:61 => AExp.step st a b


inductive BExp.step (st : State) : Relation BExp where
  | Eq1 {a1 a1' a2: AExp}:
      a1 / st a-> a1' ->
      <{B| [a1] == [a2] }>.step st <{B| [a1'] == [a2] }>
  | Eq2 {v1 a2 a2': AExp}:
      v1.value ->
      a2 / st a-> a2' ->
      <{B| [v1] == [a2] }>.step st <{B| [v1] == [a2'] }>
  | Eq {v1 v2 : Nat}:
      <{B| [v1] == [v2] }>.step st
        (if (v1 == v2) then <{ true }> else <{ false }>)
  | LtEq1 {a1 a1' a2: AExp}:
      a1 / st a-> a1' ->
      <{B| [a1] <= [a2] }>.step st <{B| [a1'] <= [a2] }>
  | LtEq2 {v1 a2 a2': AExp}:
      v1.value ->
      a2 / st a-> a2' ->
      <{B| [v1] <= [a2] }>.step st <{B| [v1] <= [a2'] }>
  | LtEq {v1 v2 : Nat}:
      <{B| [v1] <= [v2] }>.step st
        (if (v1.ble v2) then <{ true }> else <{ false }>)
  | NotStep {b1 b1': BExp}:
      b1.step st b1' ->
      <{B| ~[b1] }>.step st <{B| ~ [b1'] }>
  | NotTrue: <{B| ~true }>.step st <{B| false }>
  | NotFalse: <{B| ~false }>.step st <{B| true }>
  | AndStep {b1 b1' b2: BExp}:
      b1.step st b1' ->
      <{B| [b1] && [b2] }>.step st <{B| [b1'] && [b2] }>
  | AndTrueStep {b2 b2': BExp}:
      b2.step st b2' ->
      <{B| true && [b2] }>.step st <{B| true && [b2'] }>
  | AndFalse {b2: BExp}:
      <{B| false && [b2] }>.step st <{B| false }>
  | AndTrueTrue: <{B| true && true }>.step st <{B| true }>
  | AndTrueFalse: <{B| true && false }>.step st <{B| false }>

notation:60 a "/" st "b->" b:61 => BExp.step st a b


-- Skip behaviors like the normal form
inductive Imp.step : Relation (Imp × State) where
  | AsgnStep {st} {i} {a1 a1'}:
    a1 / st a-> a1' ->
    Imp.step (<{ [i] := [a1] }>, st) (<{ [i] := [a1'] }>, st)
  | Asgn {st i} {n : Nat}:
    Imp.step (<{ [i] := [n] }>, st) (<{ skip }>, state![i => n ; st])
  | SeqStep {st c1 c1' st' c2}:
    Imp.step (c1, st) (c1', st') ->
    Imp.step (<{ c1 ; c2 }>, st) (<{ c1' ; c2 }>, st')
  | SeqFinish : ∀ st c2,
    Imp.step (<{ skip ; c2 }>, st) (c2, st)
  | IfStep {st b1 b1' c1 c2}:
    b1 / st b-> b1' ->
    Imp.step
      (<{ if b1 then c1 else c2 end }>, st)
      (<{ if b1' then c1 else c2 end }>, st)
  | IfTrue {st c1 c2}:
    Imp.step (<{ if true then c1 else c2 end }>, st) (c1, st)
  | IfFalse {st c1 c2}:
    Imp.step (<{ if false then c1 else c2 end }>, st) (c2, st)
  | While {st b1 c1}:
    Imp.step
      (<{ while b1 do c1 end }>, st)
      (<{ if b1 then c1; while b1 do c1 end else skip end }>, st)


notation:60 t1 "/" st1:75 "c->" t2:75 "/" st2 => Imp.step (t1, st1) (t2, st2)
abbrev Imp.multistep := RTCl Imp.step

notation:60 t1 "/" st1:75 "c->*" t2:75 "|" st2 => Imp.multistep (t1, st1) (t2, st2)


section StackCalculator

abbrev Stack := List Nat
abbrev Prog := List SInstr

inductive StackStep (st : State) : Relation (Prog × Stack) where
  | Push {stk n p}:
    StackStep st (.SPush n :: p, stk) (p, n :: stk)
  | Load {stk i p}:
    StackStep st (.SLoad i :: p, stk) (p, st i :: stk)
  | Plus {stk n m p}:
    StackStep st (.SPlus :: p, n::m::stk) (p, (m+n)::stk)
  | Minus {stk n m p}:
    StackStep st (.SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | Mult {stk n m p}:
    StackStep st (.SMult :: p, n::m::stk) (p, (m*n)::stk)


theorem StackStep.deterministic {st p s p1 s1 p2 s2}:
  StackStep st (p, s) (p1, s1) ->
  StackStep st (p, s) (p2, s2) ->
  (p1, s1) = (p2, s2)
:= by
  intros H1 H2
  cases p with
  | nil =>
    cases H1
  | cons x xs =>
    cases x with (cases H1 <;> cases H2 <;> eq_refl)


abbrev StackMultiStep st := RTCl (StackStep st)


-- The original correctness is the big step. We only compare the
-- final state. Now, I want to compare some intermediate state by
-- the multistep relation.
theorem AExp.s_compile.step_correct {st: State} {e: AExp} {stk prog}:
  StackMultiStep st (e.s_compile ++ prog, stk) (prog, st.aeval e::stk)
:= by
  revert stk prog
  induction e with
  | Num n | Var x =>
    intros stk prog
    simp
    apply (StackStep st).super
    constructor
  | Plus n1 n2 IH1 IH2 | Minus _ _ IH1 IH2 | Mult _ _ IH1 IH2 =>
    intros stk prog
    simp
    apply RTCl.trans
    . apply IH1
    . apply RTCl.trans
      . apply IH2
      . apply (StackStep st).super
        constructor

end StackCalculator
