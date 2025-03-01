import PLF.Imp
import PLF.Relation


@[simp]
def AExp.equiv: Relation AExp := fun (a1 a2: AExp) =>
  forall (st: State), st.aeval a1 = st.aeval a2


@[simp]
def BExp.equiv: Relation BExp := fun (b1 b2: BExp) =>
  forall (st: State), st.beval b1 = st.beval b2


example: <{A| X - X }>.equiv <{ 0 }> := by
  intros st
  simp


example: <{B| X - X == 0 }>.equiv <{B| true }> := by
  intros st
  simp


def Imp.equiv: Relation Imp := fun (c1 c2: Imp) =>
  forall {st1 st2 : State}, (st1 =[ c1 ]=> st2) <-> (st1 =[ c2 ]=> st2)


def Imp.refines: Relation Imp := fun (c1 c2 : Imp) =>
  forall (st1 st2 : State), (st1 =[ c1 ]=> st2) → (st1 =[ c2 ]=> st2)


theorem Imp.skip_left {c: Imp}: <{ skip; c }>.equiv c := by
  intros st1 st2
  apply Iff.intro
  . intros H
    cases H with
    | @BSeq _ _ _ st3 _ H13 H32 =>
      cases H13
      apply H32
  . intros H
    apply BigStep.BSeq
    . apply BigStep.BSkip
    . exact H


theorem Imp.skip_right {c: Imp}: <{ c; skip }>.equiv c := by
  intros st1 st2
  apply Iff.intro
  . intros H
    cases H with
    | @BSeq _ _ _ st3 _ H13 H32 =>
      cases H32
      apply H13
  . intros H
    apply BigStep.BSeq
    . exact H
    . apply BigStep.BSkip


theorem Imp.if_true_simple {c1 c2: Imp}:
  <{ if true then c1 else c2 end }>.equiv c1
:= by
  intros st1 st2
  apply Iff.intro
  . intros H
    cases H with
    | BIfTrue HT HB =>
      apply HB
    | BIfFalse HF _ =>
      simp at HF
  . intros H
    apply BigStep.BIfTrue
    . simp
    . exact H


theorem Imp.if_true {b: BExp} {c1 c2: Imp}:
  b.equiv .True -> <{ if b then c1 else c2 end }>.equiv c1
:= by
  intros H
  intros st1 st2
  apply Iff.intro
  . intros K
    cases K with
    | BIfTrue HT K =>
      exact K
    | BIfFalse HF K =>
      specialize (H st1)
      simp at H
      rewrite [HF] at H
      contradiction
  . intros K
    apply BigStep.BIfTrue
    . apply H
    . exact K


theorem Imp.if_false {b: BExp} {c1 c2: Imp}:
  b.equiv .False -> <{ if b then c1 else c2 end }>.equiv c2
:= by
  intros H
  intros st1 st2
  apply Iff.intro
  . intros K
    cases K with
    | BIfFalse _ K =>
      exact K
    | BIfTrue HF K =>
      specialize (H st1)
      simp at H
      rewrite [HF] at H
      contradiction
  . intros K
    apply BigStep.BIfFalse
    . apply H
    . exact K


theorem Imp.swap_if_branches {b: BExp} {c1 c2: Imp}:
  <{ if b then c1 else c2 end }>.equiv <{ if ~b then c2 else c1 end }>
:= by
  intros st1 st2
  apply Iff.intro
  . intros H
    generalize E: st1.beval b = t
    cases t with
    | true =>
      apply BigStep.BIfFalse
      . simp
        exact E
      . cases H with
        | BIfTrue _ H =>
          apply H
        | BIfFalse HF =>
          rewrite [E] at HF
          contradiction
    | false =>
      apply BigStep.BIfTrue
      . simp
        exact E
      . cases H with
        | BIfTrue HT _ =>
          rewrite [E] at HT
          contradiction
        | BIfFalse _ H =>
          exact H
  . intros H
    generalize E: st1.beval b = t
    cases t with
    | false =>
      apply BigStep.BIfFalse
      . exact E
      . cases H with
        | BIfTrue _ H =>
          apply H
        | BIfFalse HF =>
          simp at HF
          rewrite [E] at HF
          contradiction
    | true =>
      apply BigStep.BIfTrue
      . exact E
      . cases H with
        | BIfTrue HT _ =>
          simp at HT
          rewrite [E] at HT
          contradiction
        | BIfFalse _ H =>
          exact H


theorem Imp.while_false {b: BExp} {c: Imp}:
  b.equiv false ->
  <{ while b do c end }>.equiv <{ skip }>
:= by
  simp
  intros Hb st1 st2
  specialize (Hb st1)
  apply Iff.intro
  . intro HW
    cases HW with
    | BWhileTrue HT =>
      rewrite [Hb] at HT
      contradiction
    | BWhileFalse =>
      apply BigStep.BSkip
  . intros H
    cases H
    apply BigStep.BWhileFalse
    exact Hb


theorem Imp.while_true_nonterm {b: BExp} {c st1 st2}:
  b.equiv true -> Not ( st1 =[ while b do c end ]=> st2 )
:= by
  simp
  intros Hb
  generalize E: <{ while b do c end }> = l
  intros contra
  induction contra with
  | BWhileTrue HT H12 H23 IH1 IH2 =>
    cases E
    apply IH2
    eq_refl
  | BWhileFalse HF =>
    cases E
    rewrite [Hb] at HF
    contradiction
  | _ => cases E


theorem Imp.while_true {b: BExp} {c}:
  b.equiv true ->
  <{ while b do c end }>.equiv <{ while true do skip end }>
:= by
  simp
  intros Hb
  intros st1 st2
  apply Iff.intro
  . intros H
    exfalso
    apply Imp.while_true_nonterm Hb
    apply H
  . intros HW
    exfalso
    apply Imp.while_true_nonterm (b := .True) (c := .Skip)
    simp
    apply HW


theorem Imp.loop_unrolling {b c}:
    <{ while b do c end }>.equiv
    <{ if b then c ; while b do c end else skip end }>
:= by
  intros st1 st2
  generalize E: st1.beval b = t
  cases t with
  | true =>
    apply Iff.intro
    . intros H
      apply BigStep.BIfTrue E
      cases H with
      | BWhileTrue _ H1 H2=>
        apply BigStep.BSeq H1
        exact H2
      | BWhileFalse HF =>
        rewrite [E] at HF
        contradiction
    . intros H
      cases H with
      | BIfTrue HT H =>
        cases H with
        | @BSeq _ _ st1 t st2 H1t Ht2 =>
          apply BigStep.BWhileTrue E
          . apply H1t
          . apply Ht2
      | BIfFalse HF =>
        rewrite [E] at HF
        contradiction
  | false =>
    apply Iff.intro
    . intros H
      apply BigStep.BIfFalse E
      cases H with
      | BWhileTrue HT =>
        rewrite [E] at HT
        contradiction
      | BWhileFalse =>
        apply BigStep.BSkip
    . intros H
      cases H with
      | BIfTrue HT =>
        rewrite [E] at HT
        contradiction
      | BIfFalse _ H =>
        cases H
        apply BigStep.BWhileFalse
        exact E


theorem Imp.seq_assoc {c1 c2 c3}:
  <{ (c1; c2) ;c3 }>.equiv <{ c1; (c2; c3) }>
:= by
  intros st1 st4
  apply Iff.intro
  . intros H
    cases H with
    | @BSeq _ _ _ st3 _ H1 H3 =>
      cases H1 with
      | @BSeq _ _ _ st2 _ H1 H2 =>
        apply H1.BSeq
        apply H2.BSeq
        apply H3
  . intros H
    cases H with
    | @BSeq _ _ _ st2 _ H1 H2 =>
      cases H2 with
      | @BSeq _ _ _ st3 _ H2 H3 =>
        apply BigStep.BSeq
        . apply H1.BSeq
          apply H2
        . exact H3


theorem Imp.identity_assignment {x}:
  <{ [x] := [x] }>.equiv <{ skip }>
:= by
  intros st1 st2
  have E: st1.update x (st1 x) = st1 := by
        apply TotalMap.update_same
  apply Iff.intro
  . intros H
    cases H with
    | @BAsgn _ _ n _ H =>
      simp at H
      rewrite [H] at E
      rewrite [E]
      apply BigStep.BSkip
  . intros H
    have E: st2 = st1.update x (st1 x) := by
      cases H
      symm
      exact E
    rewrite [E]
    apply BigStep.BAsgn
    eq_refl

theorem Imp.assign_aequiv {x: String} {a}:
  <{A| [x] }>.equiv a -> <{ skip }>.equiv <{ [x] := [a] }>
:= by
  intros Hx
  intros st1 st2
  specialize (Hx st1)
  simp at Hx
  apply Iff.intro
  . intros H
    have E: st1.update x (st1.aeval a) = st2 := by
      rewrite [<-Hx]
      cases H
      apply TotalMap.update_same
    rewrite [<-E]
    apply BigStep.BAsgn
    eq_refl
  . intros H
    cases H with
    | BAsgn E =>
      rewrite [E] at Hx
      rewrite [<-Hx]
      let E := st1.update_same (x := x)
      unfold State.update
      rewrite [E]
      apply BigStep.BSkip


instance: Reflexive AExp.equiv where
  refl {a} := by
    intros st
    eq_refl

instance: Symmetric AExp.equiv where
  symm {a b} := by
    intros H st
    specialize (H st)
    symm
    exact H

instance: Transitive AExp.equiv where
  trans {a b c} := by
    intros Hab Hbc
    intros st
    specialize (Hab st)
    specialize (Hbc st)
    apply Hab.trans Hbc


instance: Reflexive BExp.equiv where
  refl {a} := by
    intros st
    eq_refl

instance: Symmetric BExp.equiv where
  symm {a b} := by
    intros H st
    specialize (H st)
    symm
    exact H

instance: Transitive BExp.equiv where
  trans {a b c} := by
    intros Hab Hbc
    intros st
    specialize (Hab st)
    specialize (Hbc st)
    apply Hab.trans Hbc


instance: Reflexive Imp.equiv where
  refl {a} := by
    intros st1 st2
    apply Iff.refl

instance: Symmetric Imp.equiv where
  symm {a b} := by
    intros H st1 st2
    apply H.symm

instance: Transitive Imp.equiv where
  trans {a b c} := by
    intros Hab Hbc
    intros st1 st2
    apply Hab.trans Hbc


theorem Imp.Asgn.congruence_st {x} {a1 a2: AExp} {st1: State}:
  (st1.aeval a1 = st1.aeval a2) -> {st2: State} ->
  st1 =[ [x] := [a1] ]=> st2 <-> st1 =[ [x] := [a2] ]=> st2
:= by
  intros E
  intros st2
  apply Iff.intro
  . intros H
    cases H with
    | BAsgn H =>
      rewrite [<-H]
      rewrite [E]
      apply BigStep.BAsgn
      eq_refl
  . intros H
    cases H with
    | BAsgn H =>
      rewrite [<-H]
      rewrite [<-E]
      apply BigStep.BAsgn
      eq_refl


theorem Imp.Asgn.congruence {x} {a1 a2: AExp}:
  a1.equiv a2 -> <{[x] := [a1]}>.equiv <{[x] := [a2]}>
:= by
  intros E
  intros st1 st2
  specialize E st1
  apply Imp.Asgn.congruence_st
  apply E


theorem Imp.While.congruence {b1 b2: BExp} {c1 c2: Imp}:
  b1.equiv b2 -> c1.equiv c2 ->
  <{ while b1 do c1 end }>.equiv <{ while b2 do c2 end }>
:= by
  have A {b1 b2 : BExp} {c1 c2 : Imp} {st1 st2}:
    b1.equiv b2 -> c1.equiv c2 ->
    st1 =[ while b1 do c1 end ]=> st2 ->
    st1 =[ while b2 do c2 end ]=> st2 := by
      intros Hb Hc
      generalize E: <{ while b1 do c1 end }> = t
      intros H
      induction H with
      | @BWhileFalse b c st HF =>
        cases E
        rewrite [Hb] at HF
        apply BigStep.BWhileFalse HF
      | @BWhileTrue b c st1 st2 st3 HT H12 H23 IH12 IH23 =>
        cases E
        rewrite [Hb] at HT
        apply BigStep.BWhileTrue HT
        . apply Hc.mp
          apply H12
        . apply IH23
          eq_refl
      | _ => cases E
  intros Hb Hc
  intros st1 st2
  apply Iff.intro
  . apply A Hb Hc
  . apply A
    . apply BExp.equiv.symm
      apply Hb
    . apply Imp.equiv.symm
      apply Hc


theorem Imp.Seq.congruence {c1 c2 d1 d2: Imp}:
  c1.equiv c2 -> d1.equiv d2 ->
  <{ c1; d1 }>.equiv <{ c2; d2 }>
:= by
  intros Hc Hd
  intros st1 st2
  apply Iff.intro
  . intros H
    cases H with
    | @BSeq _ _ _ t _ H1 H2 =>
      apply BigStep.BSeq
      . apply Hc.mp
        apply H1
      . apply Hd.mp
        apply H2
  . intros H
    cases H with
    | @BSeq _ _ _ t _ H1 H2 =>
      apply BigStep.BSeq
      . apply Hc.mpr
        apply H1
      . apply Hd.mpr
        apply H2


theorem Imp.If.congruence {b1 b2: BExp} {c1 c2 d1 d2: Imp}:
  b1.equiv b2 -> c1.equiv c2 -> d1.equiv d2 ->
    <{ if b1 then c1 else d1 end }>.equiv
    <{ if b2 then c2 else d2 end }>
:= by
  intros Hb Hc Hd
  intros st1 st2
  generalize E: st1.beval b1 = t
  cases t with
  | true =>
    apply Iff.intro
    . intros H
      cases H with
      | BIfTrue _ H =>
        rewrite [Hb] at E
        apply BigStep.BIfTrue E
        apply Hc.mp
        exact H
      | BIfFalse HF =>
        rewrite [E] at HF
        contradiction
    . intros H
      cases H with
      | BIfTrue _ H =>
        apply BigStep.BIfTrue E
        rewrite [Hc]
        exact H
      | BIfFalse HF =>
        rewrite [Hb] at E
        rewrite [E] at HF
        contradiction
  | false =>
    apply Iff.intro
    . intros H
      cases H with
      | BIfTrue HT =>
        rewrite [E] at HT
        contradiction
      | BIfFalse _ H =>
        rewrite [Hb] at E
        apply BigStep.BIfFalse E
        apply Hd.mp
        exact H
    . intros H
      cases H with
      | BIfTrue HT =>
        rewrite [Hb] at E
        rewrite [E] at HT
        contradiction
      | BIfFalse _ H =>
        apply BigStep.BIfFalse E
        apply Hd.mpr
        exact H

example:
  <{ X := 0;
      if X == 0 then Y := 0
      else Y := 42 end }>.equiv
  <{ X := 0;
      if X == 0 then Y := X - X
      else Y := 42 end }>
:= by
  apply Imp.Seq.congruence
  . apply @Imp.equiv.refl
  . apply Imp.If.congruence
    . apply BExp.equiv.refl
    . apply Imp.Asgn.congruence
      intros st
      simp
    . apply @Imp.equiv.refl


abbrev Transformation (A: Type) := A -> A

class Transformation.Sound
  {A: Type}
  (t: Transformation A)
  (R: outParam (Relation A))
where
  sound {a: A}: R a (t a)


def Transformation.sound {A: Type} {t: Transformation A} {R: Relation A}
  [inst: t.Sound R] {a: A}: R a (t a) := inst.sound

def Relation.sound {A: Type} {t: Transformation A} {R: Relation A}
  [inst: t.Sound R] {a: A} : R a (t a) := inst.sound


abbrev AExp.transformation := Transformation AExp
abbrev BExp.transformation := Transformation BExp
abbrev Imp.transformation := Transformation Imp


@[simp]
def AExp.fold_constants: AExp.transformation := fun a =>
  match a with
  | .Num n => .Num n
  | .Var x => .Var x
  | .Plus a1 a2 =>
    match (a1.fold_constants, a2.fold_constants) with
    | (.Num n1, .Num n2) => .Num (n1 + n2)
    | (b1, b2) => b1 + b2
  | .Minus a1 a2 =>
    match (a1.fold_constants, a2.fold_constants) with
    | (.Num n1, .Num n2) => .Num (n1 - n2)
    | (b1, b2) => b1 - b2
  | .Mult a1 a2 =>
    match (a1.fold_constants, a2.fold_constants) with
    | (.Num n1, .Num n2) => .Num (n1 * n2)
    | (b1, b2) => b1 * b2

example : <{A| (1 + 2) * X }>.fold_constants = <{A| 3 * X }> :=
  by
  eq_refl

example : <{A| X - ((0 * 6) + Y) }>.fold_constants = <{A| X - (0 + Y) }> :=
  by
  eq_refl


instance: AExp.fold_constants.Sound AExp.equiv where
  sound {a} := by
    intros st
    induction a with (try eq_refl)
    | Plus a1 a2 IHa1 IHa2 =>
      simp
      generalize E1: a1.fold_constants = t1
      generalize E2: a2.fold_constants = t2
      cases t1 with
      | _ => cases t2 with
        | _ =>
          simp
          rewrite [E1] at IHa1
          rewrite [E2] at IHa2
          rewrite [IHa1]
          rewrite [IHa2]
          eq_refl
    | Minus a1 a2 IHa1 IHa2 =>
      simp
      generalize E1: a1.fold_constants = t1
      generalize E2: a2.fold_constants = t2
      cases t1 with
      | _ => cases t2 with
        | _ =>
          simp
          rewrite [E1] at IHa1
          rewrite [E2] at IHa2
          rewrite [IHa1]
          rewrite [IHa2]
          eq_refl
    | Mult a1 a2 IHa1 IHa2 =>
      simp
      generalize E1: a1.fold_constants = t1
      generalize E2: a2.fold_constants = t2
      cases t1 with
      | _ => cases t2 with
        | _ =>
          simp
          rewrite [E1] at IHa1
          rewrite [E2] at IHa2
          rewrite [IHa1]
          rewrite [IHa2]
          eq_refl


@[simp]
def BExp.fold_constants: BExp.transformation := fun b =>
  match b with
  | .True => .True
  | .False => .False
  | .Eq a1 a2 => match (a1.fold_constants, a2.fold_constants) with
    | (.Num n1, .Num n2) => n1.beq n2
    | (b1, b2) => .Eq b1 b2
  | .Le a1 a2 => match (a1.fold_constants, a2.fold_constants) with
    | (.Num n1, .Num n2) => n1.ble n2
    | (b1, b2) => .Le b1 b2
  | .And b1 b2 => match (b1.fold_constants, b2.fold_constants) with
    | (.True, .True) => .True
    | (.True, .False) => .False
    | (.False, .True) => .False
    | (.False, .False) => .False
    | (c1, c2) => c1.And c2
  | .Not b => match b.fold_constants with
    | .True => .False
    | .False => .True
    | c => c.Not

example: <{B| true && ~(false && true) }>.fold_constants = .True := by
  eq_refl

example: <{B| (X == Y) && (0 == (2 - (1 + 1))) }>.fold_constants
  = <{B| (X == Y) && true }>
  := by
  eq_refl


instance: BExp.fold_constants.Sound BExp.equiv where
  sound {b} := by
    intros st
    induction b with (try eq_refl)
    | Eq a1 a2=>
      simp
      generalize E1: a1.fold_constants = a1'
      generalize E2: a2.fold_constants = a2'

      have R1: st.aeval a1 = st.aeval a1' := by
        subst E1
        apply AExp.fold_constants.sound

      have R2: st.aeval a2 = st.aeval a2' := by
        subst E2
        apply AExp.fold_constants.sound

      rewrite [R1, R2]

      cases a1' <;> cases a2' <;> try eq_refl
      simp
      split <;> simp <;> (try rewrite [<-Nat.beq_eq]) <;> assumption
    | Le a1 a2=>
      simp
      generalize E1: a1.fold_constants = a1'
      generalize E2: a2.fold_constants = a2'

      have R1: st.aeval a1 = st.aeval a1' := by
        subst E1
        apply AExp.fold_constants.sound

      have R2: st.aeval a2 = st.aeval a2' := by
        subst E2
        apply AExp.fold_constants.sound

      rewrite [R1, R2]
      cases a1' <;> cases a2' <;> try eq_refl
      simp
      split <;> simp <;> (try rewrite [<-Nat.ble_eq]) <;> assumption
    | And b1 b2 IHb1 IHb2 =>
      simp
      rewrite [IHb1, IHb2]
      generalize b1.fold_constants = b1'
      generalize b2.fold_constants = b2'
      cases b1' <;> cases b2' <;> eq_refl
    | Not b IHb =>
      simp
      rewrite [IHb]
      generalize E: b.fold_constants = b'
      cases b' <;> simp -- it contains simp


@[simp]
def Imp.fold_constants: Imp.transformation := fun c =>
  match c with
  | <{ skip }> => <{ skip }>
  | <{ [x] := [a] }> => <{ [x] := [a.fold_constants] }>
  | <{ c1 ; c2 }> =>
      <{ c1.fold_constants ; c2.fold_constants }>
  | <{ if b then c1 else c2 end }> =>
      match b.fold_constants with
      | <{true}> => c1.fold_constants
      | <{false}> => c2.fold_constants
      | b' => <{ if b' then c1.fold_constants
                       else c2.fold_constants end}>
  | <{ while b do c end }> =>
      match b.fold_constants with
      | <{true}> => <{ while true do skip end }>
      | <{false}> => <{ skip }>
      | b' => <{ while b' do c.fold_constants end }>


example:
  <{  X := 4 + 5;
      Y := X - 3;
      if (X - Y) == (2 + 4)
      then skip
      else Y := 0 end;

      if 0 <= (4 - (2 + 1))
      then Y := 0
      else skip end;

      while Y == 0 do
        X := X + 1
      end }>.fold_constants
  = <{  X := 9;
        Y := X - 3;
        if (X - Y) == 6
        then skip
        else Y := 0 end;

        Y := 0;
        while Y == 0 do
          X := X + 1
        end  }>
:= by
  eq_refl


instance: Imp.fold_constants.Sound Imp.equiv where
  sound {c} := by
    induction c with
    | Skip =>
      simp
      apply @Imp.equiv.refl
    | Asgn x a =>
      simp
      apply Imp.Asgn.congruence
      apply AExp.fold_constants.sound
    | Seq c1 c2 IHc1 IHc2 =>
      apply Imp.Seq.congruence
      . apply IHc1
      . apply IHc2
    | If b c1 c2 IHc1 IHc2 =>
      have S: b.equiv b.fold_constants := BExp.equiv.sound
      generalize E: b.fold_constants = b'

      cases b' with (simp <;> rewrite[E] <;> simp)
      | True =>
        apply Imp.equiv.trans
        . apply Imp.if_true
          rewrite [E] at S
          assumption
        . apply IHc1
      | False =>
        apply Imp.equiv.trans
        . apply Imp.if_false
          rewrite [E] at S
          assumption
        . apply IHc2
      | _ =>
        apply Imp.If.congruence
        . rewrite [<-E]
          apply S
        . apply IHc1
        . apply IHc2
    | While b c IHc =>
      have S: b.equiv b.fold_constants := BExp.equiv.sound
      generalize E: b.fold_constants = b'
      cases b' with (simp <;> rewrite[E] <;> simp)
      | True =>
        apply Imp.while_true
        rewrite [E] at S
        assumption
      | False =>
        apply Imp.while_false
        rewrite [E] at S
        simp
        intros st
        rewrite [S]
        eq_refl
      | _ =>
        apply Imp.While.congruence
        . rewrite [<-E]
          apply S
        . apply IHc


@[simp]
def AExp.subst (a: AExp) (x: String) (u: AExp): AExp :=
  match a with
  | .Num n => .Num n
  | .Var y =>
    if y == x then u else .Var y
  | .Plus a1 a2 =>
    (a1.subst x u) + (a2.subst x u)
  | .Minus a1 a2 =>
    (a1.subst x u) - (a2.subst x u)
  | .Mult a1 a2 =>
    (a1.subst x u) * (a2.subst x u)


example:
  <{A| Y + X }>.subst "X" <{A| 42 + 53}>
  = <{A| Y + (42 + 53) }>
:= by
  eq_refl


namespace UnsuitableSubst

def AExp.subst.equiv_property : Prop := forall x1 x2 a1 a2,
  <{ [x1] := [a1]; [x2] := [a2] }>.equiv
    <{ [x1] := [a1]; [x2] := [a2.subst x1 a1] }>

theorem AExp.subst.inequiv: Not AExp.subst.equiv_property := by
  unfold equiv_property
  intros H
  let X := "X"
  let Y := "Y"
  let a1 := <{A| [X] + 1 }>
  let a2 := <{A| [X] }>
  let a2' := a2.subst X a1
  let st1 := State.empty
  let st2 := state!["X" => 1]
  let st3 := state!["Y" => 2; "X" => 1]

  have Hst12: (st1.update X (st1.aeval a1)) = st2 := by
    eq_refl

  have Hst23: st3 = (st2.update Y (st2.aeval a2')) := by
    eq_refl

  specialize (@H X Y a1 a2 st1 st3)
  have T: <{ [X] := [a1]; [Y] := [a2.subst X a1] }>.BigStep st1 st3
  := by
    apply Imp.BigStep.BSeq
    . apply Imp.BigStep.BAsgn (n := 1)
      unfold a1
      unfold st1
      eq_refl
    . apply Imp.BigStep.BAsgn
      eq_refl

  have K {st1 st2: State}:
    (Imp.Asgn Y a2).BigStep st1 st2 ->
    st2.aeval Y = st1.aeval a2
  := by
    intros H
    cases H with
    | @BAsgn _ _ n x E =>
      simp
      symm
      exact E

  let H := H.mpr T
  cases H with
  | @BSeq _ _ _ t1 _ H1 H2 =>
    cases H1 with
    | @BAsgn _ _ n1 x E1 =>
      rewrite [<-E1] at H2
      rewrite [Hst12] at H2
      specialize (K H2)
      unfold Y st2 st3 a2 at K
      simp at K
      have E: 1 = if X = "X" then 1 else 0 := by
        eq_refl
      rewrite [<-E] at K
      contradiction

end UnsuitableSubst


inductive AExp.not_contain_var (x: String): AExp -> Prop where
  | NNum {n: Nat} : (AExp.Num n).not_contain_var x
  | NVar {y}: x ≠ y -> (AExp.Var y).not_contain_var x
  | NPlus {a1 a2: AExp}:
    a1.not_contain_var x ->
    a2.not_contain_var x ->
    <{A| [a1] + [a2] }>.not_contain_var x

  | NMinus {a1 a2: AExp}:
    a1.not_contain_var x ->
    a2.not_contain_var x ->
    <{A| [a1] - [a2] }>.not_contain_var x
  | NMult {a1 a2: AExp}:
    a1.not_contain_var x ->
    a2.not_contain_var x ->
    <{A| [a1] * [a2] }>.not_contain_var x


theorem State.aeval.weakening {a: AExp} {x}:
  a.not_contain_var x ->
  forall (st: State) (ni), state![x => ni ; st].aeval a = st.aeval a
:= by
  intros H
  intros st ni
  induction a with
  | Num n =>
    eq_refl
  | Var s =>
    cases H
    unfold aeval
    apply TotalMap.update_neq
    assumption
  | Plus n1 n2 IHn1 IHn2 | Minus n1 n2 IHn1 IHn2 | Mult n1 n2 IHn1 IHn2 =>
    cases H
    unfold aeval
    rewrite [IHn1] <;> try assumption
    rewrite [IHn2] <;> try assumption
    eq_refl


theorem State.aeval.subst_eq {a u: AExp} {x}:
  u.not_contain_var x ->
  forall (st: State),
    st.aeval u = st.aeval x ->
    st.aeval a = st.aeval (a.subst x u)
:= by
  induction a with
  | Num n =>
    simp
  | Var y =>
    simp
    intros NC st H
    cases String.decEq y x with
    | isTrue K =>
      simp [K]
      symm
      apply H
    | isFalse K =>
      simp [K]
  | Plus n1 n2 IH1 IH2 | Minus n1 n2 IH1 IH2 | Mult n1 n2 IH1 IH2 =>
    intros NC st H
    specialize (IH1 NC st H)
    specialize (IH2 NC st H)
    simp
    rewrite [IH1, IH2]
    eq_refl


theorem AExp.subst.equiv_property {x1 x2} {a1 a2: AExp}:
  a1.not_contain_var x1 ->
  <{ [x1] := [a1]; [x2] := [a2] }>.equiv
    <{ [x1] := [a1]; [x2] := [a2.subst x1 a1] }>
:= by
  intros NC
  intros st1 st3

  let st2 := st1.update x1 (st1.aeval a1)

  have H12: st1 =[ [x1] := [a1] ]=> st2 := by
    apply Imp.BigStep.BAsgn
    eq_refl

  have Ust2 {t}: st1 =[ [x1] := [a1] ]=> t -> t = st2 := by
    intros H
    apply Imp.BigStep.deterministic
    . apply H
    . apply H12

  have E: st1.aeval a1 = st2 x1 := by
    unfold st2
    simp

  have K: st2.aeval a2 = st2.aeval (a2.subst x1 a1) := by
    induction a2 with
    | Num n =>
      eq_refl
    | Var y =>
      simp
      cases String.decEq y x1 with
      | isTrue K =>
        simp [K]
        rewrite [<-E]
        unfold st2
        symm
        apply State.aeval.weakening NC
      | isFalse K =>
        simp [K]
    | Plus a1 a2 IHa1 IHa2 | Minus a1 a2 IHa1 IHa2 | Mult a1 a2 IHa1 IHa2 =>
      simp
      rewrite [IHa1]
      rewrite [IHa2]
      eq_refl

  apply Iff.intro <;> (
    intros H
    cases H with
    | @BSeq _ _ _ t _ H1 H2 =>
      specialize (Ust2 H1)
      cases H2 with
      | BAsgn E =>
        apply Imp.BigStep.BSeq
        . apply H1
        . subst Ust2
          rewrite [<-E]
          apply Imp.BigStep.BAsgn
          rewrite [K]
          eq_refl
  )


theorem Imp.loop.not_equiv_skip:
  Not (<{ while true do skip end }>.equiv <{ skip }>)
:= by
  intros H
  specialize (@H State.empty State.empty)
  apply Imp.while_true_nonterm
  . apply BExp.equiv.refl
  . apply H.mpr
    apply BigStep.BSkip
