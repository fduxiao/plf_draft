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
  <{ if true then c1 else c2 end }>.equiv c1 := by
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
  b.equiv .True -> <{ if b then c1 else c2 end }>.equiv c1 := by
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
  b.equiv .False -> <{ if b then c1 else c2 end }>.equiv c2 := by
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
  <{ (c1; c2) ;c3 }>.equiv <{ c1; (c2; c3) }> := by
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
  <{ [x] := [x] }>.equiv <{ skip }> := by
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
  <{A| [x] }>.equiv a -> <{ skip }>.equiv <{ [x] := [a] }> := by
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


theorem Imp.Asgn.congruence {x} {a1 a2: AExp}:
  a1.equiv a2 -> <{[x] := [a1]}>.equiv <{[x] := [a2]}> := by
    intros Hequiv
    intros st1 st2
    specialize Hequiv st1
    apply Iff.intro
    . intros H
      cases H with
      | BAsgn H =>
        rewrite [<-H]
        rewrite [Hequiv]
        apply BigStep.BAsgn
        eq_refl
    . intros H
      cases H with
      | BAsgn H =>
        rewrite [<-H]
        rewrite [<-Hequiv]
        apply BigStep.BAsgn
        eq_refl


theorem Imp.While.congruence {b1 b2: BExp} {c1 c2: Imp}:
  b1.equiv b2 -> c1.equiv c2 ->
  <{ while b1 do c1 end }>.equiv <{ while b2 do c2 end }> := by
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
  <{ c1; d1 }>.equiv <{ c2; d2 }> := by
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
