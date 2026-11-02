import PLF.Hoare

@[grind]
inductive Derivable : Assertion → Imp -> Assertion -> Prop where
  | Skip {P}: Derivable P <{skip}> P
  | Asgn {Q V a}:
      Derivable ({{Q ![ [V] => [a]]}}) <{[V] := [a]}> Q
  | Seq {P c Q d R}:
      Derivable Q d R → Derivable P c Q → Derivable P <{ c; d }> R
  | If {P Q} {b: BExp} {c1 c2}:
    Derivable {{ P ∧  b }} c1 Q →
    Derivable {{ P ∧ ¬b }} c2 Q →
    Derivable P <{if b then c1 else c2 end}> Q
  | While {P} {b: BExp} {c}:
    Derivable {{ P ∧ b }} c P →
    Derivable P <{while b do c end}> {{ P ∧ ¬b}}
  | Consequence {P1 Q1 P2 Q2 : Assertion} {c}:
    Derivable P2 c Q2 →
    (P1 ->> P2) →
    (Q2 ->> Q1) →
    Derivable P1 c Q1

@[grind .]
theorem Derivable.ConsequencePre {P1 P2 Q : Assertion} {c}:
  Derivable P2 c Q →
  (P1 ->> P2) →
  Derivable P1 c Q
:= by
  intros D HImp
  apply Derivable.Consequence
  . apply D
  . apply HImp
  . simp

@[grind .]
theorem Derivable.ConsequencePost {P Q1 Q2: Assertion} {c}:
  Derivable P c Q2 →
  (Q2 ->> Q1) →
  Derivable P c Q1
:= by
  intros D HImp
  apply Derivable.Consequence
  . apply D
  . simp
  . apply HImp


example:
  Derivable
    {{ X == 3 ![X => X + 2] ![X => X + 1] }}
    <{ X := X + 1; X := X + 2}>
    {{ X == 3 }}
:= by
  apply Derivable.Seq
  . apply Derivable.Asgn
  . apply Derivable.Asgn


@[simp, grind .]
theorem Assertion.implies.true_post {P}: P ->> True := fun _ _ => True.intro
@[simp, grind .]
theorem Assertion.implies.false_pre {Q}: False ->> Q := fun _ f => f.elim

@[grind .]
theorem Derivable.true_post {c P}:
  Derivable P c True
:= match c with
  | .Skip => .ConsequencePre .Skip .true_post
  | .Seq _ _ => Derivable.Seq .true_post .true_post
  | .Asgn _ _ => .ConsequencePre .Asgn .true_post
  | .If _ _ _ => .If .true_post .true_post
  | .While _ _ => .Consequence (.While .true_post) .true_post .true_post

@[grind .]
theorem Derivable.false_pre {c Q}:
  Derivable False c Q
:= by
  induction c generalizing Q
  case Skip =>
    apply Derivable.ConsequencePre .Skip .false_pre
  case Seq c1 c2 IHc1 IHc2 =>
    apply Derivable.Seq IHc2 IHc1
  case Asgn X a =>
    apply Derivable.ConsequencePre .Asgn .false_pre
  case If b c1 c2 IHc1 IHc2 =>
    apply Derivable.If
    . simp
      apply IHc1
    . simp
      apply IHc2
  case While b c IHc =>
    apply Derivable.Consequence
    . apply Derivable.While (P := False)
      simp
      apply IHc
    . apply Assertion.implies.false_pre
    . simp

@[grind .]
theorem Derivable.sound {P c Q}:
  Derivable P c Q → {{P}}< c >{{ Q }}
:= by
  intros HD
  induction HD with
  | Skip =>
    apply HoareTriple.skip
  | Asgn =>
    apply HoareTriple.asgn
  | Seq d1 d2 IHd1 IHd2 =>
    apply HoareTriple.seq
    . apply IHd1
    . apply IHd2
  | If d1 d2 IHd1 IHd2 =>
    apply HoareTriple.if
    . apply IHd1
    . apply IHd2
  | While d IHd =>
    apply HoareTriple.while
    apply IHd
  | Consequence d HP HQ IHd =>
    apply HoareTriple.consequence
    . apply IHd
    . apply HP
    . apply HQ

@[grind]
def WP (c:Imp) (Q: Assertion) : Assertion :=
  fun st1 => forall st2, st1 =[ c ]=> st2 → Q st2

@[simp, grind .]
theorem WP.is_precondition {c: Imp} {Q}:
  {{ [WP c Q] }}< c >{{ Q }}
:= by
  intros st1 st2
  solve_by_elim

@[grind .]
theorem WP.weakest {c: Imp} {Q P: Assertion}:
  {{ P }}< c >{{ Q }} →
  (P ->> (WP c Q))
:= by
  intros HHoare
  intros st HP
  simp [WP]
  solve_by_elim

@[grind .]
theorem WP.triple {c: Imp} {Q P: Assertion}:
  (P ->> (WP c Q)) →
  {{ P }}< c >{{ Q }}
:= by
  grind

@[grind =]
theorem WP.skip_eq {Q: Assertion}:
  WP .Skip Q = Q
:= by
  ext
  . grind
  . grind

@[grind =]
theorem WP.asgn_eq {x a} {Q: Assertion}:
  WP (.Asgn x a) Q = {{ Q ![[x] => [a]]}}
:= by
  ext
  . grind
  . grind

@[grind =]
theorem WP.seq_eq {c1 c2 Q}:
  WP (<{c1; c2}>) Q = WP c1 (WP c2 Q)
:= by
  ext
  . grind
  . grind

@[grind]
def Assertion.ite (b: BExp) (P Q: Assertion) : Assertion :=
  fun st => if st.beval b then P st else Q st

theorem WP.if_eq {b: BExp} {c1 c2: Imp} {Q}:
  WP <{ if b then c1 else c2 end }> Q = Assertion.ite b (WP c1 Q) (WP c2 Q)
:= by
  ext
  . intro st
    grind
  . intro st
    simp [Assertion.ite]
    grind

theorem Assertion.ite_true {b: BExp} {P Q: Assertion}:
  {{ [Assertion.ite b P Q] ∧ [B| b] }} = {{ P ∧ b}}
:= by
  ext
  . grind
  . grind

@[simp, grind .]
theorem Assertion.ite_false {b: BExp} {P Q: Assertion}:
  {{ [Assertion.ite b P Q] ∧ ¬ [B| b] }} = {{ Q ∧ ¬ b }}
:= by
  ext
  . grind
  . grind

@[grind .]
theorem WP.if_true' {b: BExp} {c1 c2: Imp} {Q}:
  {{ [WP <{ if b then c1 else c2 end }> Q] ∧ [B| b ] }} ->> WP c1 Q
:= by
  grind

@[grind .]
theorem WP.if_true {b: BExp} {c1 c2: Imp} {Q}:
  {{ [WP c1 Q] ∧ [B| b] }} ->>
  WP <{ if b then c1 else c2 end }> Q
:= by
  intro st
  grind

@[grind .]
theorem WP.if_false' {b: BExp} {c1 c2: Imp} {Q}:
  {{ [WP <{ if b then c1 else c2 end }> Q] ∧ ¬ [B| b ] }} ->> WP c2 Q
:= by
  grind

@[grind .]
theorem WP.if_false {b: BExp} {c1 c2: Imp} {Q}:
  {{ [WP c2 Q] ∧ ¬ [B| b] }} ->>
  WP <{ if b then c1 else c2 end }> Q
:= by
  intro st
  grind

theorem WP.if {b: BExp} {c1 c2: Imp} {P Q: Assertion}:
  {{ [P] ∧ b }} ->> WP c1 Q →
  {{ [P] ∧ ¬ b }} ->> WP c2 Q →
  P ->> WP <{ if b then c1 else c2 end }> Q
:= by
  grind


@[grind .]
theorem WP.while_true' {b: BExp} {c: Imp} {Q: Assertion}:
  {{ [WP <{while b do c end}> Q] ∧ [B| b] }} ->> WP c (WP <{while b do c end}> Q)
:= by
  grind

@[grind .]
theorem WP.while_true {b: BExp} {c: Imp} {Q: Assertion}:
  {{ [WP c (WP <{while b do c end}> Q)] ∧ b }} ->>
  {{ [WP <{while b do c end}> Q] }}
:= by
  intro st
  grind

@[grind .]
theorem WP.while_false' {b: BExp} {c: Imp} {Q: Assertion}:
  {{ [WP <{while b do c end}> Q] ∧ ¬ [B| b] }} ->> Q -- i.e., (<{ skip }>.wp Q)
:= by
  grind

@[grind .]
theorem WP.while_false {b: BExp} {c: Imp} {Q: Assertion}:
  {{ Q ∧ ¬ b }} ->>
  {{ [WP <{while b do c end}> Q] }}
:= by
  grind

@[simp]
theorem WP.while {b: BExp} {c: Imp} {P Q: Assertion}:
  {{ [P] ∧ ¬ b }} ->> Q →
  {{ [P] ∧ b }} ->> WP c (WP <{while b do c end}> Q) →
  P ->> WP <{while b do c end}> Q
:= by
  intro M1 M2 st H
  cases E: st.beval b
  case true =>
    apply WP.while_true
    specialize M2 st
    simp at M2
    simp_all
  case false =>
    apply WP.while_false
    specialize M1 st
    simp at M1
    simp_all

@[grind .]
theorem Derivable.wp {c Q}:
  Derivable (WP c Q) c Q
:= by
  induction c generalizing Q
  case Skip =>
    simp [WP.skip_eq]
    apply Derivable.Skip
  case Asgn x a =>
    simp [WP.asgn_eq]
    apply Derivable.Asgn
  case Seq c1 c2 IH1 IH2 =>
    simp [WP.seq_eq]
    apply Derivable.Seq
    . apply IH2
    . apply IH1
  case If b c1 c2 IH1 IH2 =>
    apply Derivable.If
    . -- true
      apply Derivable.ConsequencePre
      . apply IH1
      . apply WP.if_true'
    . -- false
      apply Derivable.ConsequencePre
      . apply IH2
      . apply WP.if_false'
  case While b c IH =>
    apply Derivable.ConsequencePost
    . apply Derivable.While
      apply Derivable.ConsequencePre
      . apply IH
      . apply WP.while_true'
    . apply WP.while_false'

@[grind .]
theorem HoareTriple.complete {P c Q}:
  {{ P }}< c >{{ Q }} → Derivable P c Q
:= by
  intro HHoare
  apply Derivable.ConsequencePre
  . apply Derivable.wp
  . apply WP.weakest
    exact HHoare


-- the original proof. It might be constructive since I originally defined `Derivable` to be a `Type`.

@[grind .]
theorem Imp.wp.seq {P Q} {c1 c2: Imp}:
  Derivable P c1 (WP c2 Q) →
  Derivable (WP c2 Q) c2 Q →
  Derivable P <{c1; c2}> Q
:= flip .Seq  -- fun H1 H2 => .Seq H2 H1

@[grind .]
theorem Imp.wp.invariant b (c: Imp) (Q):
  {{ [ WP <{while b do c end}> Q ] ∧ b }}< c >{{ [WP <{while b do c end}> Q]}}
:= by
  apply HoareTriple.consequence_pre
  . apply WP.is_precondition
  . simp [WP, Assertion.implies]
    intros st1 H HT st2 B12 st3 B23
    cases B23 with
    | WhileFalse HF =>
      apply H
      apply BigStep.WhileTrue HT
      apply B12
      apply BigStep.WhileFalse HF
    | WhileTrue HT2 B23 BW =>
      apply H
      apply BigStep.WhileTrue HT
      . apply B12
      . apply BigStep.WhileTrue HT2
        . apply B23
        . apply BW

theorem Imp.complete_aux c: forall P Q,
  {{ P }}< c >{{ Q }} → Derivable P c Q
:= match c with
  | .Skip => by
    intros P Q HHoare
    apply Derivable.ConsequencePost
    . apply Derivable.Skip
    . intros st HP
      specialize (HHoare st st)
      apply HHoare
      apply BigStep.Skip
      apply HP
  | .Asgn x a => by
    intros P Q HHoare
    apply Derivable.ConsequencePre .Asgn
    intros st HP
    apply HHoare
    . apply Imp.BigStep.Asgn
      eq_refl
    . apply HP
  | .Seq c1 c2 => by
    intros P Q HHoare
    apply Imp.wp.seq
    . apply c1.complete_aux
      intros st1 st2 B12 HP
      intros st3 B23
      specialize (HHoare st1 st3)
      apply HHoare
      . apply BigStep.Seq B12 B23
      . apply HP
    . apply c2.complete_aux
      apply WP.is_precondition
  | .If b c1 c2 => by
    intros P Q HHoare
    apply Derivable.If
    . /- true -/
      apply c1.complete_aux
      intros st1 st2 B12 HP
      apply HHoare st1 st2
      . apply BigStep.IfTrue
        . apply HP.right
        . apply B12
      . apply HP.left
    . /- false -/
      apply c2.complete_aux
      intros st1 st2 B12 HP
      apply HHoare st1 st2
      . apply BigStep.IfFalse
        . simp at HP
          apply HP.right
        . apply B12
      . apply HP.left
  | .While b c => by
    intros P Q HHoare
    apply Derivable.Consequence
    . apply Derivable.While (P := (WP <{while b do c end}> Q))
      apply c.complete_aux
      apply Imp.wp.invariant
    . apply WP.weakest
      apply HHoare
    . simp [WP, Assertion.implies]
      intro st H HB
      apply H
      apply BigStep.WhileFalse
      apply HB
