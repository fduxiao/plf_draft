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
def Imp.wp (c:Imp) (Q: Assertion) : Assertion :=
  fun st1 => forall st2, st1 =[ c ]=> st2 → Q st2

@[simp, grind .]
theorem Imp.wp_precondition {c: Imp} {Q}:
  {{ [c.wp Q] }}< c >{{ Q }}
:= by
  intros st1 st2
  solve_by_elim

@[grind .]
theorem Imp.wp_weakest {c: Imp} {Q P: Assertion}:
  {{ P }}< c >{{ Q }} →
  (P ->> (c.wp Q))
:= by
  intros HHoare
  intros st HP
  simp [wp]
  solve_by_elim


@[simp, grind =]
theorem Imp.wp_skip {Q: Assertion}:
  Imp.wp .Skip Q = Q
:= by
  ext
  . grind
  . grind

@[simp, grind =]
theorem Imp.wp_asign {x a} {Q: Assertion}:
  Imp.wp (.Asgn x a) Q = {{ Q ![[x] => [a]]}}
:= by
  ext
  . grind
  . grind

@[simp, grind =]
theorem Imp.wp_seq {c1 c2 Q}:
  Imp.wp (<{c1; c2}>) Q = Imp.wp c1 (Imp.wp c2 Q)
:= by
  ext
  . grind
  . grind

@[grind]
def Assertion.ite (b: BExp) (P Q: Assertion) : Assertion :=
  fun st => if st.beval b then P st else Q st

theorem Imp.wp_if_eq {b: BExp} {c1 c2: Imp} {Q}:
  <{ if b then c1 else c2 end }>.wp Q = Assertion.ite b (c1.wp Q) (c2.wp Q)
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
theorem Imp.wp_if_true {b: BExp} {c1 c2: Imp} {Q}:
  {{ [<{ if b then c1 else c2 end }>.wp Q] ∧ [B| b ] }} ->> c1.wp Q
:= by
  grind

@[grind .]
theorem Imp.wp_if_false {b: BExp} {c1 c2: Imp} {Q}:
  {{ [<{ if b then c1 else c2 end }>.wp Q] ∧ ¬ [B| b ] }} ->> c2.wp Q
:= by
  grind

@[grind .]
theorem Imp.wp_while_true {b: BExp} {c: Imp} {Q: Assertion}:
  {{ [<{while b do c end}>.wp Q] ∧ [B| b] }} ->> c.wp (<{while b do c end}>.wp Q)
:= by
  grind

@[grind .]
theorem Imp.wp_while_false {b: BExp} {c: Imp} {Q: Assertion}:
  {{ [<{while b do c end}>.wp Q] ∧ ¬ [B| b] }} ->> Q -- i.e., (<{ skip }>.wp Q)
:= by
  grind

@[grind .]
theorem Derivable.wp {c Q}:
  Derivable (c.wp Q) c Q
:= by
  induction c generalizing Q
  case Skip =>
    simp
    apply Derivable.Skip
  case Asgn x a =>
    simp
    apply Derivable.Asgn
  case Seq c1 c2 IH1 IH2 =>
    simp
    apply Derivable.Seq
    . apply IH2
    . apply IH1
  case If b c1 c2 IH1 IH2 =>
    apply Derivable.If
    . -- true
      apply Derivable.ConsequencePre
      . apply IH1
      . apply Imp.wp_if_true
    . -- false
      apply Derivable.ConsequencePre
      . apply IH2
      . apply Imp.wp_if_false
  case While b c IH =>
    apply Derivable.ConsequencePost
    . apply Derivable.While (P := ((Imp.While b c).wp Q))
      apply Derivable.ConsequencePre
      . apply IH
      . apply Imp.wp_while_true
    . apply Imp.wp_while_false

@[grind .]
theorem HoareTriple.complete {P c Q}:
  {{ P }}< c >{{ Q }} → Derivable P c Q
:= by
  intro HHoare
  apply Derivable.ConsequencePre
  . apply Derivable.wp
  . apply Imp.wp_weakest
    exact HHoare


-- the original proof. It might be constructive since I originally defined `Derivable` to be a `Type`.

@[grind .]
theorem Imp.wp.seq {P Q} {c1 c2: Imp}:
  Derivable P c1 (c2.wp Q) →
  Derivable (c2.wp Q) c2 Q →
  Derivable P <{c1; c2}> Q
:= flip .Seq  -- fun H1 H2 => .Seq H2 H1

@[grind .]
theorem Imp.wp.invariant b (c: Imp) (Q):
  {{ [ <{while b do c end}>.wp Q ] ∧ b }}< c >{{ [<{while b do c end}>.wp Q]}}
:= by
  apply HoareTriple.consequence_pre
  . apply Imp.wp_precondition
  . simp [wp]
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
      apply Imp.wp_precondition
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
    . apply Derivable.While (P := ((While b c).wp Q))
      apply c.complete_aux
      apply Imp.wp.invariant
    . apply Imp.wp_weakest
      apply HHoare
    . simp [wp]
      intro st H HB
      apply H
      apply BigStep.WhileFalse
      apply HB
