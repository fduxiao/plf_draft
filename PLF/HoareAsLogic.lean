import PLF.Hoare


inductive Derivable : State.Assertion -> Imp -> State.Assertion -> Type where
  | HSkip {P}: Derivable P <{skip}> P
  | HAsgn {Q V a}:
      Derivable ({{Q ![ [V] => [a]]}}) <{[V] := [a]}> Q
  | HSeq {P c Q d R}:
      Derivable Q d R -> Derivable P c Q -> Derivable P <{ c; d }> R
  | HIf {P Q} {b: BExp} {c1 c2}:
    Derivable {{ P /\ b }} c1 Q ->
    Derivable {{ P /\ ~b }} c2 Q ->
    Derivable P <{if b then c1 else c2 end}> Q
  | HWhile {P} {b: BExp} {c}:
    Derivable {{ P /\ b }} c P ->
    Derivable P <{while b do c end}> {{ P /\ ~b}}
  | HConsequence {P1 Q1 P2 Q2 : State.Assertion} {c}:
    Derivable P2 c Q2 ->
    (P1 ->> P2) ->
    (Q2 ->> Q1) ->
    Derivable P1 c Q1


def Derivable.HConsequencePre {P1 P2 Q : State.Assertion} {c}:
  Derivable P2 c Q ->
  (P1 ->> P2) ->
  Derivable P1 c Q
:= by
  intros D HImp
  apply Derivable.HConsequence
  . apply D
  . apply HImp
  . simp


def Derivable.HConsequencePost {P Q1 Q2: State.Assertion} {c}:
  Derivable P c Q2 ->
  (Q2 ->> Q1) ->
  Derivable P c Q1
:= by
  intros D HImp
  apply Derivable.HConsequence
  . apply D
  . simp
  . apply HImp


example:
  Derivable
    {{ X = 3 ![X => X + 2] ![X => X + 1] }}
    <{ X := X + 1; X := X + 2}>
    {{ X = 3 }}
:= by
  apply Derivable.HSeq
  . apply Derivable.HAsgn
  . apply Derivable.HAsgn


def State.Assertion.implies.true_post {P}: P ->> True := fun _ _ => True.intro
def State.Assertion.implies.false_pre {Q}: False ->> Q := fun _ f => f.elim

def Derivable.true_post {c P}:
  Derivable P c True
:= match c with
  | .Skip => .HConsequencePre .HSkip .true_post
  | .Seq _ _ => Derivable.HSeq .true_post .true_post
  | .Asgn _ _ => .HConsequencePre .HAsgn .true_post
  | .If _ _ _ => .HIf .true_post .true_post
  | .While _ _ => .HConsequence (.HWhile .true_post) .true_post .true_post


def Derivable.false_pre {c Q}:
  Derivable False c Q
:= match c with
  | .Skip => .HConsequencePre .HSkip .false_pre
  | .Seq _ _ => Derivable.HSeq .false_pre .false_pre
  | .Asgn _ _ => .HConsequencePre .HAsgn .false_pre
  | .If _ _ _ => by
    apply Derivable.HIf
    . simp
      apply Derivable.false_pre
    . simp
      apply Derivable.false_pre
  | .While _ _ => by
    apply Derivable.HConsequence
    . apply Derivable.HWhile (P := False)
      simp
      apply Derivable.false_pre
    . apply State.Assertion.implies.false_pre
    . simp


theorem Derivable.sound {P c Q}:
  Derivable P c Q -> {{P}}< c >{{ Q }}
:= by
  intros HD
  induction HD with
  | HSkip =>
    apply HoareTriple.skip
  | HAsgn =>
    apply HoareTriple.asgn
  | HSeq d1 d2 IHd1 IHd2 =>
    apply HoareTriple.seq
    . apply IHd1
    . apply IHd2
  | HIf d1 d2 IHd1 IHd2 =>
    apply HoareTriple.if
    . apply IHd1
    . apply IHd2
  | HWhile d IHd =>
    apply HoareTriple.while
    apply IHd
  | HConsequence d HP HQ IHd =>
    apply HoareTriple.consequence
    . apply IHd
    . apply HP
    . apply HQ


def Imp.wp (c:Imp) (Q: State.Assertion) : State.Assertion :=
  fun st1 => forall st2, st1 =[ c ]=> st2 -> Q st2


theorem Imp.wp.is_precondition {c: Imp} {Q}:
  {{ [c.wp Q] }}< c >{{ Q }}
:= by
  intros st1 st2
  solve_by_elim


theorem Imp.wp.is_weakest {c: Imp} {Q P: State.Assertion}:
  {{ P }}< c >{{ Q }} ->
  (P ->> (c.wp Q))
:= by
  intros HHoare
  intros st HP
  simp [wp]
  solve_by_elim


def Imp.wp.seq {P Q} {c1 c2: Imp}:
  Derivable P c1 (c2.wp Q) ->
  Derivable (wp c2 Q) c2 Q ->
  Derivable P <{c1; c2}> Q
:= flip .HSeq  -- fun H1 H2 => .HSeq H2 H1


theorem Imp.wp.invariant b (c: Imp) (Q):
  {{ [ <{while b do c end}>.wp Q ] /\ b }}< c >{{ [<{while b do c end}>.wp Q]}}
:= by
  apply HoareTriple.consequence_pre
  . apply is_precondition
  . simp [wp]
    intros st1 H HT st2 B12 st3 B23
    cases B23 with
    | BWhileFalse HF =>
      apply H
      apply BigStep.BWhileTrue HT
      apply B12
      apply BigStep.BWhileFalse HF
    | BWhileTrue HT2 B23 BW =>
      apply H
      apply BigStep.BWhileTrue HT
      . apply B12
      . apply BigStep.BWhileTrue HT2
        . apply B23
        . apply BW


def Imp.complete_aux c: forall P Q,
  {{ P }}< c >{{ Q }} -> Derivable P c Q
:= match c with
  | .Skip => by
    intros P Q HHoare
    apply Derivable.HConsequencePost
    . apply Derivable.HSkip
    . intros st HP
      apply HHoare
      apply BigStep.BSkip
      apply HP
  | .Asgn x a => by
    intros P Q HHoare
    apply Derivable.HConsequencePre .HAsgn
    intros st HP
    apply HHoare
    . apply Imp.BigStep.BAsgn
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
      . apply BigStep.BSeq B12 B23
      . apply HP
    . apply c2.complete_aux
      apply Imp.wp.is_precondition
  | .If b c1 c2 => by
    intros P Q HHoare
    apply Derivable.HIf <;> simp
    . /- true -/
      apply c1.complete_aux
      intros st1 st2 B12 HP
      apply HHoare st1 st2
      . apply BigStep.BIfTrue
        . apply HP.right
        . apply B12
      . apply HP.left
    . /- false -/
      apply c2.complete_aux
      intros st1 st2 B12 HP
      apply HHoare st1 st2
      . apply BigStep.BIfFalse
        . apply HP.right
        . apply B12
      . apply HP.left
  | .While b c => by
    intros P Q HHoare
    apply Derivable.HConsequence
    . apply Derivable.HWhile (P := ((While b c).wp Q))
      simp
      apply c.complete_aux
      apply Imp.wp.invariant
    . apply Imp.wp.is_weakest
      apply HHoare
    . simp [wp]
      intro st H HB
      apply H
      apply BigStep.BWhileFalse
      apply HB


def HoareTriple.complete {P c Q}:
  {{ P }}< c >{{ Q }} -> Derivable P c Q
:= Imp.complete_aux c P Q
