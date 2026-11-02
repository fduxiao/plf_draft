import PLF.HoareAsLogic

namespace ProofUsingWP

def factorial (n: Nat): Imp := <{
  X := [n];
  Y := 1;
  while 1 <= X do
    Y := Y * X;
    X := X - 1
  end
}>

def Nat.factorial: Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

def factorial_spec (n: Nat) c := {{ True }}< c >{{ Y == [Nat.factorial n] }}


@[grind .]
theorem HoareTriple.asgn_single {m: Nat} {X: String} {a: AExp}:
  {{ [a] == [m] }}<[X] := [a]>{{ [X] == [m] }}
:= by
  apply WP.triple
  simp [WP.asgn_eq]
  intro st H
  simp at *
  exact H

@[grind .]
theorem HoareTriple.asgn_single' {P} {m n: Nat} {X: String} {a: AExp}:
  {{ P ∧ [X] == [m] ∧ [a] == [n] }}<[X] := [a]>{{ P ![[X] => [m]] ∧ [X] == [n] }}
:= by
  apply WP.triple
  simp [WP.asgn_eq]
  intro st H
  simp at *
  grind

@[grind .]
theorem WP.app_triple {P1 Q1 c P Q}:
  {{ P1 }}< c >{{ Q1 }} →
  P ->> P1 →
  Q1 ->> Q →
  P ->> WP c Q
:= by
  grind

theorem WP.asgn_fwd {P Q} {m n: Nat} {X: String} {a: AExp}:
  P ->> {{ P ∧ [X] == [m] ∧ [a] == [n] }} →
  {{ P ![[X] => [m]] ∧ [X] == [n] }} ->> Q →
  P ->> WP (<{[X] := [a] }>) Q
:= by
  intro M1 M2
  apply WP.app_triple
  . apply HoareTriple.asgn_single' (m := m) (n := n) (P := P)
  . exact M1
  . exact M2

@[grind .]
theorem WP.conseq_pre {P Q R} {c: Imp}:
  P ->> Q →
  Q ->> WP c R →
  P ->> WP c R
:= by
  grind

@[grind .]
theorem WP.exfalso {P Q} {c: Imp}:
  P ->> False →
  P ->> WP c Q
:= by
  grind

def factorial_acc: Imp := <{
  while 1 <= X do
    Y := Y * X;
    X := X - 1
  end
}>

def Nat.factorial_acc: Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => Nat.factorial_acc n ((n + 1) * acc)

theorem Nat.factorial_acc_eqc {n acc: Nat}:
  Nat.factorial_acc n acc = Nat.factorial n * acc
:= by
  induction n generalizing acc
  case zero =>
    simp [Nat.factorial_acc, Nat.factorial]
  case succ n IH =>
    simp [Nat.factorial_acc, Nat.factorial]
    rw [IH]
    ac_nf0
    rfl

theorem factorial_acc_correct (n acc: Nat):
  {{ X == [n] ∧ Y == [acc] }}< factorial_acc >{{ Y == [Nat.factorial_acc n acc] }}
:= by
  induction n generalizing acc
  case zero =>
    simp [factorial_acc]
    apply WP.triple
    apply WP.while
    . intro st
      simp [Nat.factorial_acc]
      simp_all
    . apply WP.exfalso
      intro st
      simp_all
  case succ n IH =>
    simp [factorial_acc]
    apply WP.triple
    apply WP.while
    . -- false
      intro st
      simp_all
    . -- true
      rw [WP.seq_eq]
      refine WP.asgn_fwd (m := acc) (n := acc * (n + 1)) ?_ ?_
      . intro st
        simp_all
      simp
      apply WP.conseq_pre
      . show _ ->> {{ X == [(n + 1: Nat)] ∧ Y == [acc * (n + 1)] }}
        intro st
        simp_all
      refine WP.asgn_fwd (m := n + 1) (n := n) ?_ ?_
      . intro st
        simp_all
      simp
      apply WP.app_triple
      . exact (IH (acc * (n + 1)))
      . grind
      simp [Nat.factorial_acc]
      ac_nf0
      rfl

theorem factorial_correct_aux {n: Nat}:
  forall m1 m2: Nat, {{ X == [m1] ∧ Y == [m2] }}< factorial n >{{ Y == [Nat.factorial n] }}
:= by
  intro m1 m2
  unfold factorial
  apply WP.triple
  rw [WP.seq_eq]
  refine WP.asgn_fwd (m := m1) (n := n) ?_ ?_
  . grind
  simp
  rw [WP.seq_eq]
  refine WP.asgn_fwd (m := m2) (n := 1) ?_ ?_
  . grind
  simp
  apply WP.app_triple
  . exact factorial_acc_correct n 1
  . intro st
    simp_all
  . rewrite [Nat.factorial_acc_eqc]
    simp

theorem factorial_correct (n: Nat):
  factorial_spec n (factorial n)
:= by
  unfold factorial_spec
  intro st1 st2 S H
  apply factorial_correct_aux (st1 "X") (st1 "Y") st1 st2 S
  simp
