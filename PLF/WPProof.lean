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

@[grind]
def Nat.factorial: Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * Nat.factorial n

def factorial_spec (n: Nat) c := {{ True }}< c >{{ Y == [Nat.factorial n] }}


@[grind .]
theorem HoareTriple.asgn_single {m: Nat} {X: String} {a: AExp}:
  {{ [a] == [m] }}<[X] := [a]>{{ [X] == [m] }}
:= by
  apply WP.triple
  simp only [WP.asgn_eq]
  simp

@[grind .]
theorem HoareTriple.asgn_fwd' {P} {m n: Nat} {X: String} {a: AExp}:
  {{ P ∧ [X] == [m] ∧ [a] == [n] }}<[X] := [a]>{{ P ![[X] => [m]] ∧ [X] == [n] }}
:= by
  apply WP.triple
  simp [WP.asgn_eq]
  intro st H
  simp at *
  grind

/--
If you have proved a Hoare triple `{{ P1 }}< c >{{ Q1 }}`,
you can utilize it to prove with `WP`.
-/
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
  . apply HoareTriple.asgn_fwd' (m := m) (n := n) (P := P)
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

theorem WP.add_eq (X: String) {P c Q}:
  (forall m: Nat, {{ P ∧ [X] == [m] }} ->> WP c Q) →
  P ->> WP c Q
:= by
  intro H st HP
  apply H (st X)
  simp
  exact HP

/--
This is a convenient theorem to apply the loop invariant:
```
{{ P ∧ b }}< c >{{ P }}
-----------------------------------------
{{ P }}< while b do c end >{{ P ∧ ¬ b }}
```
-/
@[grind .]
theorem WP.loop_invariant {P Q} {b: BExp} {c: Imp}:
  {{ P ∧ b }} ->> WP c P →
  {{ P ∧ ¬b }} ->> Q →
  P ->> WP (<{ while b do c end }>) Q
:= by
  intro M1 M2
  apply WP.app_triple
  . apply HoareTriple.while
    apply WP.triple
    exact M1
  . rfl
  . exact M2

theorem factorial_correct {n: Nat}:
  factorial_spec n (factorial n)
:= by
  simp [factorial_spec, factorial]
  apply WP.triple
  refine WP.add_eq "X" ?_; intro m1
  rw [WP.seq_eq]
  refine WP.asgn_fwd (m := m1) (n := n) ?_ ?_
  . grind
  simp; clear m1
  rw [WP.seq_eq]
  refine WP.add_eq "Y" ?_; intro m2
  refine WP.asgn_fwd (m := m2) (n := 1) ?_ ?_
  . grind
  simp; clear m2
  apply WP.conseq_pre
  . show _ ->> {{ Y * (#[Nat.factorial] X) == #[Nat.factorial n]}}
    intro st
    simp_all
  apply WP.loop_invariant
  . rw [WP.seq_eq]
    refine WP.add_eq "X" ?_; intro m1
    refine WP.add_eq "Y" ?_; intro m2
    refine WP.asgn_fwd (m := m2) (n := m1 * m2) ?_ ?_
    . intro st
      grind
    simp
    refine WP.asgn_fwd (m := m1) (n := m1 - 1) ?_ ?_
    . intro st
      grind
    simp
    intro st
    simp_all
    intros
    let k := m1 - 1
    have E: m1 = k + 1 := by omega
    simp_all [Nat.factorial]
    lia
  intro st
  simp
  intro E1 E2
  simp [Nat.factorial, E2] at E1
  exact E1

def factorial_acc: Imp := <{
  while 1 <= X do
    Y := Y * X;
    X := X - 1
  end
}>

def Nat.factorial_acc: Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => Nat.factorial_acc n ((n + 1) * acc)

theorem Nat.factorial_acc_eq {n acc: Nat}:
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

theorem factorial_correct' {n: Nat}:
  factorial_spec n (factorial n)
:= by
  simp [factorial_spec, factorial]
  apply WP.triple
  refine WP.add_eq "X" ?_; intro m1
  rw [WP.seq_eq]
  refine WP.asgn_fwd (m := m1) (n := n) ?_ ?_
  . grind
  simp
  rw [WP.seq_eq]
  refine WP.add_eq "Y" ?_; intro m2
  refine WP.asgn_fwd (m := m2) (n := 1) ?_ ?_
  . grind
  simp
  apply WP.app_triple
  . exact factorial_acc_correct n 1
  . intro st
    simp_all
  . rewrite [Nat.factorial_acc_eq]
    simp
