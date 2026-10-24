import PLF.Imp
namespace PLF.PE


/--
A list of key-value pairs representing a partial state mapping
variable names to their values, i.e., `List (String × Nat)`.
-/
def PartialState := List (String × Nat) deriving Membership
def PartialState.nil: PartialState := []
def PartialState.cons: String × Nat -> PartialState -> PartialState := List.cons


def PartialState.keys (ps: PartialState): List String := ps.map Prod.fst
def PartialState.values (ps: PartialState): List Nat := ps.map Prod.snd


def PartialState.ind.{u}
  {motive: PartialState -> Sort u}
  (nil: motive .nil)
  (cons: forall x xs, motive xs -> motive (.cons x xs))
:
  forall s: PartialState, motive s
| .nil => nil
| .cons x xs => cons x xs (PartialState.ind nil cons xs)


def PartialState.lookup? (ps: PartialState) (k: String): Option Nat := ps.lookup k

@[simp]
theorem PartialState.lookup?_nil (k: String): PartialState.lookup? .nil k = none := by
  simp [PartialState.lookup?, PartialState.nil]


@[simp]
theorem PartialState.lookup?_cons {k1 k2: String} {v: Nat} {ps: PartialState}:
  (ps.cons (k1, v)).lookup? k2 = if k1 = k2 then some v else ps.lookup? k2
:= by
  simp [PartialState.lookup?, PartialState.cons]
  grind


theorem eq_refl.{u} {A: Sort u} {a b: A}:
  (a = b) = (b = a)
:= by
  apply propext
  apply Iff.intro
  . apply Eq.symm
  . apply Eq.symm


@[simp]
theorem PartialState.Mem_cons {ps: PartialState} {k v x}:
  (k, v) ∈ ps.cons x <-> x = (k, v) \/ (k, v) ∈ ps
:= by
  simp [PartialState.cons]
  conv in x = (k, v) =>
    apply eq_refl
  apply List.mem_cons


def PartialState.remove (ps: PartialState) (k: String): PartialState :=
  match ps with
  | .nil => .nil
  | .cons (k', v) ps' =>
    if k = k' then ps'.remove k
    else .cons (k', v) (ps'.remove k)


@[simp]
theorem PartialState.remove_nil {k: String}:
  PartialState.remove .nil k = .nil
:= by
  simp [PartialState.remove, PartialState.nil]
  rfl


@[simp]
theorem PartialState.remove_cons {k1 k2: String} {v: Nat} {ps: PartialState}:
  PartialState.remove (.cons (k1, v) ps) k2 = if k1 = k2 then ps.remove k1 else .cons (k1, v) (PartialState.remove ps k2)
:= by
  simp [PartialState.remove, PartialState.cons]
  grind


@[simp]
theorem PartialState.remove_correct_eq {ps: PartialState} {k k': String}:
  (ps.remove k).lookup? k' = if k = k' then none else ps.lookup? k'
:= by
  induction ps using PartialState.ind generalizing k k'
  case nil =>
    simp
  case cons x xs IH =>
    rcases x with ⟨k'', v⟩
    simp
    split
    . grind
    . simp_all
      grind


scoped macro "compare" i:ident j:ident: tactic => `(tactic|
  rcases _: ($i == $j) <;>
    (try simp_all) <;>
    (try grind)
)

theorem PartialState.domain {ps: PartialState} {k v}:
  ps.lookup? k = some v -> (k, v) ∈ ps
:= by
  intro H
  induction ps using PartialState.ind
  case nil =>
    simp at H
  case cons x xs IH =>
    rcases x with ⟨k', v'⟩
    compare k' k


theorem PartialState.mem_keys {ps: PartialState} {k v}:
  (k, v) ∈ ps -> k ∈ ps.keys
:= by
  simp [PartialState.keys]
  apply List.mem_map_of_mem


def PartialState.aexp (ps: PartialState): AExp -> AExp
| .Num n => .Num n
| .Var x => match ps.lookup? x with
  | some v => .Num v
  | none => .Var x
| .Plus a1 a2 =>
  match ps.aexp a1, ps.aexp a2 with
  | .Num n1, .Num n2 => .Num (n1 + n2)
  | a1', a2' => .Plus a1' a2'
| .Minus a1 a2 =>
  match ps.aexp a1, ps.aexp a2 with
  | .Num n1, .Num n2 => .Num (n1 - n2)
  | a1', a2' => .Minus a1' a2'
| .Mult a1 a2 =>
  match ps.aexp a1, ps.aexp a2 with
  | .Num n1, .Num n2 => .Num (n1 * n2)
  | a1', a2' => .Mult a1' a2'


example: PartialState.aexp [("x", 3), ("y", 4)] (.Plus (.Var "x") (.Var "y")) = .Num 7 := by
  simp [PartialState.aexp, PartialState.lookup?, List.lookup]


example: PartialState.aexp [("x", 3)] [AExp| x + 1 + y] = [AExp| 4 + y] := by
  simp [PartialState.aexp, PartialState.lookup?, List.lookup]


example: PartialState.aexp [("y", 3)] [AExp| x + 1 + y] = [AExp| x + 1 + 3] := by
  simp [PartialState.aexp, PartialState.lookup?, List.lookup]


example: PartialState.aexp [("x", 3)] [AExp| x - y] = [AExp| 3 - y] := by
  simp [PartialState.aexp, PartialState.lookup?, List.lookup]


def PartialState.consistent (ps: PartialState) (st: State): Prop :=
  forall {k v}, ps.lookup? k = some v -> st k = v


theorem PartialState.aexp_correct_weak {ps: PartialState} {st: State}:
  ps.consistent st ->
  forall a, st.aeval a = st.aeval (ps.aexp a)
:= by
  unfold PartialState.consistent
  intro H a
  induction a <;>
    simp [PartialState.aexp] <;>
    split <;> simp_all


def PartialState.override (ps: PartialState) (st: State): State :=
  match ps with
  | [] => st
  | (k, v) :: ps' => (PartialState.override ps' st).update k v

example:
  PartialState.override [("x", 3), ("z", 2)] state![ "y" => 1] =
    state![ "x" => 3; "z" => 2; "y" => 1]
:= by
  simp [PartialState.override, State.update]


theorem PartialState.override_correct {ps: PartialState} {st: State} {k}:
  (ps.override st) k = match ps.lookup? k with
  | some v => v
  | none => st k
:= by
  induction ps using PartialState.ind
  case nil =>
    simp [PartialState.nil, PartialState.override, PartialState.lookup?]
  case cons x xs IH =>
    rcases x with ⟨k', v'⟩
    compare k' k
    case true E =>
      simp [override, cons]
    case false NE =>
      simp [override, cons]
      replace NE: k ≠ k' := by grind
      simp [NE]
      apply IH


theorem PartialState.override_consistent {ps: PartialState} {st: State}:
  ps.consistent (ps.override st)
:= by
  intro k n H
  rewrite [PartialState.override_correct]
  simp [H]


theorem PartialState.consistent_override {ps: PartialState} {st: State}:
  ps.consistent st ->
  forall k, st k = (ps.override st) k
:= by
  intro H k
  rewrite [PartialState.override_correct]
  rcases E: ps.lookup? k
  case some v =>
    simp
    apply H
    exact E
  case none =>
    simp


theorem PartialState.aexp_correct {ps: PartialState} {st: State} {a}:
  (ps.override st).aeval a = st.aeval (ps.aexp a)
:= by
  induction a
  case Num n =>
    simp [PartialState.aexp, State.aeval]
  case Var x =>
    simp [PartialState.aexp, State.aeval, PartialState.override_correct]
    split
    . simp_all
    . simp_all
  case Plus | Minus | Mult =>
    simp [PartialState.aexp, State.aeval]
    split
    . simp_all
    . simp_all


def PartialState.bexp (ps: PartialState): BExp -> BExp
| .True => .True
| .False => .False
| .Eq a1 a2 =>
  match ps.aexp a1, ps.aexp a2 with
  | .Num n1, .Num n2 => if n1 = n2 then .True else .False
  | a1', a2' => .Eq a1' a2'
| .Le a1 a2 =>
  match ps.aexp a1, ps.aexp a2 with
  | .Num n1, .Num n2 => if n1 ≤ n2 then .True else .False
  | a1', a2' => .Le a1' a2'
| .Not b =>
  match ps.bexp b with
  | .True => .False
  | .False => .True
  | b' => .Not b'
| .And b1 b2 =>
  match ps.bexp b1, ps.bexp b2 with
  | .True, .True => .True
  | .False, _ => .False
  | _, .False => .False
  | b1', b2' => .And b1' b2'


@[simp]
theorem beq_false_of_ne {n1 n2: Nat}:
  n1.beq n2 = false <-> n1 ≠ n2
:= by
  apply Iff.intro
  . apply Nat.ne_of_beq_eq_false
  . intro H
    rcases E: n1.beq n2
    . rfl
    . simp_all


@[simp]
theorem ble_false_of_le {n1 n2: Nat}:
  n1.ble n2 = false <-> n1 > n2
:= by
  rcases E: n1.ble n2
  . simp
    apply Nat.lt_of_not_ge
    intro H
    replace H: n1 ≤ n2 := by simp_all
    rewrite [<-Nat.ble_eq] at H
    simp_all
  . simp_all [Nat.ble_eq]


theorem PartialState.bexp_correct {ps: PartialState} {st: State} {b}:
  (ps.override st).beval b = st.beval (ps.bexp b)
:= by
  induction b
  case True | False =>
    simp [PartialState.bexp]
  case Eq | Le =>
    simp [PartialState.bexp]
    simp [PartialState.aexp_correct]
    split
    . simp_all
      split
      . simp_all
      . simp_all
    . simp_all
  case Not =>
    simp [PartialState.bexp, State.beval]
    split
    . simp_all
    . simp_all
    . simp_all
  case And =>
    simp [PartialState.bexp, State.beval]
    split
    . simp_all
    . simp_all
    . simp_all
    . simp_all


theorem PartialState.override_update_remove {ps: PartialState} {k v} {st: State}:
  (ps.override st).update k v = (ps.remove k).override (st.update k v)
:= by
  funext k'
  simp [PartialState.override_correct]
  grind


theorem PartialState.override_update_cons {ps: PartialState} {k v} {st: State}:
  (ps.override st).update k v = (ps.cons (k, v)).override st
:= by
  funext k'
  simp [PartialState.override_correct]
  grind


def PartialState.disagree_at (ps1 ps2: PartialState) (k: String): Bool :=
  ps1.lookup? k != ps2.lookup? k


theorem not_eq_symm {A: Type} {x y: A}:
  ¬ x = y -> ¬ y = x
:= by
  intro H contra
  apply H
  symm
  exact contra


scoped macro "not_eq_symm" : tactic => `(tactic| apply not_eq_symm)
scoped macro "not_eq_symm" "at" i:ident : tactic => `(tactic| replace $i := not_eq_symm $i)


theorem PartialState.disagree_domain {ps1 ps2: PartialState} {k}:
  ps1.disagree_at ps2 k = true ->
  k ∈ ps1.keys ++ ps2.keys
:= by
  intro H
  simp_all [PartialState.disagree_at]
  rcases E1: ps1.lookup? k
  case none =>
    simp_all
    not_eq_symm at H
    replace H := Option.ne_none_iff_exists.mp H
    right
    apply PartialState.mem_keys
    apply PartialState.domain
    symm
    apply H.choose_spec
  case some v =>
    left
    apply PartialState.mem_keys
    apply PartialState.domain
    apply E1
