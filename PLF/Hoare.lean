import PLF.Imp
import Lean.PrettyPrinter.Parenthesizer


-- This is used to forces type casting
@[simp, grind]
def Eval (A: Type) := State → A

@[simp, grind]
def State.eval {A: Type} (st: State) (f: Eval A) := f st

section EvalOps

@[grind]
def Eval.nat (n: Nat) : Eval Nat := fun _ => n

@[simp]
theorem Eval.nat_eval (n: Nat) (st: State):
  (Eval.nat n) st = n := rfl

@[grind]
def Eval.var (x: String) : Eval Nat := fun st => st.aeval x

@[simp]
theorem Eval.var_eval (x: String) (st: State):
  (Eval.var x) st = st.aeval x := rfl

@[grind]
def Eval.add (x y: Eval Nat) : Eval Nat := fun st => (st.eval x) + (st.eval y)

@[simp]
theorem Eval.add_eval (x y: Eval Nat) (st: State):
  (Eval.add x y) st = (st.eval x) + (st.eval y) := rfl

@[grind]
def Eval.sub (x y: Eval Nat) : Eval Nat := fun st => (st.eval x) - (st.eval y)

@[simp]
theorem Eval.sub_eval (x y: Eval Nat) (st: State):
  (Eval.sub x y) st = (st.eval x) - (st.eval y) := rfl

@[grind]
def Eval.mul (x y: Eval Nat) : Eval Nat := fun st => (st.eval x) * (st.eval y)

@[simp]
theorem Eval.mul_eval (x y: Eval Nat) (st: State):
  (Eval.mul x y) st = (st.eval x) * (st.eval y) := rfl

@[grind]
def Eval.aexp (a: AExp) : Eval Nat := fun st => st.aeval a

@[simp]
theorem Eval.aexp_eval (a: AExp) (st: State):
  (Eval.aexp a) st = st.aeval a := rfl

@[grind]
def Eval.pure {A} (x: A) : Eval A := fun _ => x

@[simp]
theorem Eval.pure_eval {A} (x: A) (st: State):
  (Eval.pure x) st = x := rfl

@[grind]
def Eval.app {A B} (f: Eval (A → B)) (x: Eval A) : Eval B := fun st => (st.eval f) (st.eval x)

@[simp]
theorem Eval.app_eval {A B} (f: Eval (A → B)) (x: Eval A) (st: State):
  (Eval.app f x) st = (st.eval f) (st.eval x) := rfl

instance: Coe Nat (Eval Nat) where
  coe n := Eval.nat n

instance: Coe AExp (Eval Nat) where
  coe a := Eval.aexp a

instance: Coe String (Eval Nat) where
  coe s := Eval.var s

end EvalOps

section EvalMacros
open Lean Lean.PrettyPrinter
declare_syntax_cat lfp_eval
-- numbers
syntax num: lfp_eval
-- variables
syntax ident: lfp_eval
-- operators
syntax:50 lfp_eval:50 " + " lfp_eval:51 : lfp_eval
syntax:50 lfp_eval:50 " - " lfp_eval:51 : lfp_eval
syntax:60 lfp_eval:60 " * " lfp_eval:61 : lfp_eval

syntax "[A| " lfp_aexp " ]" : lfp_eval
-- use predefined terms
syntax "[" term "]" : lfp_eval
-- constants (don't apply to st)
syntax "#[" term "]" : lfp_eval

-- parentheses
syntax "(" lfp_eval ")" : lfp_eval
-- application
syntax:30 lfp_eval:30 ppSpace lfp_eval:31 : lfp_eval
-- evaluation
syntax "[Eval| " lfp_eval " ]": term


-- Evaluation each [Eval| ... ] to fun st => some Nat
macro_rules
  | `([Eval| $x:num ]) => `(Eval.nat $x)
  | `([Eval| $x:ident ]) => `(Eval.var $(Lean.quote (toString x.getId)))
  | `([Eval| $x + $y]) => `(Eval.add [Eval| $x] [Eval| $y])
  | `([Eval| $x - $y ]) => `(Eval.sub [Eval| $x] [Eval| $y])
  | `([Eval| $x * $y ]) => `(Eval.mul [Eval| $x] [Eval| $y])
  | `([Eval| [A| $e ] ]) => `(Eval.aexp [AExp| $e])
  | `([Eval| [$x] ]) => `((($x): Eval Nat))
  | `([Eval| #[ $x ] ]) => `(Eval.pure $x)
  | `([Eval| ($x) ]) => `([Eval| $x ])
  | `([Eval| $x $y ]) => `(Eval.app [Eval| $x] [Eval| $y])

def termToEval: TSyntax `term → UnexpandM (TSyntax `lfp_eval)
  | `([Eval| $x]) => `(lfp_eval| $x )
  | `($x:term) => `(lfp_eval| [$x])

@[category_parenthesizer lfp_eval]
def lfpEval.parenthesizer : CategoryParenthesizer
  | prec =>
    Parenthesizer.maybeParenthesize `lfp_eval false
      (fun stx => Unhygienic.run `(lfp_eval|($(⟨stx⟩))))
      prec
      (Parenthesizer.parenthesizeCategoryCore `lfp_eval prec)

@[app_unexpander Eval.nat]
def unexpanderEvalNat: Unexpander :=
  fun stx => match stx with
  | `($_ $n:num) => `([Eval| $n:num])
  | `($_ $t:term) => do
    let t ← termToEval t
    `([Eval| $t])
  | _ => throw ()

@[app_unexpander Eval.var]
def unexpanderEvalVar: Unexpander :=
  fun stx => match stx with
  | `($_ $x:str) =>
    let i := mkIdent (Name.mkStr1 x.getString)
    `([Eval| $i:ident ])
  | `($_ $t) => do
    let t ← termToEval t
    `([Eval| $t])
  | _ => throw ()

@[app_unexpander Eval.add]
def unexpanderEvalAdd : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `([Eval| $x + $y])
  | _ => throw ()

@[app_unexpander Eval.sub]
def unexpanderEvalSub : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `([Eval| $x - $y])
  | _ => throw ()

@[app_unexpander Eval.mul]
def unexpanderEvalMul : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `([Eval| $x * $y])
  | _ => throw ()

@[app_unexpander Eval.aexp]
def unexpanderEvalAExp : Unexpander
  | `($_ $a) => do
    let a ← termToAExp a
    `([Eval| [A| $a]])
  | _ => throw ()

@[app_unexpander Eval.pure]
def unexpanderEvalPure : Unexpander
  | `($_ $x) => `([Eval| #[$x]])
  | _ => throw ()

@[app_unexpander Eval.app]
def unexpanderEvalApp : Unexpander
  | `($_ $f $x) => do
    let f ← termToEval f
    let x ← termToEval x
    `([Eval| $f $x])
  | _ => throw ()

end EvalMacros

namespace Playground
def test_state := state![X => 1;Y => 2]
def some_eval := fun st: State => st.aeval ("X") + 3

example: some_eval test_state = 4 := rfl
example: [Eval| X + 3 ] test_state = 4 := by rfl
example: [Eval| 3 ] test_state = 3 := by rfl
example: [Eval| X ] test_state = 1 := by rfl

example: [Eval| [some_eval]] = some_eval := by rfl
example: [Eval| [some_eval]] test_state = 4 := by rfl

example: [Eval| [Y] ] test_state = 2 := by rfl
example: [Eval| [A|X + 2] ] test_state = 3 := by rfl

example: [Eval| 6 * #[3] + 1 ] test_state = 19 := by rfl
example: [Eval| 6 * (#[3] + 1) ] test_state = 24 := by rfl
example: [Eval| #[Nat.succ] 1 ] test_state = 2 := by rfl
example: [Eval| #[Nat.add] 1 2 ] test_state = 3 := by rfl
example: [Eval| #[Nat.add] (#[Nat.succ] 1) 2 ] test_state = 4 := by rfl
example: [Eval| #[Nat.add] [some_eval] 2 ] test_state = 6 := by rfl

end Playground

@[simp, grind]
def Assertion := State → Prop

section AssertionOps

@[grind]
def Assertion.eq (m n: Eval Nat) : Assertion :=
  fun st => st.eval m == st.eval n

@[simp]
theorem Assertion.eq_eval {m n: Eval Nat} {st}:
  Assertion.eq m n st = (st.eval m = st.eval n)
:= by
  grind

@[grind]
def Assertion.lg (m n: Eval Nat) : Assertion :=
  fun st => st.eval m < st.eval n

@[simp]
theorem Assertion.lg_eval {m n: Eval Nat} {st}:
  Assertion.lg m n st = (st.eval m < st.eval n)
:= by
  grind

@[grind]
def Assertion.le (m n: Eval Nat) : Assertion :=
  fun st => st.eval m <= st.eval n

@[simp]
theorem Assertion.le_eval {m n: Eval Nat} {st}:
  Assertion.le m n st = (st.eval m <= st.eval n)
:= by
  grind

@[grind]
def Assertion.gt (m n: Eval Nat) : Assertion :=
  fun st => st.eval m > st.eval n

@[simp]
theorem Assertion.gt_eval {m n: Eval Nat} {st}:
  Assertion.gt m n st = (st.eval m > st.eval n)
:= by
  grind

@[grind]
def Assertion.ge (m n: Eval Nat) : Assertion :=
  fun st => st.eval m >= st.eval n

@[simp]
theorem Assertion.ge_eval {m n: Eval Nat} {st}:
  Assertion.ge m n st = (st.eval m >= st.eval n)
:= by
  grind

@[grind]
def Assertion.pure (P: Prop) : Assertion :=
  fun _ => P

@[simp]
theorem Assertion.pure_eval {P: Prop} {st}:
  Assertion.pure P st = P := rfl

@[grind]
def Assertion.bexp (b: BExp) : Assertion :=
  fun st => st.beval b = true

@[simp]
theorem Assertion.bexp_eval {b: BExp} {st}:
  Assertion.bexp b st = (st.beval b = true)
:= by
  grind

@[grind]
def Assertion.not (P: Assertion) : Assertion :=
  fun st => ¬ P st

@[simp]
theorem Assertion.not_eval {P: Assertion} {st}:
  Assertion.not P st = ¬ P st := rfl

@[grind]
def Assertion.and (P Q: Assertion) : Assertion :=
  fun st => P st ∧ Q st

@[simp]
theorem Assertion.and_eval {P Q: Assertion} {st}:
  Assertion.and P Q st = (P st ∧ Q st) := rfl

@[simp, grind =]
theorem Assertion.and_false {P: Assertion}:
  P.and (.pure False) = .pure False
:= by
  funext st
  grind

@[simp, grind =]
theorem Assertion.false_and {P: Assertion}:
  Assertion.and (.pure False) P = .pure False
:= by
  funext st
  grind

instance: Coe Prop Assertion where
  coe p := Assertion.pure p

@[grind]
def Assertion.or (P Q: Assertion) : Assertion :=
  fun st => P st ∨ Q st

@[simp]
theorem Assertion.or_eval {P Q: Assertion} {st}:
  Assertion.or P Q st = (P st ∨ Q st) := rfl

instance: Coe BExp Assertion where
  coe b := Assertion.bexp b

end AssertionOps

section AssertionMacros

open Lean PrettyPrinter
declare_syntax_cat lfp_assertion
-- Arithmetic comparation
syntax:30 lfp_eval " == " lfp_eval : lfp_assertion
syntax:30 lfp_eval " < " lfp_eval : lfp_assertion
syntax:30 lfp_eval " <= " lfp_eval : lfp_assertion
syntax:30 lfp_eval " > " lfp_eval : lfp_assertion
syntax:30 lfp_eval " >= " lfp_eval : lfp_assertion
-- Logic connections
syntax:25 "¬" lfp_assertion:25 : lfp_assertion
syntax:20 lfp_assertion:20 " ∧ " lfp_assertion:21 : lfp_assertion
syntax:20 lfp_assertion:20 " ∨ " lfp_assertion:21 : lfp_assertion

-- BExp can be used as an Assertion
syntax "[B| " lfp_bexp " ]": lfp_assertion

-- idents can be used directly
syntax ident: lfp_assertion
-- Normal term can be used as an Assertion
syntax "[" term "]": lfp_assertion
-- Allow parentheses
syntax  "(" lfp_assertion ")": lfp_assertion

-- Finally the evaluation
syntax "{{ " lfp_assertion " }}" : term


-- Evaluate each "{{" lfp_assertion "}}" to term
macro_rules
  -- arithmetic
  | `({{ $x:lfp_eval == $y }}) =>
    `(Assertion.eq [Eval|$x] [Eval|$y])
  | `({{ $x:lfp_eval < $y }}) =>
    `(Assertion.lg [Eval|$x] [Eval|$y])
  | `({{ $x:lfp_eval <= $y }}) =>
    `(Assertion.le [Eval|$x] [Eval|$y])
  | `({{ $x:lfp_eval > $y }}) =>
    `(Assertion.gt [Eval|$x] [Eval|$y])
  | `({{ $x:lfp_eval >= $y }}) =>
    `(Assertion.ge [Eval|$x] [Eval|$y])
  -- logic
  | `({{ ¬$x }}) => `(Assertion.not {{ $x }})
  | `({{ $x ∧ $y }}) => `(Assertion.and {{ $x }} {{ $y }})
  | `({{ $x ∨ $y }}) => `(Assertion.or {{ $x }} {{ $y }})
  -- BExp
  | `({{ [B| $b ] }}) => `(Assertion.bexp [BExp| $b ])
  -- misc
  | `({{ $x:ident }}) => `($x)
  | `({{ [$x: term] }}) => `((($x): Assertion))
  | `({{ ($x) }}) => `({{ $x }})

def termToAssertion : TSyntax `term → UnexpandM (TSyntax `lfp_assertion)
  | `({{ $P:lfp_assertion }}) => pure P
  | `($P:ident) => `(lfp_assertion| $P:ident)
  | `($P:term) => `(lfp_assertion| [$P])

@[category_parenthesizer lfp_assertion]
def lfpAssertion.parenthesizer : CategoryParenthesizer
  | prec =>
    Parenthesizer.maybeParenthesize `lfp_assertion false
      (fun stx => Unhygienic.run `(lfp_assertion|($(⟨stx⟩))))
      prec
      (Parenthesizer.parenthesizeCategoryCore `lfp_assertion prec)

@[app_unexpander Assertion.eq]
def unexpanderAssertionEq : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `({{ $x:lfp_eval == $y:lfp_eval }})
  | _ => throw ()

@[app_unexpander Assertion.lg]
def unexpanderAssertionLg : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `({{ $x:lfp_eval < $y:lfp_eval }})
  | _ => throw ()

@[app_unexpander Assertion.le]
def unexpanderAssertionLe : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `({{ $x:lfp_eval <= $y:lfp_eval }})
  | _ => throw ()

@[app_unexpander Assertion.gt]
def unexpanderAssertionGt : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `({{ $x:lfp_eval > $y:lfp_eval }})
  | _ => throw ()

@[app_unexpander Assertion.ge]
def unexpanderAssertionGe : Unexpander
  | `($_ $x $y) => do
    let x ← termToEval x
    let y ← termToEval y
    `({{ $x:lfp_eval >= $y:lfp_eval }})
  | _ => throw ()

@[app_unexpander Assertion.pure]
def unexpanderAssertionPure : Unexpander
  | `($_ $P) => `({{ [$P] }})
  | _ => throw ()

@[app_unexpander Assertion.bexp]
def unexpanderAssertionBExp : Unexpander
  | `($_ $b) => do
    let b ← termToBExp b
    `({{ [B| $b] }})
  | _ => throw ()

@[app_unexpander Assertion.not]
def unexpanderAssertionNot : Unexpander
  | `($_ $P) => do
    let P ← termToAssertion P
    `({{ ¬ $P:lfp_assertion }})
  | _ => throw ()

@[app_unexpander Assertion.and]
def unexpanderAssertionAnd : Unexpander
  | `($_ $P $Q) => do
    let P ← termToAssertion P
    let Q ← termToAssertion Q
    `({{ $P:lfp_assertion ∧ $Q:lfp_assertion }})
  | _ => throw ()

@[app_unexpander Assertion.or]
def unexpanderAssertionOr : Unexpander
  | `($_ $P $Q) => do
    let P ← termToAssertion P
    let Q ← termToAssertion Q
    `({{ $P:lfp_assertion ∨ $Q:lfp_assertion }})
  | _ => throw ()

end AssertionMacros

namespace Playground

example:
  {{ 2 <= 3 }} = fun st => [Eval| 2] st <= [Eval| 3] st
:= by rfl

example:
  {{ X == 3 ∨ X <= Y }} =
    fun st =>
      [Eval| X] st == [Eval| 3] st
      ∨
      [Eval| X] st <= [Eval| Y] st
:= by rfl

example:
  {{ ¬ X == 2 }} = fun st => ¬ (st.eval [Eval| X] == st.eval [Eval| 2])
:= by rfl

example:
  {{ [B| X == 3] }} = fun st => st.beval [BExp| X == 3] = true
:= by rfl

example:
  {{ [fun _ => True] }} = fun _: State => True
:= by rfl

example:
  {{ [False] }} = fun _: State => False
:= by rfl

example:
  {{ [True ∨ False] }} = fun _: State => True ∨ False
:= by rfl

example:
  {{ X <= [Y] }} = fun st => [Eval| X] st <= [Eval| [Y]] st
:= by rfl

example:
  {{ Z == #[max] X Y }} =
    fun st =>
      [Eval| Z] st = [Eval| #[max] X Y] st
:= by
  funext st
  simp

example: {{ ¬[True] }} = fun st => Not ([Eval| #[True]] st) := by rfl

example:
  {{ (Z * Z <= X) ∧ ¬ (#[Nat.succ] 1 <= X) }} =
    fun st =>
      [Eval| Z * Z] st <= [Eval| X] st
      ∧
      Not ([Eval| #[Nat.succ] 1] st <= [Eval| X] st)
:= by rfl

example: Assertion := {{ #[Nat.add] X Y > #[max] Y X }}

end Playground

@[grind]
def Assertion.implies (P Q : Assertion) : Prop := forall st, P st → Q st
notation:26 P:26 "->>" Q:26 => (Assertion.implies P Q)
notation:26 P:26 "<<->>" Q:26 => ((P ->> Q) ∧ (Q ->> P))

@[simp, refl, grind .]
theorem Assertion.implies_refl {P : Assertion} : P ->> P := by
  intros st HP
  apply HP

@[grind .]
theorem Assertion.implies_trans {P Q R : Assertion} :
  (P ->> Q) → (Q ->> R) → (P ->> R)
:= by
  intros HPQ HQR st HP
  apply HQR
  apply HPQ
  apply HP

@[ext, grind .]
theorem Assertion.implies_antisymm {P Q : Assertion} :
  (P ->> Q) → (Q ->> P) → (P = Q)
:= by
  intros HPQ HQP
  funext x
  grind

@[grind .]
theorem Assertion.yoneda {P Q : Assertion} :
  (forall H, H ->> P → H ->> Q) → (P ->> Q)
:= by
  intros H st HP
  apply H (fun st => P st)
  apply Assertion.implies_refl
  apply HP

theorem Assertion.yoneda_embedding {P Q : Assertion} :
  (forall H, H ->> P ↔ H ->> Q) → (P = Q)
:= by
  intro K
  ext
  . apply yoneda
    intro H
    apply (K H).mp
  . grind

@[grind]
def HoareTriple (P : Assertion) (c : Imp) (Q : Assertion) : Prop :=
  forall (st1 st2), st1 =[ c ]=> st2 → (P st1) → (Q st2)

section HoareTripleMacros
open Lean PrettyPrinter

macro:89 "{{ " P:lfp_assertion:1 " }}<" ppSpace c:lfp_imp:2 ppSpace ">{{ " Q:lfp_assertion:1 " }}": term
  => `(HoareTriple {{ $P }} <{ $c }> {{ $Q }})

@[app_unexpander HoareTriple]
def unexpanderHoareTriple : Unexpander
  | `($_ $P $c $Q) => do
    let P ← termToAssertion P
    let Q ← termToAssertion Q
    let c ← termToImp c
    `({{ $P }}< $c:lfp_imp >{{ $Q }})
  | _ => throw ()

end HoareTripleMacros

@[grind .]
theorem HoareTriple.post_true {P Q : Assertion} {c}:
  (forall st, Q st) → {{ P }}< c >{{ Q }}
:= by
  intros H
  intros st1 st2
  intros
  apply H

@[grind .]
theorem HoareTriple.pre_false {P Q : Assertion} {c}:
  (forall st, Not (P st)) → {{ P }}< c >{{ Q }}
:= by
  intros NP
  intros st1 st2
  intros H P1
  exfalso
  apply NP
  apply P1

@[grind .]
theorem HoareTriple.skip {P: Assertion}: {{ P }}< skip >{{ P }} := by
  intros st1 st2 B HP
  cases B
  apply HP

@[grind .]
theorem HoareTriple.seq {P Q R c1 c2}:
  {{ Q }}< c2 >{{ R }} →
  {{ P }}< c1 >{{ Q }} →
  {{ P }}< c1; c2 >{{ R }}
:= by
  intros Hc2 Hc1
  intros st1 st3
  intros B HP
  cases B with | @Seq c1 c2 st1 st2 st3 H12 H23 =>
  specialize (Hc1 st1 st2 H12 HP)
  specialize (Hc2 st2 st3 H23 Hc1)
  exact Hc2


-- Assignment is crucial here. We need to update the `State`. Thus, I define
-- the syntax sugar for this situation.

@[simp, grind]
def Assertion.subst (P:Assertion) (X: String) (a: AExp)
  : Assertion
:= fun (st : State) => P state![X => st.aeval a; st]

section AssertionSubstMacros
open Lean PrettyPrinter

syntax lfp_assertion " ![ " "["term"]" " => " lfp_aexp " ]": lfp_assertion
syntax lfp_assertion " ![ " str " => " lfp_aexp " ]": lfp_assertion
syntax lfp_assertion " ![ " ident " => " lfp_aexp " ]": lfp_assertion
macro_rules
  | `({{ $P ![ [$X:term] => $e ] }}) => `(Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:str => $e ] }}) => `(Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:ident => $e ] }}) =>
    `(Assertion.subst {{ $P }} $(Lean.quote (toString X.getId)) [AExp| $e])

@[app_unexpander Assertion.subst]
def unexpanderAssertionSubst : Unexpander
  | `($_ $P $X:str $a) => do
    let P ← termToAssertion P
    let a ← termToAExp a
    let X := mkIdent (Name.mkStr1 X.getString)
    `({{ $P ![ $X:ident => $a ] }})
  | `($_ $P $X $a) => do
    let P ← termToAssertion P
    let a ← termToAExp a
    `({{ $P ![ [$X:term] => $a ] }})
  | _ => throw ()

end AssertionSubstMacros

example: {{ (X <= 5) ![X => 3] }} <<->> {{ 3 <= 5 }} := by
  apply And.intro
  . intros st H
    trivial
  . intros st H
    simp

example: {{ (X <= 5) ![X => X + 1] }} <<->> {{ (X + 1) <= 5 }} := by
  apply And.intro
  . intros st H
    simp
    simp at H
    apply H
  . intros st H
    simp
    simp at H
    apply H

@[simp, grind .]
theorem HoareTriple.asgn {Q} {X: String} {a: AExp}:
  {{ Q ![[X] => [a]] }}< [X] := [a] >{{ Q }}
:= by
  intros st1 st2 B HPre
  cases B with | @Asgn _ _ n _ E =>
  simp at HPre
  rewrite[<-E]
  apply HPre


example: {{ (X < 5) ![X => X + 1] }}<X := X + 1 >{{ X < 5 }} := by
  apply HoareTriple.asgn


example : exists a: AExp,
  ¬ {{ True }}< X := [a] >{{ X == [a] }}
:= by
  let a := <{A| X + 1 }>
  exists a
  intros contra
  let st1 := state!["X" => 3]
  let st2 := st1.update "X" (st1.aeval a)
  have H: st1 =[ X := [a] ]=> st2 := by
    apply Imp.BigStep.Asgn
    eq_refl
  specialize (contra st1 st2 H True.intro)
  unfold a st2 at contra
  specialize contra
  simp at contra

@[grind .]
theorem HoareTriple.asgn_fwd {m: Nat} {X: String} {a} {P : Assertion}:
  {{ P ∧ [X] == #[m] }}<[X] := [a]>{{ [
    fun st => (
      P state![X => m ; st] ∧
      st X = state![X => m ; st].aeval a
    )
  ]}}
:= by
  intros st1 st2 B H1
  simp at H1
  cases B with | @Asgn _ _ n _ E =>
  let ⟨HP, Exm⟩ := H1
  have MEq: state![X => m; X => n; st1] = st1 := by
    simp_all
    rw [←Exm]
    simp

  rewrite [MEq]
  apply And.intro
  . apply HP
  . rewrite [E]
    simp

@[grind .]
theorem HoareTriple.asgn_fwd_exists a {X: String} {P: Assertion}:
  {{ P }}< [X] := [a] >{{ [
    fun st => ∃ m, P state![X => m ; st] ∧
                st X = state![X => m ; st].aeval a
  ] }}
:= by
  intros st1 st2 B HP
  exists st1.aeval X
  cases B with | @Asgn _ _ n _ E =>
  apply And.intro
  . simp
    exact HP
  . simp
    symm
    exact E

@[grind .]
theorem HoareTriple.consequence_pre {P1 P2 Q : Assertion} {c}:
  {{ P2 }}< c >{{ Q }} →
  P1 ->> P2 →
  {{ P1 }}< c >{{ Q }}
:= by
  intros HHoare Himp
  intros st1 st2 B HP
  specialize (HHoare st1 st2 B)
  apply HHoare
  apply Himp
  exact HP

@[grind .]
theorem HoareTriple.consequence_post {P Q1 Q2 : Assertion} {c}:
  {{ P }}< c >{{ Q2 }} →
  Q2 ->> Q1 →
  {{ P }}< c >{{ Q1 }}
:= by
  intros HHoare Himp
  intros st1 st2 B HP
  specialize (HHoare st1 st2 B)
  apply Himp
  apply HHoare
  exact HP


example: {{ True }}< X := 1 >{{X == 1}} := by
  apply HoareTriple.consequence_pre
  . apply HoareTriple.asgn
  . simp [Assertion.implies]


example: {{X < 4}}< X := X + 1 >{{X < 5}} := by
  apply HoareTriple.consequence_pre
  . apply HoareTriple.asgn
  . simp [Assertion.implies]
    intros st
    generalize st "X" = x
    intros H
    apply Nat.add_lt_add_right
    exact H

@[grind .]
theorem HoareTriple.consequence {P1 P2 Q1 Q2 : Assertion} {c}:
  {{ P2 }}< c >{{ Q2 }} →
  P1 ->> P2 →
  Q2 ->> Q1 →
  {{ P1 }}< c >{{ Q1 }}
:= by
  intros HHoare HP HQ
  apply HoareTriple.consequence_pre
  . apply HoareTriple.consequence_post
    . apply HHoare
    . apply HQ
  . apply HP


example: {{ X <= 5 }}< X := 2 * X >{{ X <= 10 }} := by
  intros st1 st2
  intros B H1
  cases B with | Asgn E =>
  subst E
  simp
  apply Nat.mul_le_mul_left 2 H1


example: forall (a: AExp) (n: Nat),
  {{ [a] == #[n] }}<
    X := [a];
    skip
  >{{ X == #[n] }}
:= by
  intros a n
  apply HoareTriple.seq
  . apply HoareTriple.skip
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp [Assertion.implies]



example:
  {{ True }}<
    X := 1;
    Y := 2
  >{{ X == 1 ∧ Y == 2 }}
:= by
  apply HoareTriple.seq
  . apply HoareTriple.asgn
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp [Assertion.implies]

@[grind .]
theorem HoareTriple.if {P Q} {b: BExp} {c1 c2}:
  {{ P ∧ b }}< c1 >{{ Q }} →
  {{ P ∧ ¬ b}}< c2 >{{ Q }} →
  {{ P }}< if b then c1 else c2 end >{{ Q }}
:= by
  intros HTrue HFalse
  intros st1 st2 B HPre
  cases B with
  | IfTrue HT B =>
    specialize (HTrue st1 st2 B)
    simp at HTrue
    specialize (HTrue HPre HT)
    apply HTrue
  | IfFalse HF B =>
    specialize (HFalse st1 st2 B)
    simp at HFalse
    specialize (HFalse HPre HF)
    apply HFalse


example:
  {{ True }}<
    if (X == 0)
      then Y := 2
      else Y := X + 1
    end
  >{{ X <= Y }}
:= by
  apply HoareTriple.if
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . intros st
      simp
      intros H
      rewrite [H]
      trivial
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp [Assertion.implies]


example :
  {{ True }}<
    if (X <= Y) then
      Z := Y - X
    else
      Y := X + Z
    end
  >{{ Y == X + Z }}
:= by
  apply HoareTriple.if
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . intro st
      simp
      generalize st "X" = x
      generalize st "Y" = y
      intros H
      symm
      apply Nat.add_sub_cancel'
      exact H
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . intro st
      simp

@[grind .]
theorem HoareTriple.while {P} {b: BExp} {c}:
  {{ P ∧ b }}< c >{{ P }} →
  {{ P }}< while b do c end >{{ P ∧ ¬ b }}
:= by
  intros HHoare
  intros st1 st3
  simp
  generalize E: <{ while b do c end }> = prog
  intros B HPre
  induction B
  case WhileFalse b c st HF =>
    cases E
    trivial
  case WhileTrue b c st1 st2 st3 HT H12 H23 IH12 IH23 =>
    cases E
    specialize (HHoare st1 st2 H12)
    simp at *
    specialize (HHoare HPre HT)
    apply IH23
    exact HHoare
  -- Other situations are impossible
  all_goals contradiction

example:
  {{ True }}<
    while (~ X == 0) do
      X := X - 1
    end
  >{{ X == 0 }}
:= by
  apply HoareTriple.consequence_post
  . apply HoareTriple.while
    apply HoareTriple.post_true
    simp
  . simp [Assertion.implies]
