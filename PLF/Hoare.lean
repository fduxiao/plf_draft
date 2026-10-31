import PLF.Imp


-- This is used to forces type casting
@[simp, grind]
def Eval (A: Type) := State → A

@[simp, grind]
def State.eval {A: Type} (st: State) (f: Eval A) := f st

section

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
def Eval.bexp (b: BExp) : Eval Bool := fun st => st.beval b

@[simp]
theorem Eval.bexp_eval (b: BExp) (st: State):
  (Eval.bexp b) st = st.beval b := rfl

@[grind]
def Eval.bexp_prop (b: BExp) : Eval Prop := fun st => st.beval b

@[simp]
theorem Eval.bexp_prop_eval (b: BExp) (st: State):
  (Eval.bexp_prop b) st = st.beval b := rfl

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

instance: Coe BExp (Eval Bool) where
  coe b := Eval.bexp b

instance: Coe BExp (Eval Prop) where
  coe b := Eval.bexp_prop b

instance: Coe Prop (Eval Prop) where
  coe P := fun _ => P

instance: Coe String (Eval Nat) where
  coe s := Eval.var s

end

section
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

def evalPrecedence : TSyntax `term → Option Nat
  | `([Eval| $_ + $_]) => some 50
  | `([Eval| $_ - $_]) => some 50
  | `([Eval| $_ * $_]) => some 60
  | `([Eval| $_ $_]) => some 30
  | _ => none

def termToEvalAt (t : TSyntax `term) (precedence : Nat) (isRight : Bool)
    : UnexpandM (TSyntax `lfp_eval) := do
  let e ← termToEval t
  match evalPrecedence t with
  | some childPrecedence =>
    if childPrecedence < precedence ||
        (isRight && childPrecedence == precedence) then
      `(lfp_eval| ($e))
    else
      pure e
  | none => pure e

def termToEvalAppArg (t : TSyntax `term) : UnexpandM (TSyntax `lfp_eval) := do
  let e ← termToEval t
  match evalPrecedence t with
  | some childPrecedence =>
    if childPrecedence >= 30 then
      `(lfp_eval| ($e))
    else
      pure e
  | none => pure e

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
    let x ← termToEvalAt x 50 false
    let y ← termToEvalAt y 50 true
    `([Eval| $x + $y])
  | _ => throw ()

@[app_unexpander Eval.sub]
def unexpanderEvalSub : Unexpander
  | `($_ $x $y) => do
    let x ← termToEvalAt x 50 false
    let y ← termToEvalAt y 50 true
    `([Eval| $x - $y])
  | _ => throw ()

@[app_unexpander Eval.mul]
def unexpanderEvalMul : Unexpander
  | `($_ $x $y) => do
    let x ← termToEvalAt x 60 false
    let y ← termToEvalAt y 60 true
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
    let f ← termToEvalAt f 30 false
    let x ← termToEvalAppArg x
    `([Eval| $f $x])
  | _ => throw ()

end

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
example: [Eval| #[Nat.add] [some_eval] 2 ] test_state = 6 := by rfl

end Playground

@[simp, grind]
def Assertion := State → Prop

section

@[grind]
def Assertion.eq (m n: Eval Nat) : Assertion :=
  fun st => st.eval m == st.eval n

@[simp]
theorem Assertion.eq_eval {m n: Eval Nat} {st}:
  Assertion.eq m n st = (st.eval m = st.eval n)
:= by
  grind

@[grind]
def Assertion.just (P: Assertion) : Assertion := P

instance: Coe Prop Assertion where
  coe p := fun _ => p

instance: Coe BExp Assertion where
  coe b := fun st => (st.beval b)

open Lean PrettyPrinter
declare_syntax_cat lfp_assertion
-- Arithmetic comparation
syntax:30 lfp_eval " == " lfp_eval : lfp_assertion
syntax:30 lfp_eval "<" lfp_eval : lfp_assertion
syntax:30 lfp_eval "<=" lfp_eval : lfp_assertion
syntax:30 lfp_eval ">" lfp_eval : lfp_assertion
syntax:30 lfp_eval ">=" lfp_eval : lfp_assertion
-- Logic connections
syntax "¬" lfp_assertion: lfp_assertion
syntax lfp_assertion "∨" lfp_assertion: lfp_assertion
syntax lfp_assertion "∧" lfp_assertion: lfp_assertion

-- BExp can be used as an Assertion
syntax "[B|" lfp_bexp "]": lfp_assertion

-- idents can be used directly
syntax ident: lfp_assertion
-- Normal term can be used as an Assertion
syntax "[" term "]": lfp_assertion
-- Allow parentheses
syntax  "(" lfp_assertion ")": lfp_assertion

-- Finally the evaluation
syntax "{{" lfp_assertion "}}": term


-- Evaluate each "{{" lfp_assertion "}}" to term
macro_rules
  -- arithmetic
  | `({{ $x:lfp_eval == $y }}) =>
    `(Assertion.eq [Eval|$x] [Eval|$y])
  | `({{ $x:lfp_eval < $y }}) =>
    `(fun (st: State) => st.eval [Eval|$x] < st.eval [Eval|$y])
  | `({{ $x:lfp_eval <= $y }}) =>
    `(fun (st: State) => st.eval [Eval|$x] <= st.eval [Eval|$y])
  | `({{ $x:lfp_eval > $y }}) =>
    `(fun (st: State) => st.eval [Eval|$x] > st.eval [Eval|$y])
  | `({{ $x:lfp_eval >= $y }}) =>
    `(fun (st: State) => st.eval [Eval|$x] >= st.eval [Eval|$y])
  -- logic
  | `({{ ¬$x }}) => `(show Assertion from fun (st: State) => Not (st.eval {{$x}}))
  | `({{ $x ∧ $y }}) => `(show Assertion from fun (st: State) => (st.eval) {{$x}} ∧ (st.eval {{$y}}))
  | `({{ $x ∨ $y }}) => `(show Assertion from fun (st: State) => (st.eval) {{$x}} ∨ (st.eval {{$y}}))
  -- BExp
  | `({{ [B| $b ] }}) => `(fun (st: State) => st.beval [BExp| $b] = true)
  -- misc
  | `({{ $x:ident }}) => `($x)
  | `({{ [$x: term] }}) => `((($x): Assertion))
  | `({{ ($x) }}) => `({{ $x }})

end

namespace Playground

example:
  {{ 2 <= 3 }} = fun st => [Eval| 2] st <= [Eval| 3] st
:= rfl

example:
  {{ X == 3 ∨ X <= Y }} =
    fun st =>
      [Eval| X] st == [Eval| 3] st
      ∨
      [Eval| X] st <= [Eval| Y] st
:= rfl

example:
  {{ ¬ X == 2 }} = fun st => ¬ (st.eval [Eval| X] == st.eval [Eval| 2])
:= rfl

example:
  {{ [B| X == 3] }} = fun st => st.beval [BExp| X == 3] = true
:= rfl

example:
  {{ [fun _ => True] }} = fun _: State => True
:= rfl

example:
  {{ [False] }} = fun _: State => False
:= rfl

example:
  {{ [True ∨ False] }} = fun _: State => True ∨ False
:= rfl

example:
  {{ X <= [Y] }} = fun st => [Eval| X] st <= [Eval| [Y]] st
:= rfl

example:
  {{ Z == #[max] X Y }} =
    fun st =>
      [Eval| Z] st = [Eval| #[max] X Y] st
:= by
  funext st
  simp

example: {{ ¬[True] }} = fun st => Not ([Eval| #[True]] st) := rfl

example:
  {{ (Z * Z <= X) ∧ ¬ (#[Nat.succ] 1 <= X) }} =
    fun st =>
      [Eval| Z * Z] st <= [Eval| X] st
      ∧
      Not ([Eval| #[Nat.succ] 1] st <= [Eval| X] st)
:= rfl

example: Assertion := {{ #[Nat.add] X Y > #[max] Y X }}

end Playground


@[simp]
abbrev Assertion.implies (P Q : Assertion) : Prop := forall st, P st → Q st
notation:26 P:26 "->>" Q:26 => (Assertion.implies P Q)
notation:26 P:26 "<<->>" Q:26 => ((P ->> Q) ∧ (Q ->> P))


def HoareTriple (P : Assertion) (c : Imp) (Q : Assertion) : Prop :=
  forall (st1 st2), st1 =[ c ]=> st2 → (P st1) → (Q st2)

macro:89 "{{" P:lfp_assertion:1 "}}<" c:lfp_imp:2 ">{{" Q:lfp_assertion:1 "}}": term
  => `(HoareTriple {{ $P }} <{ $c }> {{ $Q }})

theorem HoareTriple.post_true {P Q : Assertion} {c}:
  (forall st, Q st) → {{ P }}< c >{{ Q }}
:= by
  intros H
  intros st1 st2
  intros
  apply H


theorem HoareTriple.pre_false {P Q : Assertion} {c}:
  (forall st, Not (P st)) → {{ P }}< c >{{ Q }}
:= by
  intros NP
  intros st1 st2
  intros H P1
  exfalso
  apply NP
  apply P1


theorem HoareTriple.skip {P: Assertion}: {{ P }}< skip >{{ P }} := by
  intros st1 st2 B HP
  cases B
  apply HP


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

@[simp]
def Assertion.subst (P:Assertion) (X: String) (a: AExp)
  : Assertion
:= fun (st : State) => P state![X => st.aeval a; st]


syntax lfp_assertion "![" "["term"]" "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" str "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" term "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" ident "=>" lfp_aexp "]": lfp_assertion
macro_rules
  | `({{ $P ![ [$X:term] => $e ] }}) => `(Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:str => $e ] }}) => `(Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:ident => $e ] }}) =>
    `(Assertion.subst {{ $P }} $(Lean.quote (toString X.getId)) [AExp| $e])


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

set_option pp.all true in
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


theorem HoareTriple.asgn_fwd {m: Nat} {X: String} {a} {P : Assertion}:
  {{ P ∧ [X] == #[m] }}<[X] := [a]>{{ [
    fun st => (
      P state![X => m ; st] ∧
      st X = state![X => m ; st].aeval a
    )
  ]}}
:= by
  simp
  intros st1 st2 B H1
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
  simp
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
    . simp [Assertion.eq]



example:
  {{ True }}<
    X := 1;
    Y := 2
  >{{ X == 1 ∧ Y == 2 }}
:= by
  simp
  apply HoareTriple.seq
  . apply HoareTriple.asgn
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp


theorem HoareTriple.if {P Q} {b: BExp} {c1 c2}:
  {{ P ∧ b }}< c1 >{{ Q }} →
  {{ P ∧ ¬ b}}< c2 >{{ Q }} →
  {{ P }}< if b then c1 else c2 end >{{ Q }}
:= by
  simp
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
    . simp


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


theorem HoareTriple.while {P} {b: BExp} {c}:
  {{ P ∧ b }}< c >{{ P }} →
  {{ P }}< while b do c end >{{ P ∧ ¬ b }}
:= by
  simp
  intros HHoare
  intros st1 st3
  generalize E: <{ while b do c end }> = prog
  intros B HPre
  induction B with
  | @WhileFalse b c st HF =>
    cases E
    trivial
  | @WhileTrue b c st1 st2 st3 HT H12 H23 IH12 IH23 =>
    cases E
    specialize (HHoare st1 st2 H12)
    simp at *
    specialize (HHoare HPre HT)
    apply IH23
    exact HHoare
  -- Other situations are impossible
  | _ => cases E
