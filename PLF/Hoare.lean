import PLF.Equiv


-- This is used to forces type casting
abbrev State.Evaluation (A: Type) := State -> A

@[simp]
def State.eval_any {A: Type} (st: State) (f: State.Evaluation A) := f st

instance: Coe Nat (State.Evaluation Nat) where
  coe n := fun _ => n

instance: Coe AExp (State.Evaluation Nat) where
  coe a := fun st => st.aeval a

instance: Coe String (State.Evaluation Nat) where
  coe s := fun st => st.aeval s


abbrev State.Assertion := State -> Prop

instance: Coe Prop State.Assertion where
  coe p := fun _ => p

instance: Coe BExp State.Assertion where
  coe b := fun st => (st.beval b)


-- I am going to define the syntax for assertion.
-- I declare two syntax categories: lfp_assertion_aexp and lfp_assertion

-- The lfp_assertion is the desire {{}} syntax, and common logic connectives
-- are allowed in this category

-- The lfp_assertion_aexp is used to help evaluation under st.
-- For example, a variable X is understood as `fun st => st X`
-- Thus, the evaluation of the macro should be some `State -> Nat`
-- I also define #(x) to be a escaped function: #(Nat.succ) will not
-- be applied to `st` at all.

declare_syntax_cat lfp_assertion_aexp
-- numbers
syntax num: lfp_assertion_aexp
-- variables
syntax ident: lfp_assertion_aexp
-- operators
syntax:50 lfp_assertion_aexp:50 "+" lfp_assertion_aexp:51 : lfp_assertion_aexp
syntax:50 lfp_assertion_aexp:50 "-" lfp_assertion_aexp:51 : lfp_assertion_aexp
syntax:60 lfp_assertion_aexp:60 "*" lfp_assertion_aexp:61 : lfp_assertion_aexp

syntax "[A|" lfp_aexp "]" : lfp_assertion_aexp
-- use predefined terms
syntax "[" term "]" : lfp_assertion_aexp
-- constants (don't apply to st)
syntax "#[" term "]" : lfp_assertion_aexp

-- parentheses
syntax "(" lfp_assertion_aexp ")" : lfp_assertion_aexp
-- application
syntax:30 lfp_assertion_aexp:30 lfp_assertion_aexp:31 : lfp_assertion_aexp
-- evaluation
syntax "[AAE|" lfp_assertion_aexp "]": term


-- Evaluation each [AAE| ... ] to fun st => some Nat
macro_rules
  | `([AAE| $x:num]) => `(fun _ => $x)
  | `([AAE| $x:ident]) => `(fun st => st $(Lean.quote (toString x.getId)))
  | `([AAE| $x + $y]) => `(fun st => (st.eval_any [AAE|$x]) + (st.eval_any [AAE|$y]))
  | `([AAE| $x - $y]) => `(fun st => (st.eval_any [AAE|$x]) - (st.eval_any [AAE|$y]))
  | `([AAE| $x * $y]) => `(fun st => (st.eval_any [AAE|$x]) * (st.eval_any [AAE|$y]))
  | `([AAE| [A| $e ] ]) => `(fun st => st.eval_any [AExp| $e])
  | `([AAE| [$x] ]) => `(fun st => st.eval_any $x)
  | `([AAE| #[ $x ] ]) => `(fun _ => $x)
  | `([AAE| ($x) ]) => `([AAE| $x ])
  | `([AAE| $x $y ]) => `(fun st => (st.eval_any [AAE| $x ]) (st.eval_any [AAE| $y ]))


namespace Playground
def test_state := state![X => 1;Y => 2]

example: test_state.eval_any [AAE| 3 ] = 3 := by
  eq_refl

example: test_state.eval_any [AAE| X ] = 1 := by
  eq_refl

example: test_state.eval_any [AAE| [Y] ] = 2 := by
  eq_refl

example: test_state.eval_any [AAE| [A|X + 2] ] = 3 := by
  eq_refl

example: test_state.eval_any [AAE| 6 * #[3] + 1 ] = 19 := by
  eq_refl

example: test_state.eval_any [AAE| #[Nat.succ] 1 ] = 2 := by
  eq_refl

example: test_state.eval_any [AAE| #[Nat.add] 1 2 ] = 3 := by
  eq_refl

end Playground


declare_syntax_cat lfp_assertion
-- Arithmetic comparation
syntax:30 lfp_assertion_aexp "=" lfp_assertion_aexp : lfp_assertion
syntax:30 lfp_assertion_aexp "<" lfp_assertion_aexp : lfp_assertion
syntax:30 lfp_assertion_aexp "<=" lfp_assertion_aexp : lfp_assertion
syntax:30 lfp_assertion_aexp ">" lfp_assertion_aexp : lfp_assertion
syntax:30 lfp_assertion_aexp ">=" lfp_assertion_aexp : lfp_assertion
-- Logic connections
syntax "~" lfp_assertion: lfp_assertion
syntax "¬" lfp_assertion: lfp_assertion
syntax lfp_assertion "\\/" lfp_assertion: lfp_assertion
syntax lfp_assertion "∨" lfp_assertion: lfp_assertion
syntax lfp_assertion "/\\" lfp_assertion: lfp_assertion
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
  | `({{ $x:lfp_assertion_aexp = $y }}) =>
    `(fun (st: State) => st.eval_any [AAE|$x] = st.eval_any [AAE|$y])
  | `({{ $x:lfp_assertion_aexp < $y }}) =>
    `(fun (st: State) => st.eval_any [AAE|$x] < st.eval_any [AAE|$y])
  | `({{ $x:lfp_assertion_aexp <= $y }}) =>
    `(fun (st: State) => st.eval_any [AAE|$x] <= st.eval_any [AAE|$y])
  | `({{ $x:lfp_assertion_aexp > $y }}) =>
    `(fun (st: State) => st.eval_any [AAE|$x] > st.eval_any [AAE|$y])
  | `({{ $x:lfp_assertion_aexp >= $y }}) =>
    `(fun (st: State) => st.eval_any [AAE|$x] >= st.eval_any [AAE|$y])
  -- logic
  | `({{ ~$x }}) => `(fun (st: State) => Not (st.eval_any {{$x}}))
  | `({{ ¬$x }}) => `(fun (st: State) => Not (st.eval_any {{$x}}))
  | `({{ $x /\ $y }}) => `(fun (st: State) => (st.eval_any) {{$x}} /\ (st.eval_any {{$y}}))
  | `({{ $x ∧ $y }}) => `(fun (st: State) => (st.eval_any) {{$x}} /\ (st.eval_any {{$y}}))
  | `({{ $x \/ $y }}) => `(fun (st: State) => (st.eval_any) {{$x}} \/ (st.eval_any {{$y}}))
  | `({{ $x ∨ $y }}) => `(fun (st: State) => (st.eval_any) {{$x}} \/ (st.eval_any {{$y}}))
  -- BExp
  | `({{ [B| $b ] }}) => `(fun (st: State) => st.beval [BExp| $b] = true)
  -- misc
  | `({{ $x:ident }}) => `($x)
  | `({{ [$x: term] }}) => `($x)
  | `({{ ($x) }}) => `({{ $x }})


namespace Playground

example: State.Assertion := {{ [B| X == 3] }}
example: State.Assertion := {{ [fun _ => True] }}
example: State.Assertion := {{ [False] }}

example: State.Assertion := {{ [True \/ False] }}

example: State.Assertion := {{ X <= [Y] }}
example: State.Assertion := {{ 2 <= 3 }}

example: State.Assertion := {{ X = 3 \/ X <= Y }}
example: State.Assertion := {{ Z = #[max] X Y }}

example: State.Assertion := {{ ~[True] }}
example: State.Assertion := {{ ~ X = 2 }}

example: State.Assertion := {{ (Z * Z <= X) /\ ~(#[Nat.succ] 1 <= X) }}

example: State.Assertion := {{ #[Nat.add] X Y > #[max] Y X }}

end Playground


@[simp]
abbrev State.Assertion.implies (P Q : State.Assertion) : Prop := forall st, P st -> Q st
notation:20 P "->>" Q => (State.Assertion.implies P Q)
notation:20 P "<<->>" Q => ((P ->> Q) /\ (Q ->> P))


def HoareTriple (P : State.Assertion) (c : Imp) (Q : State.Assertion) : Prop :=
  forall (st1 st2), st1 =[ c ]=> st2 -> (P st1) -> (Q st2)

macro:89 "{{" P:lfp_assertion:1 "}}<" c:lfp_imp:2 ">{{" Q:lfp_assertion:1 "}}": term
  => `(HoareTriple {{ $P }} <{ $c }> {{ $Q }})

theorem HoareTriple.post_true {P Q : State.Assertion} {c}:
  (forall st, Q st) -> {{ P }}< c >{{ Q }}
:= by
  intros H
  intros st1 st2
  intros
  apply H


theorem HoareTriple.pre_false {P Q : State.Assertion} {c}:
  (forall st, Not (P st)) -> {{ P }}< c >{{ Q }}
:= by
  intros NP
  intros st1 st2
  intros H P1
  exfalso
  apply NP
  apply P1
