import PLF.Imp


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
syntax "[Eval|" lfp_assertion_aexp "]": term


-- Evaluation each [Eval| ... ] to fun st => some Nat
macro_rules
  | `([Eval| $x:num]) => `(fun _ => $x)
  | `([Eval| $x:ident]) => `(fun st => st $(Lean.quote (toString x.getId)))
  | `([Eval| $x + $y]) => `(fun st => (st.eval_any [Eval|$x]) + (st.eval_any [Eval|$y]))
  | `([Eval| $x - $y]) => `(fun st => (st.eval_any [Eval|$x]) - (st.eval_any [Eval|$y]))
  | `([Eval| $x * $y]) => `(fun st => (st.eval_any [Eval|$x]) * (st.eval_any [Eval|$y]))
  | `([Eval| [A| $e ] ]) => `(fun st => st.eval_any [AExp| $e])
  | `([Eval| [$x] ]) => `(fun st => st.eval_any $x)
  | `([Eval| #[ $x ] ]) => `(fun _ => $x)
  | `([Eval| ($x) ]) => `([Eval| $x ])
  | `([Eval| $x $y ]) => `(fun st => (st.eval_any [Eval| $x ]) (st.eval_any [Eval| $y ]))


namespace Playground
def test_state := state![X => 1;Y => 2]
def some_eval := fun st: State => st.aeval ("X") + 3

example: some_eval test_state = 4 := rfl
example: [Eval| X + 3 ] test_state = 4 := rfl
example: [Eval| 3 ] test_state = 3 := rfl
example: [Eval| X ] test_state = 1 := rfl

example: [Eval| [some_eval]] = some_eval := rfl
example: [Eval| [some_eval]] test_state = 4 := rfl

example: [Eval| [Y] ] test_state = 2 := rfl
example: [Eval| [A|X + 2] ] test_state = 3 := rfl

example: [Eval| 6 * #[3] + 1 ] test_state = 19 := rfl
example: [Eval| #[Nat.succ] 1 ] test_state = 2 := rfl
example: [Eval| #[Nat.add] 1 2 ] test_state = 3 := rfl
example: [Eval| #[Nat.add] [some_eval] 2 ] test_state = 6 := rfl

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
    `(fun (st: State) => st.eval_any [Eval|$x] = st.eval_any [Eval|$y])
  | `({{ $x:lfp_assertion_aexp < $y }}) =>
    `(fun (st: State) => st.eval_any [Eval|$x] < st.eval_any [Eval|$y])
  | `({{ $x:lfp_assertion_aexp <= $y }}) =>
    `(fun (st: State) => st.eval_any [Eval|$x] <= st.eval_any [Eval|$y])
  | `({{ $x:lfp_assertion_aexp > $y }}) =>
    `(fun (st: State) => st.eval_any [Eval|$x] > st.eval_any [Eval|$y])
  | `({{ $x:lfp_assertion_aexp >= $y }}) =>
    `(fun (st: State) => st.eval_any [Eval|$x] >= st.eval_any [Eval|$y])
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

example:
  {{ 2 <= 3 }} = fun st => [Eval| 2] st <= [Eval| 3] st
:= rfl

example:
  {{ X = 3 ∨ X <= Y }} =
    fun st =>
      [Eval| X] st = [Eval| 3] st
      ∨
      [Eval| X] st <= [Eval| Y] st
:= rfl

example:
  {{ ~ X = 2 }} = fun st => ¬ (st.eval_any [Eval| X] = st.eval_any [Eval| 2])
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
  {{ Z = #[max] X Y }} =
    fun st =>
      [Eval| Z] st = [Eval| #[max] X Y] st
:= rfl

example: {{ ~[True] }} = fun st => Not ([Eval| [True]] st) := rfl

example:
  {{ (Z * Z <= X) ∧ ~(#[Nat.succ] 1 <= X) }} =
    fun st =>
      [Eval| Z * Z] st <= [Eval| X] st
      ∧
      Not ([Eval| #[Nat.succ] 1] st <= [Eval| X] st)
:= rfl

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


theorem HoareTriple.skip {P: State.Assertion}: {{ P }}< skip >{{ P }} := by
  intros st1 st2 B HP
  cases B
  apply HP


theorem HoareTriple.seq {P Q R c1 c2}:
  {{ Q }}< c2 >{{ R }} ->
  {{ P }}< c1 >{{ Q }} ->
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
def State.Assertion.subst (P:State.Assertion) (X: String) (a: AExp)
  : State.Assertion
:= fun (st : State) => P state![X => st.aeval a; st]


syntax lfp_assertion "![" "["term"]" "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" str "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" term "=>" lfp_aexp "]": lfp_assertion
syntax lfp_assertion "![" ident "=>" lfp_aexp "]": lfp_assertion
macro_rules
  | `({{ $P ![ [$X:term] => $e ] }}) => `(State.Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:str => $e ] }}) => `(State.Assertion.subst {{ $P }} $X [AExp| $e])
  | `({{ $P ![ $X:ident => $e ] }}) =>
    `(State.Assertion.subst {{ $P }} $(Lean.quote (toString X.getId)) [AExp| $e])


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


example : exists a: AExp,
  ¬ {{ True }}< X := [a] >{{ X = [a] }}
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
  unfold st2 a at contra
  simp at contra


theorem HoareTriple.asgn_fwd {m: Nat} {X: String} {a} {P : State.Assertion}:
  {{ P ∧ [X] = #[m] }}<[X] := [a]>{{ [
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
  have MEq: (TotalMap.update (st1.update X n) X m) = st1 := by
    unfold State.update
    rewrite [TotalMap.update_shadow]
    rewrite [<-Exm]
    apply TotalMap.update_same

  rewrite [MEq]
  apply And.intro
  . apply HP
  . rewrite [E]
    apply TotalMap.update_eq


theorem HoareTriple.asgn_fwd_exists a {X: String} {P: State.Assertion}:
  {{ P }}< [X] := [a] >{{ [
    fun st => ∃ m, P state![X => m ; st] ∧
                st X = state![X => m ; st].aeval a
  ] }}
:= by
  intros st1 st2 B HP
  exists st1.aeval X
  cases B with | @Asgn _ _ n _ E =>
  unfold State.update
  apply And.intro
  . rewrite [TotalMap.update_shadow]
    simp
    rewrite [TotalMap.update_same]
    exact HP
  . simp
    rewrite [TotalMap.update_shadow]
    rewrite [TotalMap.update_same]
    symm
    exact E


theorem HoareTriple.consequence_pre {P1 P2 Q : State.Assertion} {c}:
  {{ P2 }}< c >{{ Q }} ->
  (P1 ->> P2) ->
  {{ P1 }}< c >{{ Q }}
:= by
  intros HHoare Himp
  intros st1 st2 B HP
  specialize (HHoare st1 st2 B)
  apply HHoare
  apply Himp
  exact HP


theorem HoareTriple.consequence_post {P Q1 Q2 : State.Assertion} {c}:
  {{ P }}< c >{{ Q2 }} ->
  (Q2 ->> Q1) ->
  {{ P }}< c >{{ Q1 }}
:= by
  intros HHoare Himp
  intros st1 st2 B HP
  specialize (HHoare st1 st2 B)
  apply Himp
  apply HHoare
  exact HP


example: {{ True }}< X := 1 >{{X = 1}} := by
  apply HoareTriple.consequence_pre
  . apply HoareTriple.asgn
  . simp [State.Assertion.implies]


example: {{X < 4}}< X := X + 1 >{{X < 5}} := by
  apply HoareTriple.consequence_pre
  . apply HoareTriple.asgn
  . simp [State.Assertion.implies]
    intros st
    generalize st "X" = x
    intros H
    apply Nat.add_lt_add_right
    exact H

theorem HoareTriple.consequence {P1 P2 Q1 Q2 : State.Assertion} {c}:
  {{ P2 }}< c >{{ Q2 }} ->
  (P1 ->> P2) ->
  (Q2 ->> Q1) ->
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
  {{ [a] = #[n] }}<
    X := [a];
    skip
  >{{ X = #[n] }}
:= by
  intros a n
  simp
  apply HoareTriple.seq
  . apply HoareTriple.skip
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp


example:
  {{ True }}<
    X := 1;
    Y := 2
  >{{ X = 1 ∧ Y = 2 }}
:= by
  simp
  apply HoareTriple.seq
  . apply HoareTriple.asgn
  . apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . simp


theorem HoareTriple.if {P Q} {b: BExp} {c1 c2}:
  {{ P ∧ b }}< c1 >{{ Q }} ->
  {{ P ∧ ~b}}< c2 >{{ Q }} ->
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
  >{{ Y = X + Z }}
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
  {{ P /\ b }}< c >{{ P }} ->
  {{ P }}< while b do c end >{{ P /\ ~b }}
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
