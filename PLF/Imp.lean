import PLF.Map


inductive AExp: Type where
  | Num (n : Nat)
  | Var (x : String)
  | Plus (a1 a2 : AExp)
  | Minus (a1 a2 : AExp)
  | Mult (a1 a2 : AExp)
  deriving Repr


instance {n: Nat}: OfNat AExp n where
  ofNat := .Num n


instance: Coe String AExp where
  coe := .Var


instance: Add AExp where
  add := .Plus


instance: Sub AExp where
  sub := .Minus


instance: Mul AExp where
  mul := .Mult


declare_syntax_cat lfp_aexp
syntax num : lfp_aexp
syntax ident: lfp_aexp
syntax str: lfp_aexp
syntax:50 lfp_aexp:50 "+" lfp_aexp:51 : lfp_aexp
syntax:50 lfp_aexp:50 "-" lfp_aexp:51 : lfp_aexp
syntax:60 lfp_aexp:60 "*" lfp_aexp:61 : lfp_aexp
syntax "(" lfp_aexp ")" : lfp_aexp
syntax "[" term "]" : lfp_aexp
syntax "[AExp|" lfp_aexp "]" : term


macro_rules
  | `([AExp| $x:num]) => `(AExp.Num $x)
  | `([AExp| $x:ident]) => `(AExp.Var $(Lean.quote (toString x.getId)))
  | `([AExp| $x:str]) => `(AExp.Var $x)
  | `([AExp| $x:lfp_aexp + $y:lfp_aexp]) => `([AExp| $x].Plus [AExp| $y])
  | `([AExp| $x:lfp_aexp - $y:lfp_aexp]) => `([AExp| $x].Minus [AExp| $y])
  | `([AExp| $x:lfp_aexp * $y:lfp_aexp]) => `([AExp| $x].Mult [AExp| $y])
  | `([AExp| ($x:lfp_aexp)]) => `([AExp| $x])
  | `([AExp| [$x:term] ]) => `(@id AExp $x)


namespace Playground

def W: String := "W"
def X: String := "X"
def Y: String := "Y"
def Z: String := "z"

def E1 := [AExp| [Z] - Z * 3 + 2 * T + W]
def E2 := [AExp| [E1] * [E1]]


example: E1 = "z" - "Z" * 3 + 2 * "T" + W := by
  eq_refl


example: E2 = E1 * E1 := by
  eq_refl


end Playground

inductive BExp : Type where
  | True
  | False
  | Eq (a1 a2 : AExp)
  | Le (a1 a2 : AExp)
  | Not (b : BExp)
  | And (b1 b2 : BExp)
  deriving Repr


instance: Coe Bool BExp where
  coe b := match b with
  | true => .True
  | false => .False


declare_syntax_cat lfp_bexp
syntax "true" : lfp_bexp
syntax "false" : lfp_bexp
syntax:30 lfp_aexp "==" lfp_aexp : lfp_bexp
syntax:30 lfp_aexp "<=" lfp_aexp : lfp_bexp
syntax:20 lfp_bexp:20 "&&" lfp_bexp:21 : lfp_bexp
syntax:25 "~" lfp_bexp:25 : lfp_bexp
syntax "(" lfp_bexp ")" : lfp_bexp
syntax "[" term "]" : lfp_bexp
syntax "[BExp|" lfp_bexp "]" : term


macro_rules
  | `([BExp| true]) => `(BExp.True)
  | `([BExp| false]) => `(BExp.False)
  | `([BExp| $x:lfp_aexp == $y:lfp_aexp]) => `(BExp.Eq [AExp|$x] [AExp|$y])
  | `([BExp| $x:lfp_aexp <= $y:lfp_aexp]) => `(BExp.Le [AExp|$x] [AExp|$y])
  | `([BExp| $x:lfp_bexp && $y:lfp_bexp]) => `(BExp.And [BExp|$x] [BExp|$y])
  | `([BExp| ~ $x:lfp_bexp]) => `(BExp.Not [BExp|$x])
  | `([BExp| ($x:lfp_bexp)]) => `([BExp| $x])
  | `([BExp| [$x:term] ]) => `(@id BExp $x)


namespace Playground
def B1 := [BExp| 4 <= 2 && ~3 == 4 + 3 && ~true]
def B2 := BExp.And (
    BExp.And (BExp.Le 4 2) (BExp.Not (BExp.Eq 3 ((4: AExp) + 3)))
  ) (BExp.Not .True)

example: B1 = B2 := by
  eq_refl

end Playground


abbrev State := TotalMap Nat
def State.empty: State := TotalMap.empty 0
def State.update: State -> String -> Nat -> State := TotalMap.update


def State.aeval (st: State) (a: AExp): Nat := match a with
  | .Num n => n
  | .Var x => st x
  | .Plus x1 x2 => st.aeval x1 + st.aeval x2
  | .Minus x1 x2 => st.aeval x1 - st.aeval x2
  | .Mult x1 x2 => st.aeval x1 * st.aeval x2


def State.beval (st: State) (b: BExp): Bool := match b with
  | .True => True
  | .False => False
  | .Eq a1 a2 => (st.aeval a1) == (st.aeval a2)
  | .Le a1 a2 => (st.aeval a1) <= (st.aeval a2)
  | .And b1 b2 => (st.beval b1) && (st.beval b2)
  | .Not b => (st.beval b).not


declare_syntax_cat lfp_state
syntax term: lfp_state
syntax "state![" "]": term
syntax "state![" lfp_state "]": term
syntax "_" "=>" term: lfp_state
syntax term "=>" term ";" lfp_state: lfp_state
syntax term "=>" term: lfp_state

macro_rules
  | `(state![ ]) =>`(State.empty)
  | `(state![ $m:term ]) =>`($m)
  | `(state![ _ => $v:term ]) => `(State.empty $v)
  | `(state![ $x:term => $v:term ; $m:lfp_state ]) => `(state![$m].update $x $v)
  | `(state![ $x:term => $v:term ]) => `(State.empty.update $x $v)


declare_syntax_cat lfp_imp
syntax lfp_aexp: lfp_imp
syntax lfp_bexp: lfp_imp
syntax "<{" lfp_imp "}>": term


macro_rules
  | `(<{ $x:lfp_aexp }>) => `([AExp| $x])
  | `(<{ $x:lfp_bexp }>) => `([BExp| $x])


namespace Playground
example: state![X => 5].aeval <{ 3 + (X * 2) }> = 13 := by
  eq_refl

example: state![X => 5; Y => 4].aeval <{ Z + (X * Y)}> = 20 := by
  eq_refl


example: state![X => 5].beval <{ true && ~(X <= 4) }> = .true := by
  eq_refl

end Playground


inductive Imp : Type where
  | Skip | Asgn (x: String) (a: AExp)
  | Seq (c1 c2: Imp) | If (b: BExp) (c1 c2: Imp)
  | While (b: BExp) (c: Imp)
  deriving Repr

syntax:100 "skip": lfp_imp
syntax:100 ident ":=" lfp_aexp:15 : lfp_imp
syntax:100 "[" term "]" ":=" lfp_aexp:15 : lfp_imp
syntax:10 lfp_imp ";" lfp_imp : lfp_imp
syntax:11 "if" lfp_bexp:5 "then" lfp_imp:5 "else" lfp_imp:5 "end": lfp_imp
syntax:11 "while" lfp_bexp:5 "do" lfp_imp:5 "end": lfp_imp
syntax:2 "[" term "]": lfp_imp


macro_rules
  | `(<{ skip }>) => `(Imp.Skip)
  | `(<{ $v:ident := $y:lfp_aexp }>) => `(Imp.Asgn $(Lean.quote (toString v.getId)) [AExp|$y])
  | `(<{ [$t] := $y:lfp_aexp }>) => `(Imp.Asgn $t [AExp|$y])
  | `(<{ $c1 ; $c2 }>) => `(Imp.Seq <{$c1}> <{$c2}>)
  | `(<{ if $b then $t else $f end }>) => `(Imp.If [BExp|$b] <{$t}> <{$f}>)
  | `(<{ while $b do $t end }>) => `(Imp.While [BExp|$b] <{$t}>)
  | `(<{ [$t] }>) => `($t)


namespace Playground

def fact_in_lean: Imp := <{
  Z := X;
  Y := 1;
  while (~Z == 0) do
    Y := Y * Z;
    Z := Z - 1
  end
}>


end Playground


def Imp.loop := <{
  while true do
    skip
  end
}>


def State.exec_no_while (st: State) (c: Imp): State :=
  match c with
  | .Skip => st
  | .Asgn x v => st.update x (st.aeval v)
  | .Seq c1 c2 => (st.exec_no_while c1).exec_no_while c2
  | .If b c1 c2 =>
    if st.beval b then st.exec_no_while c1 else st.exec_no_while c2
  | .While _ _ => st


inductive Imp.BigStep: Imp -> State -> State -> Prop where
  | BSkip {st: State}: Imp.Skip.BigStep st st
  | BAsgn {st: State} {a n x}:
    st.aeval a = n ->
    (Imp.Asgn x a).BigStep st state![x=> n; st]
  | BSeq {c1 c2: Imp} {st1 st2 st3: State}:
    c1.BigStep st1 st2 ->
    c2.BigStep st2 st3 ->
    (c1.Seq c2).BigStep st1 st3
  | BIfTrue {b c1 c2} {st1 st2: State}:
    st1.beval b = .true ->
    c1.BigStep st1 st2 ->
    (Imp.If b c1 c2).BigStep st1 st2
  | BIfFalse {b c1 c2} {st1 st2: State}:
    st1.beval b = .false ->
    c2.BigStep st1 st2 ->
    (Imp.If b c1 c2).BigStep st1 st2
  | BWhileFalse {b c} {st: State}:
    st.beval b = .false ->
    (Imp.While b c).BigStep st st
  | BWhileTrue {b c} {st1 st2 st3: State}:
    st1.beval b = .true ->
    c.BigStep st1 st2 ->
    (Imp.While b c).BigStep st2 st3 ->
    (Imp.While b c).BigStep st1 st3


macro s1:term:60 "=[" c:lfp_imp "]=>" s2:term:60 : term => `(Imp.BigStep <{$c}> $s1 $s2)


example: State.empty =[
  X := 2;
  if (X <= 1)then
    Y := 3
  else
    Z := 4
  end
]=> state!["Z" => 4; "X" => 2] := by
  apply Imp.BigStep.BSeq (st2 := state!["X" => 2])
  . apply Imp.BigStep.BAsgn
    eq_refl
  . apply Imp.BigStep.BIfFalse
    . eq_refl
    . apply Imp.BigStep.BAsgn
      eq_refl


theorem Imp.BigStep.deterministic {c} {st1 st2 st3: State}:
  st1 =[ [c] ]=> st2 ->
  st1 =[ [c] ]=> st3 ->
  st2 = st3 := by
    intros H12
    revert st3
    induction H12 with
    | BSkip =>
      intros st3 H13
      cases H13
      eq_refl
    | BAsgn E1 =>
      intros st3 H13
      cases H13 with
      | BAsgn E2 =>
        rewrite [E1] at E2
        subst E2
        eq_refl
    | @BSeq c1 c2 st1 s st2 E1 E2 IH1 IH2 =>
      intros st3 H13
      cases H13 with
      | @BSeq _ _ _ t _ H1t Ht3 =>
        specialize IH1 H1t
        apply IH2
        rewrite [IH1]
        apply Ht3
    | @BIfTrue b c1 c2 st1 st2 HT H12 IH =>
      intros st3 H13
      cases H13 with
      | BIfTrue _ H13 =>
        apply IH
        apply H13
      | BIfFalse E _ =>
        rewrite [E] at HT
        contradiction
    | @BIfFalse b c1 c2 st1 st2 HF H12 IH =>
      intros st3 H13
      cases H13 with
      | BIfTrue E _ =>
        rewrite [E] at HF
        contradiction
      | BIfFalse _ H13 =>
        apply IH
        apply H13
    | @BWhileFalse b c st HF=>
      intros st3 H13
      cases H13 with
      | BWhileFalse =>
        eq_refl
      | BWhileTrue HT =>
        rewrite [HF] at HT
        contradiction
    | @BWhileTrue b c st1 s st2 HT H12 H23 IH1 IH2 =>
      intros st3 H13
      cases H13 with
      | BWhileFalse HF =>
        rewrite [HF] at HT
        contradiction
      | @BWhileTrue _ _ _ t _ _ H1t Ht3  =>
        specialize IH1 H1t
        apply IH2
        rewrite [IH1]
        apply Ht3


theorem Imp.loop.never_stops {st1 st2: State}:
  Not (st1 =[ [loop] ]=> st2) := by
    generalize E: loop = t
    intros H
    induction H with
    | BSkip =>
      contradiction
    | BAsgn =>
      contradiction
    | BSeq =>
      contradiction
    | BIfTrue =>
      contradiction
    | BIfFalse =>
      contradiction
    | @BWhileFalse b c st HF =>
      cases E
      contradiction
    | @BWhileTrue b c st1 st2 st3 HT H12 H23 IH1 IH2 =>
      apply IH2
      apply E
