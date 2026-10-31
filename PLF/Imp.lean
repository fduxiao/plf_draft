import PLF.Map

@[grind]
inductive AExp: Type where
  | Num (n : Nat)
  | Var (x : String)
  | Plus (a1 a2 : AExp)
  | Minus (a1 a2 : AExp)
  | Mult (a1 a2 : AExp)
  deriving Repr


instance {n: Nat}: OfNat AExp n where
  ofNat := .Num n

instance: Coe Nat AExp where
  coe := .Num


instance: Coe String AExp where
  coe := .Var


instance: Add AExp where
  add := .Plus


instance: Sub AExp where
  sub := .Minus


instance: Mul AExp where
  mul := .Mult

section
open Lean PrettyPrinter

declare_syntax_cat lfp_aexp
syntax num : lfp_aexp
syntax ident: lfp_aexp
syntax str: lfp_aexp
syntax:50 lfp_aexp:50 " + " lfp_aexp:51 : lfp_aexp
syntax:50 lfp_aexp:50 " - " lfp_aexp:51 : lfp_aexp
syntax:60 lfp_aexp:60 " * " lfp_aexp:61 : lfp_aexp
syntax "(" lfp_aexp ")" : lfp_aexp
syntax "[" term "]" : lfp_aexp
syntax "[AExp| " lfp_aexp " ]" : term


macro_rules
  | `([AExp| $x:num]) => `(AExp.Num $x)
  | `([AExp| $x:ident]) => `(AExp.Var $(quote (toString x.getId)))
  | `([AExp| $x:str]) => `(AExp.Var $x)
  | `([AExp| $x:lfp_aexp + $y:lfp_aexp]) => `([AExp| $x].Plus [AExp| $y])
  | `([AExp| $x:lfp_aexp - $y:lfp_aexp]) => `([AExp| $x].Minus [AExp| $y])
  | `([AExp| $x:lfp_aexp * $y:lfp_aexp]) => `([AExp| $x].Mult [AExp| $y])
  | `([AExp| ($x:lfp_aexp)]) => `([AExp| $x])
  | `([AExp| [$x:term] ]) => `((($x): AExp))

@[app_unexpander AExp.Num]
def unexpanderAExpNum : Unexpander
  | `($_ $n:num) => `([AExp| $n:num ])
  | `($_ $n) => `([AExp| [$n] ])
  | _ => throw ()

@[app_unexpander AExp.Var]
def unexpanderAExpVar : Unexpander
  | `($_ $x:str) => do
    let i := mkIdent (Name.mkStr1 (x.getString))
    `([AExp| $i:ident ])
  | `($_ $x) => `([AExp| [$x] ])
  | _ => throw ()

def termToAExp: TSyntax `term → UnexpandM (TSyntax `lfp_aexp)
  | `([AExp| $x:lfp_aexp]) => pure x
  | `($t) => `(lfp_aexp| [ $t ] )

@[app_unexpander AExp.Plus]
def unexpanderAExpPlus : Unexpander
  | `($_ $x $y) => do
    let x ← termToAExp x
    let y ← termToAExp y
    `([AExp| $x + $y])
  | _ => throw ()

@[app_unexpander AExp.Minus]
def unexpanderAExpMinus : Unexpander
  | `($_ $x $y) => do
    let x ← termToAExp x
    let y ← termToAExp y
    `([AExp| $x - $y])
  | _ => throw ()

@[app_unexpander AExp.Mult]
def unexpanderAExpMult : Unexpander
  | `($_ $x $y) => do
    let x ← termToAExp x
    let y ← termToAExp y
    `([AExp| $x * $y])
  | _ => throw ()

end


namespace Playground

def W: String := "W"
def X: String := "X"
def Y: String := "Y"
def Z: String := "z"

def E1 := [AExp| [Z] - Z * 3 + 2 * T + W]
def E2 := [AExp| [E1] * [E1]]


example: E1 = [AExp| [Z] - Z * 3 + 2 * T + W] := by
  eq_refl

example: E1 = "z" - "Z" * 3 + 2 * "T" + W := by
  eq_refl


example: E2 = E1 * E1 := by
  eq_refl


end Playground

@[grind]
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

section
open Lean PrettyPrinter

declare_syntax_cat bool (behavior := symbol)
syntax "true": bool
syntax "false": bool

declare_syntax_cat lfp_bexp
syntax bool: lfp_bexp
syntax:30 lfp_aexp " == " lfp_aexp : lfp_bexp
syntax:30 lfp_aexp " <= " lfp_aexp : lfp_bexp
syntax:20 lfp_bexp:20 " && " lfp_bexp:21 : lfp_bexp
syntax:25 "~" lfp_bexp:25 : lfp_bexp
syntax "(" lfp_bexp ")" : lfp_bexp
syntax "[" term "]" : lfp_bexp
syntax ident : lfp_bexp
syntax "[BExp| " lfp_bexp " ]" : term


macro_rules
  | `([BExp| true ]) => `(BExp.True)
  | `([BExp| false ]) => `(BExp.False)
  | `([BExp| $x:lfp_aexp == $y:lfp_aexp]) => `(BExp.Eq [AExp|$x] [AExp|$y])
  | `([BExp| $x:lfp_aexp <= $y:lfp_aexp]) => `(BExp.Le [AExp|$x] [AExp|$y])
  | `([BExp| $x:lfp_bexp && $y:lfp_bexp]) => `(BExp.And [BExp|$x] [BExp|$y])
  | `([BExp| ~ $x:lfp_bexp]) => `(BExp.Not [BExp|$x])
  | `([BExp| ($x:lfp_bexp)]) => `([BExp| $x])
  | `([BExp| [$x:term] ]) => `((($x): BExp))
  | `([BExp| $x:ident ]) => `((($x): BExp))

@[app_unexpander BExp.True]
def unexpanderBExpTrue : Unexpander
  | `($_) => do
    let b ← `(bool| true)
    `([BExp| $b:bool ])

@[app_unexpander BExp.False]
def unexpanderBExpFalse : Unexpander
  | `($_) => do
    let b ← `(bool| false)
    `([BExp| $b:bool ])

def termToBExp : TSyntax `term → UnexpandM (TSyntax `lfp_bexp)
  | `([BExp| $x]) => pure x
  | `($t:ident) => `(lfp_bexp| $t:ident )
  | `($t) => `(lfp_bexp| [$t])

@[app_unexpander BExp.Eq]
def unexpanderBExpEq : Unexpander
  | `($_ $x $y) => do
    let x ← termToAExp x
    let y ← termToAExp y
    `([BExp| $x:lfp_aexp == $y:lfp_aexp])
  | _ => throw ()

@[app_unexpander BExp.Le]
def unexpanderBExpLe : Unexpander
  | `($_ $x $y) => do
    let x ← termToAExp x
    let y ← termToAExp y
    `([BExp| $x:lfp_aexp <= $y:lfp_aexp])
  | _ => throw ()

@[app_unexpander BExp.Not]
def unexpanderBExpNot : Unexpander
  | `($_ $b) => do
    let b ← termToBExp b
    `([BExp| ~ $b:lfp_bexp])
  | _ => throw ()

@[app_unexpander BExp.And]
def unexpanderBExpAnd : Unexpander
  | `($_ $b1 $b2) => do
    let b1 ← termToBExp b1
    let b2 ← termToBExp b2
    `([BExp| $b1:lfp_bexp && $b2:lfp_bexp])
  | _ => throw ()

end
namespace Playground
def B1 := [BExp| 4 <= 2 && ~3 == 4 + 3 && ~true]
def B2 := BExp.And (
    BExp.And (BExp.Le 4 2) (BExp.Not (BExp.Eq 3 ((4: AExp) + 3)))
  ) (BExp.Not .True)

example: B1 = B2 := by
  eq_refl

example: B1 = [BExp| 4 <= 2 && ~3 == 4 + 3 && ~true] := by
  eq_refl

example: BExp.And B1 B2 = [BExp| B1 && B2] := by
  eq_refl

end Playground


@[grind]
abbrev State := TotalMap Nat
@[simp] def State.empty: State := TotalMap.empty 0
@[simp] def State.update: State → String → Nat → State := TotalMap.update


@[simp, grind]
def State.aeval (st: State) (a: AExp): Nat := match a with
  | .Num n => n
  | .Var x => st x
  | .Plus x1 x2 => st.aeval x1 + st.aeval x2
  | .Minus x1 x2 => st.aeval x1 - st.aeval x2
  | .Mult x1 x2 => st.aeval x1 * st.aeval x2


@[simp, grind]
def State.beval (st: State) (b: BExp): Bool := match b with
  | .True => True
  | .False => False
  | .Eq a1 a2 => (st.aeval a1).beq  (st.aeval a2)
  | .Le a1 a2 => (st.aeval a1).ble (st.aeval a2)
  | .And b1 b2 => (st.beval b1) && (st.beval b2)
  | .Not b => (st.beval b).not

section
open Lean PrettyPrinter

declare_syntax_cat lfp_state
syntax term: lfp_state
syntax "state![" "]": term
syntax "state![" lfp_state "]": term
syntax "_" " => " term: lfp_state
syntax term " => " term "; " lfp_state: lfp_state
syntax term " => " term: lfp_state

macro_rules
  | `(state![ ]) =>`(State.empty)
  | `(state![ $m:term ]) =>`($m)
  | `(state![ _ => $v:term ]) => `(State.empty $v)
  | `(state![ $x:term => $v:term ; $m:lfp_state ]) => `(state![$m].update $x $v)
  | `(state![ $x:term => $v:term ]) => `(State.empty.update $x $v)

@[app_unexpander State.empty]
def unexpanderStateEmpty : Unexpander
  | `($_) => `(state![])

@[app_unexpander State.update]
def unexpanderStateUpdate : Unexpander
  | `($_ state![] $x $v) => `(state![ $x:term => $v:term ])
  | `($_ state![ $st:lfp_state ] $x $v) => `(state![ $x:term => $v:term; $st:lfp_state ])
  | `($_ $st:term $x $v) =>
    `(state![ $x:term => $v:term; $st:term ])
  | _ => throw ()

declare_syntax_cat lfp_imp
syntax "A|" lfp_aexp: lfp_imp
syntax "B|" lfp_bexp: lfp_imp
syntax "<{" lfp_imp "}>": term


macro_rules
  | `(<{A| $x:lfp_aexp }>) => `([AExp| $x])
  | `(<{B| $x:lfp_bexp }>) => `([BExp| $x])

end

namespace Playground
example: state![X => 5].aeval <{A| 3 + (X * 2) }> = 13 := by
  eq_refl

example: state![X => 5; Y => 4; Z => 3].aeval <{A| Z + (X * Y)}> = 20 := by
  eq_refl


example: state![X => 5].beval <{B| true && ~(X <= 4) }> = true := by
  eq_refl

end Playground

@[grind]
inductive Imp : Type where
  | Skip | Asgn (x: String) (a: AExp)
  | Seq (c1 c2: Imp) | If (b: BExp) (c1 c2: Imp)
  | While (b: BExp) (c: Imp)
  deriving Repr

section
open Lean PrettyPrinter

syntax:100 "skip": lfp_imp
syntax:100 ident " := " lfp_aexp:15 : lfp_imp
syntax:100 "[" term "]" " := " lfp_aexp:15 : lfp_imp
syntax:100 "(" lfp_imp ")" : lfp_imp
syntax:10 lfp_imp "; " ppDedent(ppLine lfp_imp) : lfp_imp
syntax:11
  ppGroup("if " lfp_bexp:5 " then")
    ppGroup(ppSpace lfp_imp:5)
  ppDedent(ppSpace"else ")
    ppGroup(ppSpace lfp_imp:5)
  ppDedent(ppSpace "end"): lfp_imp
syntax:11
  ppGroup("while " lfp_bexp:5 " do")
    ppGroup(ppSpace lfp_imp:5)
  ppDedent(ppSpace "end"): lfp_imp
syntax term: lfp_imp

macro_rules
  | `(<{ skip }>) => `(Imp.Skip)
  | `(<{ $v:ident := $y:lfp_aexp }>) => `(Imp.Asgn $(Lean.quote (toString v.getId)) [AExp|$y])
  | `(<{ [$t] := $y:lfp_aexp }>) => `(Imp.Asgn $t [AExp|$y])
  | `(<{ ( $x:lfp_imp ) }>) => `(<{ $x }>)
  | `(<{ $c1 ; $c2 }>) => `(Imp.Seq <{$c1}> <{$c2}>)
  | `(<{ if $b then $t else $f end }>) => `(Imp.If [BExp|$b] <{$t}> <{$f}>)
  | `(<{ while $b do $t end }>) => `(Imp.While [BExp|$b] <{$t}>)
  | `(<{ $t:term }>) => `($t)

def termToImp: TSyntax `term → UnexpandM (TSyntax `lfp_imp)
  | `(<{$x:lfp_imp}>) => pure x
  | `($t) => `(lfp_imp| [$t])

@[app_unexpander Imp.Skip]
def unexpanderSkip : Unexpander
  | `($_) => `(<{ skip }>)

@[app_unexpander Imp.Asgn]
def unexpanderAsgn : Unexpander
  | `($_ $x $a) => do
    let a ← termToAExp a
    match x with
    | `($x:str) =>
      let i := mkIdent (Name.mkStr1 x.getString)
      `(<{ $i:ident := $a }>)
    | _ => `(<{ [$x] := $a }>)
  | _ => throw ()

@[app_unexpander Imp.Seq]
def unexpanderSeq : Unexpander
  | `($_ $c1 $c2) => do
    let c1 ← termToImp c1
    let c2 ← termToImp c2
    `(<{ $c1:lfp_imp; $c2:lfp_imp }>)
  | _ => throw ()

@[app_unexpander Imp.If]
def unexpanderIf : Unexpander
  | `($_ $b $t $f) => do
    let b ← termToBExp b
    let t ← termToImp t
    let f ← termToImp f
    `(<{ if $b:lfp_bexp then $t:lfp_imp else $f:lfp_imp end }>)
  | _ => throw ()

@[app_unexpander Imp.While]
def unexpanderWhile : Unexpander
  | `($_ $b $c) => do
    let b ← termToBExp b
    let c ← termToImp c
    `(<{ while $b:lfp_bexp do $c:lfp_imp end }>)
  | _ => throw ()

end

namespace Playground

def fact_in_lean: Imp := <{
  Z := X;
  Y := 1;
  while (~Z == 0) do
    Y := Y * Z;
    Z := Z - 1
  end
}>

example: fact_in_lean = <{
    Z := X;
    Y := 1;
    while (~Z == 0) do
      Y := Y * Z;
      Z := Z - 1
    end
  }>
:= by
  rfl


end Playground


def Imp.loop := <{
  while true do
    skip
  end
}>


@[grind]
def State.exec_no_while (st: State) (c: Imp): State :=
  match c with
  | .Skip => st
  | .Asgn x v => st.update x (st.aeval v)
  | .Seq c1 c2 => (st.exec_no_while c1).exec_no_while c2
  | .If b c1 c2 =>
    if st.beval b then st.exec_no_while c1 else st.exec_no_while c2
  | .While _ _ => st

@[grind]
inductive Imp.BigStep: Imp → State → State → Prop where
  | Skip {st: State}: Imp.Skip.BigStep st st
  | Asgn {st: State} {a n x}:
    st.aeval a = n →
    (Imp.Asgn x a).BigStep st state![x=> n; st]
  | Seq {c1 c2: Imp} {st1 st2 st3: State}:
    c1.BigStep st1 st2 →
    c2.BigStep st2 st3 →
    (c1.Seq c2).BigStep st1 st3
  | IfTrue {b c1 c2} {st1 st2: State}:
    st1.beval b = .true →
    c1.BigStep st1 st2 →
    (Imp.If b c1 c2).BigStep st1 st2
  | IfFalse {b c1 c2} {st1 st2: State}:
    st1.beval b = .false →
    c2.BigStep st1 st2 →
    (Imp.If b c1 c2).BigStep st1 st2
  | WhileFalse {b c} {st: State}:
    st.beval b = .false →
    (Imp.While b c).BigStep st st
  | WhileTrue {b c} {st1 st2 st3: State}:
    st1.beval b = .true →
    c.BigStep st1 st2 →
    (Imp.While b c).BigStep st2 st3 →
    (Imp.While b c).BigStep st1 st3


section

syntax term:60 " =["
  ppDedent(
    ppIndent(ppSpace lfp_imp)
    ppDedent(ppSpace "]=> ")
  ) term:60 : term

macro_rules
  | `($s1 =[ $c ]=> $s2) => `(Imp.BigStep <{$c}> $s1 $s2)

open Lean PrettyPrinter

@[app_unexpander Imp.BigStep]
def unexpanderBigStep : Unexpander
  | `($_ $c $st1 $st2) => do
    let c ← termToImp c
    `($st1 =[ $c ]=> $st2)
  | _ => throw ()

end

example: State.empty =[
  X := 2;
  if (X <= 1)then
    Y := 3
  else
    Z := 4
  end
]=> state!["Z" => 4; "X" => 2] := by
  apply Imp.BigStep.Seq (st2 := state!["X" => 2])
  . apply Imp.BigStep.Asgn
    eq_refl
  . apply Imp.BigStep.IfFalse
    . eq_refl
    . apply Imp.BigStep.Asgn
      eq_refl

@[grind .]
theorem Imp.BigStep.deterministic {c} {st1 st2 st3: State}:
  st1 =[ c ]=> st2 →
  st1 =[ c ]=> st3 →
  st2 = st3
:= by
  intros H12
  revert st3
  induction H12
  case Skip =>
    intros st3 H13
    cases H13
    eq_refl
  case Asgn E1 =>
    intros st3 H13
    cases H13
    case Asgn E2 =>
      rewrite [E1] at E2
      subst E2
      eq_refl
  case Seq c1 c2 st1 s st2 E1 E2 IH1 IH2 =>
    intros st3 H13
    cases H13
    case Seq H1t Ht3 =>
      specialize IH1 H1t
      apply IH2
      rewrite [IH1]
      apply Ht3
  case IfTrue b c1 c2 st1 st2 HT H12 IH =>
    intros st3 H13
    cases H13
    case IfTrue _ H13 =>
      apply IH
      apply H13
    case IfFalse E _ =>
      rewrite [E] at HT
      contradiction
  case IfFalse b c1 c2 st1 st2 HF H12 IH =>
    intros st3 H13
    cases H13
    case IfTrue E _ =>
      rewrite [E] at HF
      contradiction
    case IfFalse _ H13 =>
      apply IH
      apply H13
  case WhileFalse b c st HF =>
    intros st3 H13
    cases H13
    case WhileFalse =>
      eq_refl
    case WhileTrue HT _ _ =>
      rewrite [HF] at HT
      contradiction
  case WhileTrue b c st1 s st2 HT H12 H23 IH1 IH2 =>
    intros st3 H13
    cases H13
    case WhileFalse HF =>
      rewrite [HF] at HT
      contradiction
    case WhileTrue H1t Ht3  =>
      specialize IH1 H1t
      apply IH2
      rewrite [IH1]
      apply Ht3


theorem Imp.loop.never_stops {st1 st2: State}:
  Not (st1 =[ loop ]=> st2)
:= by
  generalize E: loop = t
  intros H
  induction H
  case Skip =>
    contradiction
  case Asgn =>
    contradiction
  case Seq =>
    contradiction
  case IfTrue =>
    contradiction
  case IfFalse =>
    contradiction
  case WhileFalse b c st HF =>
    cases E
    contradiction
  case WhileTrue b c st1 st2 st3 HT H12 H23 IH1 IH2 =>
    apply IH2
    apply E


section StackCalculator

inductive SInstr : Type where
  | SPush (n: Nat)
  | SLoad (x: String)
  | SPlus
  | SMinus
  | SMult
  deriving Repr


@[simp]
def State.s_execute (st: State) (stack: List Nat) (prog: List SInstr)
  : List Nat := match prog with
  | .nil => stack
  | .cons x xs =>
    match x with
    | .SPush n => st.s_execute (n :: stack) xs
    | .SLoad s => st.s_execute (st s :: stack) xs
    | .SPlus => match stack with
      | [] | [_] => st.s_execute stack xs
      | y1 :: y2 :: ys => st.s_execute ((y2 + y1) :: ys) xs
    | .SMinus => match stack with
      | [] | [_] => st.s_execute stack xs
      | y1 :: y2 :: ys => st.s_execute ((y2 - y1) :: ys) xs
    | .SMult => match stack with
      | [] | [_] => st.s_execute stack xs
      | y1 :: y2 :: ys => st.s_execute ((y2 * y1) :: ys) xs


example: State.empty.s_execute []
  [.SPush 5, .SPush 3, .SPush 1, .SMinus] = [2, 5]
:= by
  eq_refl

example: state!["X" => 3].s_execute
  [3, 4]
  [.SPush 4, .SLoad "X", .SMult, .SPlus]
  = [15, 4]
:= by
  eq_refl

@[simp]
def AExp.s_compile (e : AExp) : List SInstr :=
  match e with
  | .Num n => [.SPush n]
  | .Var s => [.SLoad s]
  | .Plus e1 e2 => e1.s_compile ++ e2.s_compile ++ [.SPlus]
  | .Minus e1 e2 => e1.s_compile ++ e2.s_compile ++ [.SMinus]
  | .Mult e1 e2 => e1.s_compile ++ e2.s_compile ++ [.SMult]


example: <{A| X - (2 * Y) }>.s_compile
  = [.SLoad "X", .SPush 2, .SLoad "Y", .SMult, .SMinus]
:= by
  eq_refl


theorem List.cases2 {A} {motive: List A → Prop}:
  (motive []) →
  (forall x, motive [x]) →
  (forall x1 x2 xs, motive $ x1 :: x2 :: xs) →
  forall {l}, motive l
:= by
    intros H0 H1 H2
    intros l
    cases l with
    | nil =>  exact H0
    | cons x1 xs =>
      cases xs with
      | nil =>
        apply H1
      | cons x2 xs =>
        apply H2


theorem AExp.execute_app {st: State} {p1 p2 stack}:
  st.s_execute stack (p1 ++ p2)
  = st.s_execute (st.s_execute stack p1) p2
:= by
  induction p1 generalizing stack
  case nil =>
    simp
  case cons x xs IHxs =>
    cases x with
    | SPush n | SLoad =>
      simp
      apply IHxs
    | SPlus | SMinus | SMult =>
      apply stack.cases2 <;> simp <;> intros <;> apply IHxs


theorem AExp.s_compile.correct_aux {st: State} {e stack}:
  st.s_execute stack e.s_compile = st.aeval e :: stack
:= by
  induction e generalizing stack
  case Num n | Var s =>
    simp [State.aeval]
  case Plus n1 n2 IH1 IH2 | Minus n1 n2 IH1 IH2 | Mult n1 n2 IH1 IH2 =>
    simp [State.aeval]
    rewrite [AExp.execute_app]
    rewrite [AExp.execute_app]
    rewrite [IH1]
    rewrite [IH2]
    simp


theorem AExp.s_compile.correct {st: State} e:
  st.s_execute [] e.s_compile = [ st.aeval e ]
:= AExp.s_compile.correct_aux (stack := [])


end StackCalculator
