import PLF.Map


def State := TotalMap Nat

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
  | `([AExp| $x:ident]) => `(@id AExp $x)
  | `([AExp| $x:str]) => `(AExp.Var $x)
  | `([AExp| $x:lfp_aexp + $y:lfp_aexp]) => `([AExp| $x].Plus [AExp| $y])
  | `([AExp| $x:lfp_aexp - $y:lfp_aexp]) => `([AExp| $x].Minus [AExp| $y])
  | `([AExp| $x:lfp_aexp * $y:lfp_aexp]) => `([AExp| $x].Mult [AExp| $y])
  | `([AExp| ($x:lfp_aexp)]) => `([AExp| $x])
  | `([AExp| [$x:term] ]) => `($x)


namespace Playground

def W: AExp := "W"
def X: AExp := "X"
def Y: AExp := "Y"
def Z: String := "z"

def E1 := [AExp| Z * 3 + 2 * "Z" + W]
def E2 := [AExp| E1 * E1]


example: E1 = Z * 3 + 2 * "Z" + W := by
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
syntax lfp_aexp "==" lfp_aexp : lfp_bexp
syntax lfp_aexp "<=" lfp_aexp : lfp_bexp
syntax:50 lfp_bexp:50 "&&" lfp_bexp:51 : lfp_bexp
syntax:60 "~" lfp_bexp:60 : lfp_bexp
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
  | `([BExp| [$x:term] ]) => `($x)


namespace Playground
def B1 := [BExp| 4 <= 2 && ~3 == 4 + 3 && ~true]
def B2 := BExp.And (
    BExp.And (BExp.Le 4 2) (BExp.Not (BExp.Eq 3 ((4: AExp) + 3)))
  ) (BExp.Not .True)

example: B1 = B2 := by
  eq_refl

end Playground
