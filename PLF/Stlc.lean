import PLF.SmallStep
import PLF.Relation

namespace STLC

inductive Ty : Type where
  | Bool : Ty
  | To : Ty -> Ty -> Ty
  deriving Repr


inductive Tm : Type where
  | Var: String -> Tm
  | App: Tm -> Tm -> Tm
  | Abs: String -> Ty -> Tm -> Tm
  | True: Tm
  | False: Tm
  | If: Tm -> Tm -> Tm -> Tm


instance: Coe String Tm where
  coe := Tm.Var


declare_syntax_cat plf_stlc_ty (behavior := symbol)

syntax "[ty|" plf_stlc_ty "]": term
syntax:100 "(" plf_stlc_ty ")": plf_stlc_ty
syntax:1 plf_stlc_ty "->" plf_stlc_ty : plf_stlc_ty
syntax:100 "[" term "]": plf_stlc_ty
syntax "Bool": plf_stlc_ty

macro_rules
  | `([ty| ($t:plf_stlc_ty) ]) => `([ty| $t ])
  | `([ty| $s -> $t ]) => `(Ty.To [ty| $s ] [ty| $t ])
  | `([ty| [ $t ] ]) => `($t)
  | `([ty| Bool ]) => `(Ty.Bool)


declare_syntax_cat plf_stlc_tm (behavior := symbol)
syntax "[tm|" plf_stlc_tm "]": term
syntax:100 "(" plf_stlc_tm ")": plf_stlc_tm
syntax "[" term "]": plf_stlc_tm
syntax:11 "if" plf_stlc_tm:5 "then" plf_stlc_tm:5 "else" plf_stlc_tm:5: plf_stlc_tm
syntax "true": plf_stlc_tm
syntax "false": plf_stlc_tm
syntax:90 plf_stlc_tm:90 plf_stlc_tm:91 : plf_stlc_tm
syntax ident: plf_stlc_tm
syntax:0 "λ" ident ":" plf_stlc_ty "," plf_stlc_tm: plf_stlc_tm
syntax:0 "λ" "[" term "]" ":" plf_stlc_ty "," plf_stlc_tm: plf_stlc_tm

macro_rules
  | `([tm| if $c:plf_stlc_tm then $t else $f ]) => `(Tm.If [tm| $c ] [tm| $t ] [tm| $f ])
  | `([tm| [ $t ] ]) => `((($t): Tm))
  | `([tm| ($t:plf_stlc_tm) ]) => `([tm| $t ])
  | `([tm| true ]) => `(Tm.True)
  | `([tm| false ]) => `(Tm.False)
  | `([tm| $x $y ]) => `(Tm.App [tm| $x ] [tm| $y ])
  | `([tm| $x:ident ]) => `(Tm.Var $(Lean.quote (toString x.getId)))
  | `([tm| λ $x : $t, $b ]) => `(Tm.Abs $(Lean.quote (toString x.getId)) [ty| $t ] [tm| $b ])
  | `([tm| λ [$x]: $t, $b ]) => `(Tm.Abs $x [ty| $t ] [tm| $b ])

example: [tm| x y z] = ((Tm.Var "x").App (Tm.Var "y")).App (Tm.Var "z")
:= by eq_refl

example: [tm| λ ["x"]: Bool, ["x"] ] = Tm.Abs "x" Ty.Bool (Tm.Var "x") := by eq_refl
example: [tm| λ x: Bool, λ y: Bool -> Bool, x y ] = Tm.Abs "x" Ty.Bool (
  Tm.Abs "y" (Ty.Bool.To Ty.Bool) (
    (Tm.Var "x").App (Tm.Var "y")
  )
)
:= by
  eq_refl


example: [tm| if true then y else x] = Tm.True.If (Tm.Var "y") (Tm.Var "x")
:= by eq_refl


inductive Tm.value: Tm -> Prop where
  | Abs {x t b}: (Tm.Abs x t b).value
  | True: Tm.True.value
  | False: Tm.False.value


@[simp]
def Tm.subst (x: String) (s: Tm) (t: Tm): Tm :=
  match t with
  | .Var y => if x = y then s else t
  | .Abs y T b => if x = y then t else .Abs y T (subst x s b)
  | .App p q => .App (subst x s p) (subst x s q)
  | .True => .True
  | .False => .False
  | .If c y n => .If (subst x s c) (subst x s y) (subst x s n)

notation "[" x ":=" s "]" => (Tm.subst x s)


inductive Tm.step: Tm -> Tm -> Prop where
  | AppAbs {x T b} {v: Tm}: v.value -> ((Tm.Abs x T b).App v).step ([x := v] b)
  | App1 {f1 f2 x: Tm}: f1.step f2 -> (f1.App x).step (f2.App x)
  | App2 {f x1 x2: Tm}: x1.step x2 -> (f.App x1).step (f.App x2)
  | IfTrue {t f: Tm}: (Tm.If .True t f).step t
  | IfFalse {t f: Tm}: (Tm.If .False t f).step f
  | If {c1 c2 t f: Tm}: c1.step c2 -> (Tm.If c1 t f).step (Tm.If c2 t f)


abbrev Tm.multistep := RTCl (Tm.step)
abbrev Tm.step_normal := Relation.Normal Tm.step

@[simp]
def idB := [tm| λ x: Bool, x]
@[simp]
def idBB := [tm| λ x: Bool -> Bool, x]

example: [tm| [idBB] [idB] ].multistep idB := by
  apply RTCl.step
  . unfold idBB
    apply Tm.step.AppAbs
    apply Tm.value.Abs
  . simp
    apply RTCl.refl


abbrev Context := PartialMap Ty
abbrev Context.empty: Context := PartialMap.empty

declare_syntax_cat plf_stlc_context (behavior := symbol)
syntax "∅": lfp_aexp
syntax term: plf_stlc_context
syntax ident ":" plf_stlc_ty: plf_stlc_context
syntax "[" term "]" ":" plf_stlc_ty: plf_stlc_context
syntax plf_stlc_context "," plf_stlc_context: plf_stlc_context
syntax "[ctx|" plf_stlc_context "]": term

macro_rules
  | `([ctx| ∅ ]) => `(Context.empty)
  | `([ctx| $t:term ]) => `($t)
  | `([ctx| $x:ident : $T]) => `(
    PartialMap.update .empty $(Lean.quote (toString x.getId)) [ty| $T ]
  )
  | `([ctx| [$x] : $T]) => `(PartialMap.update .empty $x [ty| $T])
  | `([ctx| $c1, $c2 ]) => `(PartialMap.merge [ctx| $c1] [ctx| $c2])


example: [ctx| x: Bool ] = PartialMap.empty.update "x" Ty.Bool := by eq_refl
example: [ctx| x: [Ty.Bool] ] = PartialMap.empty.update "x" Ty.Bool := by eq_refl
example: [ctx| ∅] = Context.empty := by eq_refl
example: [ctx| f: Bool -> Bool, x: Bool] = (
  PartialMap.empty.update "f" (Ty.Bool.To Ty.Bool)).merge
    (PartialMap.empty.update "x" Ty.Bool
)
:= by
  eq_refl


inductive Tm.has_type: Context -> Tm -> Ty -> Prop where
  | Var {Gamma: Context} {x T}:
    Gamma x = Option.some T ->
    Tm.has_type Gamma x T
  | Abs {Gamma: Context} {x b} {A B: Ty}:
    Tm.has_type map![ x => A; Gamma] b B ->
    Tm.has_type Gamma (.Abs x A b) (.To A B)
  | App {Gamma: Context} {f x} {A B}:
    Tm.has_type Gamma f (.To A B) ->
    Tm.has_type Gamma x A ->
    Tm.has_type Gamma (.App f x) B
  | True {Gamma}: Tm.has_type Gamma .True .Bool
  | False {Gamma}: Tm.has_type Gamma .False .Bool
  | If {Gamma c t f} {A: Ty}:
    Tm.has_type Gamma c .Bool ->
    Tm.has_type Gamma t A ->
    Tm.has_type Gamma f A ->
    Tm.has_type Gamma (.If c t f) A


def Tm.has_type.type {c t T} (_: Tm.has_type c t T) := T


macro "ty{" C:plf_stlc_context "|-" t:plf_stlc_tm ":" T:plf_stlc_ty "}": term
  => `(Tm.has_type [ctx| $C ] [tm|$t] [ty| $T])

example: ty{ y: Bool |- λ x: Bool, y : Bool -> Bool } =
  Tm.has_type
    (PartialMap.empty.update "y" Ty.Bool)
    (Tm.Abs "x" Ty.Bool (Tm.Var "y"))
    (Ty.Bool.To Ty.Bool)
:= by
  eq_refl

example: ty{ ∅ |- λ x: Bool, x: Bool -> Bool} := by
  repeat constructor

example: ty{ ∅ |-
  λ x: Bool,
  λ y: Bool -> Bool,
    y (y x): Bool -> (Bool -> Bool) -> Bool
} := by
  repeat constructor

example: ¬ exists T, ty{ ∅ |- λ x: Bool, λ y: Bool, x y: [T]} := by
  intros contra
  let ⟨T, t⟩ := contra
  cases t with | Abs t =>
  cases t with | Abs t =>
  cases t with | App tx ty =>
  cases tx with | Var ctx =>
  simp at ctx

example: ¬ exists S T, ty{ ∅ |- λ x: [S], x x : [T] } := by
  intros contra
  let ⟨S, ⟨T, t⟩⟩ := contra
  cases t with | Abs t =>
  cases t with | App f x =>
  cases x with | Var Hx =>
  simp at Hx
  cases f with | Var Hf =>
  simp at Hf
  subst_eqs

end STLC


namespace STLC

-- a more delicated head normal form
mutual
  -- normal form by elimination
  inductive Tm.normal_form_elim: Tm -> Prop where
    | Var {s}: (Tm.Var s).normal_form_elim
    | App {x y}: x.normal_form_elim -> y.normal_form -> (Tm.App x y).normal_form_elim
    | If {c t f: Tm}: c.normal_form_elim -> t.normal_form -> f.normal_form -> (Tm.If c t f).normal_form_elim

  -- normal forms by constructors
  inductive Tm.normal_form: Tm -> Prop where
    | True: Tm.True.normal_form
    | False: Tm.False.normal_form
    | Abs {x t} {b: Tm}: b.normal_form -> (Tm.Abs x t b).normal_form
    | Elim (t: Tm): t.normal_form_elim -> t.normal_form
end

end STLC
