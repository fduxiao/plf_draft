import Lean.Meta
import PLF.Map
import PLF.Relation
import PLF.SyntaxCat

namespace Normalize

inductive Ty where
  | Bool | Arrow: Ty -> Ty -> Ty | Prod: Ty -> Ty -> Ty


abbrev Var := String


inductive Tm where
  | var: Var -> Tm
  | app: Tm -> Tm -> Tm
  | abs: Var -> Ty -> Tm -> Tm
  | true | false | ite: Tm -> Tm -> Tm -> Tm
  | pair: Tm -> Tm -> Tm
  | fst: Tm -> Tm
  | snd: Tm -> Tm


instance: Coe Var Tm where
  coe := .var


-- syntax
-- type
declare_syntax_cat plf_stlc_norm_ty (behavior := symbol)

scoped syntax "[ty| " plf_stlc_norm_ty " ]": term
scoped syntax:100 "(" plf_stlc_norm_ty ")": plf_stlc_norm_ty
scoped syntax:1 plf_stlc_norm_ty:1 " -> " plf_stlc_norm_ty:1 : plf_stlc_norm_ty
scoped syntax:0 plf_stlc_norm_ty " * " plf_stlc_norm_ty : plf_stlc_norm_ty
scoped syntax:100 "[" term "]": plf_stlc_norm_ty
scoped syntax "Bool": plf_stlc_norm_ty

scoped macro_rules
  | `([ty| ($t:plf_stlc_norm_ty) ]) => `([ty| $t ])
  | `([ty| $s -> $t ]) => `(Ty.Arrow [ty| $s ] [ty| $t ])
  | `([ty| [ $t ] ]) => `($t)
  | `([ty| Bool ]) => `(Ty.Bool)
  | `([ty| $x * $y ]) => `(Ty.Prod [ty| $x ] [ty| $y ])

-- pretty print
@[app_unexpander Ty.Bool]
def unexpandBool: Lean.PrettyPrinter.Unexpander
  | `($_) => `([ty| Bool ])


@[app_unexpander Ty.Arrow]
def unexpandArrow: Lean.PrettyPrinter.Unexpander
  | `($_ [ty| $a1 -> $a2] [ty|$b]) => `([ty| ($a1 -> $a2) -> $b ])
  | `($_ [ty| $a1 * $a2] [ty|$b]) => `([ty| ($a1 * $a2) -> $b ])
  | `($_ [ty|$a] $b) =>
    match b with
    | `([ty| $b1 * $b2 ]) => `([ty| $a -> ($b1 * $b2) ])
    | `([ty| $b ]) => `([ty| $a -> $b ])
    | _ => `([ty| $a -> [$b] ])
  | _ => throw ()

@[app_unexpander Ty.Prod]
def unexpandProd: Lean.PrettyPrinter.Unexpander
  | `($_ [ty| $a] [ty| $b1 -> $b2]) => `([ty| $a * ($b1 -> $b2) ])
  | `($_ [ty| $a] [ty| $b]) => `([ty| $a * $b ])
  | `($_ [ty| $a1 -> $a2 ] [ty| $b]) => `([ty| ($a1 -> $a2) * $b ])
  | _ => throw ()


-- term
declare_syntax_cat plf_stlc_norm_tm (behavior := symbol)
-- interpret the syntax
scoped syntax "[tm| " plf_stlc_norm_tm " ]": term
-- priority
scoped syntax:100 "(" plf_stlc_norm_tm ")": plf_stlc_norm_tm
-- meta expression
scoped syntax "[" term "]": plf_stlc_norm_tm
-- λ-calculus
-- variable
scoped syntax ident: plf_stlc_norm_tm
-- application
scoped syntax:90 plf_stlc_norm_tm:90 plf_stlc_norm_tm:91 : plf_stlc_norm_tm
-- abstraction
scoped syntax:0 "λ" ident " : " plf_stlc_norm_ty ", " plf_stlc_norm_tm: plf_stlc_norm_tm
scoped syntax:0 "λ" "[" term "]" " : " plf_stlc_norm_ty ", " plf_stlc_norm_tm: plf_stlc_norm_tm

-- boolean
scoped syntax "true": plf_stlc_norm_tm
scoped syntax "false": plf_stlc_norm_tm
scoped syntax:11 "if" plf_stlc_norm_tm:5 "then" plf_stlc_norm_tm:5 "else" plf_stlc_norm_tm:5: plf_stlc_norm_tm

-- prod
scoped syntax:20 "(" plf_stlc_norm_tm ", " plf_stlc_norm_tm ")": plf_stlc_norm_tm
scoped syntax:90 "fst " plf_stlc_norm_tm: plf_stlc_norm_tm
scoped syntax:90 "snd " plf_stlc_norm_tm: plf_stlc_norm_tm


scoped macro_rules
  -- priority and meta variables
  | `([tm| ($t:plf_stlc_norm_tm) ]) => `([tm| $t ])
  | `([tm| [ $t ] ]) => `((($t): Tm))
  -- λ-calculus
  | `([tm| $x:ident ]) => `(Tm.var $(Lean.quote (toString x.getId)))
  | `([tm| $x $y ]) => `(Tm.app [tm| $x ] [tm| $y ])
  | `([tm| λ $x : $t, $b ]) => `(Tm.abs $(Lean.quote (toString x.getId)) [ty| $t ] [tm| $b ])
  | `([tm| λ [$x]: $t, $b ]) => `(Tm.abs $x [ty| $t ] [tm| $b ])
  -- bool
  | `([tm| true ]) => `(Tm.true)
  | `([tm| false ]) => `(Tm.false)
  | `([tm| if $c then $t else $f ]) => `(Tm.ite [tm| $c ] [tm| $t ] [tm| $f ])
  -- prod
  | `([tm| fst $x ]) => `(Tm.fst [tm| $x ])
  | `([tm| snd $x ]) => `(Tm.snd [tm| $x ])
  | `([tm| ($x, $y) ]) => `(Tm.pair [tm| $x] [tm| $y])

-- pretty print
instance : Coe Lean.NumLit (Lean.TSyntax `plf_stlc_ref_tm) where
  coe s := ⟨s.raw⟩

instance : Coe Lean.Ident (Lean.TSyntax `plf_stlc_ref_tm) where
  coe s := ⟨s.raw⟩

@[app_unexpander Tm.var]
def unexpandVar: Lean.PrettyPrinter.Unexpander
  | `($_ $x:str) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| $name:ident ])
  | `($_ $x:term) => `([tm| [$x] ])
  | _ => throw ()

@[app_unexpander Tm.app]
def unexpandApp: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $a] [tm| $b1 $b2 ]) => `([tm| $a ($b1 $b2) ])
  | `($_ [tm| λ $x:ident : $T, $a] [tm| $b ]) => `([tm| (λ $x : $T, $a) $b ])
  | `($_ [tm| λ [$x]: $T, $a] [tm| $b ]) => `([tm| (λ [$x]: $T, $a) $b ])
  | `($_ [tm| $a ] [tm| $b ]) => `([tm| $a $b ])
  | _ => throw ()


@[app_unexpander Tm.abs]
def unexpandAbs: Lean.PrettyPrinter.Unexpander
  | `($_ $x:str [ty| $T ] [tm| $b ]) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| λ $name : $T, $b ])
  | `($_ $x:str $T [tm| $b ]) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| λ $name : [$T], $b ])
  | `($_ $x:str [ty| $T ] $b) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| λ $name : $T, [$b] ])
  | `($_ $x:str $T $b) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| λ $name : [$T], [$b] ])
  | `($_ $x:term [ty| $T ] [tm| $b ]) => `([tm| λ [$x] : $T, $b ])
  | `($_ $x:term [ty| $T ] $b) => `([tm| λ [$x] : $T, [$b] ])
  | `($_ $x:term $T [tm| $b ]) => `([tm| λ [$x] : [$T], $b ])
  | `($_ $x:term $T $b) => `([tm| λ [$x] : [$T], [$b] ])
  | _ => throw ()



@[app_unexpander Tm.true]
def unexpandTrue: Lean.PrettyPrinter.Unexpander
  | `($_) => `([tm| true ])


@[app_unexpander Tm.false]
def unexpandFalse: Lean.PrettyPrinter.Unexpander
  | `($_) => `([tm| false ])


@[app_unexpander Tm.ite]
def unexpandIf0: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $c] [tm| $t] [tm| $f]) => `([tm| if ($c) then ($t) else ($f) ])
  | _ => throw ()


@[app_unexpander Tm.pair]
def unexpandPair: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x] [tm| $y]) => `([tm| ($x, $y) ])
  | _ => throw ()


@[app_unexpander Tm.fst]
def unexpandFst: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| (fst $x) ])
  | _ => throw ()


@[app_unexpander Tm.snd]
def unexpandSnd: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| (snd $x) ])
  | _ => throw ()



@[simp]
def Tm.subst (t: Tm) (x: Var) (s: Tm): Tm :=
  match t with
  -- λ-calculus
  | .var y =>
    if y = x then s else t
  | .abs y T b =>
    if y = x then t else .abs y T (b.subst x s)
  | .app t1 t2 =>
    .app (t1.subst x s) (t2.subst x s)
  -- bool
  | .true => .true
  | .false => .false
  | .ite c t f => .ite (c.subst x s) (t.subst x s) (f.subst x s)
  -- prod
  | .pair a b => .pair (a.subst x s) (b.subst x s)
  | .fst m => .fst (m.subst x s)
  | .snd m => .snd (m.subst x s)


declare_syntax_cat subst_norm_cat
scoped syntax "subst[ " my_ident " := " plf_stlc_norm_tm " ] ": subst_norm_cat

scoped syntax subst_norm_cat: plf_stlc_norm_tm

scoped macro_rules
  | `([tm| subst[ $x:my_ident := $s:plf_stlc_norm_tm ] $t ]) =>
    `(Tm.subst [tm| $t ] [ident| $x ] [tm| $s])

@[app_unexpander Tm.subst]
def unexpandSubst: Lean.PrettyPrinter.Unexpander
  | `($_subst [tm| $t] $x:str [tm| $s ]) =>
    let ident := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([tm| (subst[ $ident:ident := $s] $t ) ])
  | `($_subst [tm| $t] $x:term [tm| $s ]) => `([tm| (subst[ [$x] := $s] $t ) ])
  | `($_subst $t $x:term $s) => `([tm| (subst[ [$x] := [$s]] [$t] ) ])
  | _ => throw ()


inductive Tm.Value: Tm -> Prop where
  | abs {x T b}: (Tm.abs x T b).Value
  | true: Tm.true.Value
  | false: Tm.false.Value
  | pair {t1 t2: Tm}:
    t1.Value ->
    t2.Value ->
    (Tm.pair t1 t2).Value


inductive Tm.step: Tm -> Tm -> Prop where
  | appAbs {x T b} {v: Tm}:
    v.Value ->
    [tm| (λ [x]: [T], [b]) [v]].step (b.subst x v)
  | app1 {t1 t1' t2: Tm}:
    t1.step t1' ->
    (Tm.app t1 t2).step (Tm.app t1' t2)
  | app2 {v t2 t2': Tm}:
    v.Value ->
    t2.step t2' ->
    (Tm.app v t2).step (Tm.app v t2')
  | ifTrue {t f}:
    (Tm.ite .true t f).step t
  | ifFalse {t f}:
    (Tm.ite .false t f).step f
  | ite {c c' t f: Tm}:
    c.step c' ->
    (Tm.ite c t f).step (.ite c' t f)
  | pair1 {t1 t1' t2: Tm}:
    t1.step t1' ->
    (Tm.pair t1 t2).step (.pair t1' t2)
  | pair2 {v t2 t2': Tm}:
    v.Value ->
    t2.step t2' ->
    (Tm.pair v t2).step (.pair v t2')
  | fst {t t': Tm}:
    t.step t' ->
    t.fst.step t'.fst
  | fstPair {v1 v2: Tm}:
    v1.Value ->
    v2.Value ->
    (Tm.pair v1 v2).fst.step v1
  | snd {t t': Tm}:
    t.step t' ->
    t.snd.step t'.snd
  | sndPair {v1 v2: Tm}:
    v1.Value ->
    v2.Value ->
    (Tm.pair v1 v2).snd.step v2


abbrev Tm.mstep := RTCl Tm.step
abbrev Tm.step_normal := Relation.Normal Tm.step


theorem Tm.Value.step_normal {t: Tm}: t.Value -> t.step_normal := by
  intro Hv
  induction Hv with (
    intro contra
    let ⟨y, Hstep⟩ := contra
    try (cases Hstep <;> done)
  )
  | pair H1 H2 IH1 IH2 =>
    cases Hstep with
    | _ =>
      solve_by_elim

abbrev Context := PartialMap Ty
def Context.empty: Context := PartialMap.empty (A := Ty)

declare_syntax_cat plf_stlc_norm_context (behavior := symbol)
syntax "[]": plf_stlc_norm_context
syntax term: plf_stlc_norm_context
syntax my_ident " : " plf_stlc_norm_ty: plf_stlc_norm_context
syntax plf_stlc_norm_context ", " plf_stlc_norm_context: plf_stlc_norm_context
syntax "[ctx| " plf_stlc_norm_context " ]": term

macro_rules
  | `([ctx| [] ]) => `(Context.empty)
  | `([ctx| $t:term ]) => `($t)
  | `([ctx| $x:my_ident : $T]) => `(
      PartialMap.update Context.empty [ident| $x ] [ty| $T ]
    )
  | `([ctx| $x:my_ident : $T, $G]) => `(
      PartialMap.update [ctx| $G ] [ident| $x ] [ty| $T ]
    )
  | `([ctx| $c1, $c2 ]) => `(PartialMap.merge [ctx| $c1] [ctx| $c2])


instance : Coe Lean.Term (Lean.TSyntax `plf_stlc_norm_context) where
  coe s := ⟨s.raw⟩

@[app_unexpander Context.empty]
def unexpandContext_empty: Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `([ctx| [] ] $x)
  | `($_) => `([ctx| [] ])


@[app_unexpander PartialMap.update]
def unexpandContext_update: Lean.PrettyPrinter.Unexpander
  -- | `($_ $_ $x:str [ty| $v]) =>
  --   let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
  --   `([ctx| $name:ident : $v ])
  -- variables
  | `($_ [ctx| [] ] $x:str [ty| $v]) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : $v ])
  | `($_ [ctx| $G ] $x:str [ty| $v]) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : $v, $G ])
  | `($_ [ctx| [] ] $x:str $v) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : [$v]])
  | `($_ [ctx| $G ] $x:str $v) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : [$v], $G ])
  | `($_ $G $x:str [ty| $v]) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : $v, $G ])
  | `($_ $G $x:str $v) =>
    let name := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([ctx| $name:ident : [$v], $G ])
  -- terms
  | `($_ [ctx| [] ] $x:term [ty| $v]) => `([ctx| [$x] : $v ])
  | `($_ [ctx| $G ] $x:term [ty| $v]) => `([ctx| [$x] : $v, $G ])
  | `($_ [ctx| [] ] $x:term $v) => `([ctx| [$x] : [$v]])
  | `($_ [ctx| $G ] $x:term $v) => `([ctx| [$x] : [$v], $G ])
  | `($_ $G $x:term [ty| $v]) => `([ctx| [$x] : $v, $G ])
  | `($_ $G $x:term $v) => `([ctx| [$x] : [$v], $G ])
  | _ => throw ()


@[app_unexpander PartialMap.merge]
def unexpandContext_merge: Lean.PrettyPrinter.Unexpander
  | `($_ [ctx| $x] [ctx| $y]) => `([ctx| $x, $y ])
  | `($_ [ctx| $x] $y) => `([ctx| $x, $y ])
  | `($_ $x [ctx| $y]) => `([ctx| $x, $y ])
  | `($_ $x $y) => `([ctx| $x, $y ])
  | _ => throw ()


inductive Context.has_type: Context -> Tm -> Ty -> Prop where
  | var {Gamma: Context} {x: Var} {T}:
    Gamma x = Option.some T ->
    Context.has_type Gamma x T
  | abs {Gamma: Context} {x b} {A B: Ty}:
    Context.has_type map![ x => A; Gamma] b B ->
    Context.has_type Gamma (.abs x A b) (.Arrow A B)
  | app {Gamma: Context} {f x} {A B}:
    Context.has_type Gamma f (.Arrow A B) ->
    Context.has_type Gamma x A ->
    Context.has_type Gamma (.app f x) B
  | true {Gamma}: Context.has_type Gamma .true .Bool
  | false {Gamma}: Context.has_type Gamma .false .Bool
  | ite {Gamma c t f} {A: Ty}:
    Context.has_type Gamma c .Bool ->
    Context.has_type Gamma t A ->
    Context.has_type Gamma f A ->
    Context.has_type Gamma (.ite c t f) A
  | pair {Gamma t1 t2 T1 T2}:
    Context.has_type Gamma t1 T1 ->
    Context.has_type Gamma t2 T2 ->
    Context.has_type Gamma (.pair t1 t2) (.Prod T1 T2)
  | fst {Gamma t T1 T2}:
    Context.has_type Gamma t (.Prod T1 T2) ->
    Context.has_type Gamma t.fst T1
  | snd {Gamma t T1 T2}:
    Context.has_type Gamma t (.Prod T1 T2) ->
    Context.has_type Gamma t.snd T2


scoped macro "ty{ " G:plf_stlc_norm_context " |- " t:plf_stlc_norm_tm " : " T:plf_stlc_norm_ty " }": term
  => `(Context.has_type [ctx| $G ] [tm| $t ] [ty| $T ])


@[app_unexpander Context.has_type]
def unexpandhas_type: Lean.PrettyPrinter.Unexpander
  | `($_ [ctx| $G ] [tm| $t ] [ty| $T ]) => `(ty{ $G |- $t : $T})
  | `($_ [ctx| $G ] [tm| $t ] $T) => `(ty{ $G |- $t : [$T]})
  | `($_ [ctx| $G ] $t [ty| $T]) => `(ty{ $G |- [$t] : $T})
  | `($_ [ctx| $G ] $t $T) => `(ty{ $G |- [$t] : [$T]})
  | `($_ $G [tm| $t ] [ty| $T ]) => `(ty{ $G |- $t : $T})
  | `($_ $G $t [ty| $T ]) => `(ty{ $G |- [$t] : $T})
  | `($_ $G [tm| $t] $T) => `(ty{ $G |- $t : [$T]})
  | `($_ $G $t $T) => `(ty{ $G |- [$t] : [$T]})
  | _ => throw ()


theorem Tm.weakening {Gamma Gamma': Context} {t T}:
  Gamma.included_in Gamma' ->
  ty{ Gamma |- [t]: [T]} ->
  ty{ Gamma' |- [t]: [T]}
:= by
  intro H Ht
  induction Ht generalizing Gamma' with
  | var | abs | app | true | false | ite | pair | fst | snd =>
    constructor <;> solve_by_elim [PartialMap.included_in_update]


theorem Tm.weakening_empty {Gamma: Context} {t T}:
  ty{ [] |- [t]: [T]} ->
  ty{ Gamma |- [t]: [T]}
:= by
  intro H
  apply Tm.weakening _ H
  simp
  intros
  contradiction


theorem Tm.subst_preserves_typing {Gamma x U t v T}:
  ty{ [x]: [U], Gamma |- [t]: [T]} ->
  ty{ [] |- [v]: [U] } ->
  ty{ Gamma |- subst[[x] := [v]] [t]: [T]}
:= by
  intro Ht Hv
  induction t generalizing Gamma T with
  | var =>
    cases Ht with | var Ht =>
    simp
    split
    . next E =>
      simp [E] at Ht
      simp [<-Ht]
      solve_by_elim [Tm.weakening_empty]
    . next NE =>
      simp [NE] at Ht
      constructor
      assumption
  | abs _ _ _ IH =>
    cases Ht with | abs Ht =>
    simp
    split
    . subst_eqs
      constructor
      rewrite [PartialMap.update_shadow] at Ht
      assumption
    . next NE =>
      constructor
      apply IH
      rewrite [PartialMap.update_permute]
      . assumption
      . solve_by_elim
  | _ =>
    cases Ht
    constructor <;> solve_by_elim


theorem Tm.step.preservation {t t': Tm} {T}:
  ty{ [] |- [t]: [T]} ->
  t.step t' ->
  ty{ [] |- [t']: [T]}
:= by
  generalize E: [ctx| [] ] = Gamma
  intro Ht Hstep
  induction Hstep generalizing T with (
    rewrite [<-E] at *
    cases Ht
  )
  | appAbs Hv =>
    next Ht =>
    cases Ht
    solve_by_elim [Tm.subst_preserves_typing]
  | ifTrue | ifFalse =>
    assumption
  | fstPair | sndPair =>
    next H =>
    cases H
    assumption
  -- compatibility
  | app1 | app2
  | ite
  | fst | snd
  | pair1 | pair2 =>
    constructor <;>
      solve_by_elim


theorem Tm.mstep.preservation {t t': Tm} {T}:
  ty{ [] |- [t]: [T]} ->
  t.mstep t' ->
  ty{ [] |- [t']: [T]}
:= by
  intro Ht Hstep
  induction Hstep with
  | refl =>
    trivial
  | step Hab Hbc IHbc =>
    apply IHbc
    apply Tm.step.preservation
    . exact Ht
    . exact Hab


inductive Var.free_in (x: Var): Tm -> Prop where
  | var: x.free_in x
  | abs {y T b}:
    y ≠ x ->
    x.free_in b ->
    x.free_in [tm| λ [y]: [T], [b]]
  | app1 {t1 t2}:
    x.free_in t1 ->
    x.free_in [tm| [t1] [t2]]
  | app2 {t1 t2}:
    x.free_in t2 ->
    x.free_in [tm| [t1] [t2]]
  | if1 {c t f}:
    x.free_in c ->
    x.free_in (.ite c t f)
  | if2 {c t f}:
    x.free_in t ->
    x.free_in (.ite c t f)
  | if3 {c t f}:
    x.free_in f ->
    x.free_in (.ite c t f)
  | pair1 {t1 t2}:
    x.free_in t1 ->
    x.free_in [tm| ([t1], [t2])]
  | pair2 {t1 t2}:
    x.free_in t2 ->
    x.free_in [tm| ([t1], [t2])]
  | fst {t}:
    x.free_in t ->
    x.free_in t.fst
  | snd {t}:
    x.free_in t ->
    x.free_in t.snd


def Tm.closed (t: Tm) := forall (x: Var), ¬ x.free_in t

theorem Context.invarance {Gamma Gamma'} {t S}:
  ty{ Gamma |- [t]: [S]} ->
  (forall x: Var, x.free_in t -> Gamma x = Gamma' x) ->
  ty{ Gamma' |- [t]: [S]}
:= by
  intro Ht H
  induction Ht generalizing Gamma' with
  | var =>
    constructor
    rewrite [<-H]
    . assumption
    . constructor
  | abs Ht IH =>
    constructor
    apply IH
    intro y Hf
    simp
    split
    . trivial
    . apply H
      constructor
      . solve_by_elim
      . assumption
  | app
  | true | false | ite
  | pair | fst | snd =>
    constructor <;>
      solve_by_elim (maxDepth := 13) [
        Var.free_in.app2,
        Var.free_in.if2, Var.free_in.if3,
        Var.free_in.pair2
      ]


theorem Var.free_in.context {x: Var} {t T Gamma}:
  x.free_in t ->
  ty{ Gamma |- [t]: [T]} ->
  exists T', Gamma x = .some T'
:= by
  intro Hf Ht
  induction Ht with
  | var =>
    cases Hf
    constructor
    assumption
  | abs H IH =>
    cases Hf with | abs NE Hf =>
    next Gamma _ _ A B =>
    specialize IH Hf
    let ⟨T', IH⟩ := IH
    exists T'
    rewrite [<-IH]
    unfold PartialMap.update
    rewrite [TotalMap.update_neq NE]
    trivial
  | app
  | true | false | ite
  | pair | fst | snd  =>
    cases Hf <;>
      solve_by_elim


theorem Tm.typed_empty_closed {t: Tm} {T}:
  ty{ [] |- [t]: [T]} ->
  t.closed
:= by
  intro Ht
  intro x Hf
  let ⟨_, H⟩ := Hf.context Ht
  contradiction


elab "add_value_nf_promise" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let ctx <- Lean.MonadLCtx.getLCtx
    for decl in ctx do
      let name := decl.userName
      let type := decl.type
      if ! type.isAppOf `Normalize.Tm.step then
        continue
      let ident := Lean.mkIdent name
      Lean.Elab.Tactic.evalTactic (← `(tactic|
        have _ := fun Hv => Tm.Value.step_normal Hv ⟨_, $ident⟩
      ))


scoped macro "value_nf": tactic =>
  `(tactic|
    (try solve_by_elim [Tm.Value.step_normal]) <;>
    exfalso <;>
    add_value_nf_promise <;> solve_by_elim)


theorem Tm.step.deterministic {x y1 y2: Tm}:
  x.step y1 -> x.step y2 -> y1 = y2
:= by
  intro H1 H2
  induction H1 generalizing y2 with
  | _ =>
    cases H2 with
    | _ =>
      value_nf



abbrev Tm.halts (t: Tm): Prop := exists t', t.mstep t' ∧ t'.Value


theorem Tm.Value.halts {t: Tm}:
  t.Value -> t.halts
:= by
  intro H
  solve_by_elim


@[simp]
def Ty.R (T: Ty) (t: Tm) : Prop :=
  ty{ [] |- [t]: [T]} ∧ t.halts ∧
  match T with
  | .Bool => True
  | .Arrow T1 T2 => forall s, T1.R s -> T2.R (t.app s)
  | .Prod T1 T2 => T1.R t.fst ∧ T2.R t.snd


namespace Explain_The_TyR_Definition

inductive Pred: Nat -> Prop where
  | zero: Pred Nat.zero
  | succ {n}: Pred n -> Pred n.succ


@[simp]
def Pred2 (n: Nat): Prop :=
  match n with
  | .zero => True
  | .succ m => Pred2 m


theorem Pred.Pred2 {n: Nat}:
  Pred n -> Pred2 n
:= by
  intro H
  induction H with
  | zero =>
    simp
  | succ H IH =>
    simp
    exact IH

theorem Pred2.Pred {n: Nat}:
  Pred2 n -> Pred n
:= by
  intro H
  induction n with
  | zero =>
    constructor
  | succ m IH =>
    constructor
    simp at H
    apply IH
    exact H


theorem PredPred2: Pred = Pred2 := by
  apply funext
  intro x
  apply propext
  solve_by_elim [Pred.Pred2, Pred2.Pred]

end Explain_The_TyR_Definition

theorem Ty.R.halts {T: Ty} {t: Tm}:
  T.R t -> t.halts
:= by
  intro H
  unfold R at H
  exact H.right.left


theorem Ty.R.typable_empty {T: Ty} {t: Tm}:
  T.R t -> ty{ [] |- [t]: [T]}
:= by
  intro H
  unfold R at H
  exact H.left


theorem Tm.step.preserves_halting {t t': Tm}:
  t.step t' ->
  (t.halts <-> t'.halts)
:= by
  intro Hstep
  unfold Tm.halts
  apply Iff.intro
  . intro ⟨t', ⟨step, Hv⟩⟩
    cases step with
    | refl =>
      value_nf
    | step =>
      -- should use Church-Rosser theorem
      let H := Tm.step.deterministic Hstep (by assumption)
      subst_vars
      exists t'
  . intro ⟨t', ⟨step, Hv⟩⟩
    exists t'
    and_intros
    . solve_by_elim [Relation.trans, RTCl.inclusion]
    . assumption


theorem Tm.step.preserves_R {T: Ty} {t t': Tm}:
  t.step t' ->
  T.R t ->
  T.R t'
:= by
  induction T generalizing t t' with (
    intro Hstep HR
  )
  | Bool =>
    simp at *
    and_intros
    . apply Tm.step.preservation
      . exact HR.left
      . exact Hstep
    . apply Hstep.preserves_halting.mp
      exact HR.right
  | Arrow T1 T2 IH1 IH2 =>
    simp at *
    let ⟨H1, ⟨H2, H3⟩⟩ := HR
    and_intros
    . apply Tm.step.preservation <;> assumption
    . apply Hstep.preserves_halting.mp
      assumption
    . intro s H
      apply IH2
      . apply Tm.step.app1
        assumption
      . solve_by_elim
  | Prod T1 T2 IH1 IH2 =>
    simp at *
    let ⟨_, ⟨_, ⟨_, _⟩⟩⟩ := HR
    apply And.intro
    . apply Tm.step.preservation <;> assumption
    apply And.intro
    . apply Hstep.preserves_halting.mp
      assumption
    . apply And.intro
      . apply IH1
        . apply Tm.step.fst
          exact Hstep
        . assumption
      . apply IH2
        . apply Tm.step.snd
          exact Hstep
        . assumption


theorem Tm.mstep.preserves_R {T: Ty} {t t': Tm}:
  t.mstep t' ->
  T.R t ->
  T.R t'
:= by
  intro H
  induction H generalizing T with
  | refl =>
    intros
    trivial
  | step Hab Hbc IHbc =>
    intro Ha
    apply IHbc
    apply Hab.preserves_R
    exact Ha


theorem Tm.step.preserves_R' {T: Ty} {t t': Tm}:
  ty{ [] |- [t]: [T]} ->
  t.step t' ->
  T.R t' ->
  T.R t
:= by
  induction T generalizing t t' with (
    intro Ht Hstep HR
  )
  | Bool =>
    simp at *
    and_intros
    . assumption
    . apply Hstep.preserves_halting.mpr
      exact HR.right
  | Arrow T1 T2 IH1 IH2 =>
    simp at *
    let ⟨H1, ⟨H2, H3⟩⟩ := HR
    and_intros
    . assumption
    . apply Hstep.preserves_halting.mpr
      assumption
    . intro s H
      let H' := H
      unfold Ty.R at H'
      rcases H' with ⟨_, ⟨_, _⟩⟩
      apply IH2
      . solve_by_elim
      . apply Tm.step.app1
        assumption
      . apply H3
        exact H
  | Prod T1 T2 IH1 IH2 =>
    simp at *
    let ⟨_, ⟨_, ⟨_, _⟩⟩⟩ := HR
    apply And.intro
    . assumption
    apply And.intro
    . apply Hstep.preserves_halting.mpr
      assumption
    . apply And.intro
      . apply IH1 <;> solve_by_elim
      . apply IH2 <;> solve_by_elim


theorem Tm.mstep.preserves_R' {T t t'} :
  ty{ [] |- [t]: [T]} ->
  t.mstep t' ->
  T.R t' ->
  T.R t
:= by
  intro Ht H
  induction H generalizing T with
  | refl =>
    intros
    trivial
  | step Hab Hbc IHbc =>
    intro Ha
    apply step.preserves_R'
      <;> solve_by_elim [Tm.step.preservation]


abbrev Env := List (Var × Tm)


@[simp]
def Env.msubst (ss: Env) (t: Tm): Tm :=
  match ss with
  | [] => t
  | (x, s) :: ss' => Env.msubst ss' (t.subst x s)


abbrev TyAsgmt := List (Var × Ty)


@[simp]
def Context.mupdate (Gamma: Context) (xts: TyAsgmt) :=
  match xts with
  | [] => Gamma
  | (x, v) :: xts' => (Gamma.mupdate xts').update x v


@[simp]
def List.dropKey {A: Type} (nxs: List (Var × A)) (n: Var): List (Var × A) :=
  match nxs with
  | [] => []
  | (n', x) :: nxs' =>
    if n' = n then
      List.dropKey nxs' n
    else
      (n', x) :: (List.dropKey nxs' n)


@[simp]
abbrev Env.dropKey: Env -> Var -> Env := List.dropKey

@[simp]
abbrev TyAsgmt.dropKey: TyAsgmt -> Var -> TyAsgmt := List.dropKey


inductive TyAsgmt.Instantiate : TyAsgmt -> Env -> Prop where
  | nil : TyAsgmt.Instantiate [] []
  | cons {x} {T: Ty} {v: Tm} {c: TyAsgmt} {e} :
    v.Value ->
    T.R v ->
    c.Instantiate e ->
    TyAsgmt.Instantiate ((x, T) :: c) ((x, v) :: e)


theorem Tm.vacuous_subst {t: Tm} {x: Var}:
  ¬ x.free_in t ->
  forall t', t.subst x t' = t
:= by
  induction t generalizing x with (
    intro Hf t'
  )
  | var a =>
    simp only [subst]
    split
    . exfalso
      apply Hf
      have H: a = x := by
        grind
      rewrite [H]
      constructor
    . trivial
  | abs y T b IH =>
    simp only [subst]
    split
    . trivial
    . rewrite [IH]
      . trivial
      . grind [Var.free_in]
  | app t1 t2 IH1 IH2
  | true | false | ite
  | pair | fst | snd =>
    first | trivial |
      simp
      grind [Var.free_in]


theorem Tm.subst_closed {t: Tm}:
  t.closed ->
  forall x t', t.subst x t' = t
:= by
  solve_by_elim [Tm.vacuous_subst]


theorem Tm.subst_not_free_in {t: Tm} {x: Var} {v: Tm}:
  v.closed ->
  ¬ x.free_in (t.subst x v)
:= by
  intro Hv contra
  induction t with
  | var =>
    simp at contra
    split at contra
    . /- eq -/
      solve_by_elim
    . /- neq -/
      cases contra
      contradiction
  | abs =>
    simp at contra
    split at contra
    . /- eq -/
      cases contra
      contradiction
    . /- neq -/
      cases contra
      solve_by_elim
  | _ =>
    cases contra <;>
      solve_by_elim


theorem Tm.subst_eq {t' x t} {v: Tm}:
  v.closed ->
  [tm| subst[ [x] := [t] ] (subst[ [x] := [v]] [t']) ] = [tm| subst[ [x] := [v]] [t'] ]
:= by
  intro Hv
  apply Tm.vacuous_subst
  apply subst_not_free_in
  assumption


theorem Tm.subst_permute {t} {x1 x2: Var} {v1 v2: Tm}:
  x1 ≠ x2 ->
  v1.closed -> v2.closed ->
  [tm| subst[ [x1] := [v1] ] (subst[ [x2] := [v2]] [t]) ]
    = [tm| subst[ [x2] := [v2] ] (subst[ [x1] := [v1]] [t]) ]
:= by
  intro NE Hv1 Hv2
  have NE2: x2 ≠ x1 := by
    solve_by_elim
  induction t with
  | var =>
    simp
    split
    . subst_vars
      simp [NE2]
      apply Tm.subst_closed
      assumption
    . simp
      split
      . symm
        apply Tm.subst_closed
        assumption
      . simp
        intros
        contradiction
  | abs y T b IH =>
    simp
    split <;> split <;> subst_eqs
    . simp
    . simp
      intros
      contradiction
    . simp
      intros
      contradiction
    . next H1 H2 =>
      simp [H1, H2]
      assumption
  | _ =>
    simp <;>
      solve_by_elim


theorem Tm.msubst_closed {t: Tm}:
  t.closed ->
  forall ss: Env, ss.msubst t = t
:= by
  intro H ss
  induction ss with
  | nil =>
    trivial
  | cons x xs IH =>
    simp [Env.msubst]
    rewrite [Tm.subst_closed H]
    exact IH


@[simp]
def Env.closed: Env -> Prop
  | [] => True
  | (_x, t) :: env' => t.closed ∧ Env.closed env'


def Tm.subst_msubst {env: Env} {x} {v t: Tm}:
  v.closed ->
  env.closed ->
  env.msubst (t.subst x v) = ((env.dropKey x).msubst t).subst x v
:= by
  intro Hv Henv
  induction env generalizing x v t with
  | nil =>
    simp
  | cons y ys IH =>
    simp at *
    cases Henv
    split
    . /- eq -/
      subst_vars
      rewrite [<-IH Hv (by assumption)]
      rewrite [Tm.subst_eq Hv]
      trivial
    . /- neq -/
      next NE =>
      rewrite [Tm.subst_permute NE (by assumption) (by assumption)]
      simp
      apply IH
      . exact Hv
      . assumption


theorem Tm.msubst_var {ss: Env} {x: Var}:
  ss.closed ->
  ss.msubst (.var x) =
    match ss.lookup x with
    | .some t => t
    | .none => .var x
:= by
  intro Hss
  induction ss with
  | nil =>
    simp
  | cons y ys IH =>
    simp at Hss
    rcases Hss with ⟨H1, H2⟩
    specialize IH H2
    simp only [Env.msubst]
    simp only [Tm.subst]
    split
    . /- eq -/
      subst_vars
      simp [List.lookup] at *
      rewrite [Tm.msubst_closed (by assumption)]
      trivial
    . /- neq -/
      next NE =>
      simp [List.lookup]
      have H: (x == y.fst) = Bool.false := by
        grind
      simp [H]
      exact IH


theorem neq_symm {A} {x y: A}: (¬ x = y) -> (¬ y = x) := by
  solve_by_elim


theorem Tm.msubst_abs {ss: Env} {x T t}:
  ss.msubst [tm| λ [x]: [T], [t]] = [tm| λ [x]: [T], [(ss.dropKey x).msubst t]]
:= by
  induction ss generalizing x T t with
  | nil =>
    simp
  | cons =>
    simp
    split
    . subst_vars
      simp
      solve_by_elim
    . next NE =>
      have NE2 := neq_symm NE
      simp [NE2]
      solve_by_elim


theorem Tm.msubst_app {ss: Env} {t1 t2}:
  ss.msubst [tm| [t1] [t2]] = [tm| [ss.msubst t1] [ss.msubst t2]]
:= by
  induction ss generalizing t1 t2 with
  | nil =>
    simp
  | cons =>
    simp
    solve_by_elim


theorem Tm.msubst_true {ss: Env}:
  ss.msubst [tm| true ] = [tm| true]
:= by
  induction ss with
  | nil =>
    simp
  | cons =>
    simp
    solve_by_elim


theorem Tm.msubst_false {ss: Env}:
  ss.msubst [tm| false ] = [tm| false]
:= by
  induction ss with
  | nil =>
    simp
  | cons =>
    simp
    solve_by_elim


theorem Tm.msubst_ite {ss: Env} {c t f}:
  ss.msubst [tm| if [c] then [t] else [f] ] =
    [tm| if [ss.msubst c] then [ss.msubst t] else [ss.msubst f]]
:= by
  induction ss generalizing c t f with
  | nil =>
    simp
  | cons x xs IH =>
    simp
    solve_by_elim


theorem Tm.msubst_pair {ss: Env} {t1 t2}:
  ss.msubst [tm| ([t1], [t2]) ] =
    [tm| ([ss.msubst t1], [ss.msubst t2]) ]
:= by
  induction ss generalizing t1 t2 with
  | nil =>
    simp
  | cons x xs IH =>
    simp
    solve_by_elim


theorem Tm.msubst_fst {ss: Env} {t}:
  ss.msubst [tm| fst [t] ] = [tm| fst [ss.msubst t] ]
:= by
  induction ss generalizing t with
  | nil =>
    simp
  | cons x xs IH =>
    simp
    solve_by_elim


theorem Tm.msubst_snd {ss: Env} {t}:
  ss.msubst [tm| snd [t] ] = [tm| snd [ss.msubst t] ]
:= by
  induction ss generalizing t with
  | nil =>
    simp
  | cons x xs IH =>
    simp
    solve_by_elim


theorem Tm.mupdate_lookup {c: TyAsgmt} {x: Var}:
  c.lookup x = (Context.mupdate .empty c) x
:= by
  induction c with
  | nil =>
    simp [Context.empty]
  | cons y ys IH =>
    simp [Context.empty]
    split
    . next E =>
      simp [List.lookup, E]
    . next NE =>
      simp [List.lookup]
      have NE: (x == y.fst) = Bool.false := by
        grind
      simp [NE]
      assumption


theorem Tm.mupdate_drop {c: TyAsgmt} {Gamma: Context} {x x': Var}:
  Gamma.mupdate (c.dropKey x) x' =
    if x = x' then Gamma x' else (Gamma.mupdate c) x'
:= by
  induction c with
  | nil =>
    simp
  | cons y ys IH =>
    simp
    split
    . next E =>
      subst_vars
      split
      . next E =>
        simp [E] at *
        exact IH
      . next NE =>
        have NE2 := neq_symm NE
        simp [NE2]
        simp [NE] at IH
        assumption
    . next NE =>
      have NE2 := neq_symm NE
      split
      . subst_vars
        simp [NE2] at *
        assumption
      . next NE' =>
        have NE2' := neq_symm NE'
        simp [NE'] at IH
        simp
        rewrite [<-IH]
        trivial


theorem TyAsgmt.Instantiate.domains_match {c: TyAsgmt} {e}:
  c.Instantiate e ->
  forall {x T},
    c.lookup x = .some T ->
    exists t, e.lookup x = .some t
:= by
  intro Hinst
  induction Hinst with (
    intro x T Hc
  )
  | nil =>
    contradiction
  | cons =>
    simp [List.lookup] at *
    split at Hc
    . cases Hc
      simp
    . solve_by_elim



theorem TyAsgmt.Instantiate.env_closed {c: TyAsgmt} {e}:
  c.Instantiate e -> e.closed
:= by
  intro Hinst
  induction Hinst with
  | nil =>
    simp
  | cons Hv HR =>
    simp
    unfold Ty.R at HR
    rcases HR
    and_intros
    . apply Tm.typed_empty_closed
      assumption
    . assumption


theorem TyAsgmt.Instantiate.R {c: TyAsgmt} {e}:
  c.Instantiate e ->
  forall x t T,
    c.lookup x = .some T ->
    e.lookup x = .some t ->
    T.R t
:= by
  intro Hinst
  induction Hinst with (
    intro x t T Hc He
  )
  | nil =>
    contradiction
  | cons =>
    simp [List.lookup] at *
    split at Hc
    . next E =>
      simp [E] at He
      cases Hc
      subst_vars
      assumption
    . next NE =>
      simp [NE] at He
      solve_by_elim


theorem TyAsgmt.Instantiate.drop {c: TyAsgmt} {env}:
  c.Instantiate env ->
  forall x, (c.dropKey x).Instantiate (env.dropKey x)
:= by
  intro Hinst
  induction Hinst with (
    intro x
  )
  | nil =>
    simp
    constructor
  | cons Hv HR Hinst IH =>
    simp
    split
    . apply IH
    . constructor
      . assumption
      . assumption
      . apply IH


theorem Tm.mstep.cong {t t': Tm} {f: Tm -> Tm}:
  (cong: ∀ {a b : Tm}, a.step b → (f a).step (f b)) ->
  t.mstep t' ->
  (f t).mstep (f t')
:= by
  intro cong
  apply Relation.keep_cong (P := step) (Q := mstep)
  exact cong


theorem Tm.mstep.app2 {v: Tm} {t t'}:
  v.Value ->
  t.mstep t' ->
  (v.app t).mstep (v.app t')
:= by
  intro
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption


theorem Tm.mstep.if1 {c c' t f: Tm}:
  c.mstep c' ->
  (c.ite t f).mstep (c'.ite t f)
:= by
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption


theorem Tm.mstep.pair1 {t1 t1' t2: Tm}:
  t1.mstep t1' ->
  (t1.pair t2).mstep (t1'.pair t2)
:= by
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption



theorem Tm.mstep.pair2 {v t2 t2': Tm}:
  v.Value ->
  t2.mstep t2' ->
  (v.pair t2).mstep (v.pair t2')
:= by
  intro
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption


theorem Tm.mstep.fst {t t': Tm}:
  t.mstep t' ->
  t.fst.mstep t'.fst
:= by
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption


theorem Tm.mstep.snd {t t': Tm}:
  t.mstep t' ->
  t.snd.mstep t'.snd
:= by
  apply Tm.mstep.cong
  intros
  constructor <;>
    assumption


theorem Tm.msubst_preserves_typing {c: TyAsgmt} {e}:
  c.Instantiate e ->
  forall (Gamma: Context) t S,
    ty{Gamma.mupdate c |- [t]: [S]} ->
    ty{Gamma |- [ e.msubst t ]: [S]}
:= by
  intro Hinst
  induction Hinst with (
    intro Gamma t s Ht
  )
  | nil =>
    simp at *
    assumption
  | cons Hv HR Hinst IH =>
    apply IH
    apply subst_preserves_typing
    . simp only [Context.mupdate] at Ht
      exact Ht
    . unfold Ty.R at HR
      rcases HR with ⟨_, ⟨_⟩⟩
      assumption


theorem Tm.msubst_R_lemma {c: TyAsgmt} {env t T} {Gamma}:
  (forall x, Gamma x = c.lookup x) ->
  ty{ Gamma |- [t]: [T]} ->
  c.Instantiate env ->
  T.R (env.msubst t)
:= by
  intros H Ht Hinst
  induction Ht generalizing env c with
  | var Hx =>
    rewrite [H] at Hx
    rcases Hinst.domains_match Hx with ⟨t, P⟩
    apply Hinst.R
    . exact Hx
    . rewrite [Tm.msubst_var]
      . simp [P]
      . apply Hinst.env_closed
  | @abs Gamma x b A B Ha IHb =>
    rewrite [msubst_abs]
    have WT: ty{[] |- λ [x]: [A], [(env.dropKey x).msubst b]: [A] -> [B]} := by {
      constructor
      apply msubst_preserves_typing
      . apply Hinst.drop
      apply Context.invarance
      . exact Ha
      . intro y Hf
        rewrite [mupdate_drop]
        split
        . next E =>
          simp [E]
        . next NE =>
          have NE2 := neq_symm NE
          have E: ([ctx| [x] : [A], Gamma ]) y = Gamma y := by
            simp [NE2]
          rewrite [E]
          rewrite [H]
          clear H Hinst IHb
          induction c with
          | nil =>
            simp [NE2]
            trivial
          | cons z zs IH =>
            simp only [List.lookup]
            split
            . next E =>
              simp [E]
            . next NE =>
              simp
              have NE: y ≠ z.fst := by
                grind
              simp [NE]
              apply IH
    }
    -- finished WT
    simp; and_intros
    . exact WT
    . apply Tm.Value.halts
      constructor
    . intro s HARs
      let ⟨t', ⟨Hstep, Hv⟩⟩ := HARs.halts
      have HARt' := Tm.mstep.preserves_R Hstep HARs
      let env': Env := (x, t') :: env
      apply Tm.mstep.preserves_R' (t' := env'.msubst b)
      . constructor
        . exact WT
        . apply HARs.typable_empty
      . rel_trans
        . apply mstep.app2
          . constructor
          . exact Hstep
        . rtcl_incl
          unfold env'
          simp
          rewrite [subst_msubst]
          . constructor
            exact Hv
          . apply typed_empty_closed
            apply HARt'.typable_empty
          . apply Hinst.env_closed
      . apply IHb (c := (x, A) :: c)
        . intro y
          simp [List.lookup]
          split
          . next E =>
            simp [E]
          . next NE =>
            have NE: (y == x) = Bool.false := by
              grind
            simp [NE]
            apply H
        . unfold env'
          constructor
          . exact Hv
          . exact HARt'
          . exact Hinst
  | app Ht1 Ht2 IHt1 IHt2 =>
    rewrite [msubst_app]
    specialize IHt1 H Hinst
    specialize IHt2 H Hinst
    simp at IHt1
    rcases IHt1 with ⟨_, ⟨_, H⟩⟩
    apply H
    exact IHt2
  | true | false =>
    try rewrite [msubst_true]
    try rewrite [msubst_false]
    unfold Ty.R
    solve_by_elim (maxDepth := 7) [Value.halts]
  | ite Hc Ht Hf IHc IHt IHf =>
    rewrite [msubst_ite]
    specialize IHc H Hinst
    specialize IHt H Hinst
    specialize IHf H Hinst
    -- c must be reduced to either true or false
    rcases IHc.halts with ⟨c', ⟨step_c', Vc'⟩⟩
    have Hc': c' = [tm| true ] ∨ c' = [tm| false ] := by
      let HR := step_c'.preserves_R IHc
      let Ht := HR.typable_empty
      cases Vc' with
      | true | false =>
        simp
      | _ =>
        cases Ht
    rcases Hc' <;>
    . subst_vars
      apply Tm.mstep.preserves_R'
      . constructor
        . apply IHc.typable_empty
        . apply IHt.typable_empty
        . apply IHf.typable_empty
      . rel_trans
        . apply mstep.if1
          exact step_c'
        . rtcl_incl
          constructor
      . assumption
  | fst Ht IH | snd Ht IH =>
    try rewrite [msubst_fst]
    try rewrite [msubst_snd]
    specialize IH H Hinst
    simp at IH
    rcases IH with ⟨_, ⟨_, ⟨_, _⟩⟩⟩
    assumption
  | @pair Gamma t1 t2 T1 T2 H1 H2 IH1 IH2 =>
    rewrite [msubst_pair]
    specialize IH1 H Hinst
    specialize IH2 H Hinst
    have WT: ty{[] |- ([env.msubst t1], [env.msubst t2]): [T1] * [T2]} := by
      constructor
      . apply IH1.typable_empty
      . apply IH2.typable_empty
    simp
    let IH1' := IH1
    let IH2' := IH2
    unfold Ty.R at IH1 IH2
    let ⟨_, ⟨halt1, _⟩⟩ := IH1
    let ⟨t1', ⟨Hstep1, Hv1⟩⟩ := halt1
    let ⟨_, ⟨halt2, _⟩⟩ := IH2
    let ⟨t2', ⟨Hstep2, Hv2⟩⟩ := halt2
    and_intros
    . exact WT
    . exists [tm| ([t1'], [t2'])]
      and_intros
      . rel_trans
        . apply Hstep1.pair1
        . apply mstep.pair2
          . exact Hv1
          . exact Hstep2
      . constructor
        . exact Hv1
        . exact Hv2
    . apply Tm.mstep.preserves_R'
      . constructor
        exact WT
      . rel_trans
        . apply mstep.fst
          apply mstep.pair1
          exact Hstep1
        rel_trans
        . apply mstep.fst
          apply mstep.pair2
          . exact Hv1
          . exact Hstep2
        . rtcl_incl
          apply Tm.step.fstPair
          . exact Hv1
          . exact Hv2
      . apply Tm.mstep.preserves_R
        . exact Hstep1
        . exact IH1'
    . apply Tm.mstep.preserves_R'
      . constructor
        exact WT
      . rel_trans
        . apply mstep.snd
          apply mstep.pair1
          exact Hstep1
        rel_trans
        . apply mstep.snd
          apply mstep.pair2
          . exact Hv1
          . exact Hstep2
        . rtcl_incl
          apply Tm.step.sndPair
          . exact Hv1
          . exact Hv2
      . apply Tm.mstep.preserves_R
        . exact Hstep2
        . exact IH2'



theorem Tm.msubst_R (c: TyAsgmt) env t T:
  ty{ Context.empty.mupdate c |- [t]: [T]} ->
  c.Instantiate env ->
  T.R (env.msubst t)
:= by
  apply msubst_R_lemma
  intro x
  symm
  apply mupdate_lookup


theorem Tm.normalization {t: Tm} {T}:
  ty{ [] |- [t]: [T]} -> t.halts
:= by
  have E: t = Env.msubst [] t := by
    simp
  rewrite [E]
  clear E
  intro Ht
  apply Ty.R.halts
  apply msubst_R [] []
  . simp at *
    assumption
  . constructor

end Normalize
