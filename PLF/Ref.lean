/-
Mutable reference
-/
import PLF.Relation
import PLF.Map
import PLF.SyntaxCat


namespace STLCRef

inductive Ty where
  | Nat: Ty
  | Unit: Ty
  | Arrow: Ty -> Ty -> Ty
  | Ref: Ty -> Ty
  deriving Repr


inductive Tm where
  | Var: String -> Tm
  | App: Tm -> Tm -> Tm
  | Abs: String -> Ty -> Tm -> Tm
  -- for sequent expression
  | Seq: Tm -> Tm -> Tm
  | Const : Nat -> Tm
  | Succ : Tm -> Tm
  | Pred : Tm -> Tm
  | Mult : Tm -> Tm -> Tm
  | If0 : Tm -> Tm -> Tm -> Tm
  -- new terms
  | Unit : Tm
  | Ref : Tm -> Tm
  | Deref : Tm -> Tm
  | Assign : Tm -> Tm -> Tm
  | Loc : Nat -> Tm
  deriving Repr


instance: Coe String Tm where
  coe := .Var


instance: Coe Nat Tm where
  coe := .Const


-- syntax
-- type
declare_syntax_cat plf_stlc_ref_ty (behavior := symbol)

scoped syntax "[ty| " plf_stlc_ref_ty " ]": term
scoped syntax:100 "(" plf_stlc_ref_ty ")": plf_stlc_ref_ty
scoped syntax:1 plf_stlc_ref_ty " -> " plf_stlc_ref_ty : plf_stlc_ref_ty
scoped syntax:100 "[" term "]": plf_stlc_ref_ty
scoped syntax "Nat": plf_stlc_ref_ty
scoped syntax "Unit": plf_stlc_ref_ty
scoped syntax:96 "Ref" plf_stlc_ref_ty:96: plf_stlc_ref_ty

scoped macro_rules
  | `([ty| ($t:plf_stlc_ref_ty) ]) => `([ty| $t ])
  | `([ty| $s -> $t ]) => `(Ty.Arrow [ty| $s ] [ty| $t ])
  | `([ty| [ $t ] ]) => `($t)
  | `([ty| Nat ]) => `(Ty.Nat)
  | `([ty| Unit ]) => `(Ty.Unit)
  | `([ty| Ref $x ]) => `(Ty.Ref [ty| $x])

-- pretty print
@[app_unexpander Ty.Nat]
def unexpandNat: Lean.PrettyPrinter.Unexpander
  | `($_) => `([ty| Nat ])

@[app_unexpander Ty.Unit]
def unexpandTyUnit: Lean.PrettyPrinter.Unexpander
  | `($_) => `([ty| Unit ])

@[app_unexpander Ty.Arrow]
def unexpandArrow: Lean.PrettyPrinter.Unexpander
  | `($_ [ty| $a1 -> $a2] [ty|$b]) => `([ty| ($a1 -> $a2) -> $b ])
  | `($_ [ty|$a] [ty|$b]) => `([ty| $a -> $b ])
  | _ => throw ()

@[app_unexpander Ty.Ref]
def unexpandTyRef: Lean.PrettyPrinter.Unexpander
  | `($_ [ty| $a -> $b]) => `([ty| Ref ($a -> $b) ])
  | `($_ [ty| $ty]) => `([ty| Ref $ty ])
  | _ => throw ()

-- term
declare_syntax_cat plf_stlc_ref_tm (behavior := symbol)
-- interpret the syntax
scoped syntax "[tm| " plf_stlc_ref_tm " ]": term
-- priority
scoped syntax:100 "(" plf_stlc_ref_tm ")": plf_stlc_ref_tm
-- meta expression
scoped syntax "[" term "]": plf_stlc_ref_tm
-- λ-calculus
-- variable
scoped syntax ident: plf_stlc_ref_tm
-- application
scoped syntax:90 plf_stlc_ref_tm:90 plf_stlc_ref_tm:91 : plf_stlc_ref_tm
-- abstraction
scoped syntax:0 "λ" ident " : " plf_stlc_ref_ty ", " plf_stlc_ref_tm: plf_stlc_ref_tm
scoped syntax:0 "λ" "[" term "]" " : " plf_stlc_ref_ty ", " plf_stlc_ref_tm: plf_stlc_ref_tm
scoped syntax:10 plf_stlc_ref_tm:10 "; " plf_stlc_ref_tm:10 : plf_stlc_ref_tm

-- -- arithmetic
scoped syntax num : plf_stlc_ref_tm
scoped syntax:90 "succ" plf_stlc_ref_tm:100 : plf_stlc_ref_tm
scoped syntax:90 "pred" plf_stlc_ref_tm:100 : plf_stlc_ref_tm
scoped syntax:90 plf_stlc_ref_tm " * " plf_stlc_ref_tm : plf_stlc_ref_tm
scoped syntax:11 "if0" plf_stlc_ref_tm:5 "then" plf_stlc_ref_tm:5 "else" plf_stlc_ref_tm:5: plf_stlc_ref_tm
-- unit
scoped syntax "unit": plf_stlc_ref_tm
-- ref
scoped syntax:98 "ref " plf_stlc_ref_tm: plf_stlc_ref_tm
scoped syntax:98 "loc " term: plf_stlc_ref_tm
-- dref
scoped syntax:98 "!" plf_stlc_ref_tm: plf_stlc_ref_tm
-- assign
scoped syntax:79 plf_stlc_ref_tm ":=" plf_stlc_ref_tm: plf_stlc_ref_tm


scoped macro_rules
  -- priority and meta variables
  | `([tm| ($t:plf_stlc_ref_tm) ]) => `([tm| $t ])
  | `([tm| [ $t ] ]) => `((($t): Tm))
  -- λ-calculus
  | `([tm| $x:ident ]) => `(Tm.Var $(Lean.quote (toString x.getId)))
  | `([tm| $x $y ]) => `(Tm.App [tm| $x ] [tm| $y ])
  | `([tm| λ $x : $t, $b ]) => `(Tm.Abs $(Lean.quote (toString x.getId)) [ty| $t ] [tm| $b ])
  | `([tm| λ [$x]: $t, $b ]) => `(Tm.Abs $x [ty| $t ] [tm| $b ])
  -- sequence is a special case of abstraction
  | `([tm| $t1 ; $t2 ]) => `(Tm.Seq [tm|$t1] [tm|$t2])
  -- arithmetic
  | `([tm| $x:num]) => `(Tm.Const $x)
  | `([tm| succ $x ]) => `(Tm.Succ [tm| $x ])
  | `([tm| pred $x ]) => `(Tm.Pred [tm| $x ])
  | `([tm| $x * $y ]) => `(Tm.Mult [tm| $x ] [tm| $y ])
  | `([tm| if0 $c then $t else $f ]) => `(Tm.If0 [tm| $c ] [tm| $t ] [tm| $f ])
  -- unit
  | `([tm| unit ]) => `(Tm.Unit)
  -- ref
  | `([tm| loc $x ]) => `(Tm.Loc $x)
  | `([tm| ref $x ]) => `(Tm.Ref [tm| $x ])
  | `([tm| ! $x ]) => `(Tm.Deref [tm| $x ])
  | `([tm| $x := $e ]) => `(Tm.Assign [tm| $x] [tm| $e ])

-- pretty print
instance : Coe Lean.NumLit (Lean.TSyntax `plf_stlc_ref_tm) where
  coe s := ⟨s.raw⟩

instance : Coe Lean.Ident (Lean.TSyntax `plf_stlc_ref_tm) where
  coe s := ⟨s.raw⟩

@[app_unexpander Tm.Var]
def unexpandVar: Lean.PrettyPrinter.Unexpander
  | `($_ $x:str) =>
    let name := Lean.mkIdent (Lean.Name.mkStr1 x.getString)
    `([tm| $name ])
  | `($_ $x:term) => `([tm| [$x] ])
  | _ => throw ()

@[app_unexpander Tm.App]
def unexpandApp: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $a] [tm| $b1 $b2 ]) => `([tm| $a ($b1 $b2) ])
  | `($_ [tm| λ $x:ident : $T, $a] [tm| $b ]) => `([tm| (λ $x : $T, $a) $b ])
  | `($_ [tm| λ [$x]: $T, $a] [tm| $b ]) => `([tm| (λ [$x]: $T, $a) $b ])
  | `($_ [tm| $a ] [tm| $b ]) => `([tm| $a $b ])
  | _ => throw ()


@[app_unexpander Tm.Abs]
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


@[app_unexpander Tm.Seq]
def unexpandSeq: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $a ] [tm| $b ]) => `([tm| $a; $b])
  | _ => throw ()

@[app_unexpander Tm.Const]
def unexpandConst: Lean.PrettyPrinter.Unexpander
  | `($_ $x:num) => `([tm| $x ])
  | _ => throw ()


@[app_unexpander Tm.Succ]
def unexpandSucc: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| (succ $x) ])
  | _ => throw ()


@[app_unexpander Tm.Pred]
def unexpandPred: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| (pred $x) ])
  | _ => throw ()


@[app_unexpander Tm.Mult]
def unexpandMult: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x] [tm| $y]) => `([tm| $x * $y ])
  | _ => throw ()


@[app_unexpander Tm.If0]
def unexpandIf0: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $c] [tm| $t] [tm| $f]) => `([tm| if0 ($c) then ($t) else ($f) ])
  | _ => throw ()

@[app_unexpander Tm.Unit]
def unexpandTmUnit: Lean.PrettyPrinter.Unexpander
  | `($_) => `([tm| unit ])


@[app_unexpander Tm.Ref]
def unexpandTmRef: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| ref $x ])
  | _ => throw ()


@[app_unexpander Tm.Deref]
def unexpandDeref: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x]) => `([tm| ! $x ])
  | _ => throw ()


@[app_unexpander Tm.Loc]
def unexpandLoc: Lean.PrettyPrinter.Unexpander
  | `($_ $x) => `([tm| (loc $x) ])
  | _ => throw ()


@[app_unexpander Tm.Assign]
def unexpandAssign: Lean.PrettyPrinter.Unexpander
  | `($_ [tm| $x] [tm| $y]) => `([tm| $x := $y ])
  | `($_ $x [tm| $y]) => `([tm| [$x] := $y ])
  | `($_ [tm| $x] $y:term) => `([tm| $x := [$y] ])
  | `($_ $x:term $y:term) => `([tm| [$x] := [$y] ])
  | _ => throw ()


-- values
inductive Tm.Value: Tm -> Prop where
  | Abs {x: String} {T: Ty} {b: Tm}: Tm.Value [tm| λ [x]: [T], [b]]
  | Nat {n: Nat}: Tm.Value [tm| [n] ]
  | Unit: Tm.Value [tm| unit ]
  | Loc {l: Nat}: Tm.Value [tm| loc l]


@[simp]
def Tm.subst (t: Tm) (x: String) (s: Tm): Tm :=
  match t with
  -- λ-calculus
  | .Var y =>
    if x == y then s else t
  | .Abs y T b =>
    if x == y then t else .Abs y T (b.subst x s)
  | .Seq s1 s2 =>
    .Seq (s1.subst x s) (s2.subst x s)
  | .App t1 t2 =>
    .App (t1.subst x s) (t2.subst x s)
  -- arithmetic
  | .Const _ => t
  | .Succ t1 => (t1.subst x s).Succ
  | .Pred t1 => (t1.subst x s).Pred
  | .Mult t1 t2 => (t1.subst x s).Mult (t2.subst x s)
  | .If0 t1 t2 t3 => .If0 (t1.subst x s) (t2.subst x s) (t3.subst x s)
  -- unit
  | .Unit => .Unit
  -- references
  | .Ref t1 => .Ref (t1.subst x s)
  | .Deref t1 => .Deref (t1.subst x s)
  | .Assign y e => .Assign (y.subst x s) (e.subst x s)
  | .Loc _ => t


declare_syntax_cat subst_cat
scoped syntax "subst[ " my_ident " := " plf_stlc_ref_tm " ] ": subst_cat

scoped syntax subst_cat: plf_stlc_ref_tm

scoped macro_rules
  | `([tm| subst[ $x:my_ident := $s:plf_stlc_ref_tm ] $t ]) =>
    `(Tm.subst [tm| $t ] [ident| $x ] [tm| $s])

@[app_unexpander Tm.subst]
def unexpandSubst: Lean.PrettyPrinter.Unexpander
  | `($_subst [tm| $t] $x:str [tm| $s ]) =>
    let ident := Lean.mkIdent (Lean.Name.mkSimple x.getString)
    `([tm| (subst[ $ident:ident := $s] $t ) ])
  | `($_subst [tm| $t] $x:term [tm| $s ]) => `([tm| (subst[ [$x] := $s] $t ) ])
  | `($_subst $t $x:term $s) => `([tm| (subst[ [$x] := [$s]] [$t] ) ])
  | _ => throw ()


abbrev Store := List Tm
abbrev Store.lookup (s: Store) (i: Nat): Tm := List.getD s i .Unit
abbrev Store.replace (s: Store) (i: Nat) (v: Tm): Store := List.set s i v


theorem Store.replace_nil {i v}: Store.replace [] i v = [] := List.set_nil
theorem Store.relpace_eq {s: Store} {i: Nat} {v: Tm}:
  i < s.length -> (s.replace i v).lookup i = v
:= by
  intro H
  unfold replace
  unfold lookup
  rewrite [List.getD_eq_getElem?_getD]
  rewrite [List.getD_getElem?]
  simp
  intro K
  omega

theorem Store.replace_neq {s: Store} {i1 i2: Nat} {v}:
  i1 != i2 ->
  (s.replace i2 v).lookup i1 = s.lookup i1
:= by
  intro H
  unfold replace
  unfold lookup
  repeat rewrite [List.getD_eq_getElem?_getD]
  repeat rewrite [List.getD_getElem?]
  simp
  split
  . apply List.getElem_set_ne
    simp at *
    solve_by_elim
  . eq_refl


inductive Tm.step: Relation (Tm × Store) where
  -- lambda calculus
  | AppAbs {x T} {b v: Tm} {st}:
    v.Value -> Tm.step ([tm| (λ [x]: [T], [b]) [v] ], st) (b.subst x v, st)
  | App1 {t1 t2 s} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (.App t1 s, st1) (.App t2 s, st2)
  | App2 {v n1 n2: Tm} {st1 st2}:
    v.Value ->
    Tm.step (n1, st1) (n2, st2) ->
    Tm.step (.App v n1, st1) (.App v n2, st2)
  -- sequence is a special case of application
  | Seq1 {t1 t2 s: Tm} {st1 st2}:  -- equivalent to App2
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (.Seq t1 s, st1) (.Seq t2 s, st2)
  | Seq2 {v b: Tm} {st}: -- the same as [tm|(λ _: Unit, [t_2]) [t_1]]
    v.Value ->
    Tm.step (.Seq v b, st) (b, st)
  -- arithmetic
  | SuccNat {n: Nat} {st}:
    Tm.step ([tm| succ [n]], st) (n.succ, st)
  | Succ {t1 t2} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Succ, st1) (t2.Succ, st2)
  | PredNat {n: Nat} {st}:
    Tm.step ([tm| pred [n]], st) (n.pred, st)
  | Pred {t1 t2} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Pred, st1) (t2.Pred, st2)
  | MultNats {n1 n2: Nat} {st}:
    Tm.step ([tm| [n1] * [n2]], st) (n1 * n2, st)
  | Mult1 {t1 t2 s: Tm} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Mult s, st1) (t2.Mult s, st2)
  | Mult2 {v t1 t2: Tm} {st1 st2}:
    v.Value ->
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (v.Mult t1, st1) (v.Mult t2, st2)
  | If0 {c1 c2 t f: Tm} {st1 st2}:
    Tm.step (c1, st1) (c2, st2) ->
    Tm.step (c1.If0 t f, st1) (c2.If0 t f, st2)
  | If0Zero {t f st}:
    Tm.step ([tm| if0 0 then [t] else [f]], st) (t, st)
  | If0NonZero {n: Nat} {t f st}:
    Tm.step ([tm| if0 [n.succ] then [t] else [f]], st) (f, st)
  -- reference
  | RefValue {v: Tm} {st}:
    v.Value -> Tm.step (v.Ref, st) (.Loc st.length, st ++ [v])
  | Ref {t1 t2 st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Ref, st1) (t2.Ref, st2)
  | DerefLoc {st: Store} {i}:
    i < st.length -> Tm.step ([tm| !loc i ], st) (st.lookup i, st)
  | Deref {t1 t2} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Deref, st1) (t2.Deref, st2)
  | Assign {v: Tm} {i} {st: Store}:
    v.Value ->
    i < st.length ->
    Tm.step ([tm| (loc i) := [v]], st) (.Unit, st.replace i v)
  | Assign1 {t1 t2 s} {st1 st2}:
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (t1.Assign s, st1) (t2.Assign s, st2)
  | Assign2 {v t1 t2: Tm} {st1 st2}:
    v.Value ->
    Tm.step (t1, st1) (t2, st2) ->
    Tm.step (v.Assign t1, st1) (v.Assign t2, st2)


scoped macro "step[" t1:plf_stlc_ref_tm "/" st1:term "]->[" t2:plf_stlc_ref_tm "/" st2:term "]": term
  => `(Tm.step ([tm| $t1 ], $st1) ([tm| $t2 ], $st2))


abbrev Tm.mstep := RTCl Tm.step
scoped macro "mstep[" t1:plf_stlc_ref_tm "/" st1:term "]->[" t2:plf_stlc_ref_tm "/" st2:term "]": term
  => `(Tm.mstep ([tm| $t1 ], $st1) ([tm| $t2 ], $st2))

example: mstep[unit / [] ]->[ unit / []] := by
  apply RTCl.refl


abbrev Context := PartialMap Ty
def Context.empty := PartialMap.empty (A := Ty)

declare_syntax_cat plf_stlc_ref_context (behavior := symbol)
syntax "[]": plf_stlc_ref_context
syntax term: plf_stlc_ref_context
syntax my_ident " : " plf_stlc_ref_ty: plf_stlc_ref_context
syntax plf_stlc_ref_context ", " plf_stlc_ref_context: plf_stlc_ref_context
syntax "[ctx| " plf_stlc_ref_context " ]": term

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


instance : Coe Lean.Term (Lean.TSyntax `plf_stlc_ref_context) where
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


-- cyclic store
theorem Tm.cyclic_store:
  ∃ t, mstep[ [t] / [] ]->[ unit / [
    [tm| λ x: Nat, (!(loc 1)) x ],
    [tm| λ x: Nat, (!(loc 0)) x ]
  ] ]
:= by
  exists [tm|
    (ref λ x: Nat, (!(loc 1)) x) ;
    (ref λ x: Nat, (!(loc 0)) x) ;
    unit
  ]
  rel_trans
  . rtcl_incl
    apply Tm.step.Seq1
    apply Tm.step.RefValue
    constructor
  rel_trans
  . rtcl_incl
    apply Tm.step.Seq2
    constructor
  rel_trans
  . rtcl_incl
    apply Tm.step.Seq1
    apply Tm.step.RefValue
    constructor
  . rtcl_incl
    apply Tm.step.Seq2
    constructor


abbrev StoreTy := List Ty
abbrev StoreTy.lookup (s: StoreTy) (i: Nat): Ty := List.getD s i .Unit
abbrev StoreTy.replace (s: StoreTy) (i: Nat) (v: Ty): StoreTy := List.set s i v

inductive StoreTy.has_type (ST: StoreTy): Context -> Tm -> Ty -> Prop where
  | Var {Gamma: Context} {x T}:
    Gamma x = .some T ->
    ST.has_type Gamma x T
  | Abs {Gamma: Context} {x M A B}:
    ST.has_type map![x => A; Gamma] M B ->
    ST.has_type Gamma [tm| λ [x]: [A], [M]] (.Arrow A B)
  | App {Gamma A B f x}:
    ST.has_type Gamma f (A.Arrow B) ->
    ST.has_type Gamma x A ->
    ST.has_type Gamma (f.App x) B
  | Seq {Gamma A B t1 t2}:
    ST.has_type Gamma t1 A ->
    ST.has_type Gamma t2 B ->
    ST.has_type Gamma (t1.Seq t2) B
  | Nat {Gamma} {n: Nat}:
    ST.has_type Gamma (.Const n) .Nat
  | Succ {Gamma t}:
    ST.has_type Gamma t .Nat ->
    ST.has_type Gamma t.Succ .Nat
  | Pred {Gamma t}:
    ST.has_type Gamma t .Nat ->
    ST.has_type Gamma t.Pred .Nat
  | Mult {Gamma t1 t2}:
    ST.has_type Gamma t1 .Nat ->
    ST.has_type Gamma t2 .Nat ->
    ST.has_type Gamma (t1.Mult t2) .Nat
  | If0 {Gamma c t f T}:
    ST.has_type Gamma c .Nat ->
    ST.has_type Gamma t T ->
    ST.has_type Gamma f T ->
    ST.has_type Gamma (.If0 c t f) T
  | Unit {Gamma}:
    ST.has_type Gamma .Unit .Unit
  | Loc {Gamma i T}:
    i < ST.length ->
    T = ST.lookup i ->
    ST.has_type Gamma (.Loc i) (.Ref T)
  | Ref {Gamma t T}:
    ST.has_type Gamma t T ->
    ST.has_type Gamma (.Ref t) (.Ref T)
  | Deref {Gamma t T}:
    ST.has_type Gamma t (.Ref T) ->
    ST.has_type Gamma t.Deref T
  | Assign {Gamma t1 t2 T}:
    ST.has_type Gamma t1 (.Ref T) ->
    ST.has_type Gamma t2 T ->
    ST.has_type Gamma (.Assign t1 t2) .Unit

scoped macro "ty{ " G:plf_stlc_ref_context " // " st:term " |- " t:plf_stlc_ref_tm " : " T:plf_stlc_ref_ty " }": term
  => `(StoreTy.has_type $st [ctx| $G ] [tm| $t ] [ty| $T ])


@[app_unexpander StoreTy.has_type]
def unexpandhas_type: Lean.PrettyPrinter.Unexpander
  | `($_ $st [ctx| $G ] [tm| $t ] [ty| $T ]) => `(ty{ $G // $st |- $t : $T})
  | `($_ $st [ctx| $G ] [tm| $t ] $T) => `(ty{ $G // $st |- $t : [$T]})
  | `($_ $st [ctx| $G ] $t [ty| $T]) => `(ty{ $G // $st |- [$t] : $T})
  | `($_ $st [ctx| $G ] $t $T) => `(ty{ $G // $st |- [$t] : [$T]})
  | `($_ $st $G [tm| $t ] [ty| $T ]) => `(ty{ $G // $st |- $t : $T})
  | `($_ $st $G $t [ty| $T ]) => `(ty{ $G // $st |- [$t] : $T})
  | `($_ $st $G [tm| $t] $T) => `(ty{ $G // $st |- $t : [$T]})
  | `($_ $st $G $t $T) => `(ty{ $G // $st |- [$t] : [$T]})
  | _ => throw ()


def StoreTy.well_typed (ST: StoreTy) (st: Store) :=
  st.length = ST.length ∧ (
    forall i, i < st.length ->
      ty{ [] // ST |- [st.lookup i] : [ST.lookup i] }
  )


theorem StoreTy.not_unique:
  ∃ st, ∃ (ST1 ST2: StoreTy),
    ST1.well_typed st ∧
    ST2.well_typed st ∧
    ST1 ≠ ST2
:= by
  let st := [[tm| !loc 0]]
  let ST1 := [[ty| Unit]]
  let ST2 := [[ty| Nat]]
  exists st
  exists ST1
  exists ST2
  apply And.intro
  . -- ST1.well_typed st
    apply And.intro
    . simp [st, ST1]
    . simp [st, ST1] at * <;>
        solve_by_elim
  apply And.intro
  . -- ST2.well_typed st
    apply And.intro
    . simp [st, ST2]
    . simp [st, ST2] at *
      constructor
      constructor
      simp
      simp
  . -- ST1 ≠ ST2
    simp [ST1, ST2]


inductive StoreTy.Extends : StoreTy -> StoreTy -> Prop where
  | nil {ST: StoreTy}: ST.Extends .nil
  | cons {x} {ST1 ST2: StoreTy}:
    ST1.Extends ST2 ->
    StoreTy.Extends (x::ST1) (x::ST2)


theorem StoreTy.extends_lookup {i} {ST1 ST2: StoreTy}:
  i < ST1.length ->
  ST2.Extends ST1 ->
  ST1.lookup i = ST2.lookup i
:= by
  induction ST1 generalizing i ST2 with
  | nil =>
    simp
  | cons x xs IH =>
    intro Hlen HST2
    cases ST2 with
    | nil =>
      cases HST2
    | cons y ys =>
      cases HST2 with | cons H =>
      cases i with
      | zero =>
        simp
      | succ n =>
        simp at Hlen
        specialize (IH Hlen H)
        simp at *
        exact IH


theorem StoreTy.length_extends {i} {ST1 ST2: StoreTy}:
  i < ST1.length ->
  ST2.Extends ST1 ->
  i < ST2.length
:= by
  induction ST1 generalizing i ST2 with
  | nil =>
    simp
  | cons x xs IH =>
    intro Hlen Hext
    cases i with
    | zero =>
      cases Hext with | cons H =>
      simp
    | succ n =>
      simp at *
      cases Hext with | cons H =>
      simp at *
      apply IH
      . exact Hlen
      . assumption


theorem StoreTy.app_extends {ST T: StoreTy}:
  (ST ++ T).Extends ST
:= by
  induction ST with
  | nil =>
    simp
    constructor
  | cons x xs IH =>
    constructor
    exact IH


instance: Reflexive StoreTy.Extends where
  refl := by
    intro ST
    induction ST with
    | nil =>
      constructor
    | cons x xs IH =>
      constructor
      exact IH


@[refl]
theorem StoreTy.extends_refl {ST: StoreTy}:
  ST.Extends ST
:= by
  rel_refl


-- Now, we can prove the preservation theorem.
theorem Tm.weakening {Gamma1 Gamma2: Context} {ST t T}:
  Gamma1.included_in Gamma2 ->
  ty{ Gamma1 // ST |- [t]: [T] } ->
  ty{ Gamma2 // ST |- [t]: [T] }
:= by
  intro Hinc Ht
  induction Ht generalizing Gamma2 with
  | _ =>
    constructor <;>
      solve_by_elim [PartialMap.included_in_update]

theorem Tm.weakening_empty {Gamma: Context} {ST t T}:
  ty{ [] // ST |- [t]: [T] } ->
  ty{ Gamma // ST |- [t]: [T] }
:= by
  apply Tm.weakening
  simp [Context.empty]


theorem Tm.subst_preserves_typing {Gamma ST x U t v T}:
  ty{ [x]: [U], Gamma // ST |- [t]: [T]} ->
  ty{ [] // ST |- [v]: [U] } ->
  ty{ Gamma // ST |- (subst[ [x] := [v] ] [t]): [T] }
:= by
  intro Ht Hv
  induction t generalizing Gamma T with
  | Var y =>
    cases Ht with | Var Ht =>
    simp
    split
    . /- x = y -/
      subst_eqs
      simp at *
      rewrite [Ht] at Hv
      apply Tm.weakening_empty
      assumption
    . /- x ≠ y -/
      next Hne =>
      have Hne: ¬ y = x := by
        solve_by_elim
      constructor
      simp [Hne] at *
      exact Ht
  | Abs y A b IHb =>
    cases Ht with | Abs Hb =>
    simp
    split
    . /- x = y -/
      subst_eqs
      constructor
      apply weakening _ Hb
      rewrite [PartialMap.update_shadow]
      simp
    . /- x ≠ y -/
      next Hne =>
      constructor
      apply IHb
      rewrite [PartialMap.update_permute Hne]
      exact Hb
  | App | Seq
  | Const | Pred | Succ | Mult | If0
  | Unit
  | Ref | Deref | Loc | Assign =>
    cases Ht <;>
    constructor <;>
      solve_by_elim


theorem Tm.assign_pres_store_typing {ST: StoreTy} {st i t}:
  i < ST.length ->
  ST.well_typed st ->
  ty{ [] // ST |- [t]: [ST.lookup i]} ->
  ST.well_typed (st.replace i t)
:= by
  intro Hlen HST Ht
  unfold StoreTy.well_typed
  apply And.intro
  . /- length -/
    simp
    simp [HST.left]  -- the equality
  . /- typing -/
    have H := HST.right
    intro j Hj
    simp at Hj
    cases Nat.decEq i j with
    | isTrue E =>
      subst_eqs
      rewrite [Store.relpace_eq Hj]
      exact Ht
    | isFalse NE =>
      rewrite [Store.replace_neq]
      . apply H
        exact Hj
      . simp
        solve_by_elim

theorem Store.weakening {Gamma} {ST1 ST2: StoreTy} {t T}:
  ST2.Extends ST1 ->
  ty{ Gamma // ST1 |- [t]: [T] } ->
  ty{ Gamma // ST2 |- [t]: [T] }
:= by
  intro HExt HT
  induction HT with
  | Var | Abs | App | Seq
  | Nat | Pred | Succ | Mult | If0
  | Unit | Ref | Deref | Assign =>
    solve_by_elim
  | Loc =>
    rewrite [StoreTy.extends_lookup] at * <;>
      solve_by_elim [StoreTy.length_extends]


theorem Store.well_typed_app {ST: StoreTy} {st t T}:
  ST.well_typed st ->
  ty{ [] // ST |- [t]: [T]} ->
  (ST ++ [T]).well_typed (st ++ [t])
:= by
  intro HST Ht
  let ⟨Hlen, HST⟩ := HST
  unfold StoreTy.well_typed
  apply And.intro
  . simp
    exact Hlen
  . intro i Hi
    simp at Hi
    let Hle := Nat.le_of_lt_succ Hi
    generalize E: st.length = j
    rewrite [E] at Hle
    cases Hle with
    | refl =>
      have EST: ST.length = i := by
        rewrite [<-Hlen]
        assumption
      simp [E, EST]
      apply Store.weakening
      . apply StoreTy.app_extends
      . exact Ht
    | step Hle =>
      have H1: i < st.length := by
        rewrite [E]
        apply Nat.lt_succ_of_le
        assumption
      have H2: i < ST.length := by
        rewrite [<-Hlen]
        exact H1
      simp
      rewrite [List.getElem?_append_left H1]
      rewrite [List.getElem?_append_left H2]
      simp [H1, H2]
      specialize HST i H1
      apply Store.weakening
      . apply StoreTy.app_extends
      . simp [H1, H2] at HST
        assumption


theorem split_and3 {A B C}: A -> B -> C -> A ∧ B ∧ C := by
  intro a b c
  solve_by_elim


macro "split_and3": tactic => `(tactic| apply split_and3)


theorem Tm.preservation {ST1: StoreTy} {t1 t2 T st1 st2}:
  ty{ [] // ST1 |- [t1]: [T]} ->
  ST1.well_typed st1 ->
  step[[t1] / st1]->[[t2] / st2] ->
  exists ST2: StoreTy,
    ST2.Extends ST1 ∧
    ty{ [] // ST2 |- [t2]: [T]} ∧
    ST2.well_typed st2
:= by
  intro Ht
  generalize E: [ctx| []] = G
  rewrite [E] at Ht
  induction Ht
    generalizing t2
  with (
      rewrite [<-E]
      intro HST Hstep
      let ⟨Hlen, HST'⟩ := HST
    )
  | Var | Abs | Nat | Unit | Loc =>
    contradiction
  | App H1 H2 IH1 IH2 =>
    rewrite [<-E] at H1 IH1
    rewrite [<-E] at H2 IH2
    cases Hstep with
    | AppAbs =>
      exists ST1
      split_and3
      . rfl
      . cases H1
        solve_by_elim [subst_preserves_typing]
      . assumption
    | App1 | App2 =>
      try next Hstep =>
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH1 (Eq.refl _) HST Hstep
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH2 (Eq.refl _) HST Hstep
      constructor
      split_and3
      . solve_by_elim [Relation.refl, Store.weakening, StoreTy.app_extends]
      . (try assumption) <;>
        constructor <;>
        solve_by_elim [Store.weakening]
      . solve_by_elim [Store.well_typed_app]
  | Seq H1 H2 IH1 IH2
  | Pred H1 IH1 | Succ H1 IH1 | Mult H1 H2 IH1 IH2
  | If0 H1 H2 H3 IH1 IH2 IH3 =>
    rewrite [<-E] at H1 IH1
    try rewrite [<-E] at H2 IH2
    try rewrite [<-E] at H3 IH3
    cases Hstep <;>
      try next Hstep =>
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH1 (Eq.refl _) HST Hstep
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH2 (Eq.refl _) HST Hstep
      constructor <;> (
        split_and3
        . solve_by_elim [Relation.refl, Store.weakening, StoreTy.app_extends]
        . (try assumption) <;>
          constructor <;>
          solve_by_elim [Store.weakening]
        . solve_by_elim [Store.well_typed_app]
      )
  | Ref H1 IH1 =>
    rewrite [<-E] at H1 IH1
    cases Hstep with
    | Ref =>
      next Hstep =>
      let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH1 (Eq.refl _) HST Hstep
      constructor
      split_and3 <;>
        solve_by_elim [Relation.refl]
    | RefValue =>
      next t T Hval =>
      exists ST1 ++ [T]
      split_and3
      . solve_by_elim [StoreTy.app_extends]
      . rewrite [Hlen]
        constructor
        . simp
        . simp
      . solve_by_elim [Store.well_typed_app]
  | Deref H1 IH1 =>
    rewrite [<-E] at H1 IH1
    cases Hstep with
    | Deref =>
      next Hstep =>
      let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH1 (Eq.refl _) HST Hstep
      constructor
      split_and3 <;>
        solve_by_elim [Relation.refl]
    | DerefLoc =>
      exists ST1
      split_and3
      . rel_refl
      . cases H1
        subst_eqs
        solve_by_elim
      . assumption
  | Assign H1 H2 IH1 IH2 =>
    next T =>
    simp [<-E, HST] at H1 H2 IH1 IH2
    cases Hstep with
    | @Assign v i _ Hv Hi =>
      cases H1
      next HT =>
      exists ST1
      split_and3
      . rel_refl
      . constructor
      . and_intros
        . simp [Hlen]
        . intro j Hj
          cases Nat.decEq i j with
          | isTrue E =>
            rewrite [<-E]
            rewrite [Store.relpace_eq]
            . rewrite [<-HT]
              exact H2
            . assumption
          | isFalse NE =>
            rewrite [Store.replace_neq]
            . simp at Hj
              solve_by_elim
            . simp
              solve_by_elim
    | Assign1 | Assign2 =>
      next Hstep =>
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH1 Hstep
      try let ⟨ST2, ⟨H1, ⟨H2, H3⟩⟩⟩ := IH2 Hstep
      constructor
      split_and3
      . assumption
      . constructor <;>
        solve_by_elim [Store.weakening]
      . assumption


theorem Tm.progress {ST t T st}:
  ty{ [] // ST |- [t]: [T]} ->
  ST.well_typed st ->
  (t.Value ∨ ∃ t' st', step[[t] / st]->[ [t'] / st' ])
:= by
  generalize E: [ctx| [] ] = Gamma
  intro Ht HST
  induction Ht with (
    subst E
  )
  | Var =>
    contradiction
  | Nat | Unit | Loc | Abs  =>
    left
    constructor
  | App H1 H2 IH1 IH2 =>
    simp at *
    right
    cases IH1 with
    | inl H =>
      cases H <;> try contradiction
      cases IH2 with
      | inl =>
        constructor <;> solve_by_elim
      | inr H =>
        let ⟨t', ⟨st', Hstep⟩⟩ := H
        constructor; constructor
        apply Tm.step.App2
        . constructor
        . exact Hstep
    | inr =>
      next H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Seq H1 H2 IH1 IH2 => -- should be the same as App
    simp at *
    right
    cases IH1 with
    | inl H =>
      constructor; constructor
      apply Tm.step.Seq2
      exact H
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Succ H IH | Pred H IH =>
    simp at *
    right
    cases IH with
    | inl H =>
      cases H <;> try contradiction
      repeat constructor
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Mult H1 H2 IH1 IH2 =>
    simp at *
    right
    cases IH1 with
    | inl H =>
      cases H <;> try contradiction
      cases IH2 with
      | inl H =>
        cases H <;> try contradiction
        constructor <;> solve_by_elim
      | inr H =>
        let ⟨t', ⟨st', Hstep⟩⟩ := H
        constructor <;> solve_by_elim [Tm.step.Mult2]
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | If0 Hc Ht Hf IHc IHt IHf =>
    simp at *
    right
    cases IHc with
    | inl H =>
      cases H <;> try contradiction
      next n =>
      cases n with
      | zero =>
        constructor; constructor
        apply Tm.step.If0Zero
      | succ m =>
        constructor; constructor
        apply Tm.step.If0NonZero
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Ref H IH =>
    simp at *
    right
    cases IH with
    | inl H =>
      cases H <;>
        repeat constructor
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Deref H IH =>
    simp at *
    right
    cases IH with
    | inl H =>
      cases H <;> try contradiction
      cases H
      constructor; constructor
      apply Tm.step.DerefLoc
      simp [HST.left]
      assumption
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim
  | Assign H1 H2 IH1 IH2 =>
    simp at *
    right
    cases IH1 with
    | inl H =>
      cases H <;> try contradiction
      cases H1
      cases IH2 with
      | inl H =>
        constructor; constructor
        apply Tm.step.Assign
        . exact H
        . simp [HST.left]
          assumption
      | inr H =>
        let ⟨t', ⟨st', Hstep⟩⟩ := H
        constructor; constructor
        apply Tm.step.Assign2
        . constructor
        . assumption
    | inr H =>
      let ⟨t', ⟨st', Hstep⟩⟩ := H
      constructor <;> solve_by_elim

end STLCRef
