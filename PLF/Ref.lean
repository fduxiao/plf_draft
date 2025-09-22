/-
Mutable reference
-/
import PLF.Relation
import PLF.Map


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
  | `($_ $x:term [ty| $T ] [tm| $b ]) => `([tm| λ [$x] : $T, $b ])
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


scoped macro "subst" t:term "[" x:ident ":=" v:plf_stlc_ref_tm "]": term =>
  `(Tm.subst $t $(Lean.quote (toString x.getId)) [tm| $v ])
scoped macro "subst" t:term "[" "[" x:term "]" ":=" v:plf_stlc_ref_tm "]": term =>
  `(Tm.subst $t $x [tm| $v ])

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
  | If0NoneZero {n: Nat} {t f st}:
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
    Tm.step ([tm| (loc i) := v], st) (.Unit, st.replace i v)
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


end STLCRef
