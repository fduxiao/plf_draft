abbrev Relation (A: Type) := A -> A -> Prop


class Reflexive {A} (P: Relation A) where
  refl: forall {a: A}, P a a

def Relation.refl {A: Type} {P: Relation A} [inst: Reflexive P]:
  forall {a: A}, P a a := inst.refl

macro "rel_refl": tactic => `(tactic| apply Relation.refl)

class Irreflexive {A} (P: Relation A) where
  irrefl: forall {a: A}, Not (P a a)

def Relation.irrefl {A: Type} {P: Relation A} [inst: Irreflexive P]:
  forall {a: A}, Not (P a a) := inst.irrefl


class Antisymmetric {A} (P: Relation A) where
  anti: forall {a b: A}, P a b -> P b a -> a = b

def Relation.anti {A} {P: Relation A} [inst: Antisymmetric P]:
  forall {a b: A}, P a b -> P b a -> a = b := inst.anti


class Transitive {A} (P: Relation A) where
  trans: forall {a b c: A}, P a b -> P b c -> P a c

def Relation.trans {A: Type} {P: Relation A} [inst: Transitive P]:
  forall {a b c: A}, P a b -> P b c -> P a c := inst.trans


macro "rel_trans": tactic => `(tactic| apply Relation.trans)

class Symmetric {A} (P: Relation A) where
  symm: forall {a b: A}, P a b -> P b a

def Relation.symm {A} {P: Relation A} [inst: Symmetric P]:
  forall {a b: A}, P a b -> P b a := inst.symm

class Congruence {A: Type} (P: Relation A) (S: A -> A) where
  rel_cong: forall {a b: A}, (P a b) -> P (S a) (S b)


class KeepCong {A: Type} (P Q: Relation A) where
  keep_cong: forall (f: A -> A),
    (forall {a b}, (P a b) -> P (f a) (f b)) ->
    forall {a b}, (Q a b) -> Q (f a) (f b)


def Relation.keep_cong {A: Type}
  {P Q: Relation A} (f: A -> A)
  [inst: KeepCong P Q]:
    (forall {a b}, (P a b) -> P (f a) (f b)) ->
    forall {a b}, (Q a b) -> Q (f a) (f b) :=
    inst.keep_cong f


class SubRel {A} (P: Relation A) (Q: Relation A): Prop where
  inclusion: forall {a b: A}, P a b -> Q a b

notation: 60 P " sub_rel " Q => SubRel P Q

def Relation.super {A: Type} {P: Relation A} {Super: Relation A}
  [inst: P sub_rel Super]: forall {a b: A}, P a b -> Super a b
:=
  inst.inclusion

/-!
`SubRel` is it self a poset on all relations
-/
section

instance sub_rel_refl {A} {P: Relation A}: P sub_rel P where
  inclusion := id

instance: forall {A: Type}, Reflexive (SubRel (A := A)) where
  refl := by
    intros P
    apply sub_rel_refl


instance: forall {A: Type}, Transitive (SubRel (A := A)) where
  trans {P Q R} {s1 s2} := by
    apply SubRel.mk
    intros a b H
    apply Q.super
    apply P.super
    apply H


theorem sub_rel_equiv: forall {A: Type} {P Q: Relation A},
  (P sub_rel Q) -> (Q sub_rel P) -> forall {a b: A}, P a b <-> Q a b
:= by
  intros A P Q s1 s2
  intros a b
  constructor
  . apply s1.inclusion
  . apply s2.inclusion

theorem rel_eq: forall {A: Type} {P Q: Relation A},
  (forall x y: A, P x y <-> Q x y) ->
  P = Q
:= by
  intros A P Q H
  apply funext
  intros x
  apply funext
  intros y
  apply propext
  apply H

instance: forall {A: Type}, Antisymmetric (SubRel (A := A)) where
  anti := by
    intros P Q s1 s2
    apply rel_eq
    intros a b
    apply Iff.intro
    . apply s1.inclusion
    . apply s2.inclusion

end

section Closure

abbrev RelationOp (A: Type) := Relation A -> Relation A
abbrev RelationPred (A: Type) := Relation A -> Prop

/-!
The closure fo each type is clear.
-/
class Closure {A: Type} (Pred: outParam (RelationPred A)) (P: outParam (Relation A)) (C: Relation A) where
  sub: P sub_rel C
  pred: Pred C
  least: forall {Q: Relation A}, Pred Q -> (P sub_rel Q) -> C sub_rel Q



instance {A: Type} {P C: Relation A} {Pred: RelationPred A} [inst: Closure Pred P C]:
  P sub_rel C := inst.sub

instance cl_cl_sub {A: Type} {Pred: RelationPred A} {P: Relation A} {C1 C2: Relation A}
  [inst1: Closure Pred P C1] [inst2: Closure Pred P C2]: C1 sub_rel C2
where
  inclusion := by
    intros a b
    let sub := @inst1.least C2 inst2.pred inst2.sub
    apply sub.inclusion


class ClosureOp {A: Type} (Pred: outParam (RelationPred A)) (Cl: outParam (RelationOp A)) where
  close (P: Relation A): Closure Pred P (Cl P)
  sub {P: Relation A} := (close P).sub (P := P)
  pred {P: Relation A} := (close P).pred (P := P)
  least {P Q: Relation A} := (close P).least (P := P) (Q := Q)


def RelationOp.close {A: Type}
  (Cl: RelationOp A) (P: Relation A) {Pred: RelationPred A}
  [inst: ClosureOp Pred Cl]
:= inst.close P


instance {A: Type} {Pred: RelationPred A} (Cl: RelationOp A) [inst: ClosureOp Pred Cl]
  (P: Relation A): Closure Pred P (Cl P)
:= inst.close P


instance {A: Type} {Pred: RelationPred A} {Cl: RelationOp A}
  [inst: ClosureOp Pred Cl] {P: Relation A}: P sub_rel (Cl P)
:= (inst.close P).sub

instance cl_op_cl_op_sub {A: Type} {Pred: RelationPred A} {C1 C2: RelationOp A}
  [inst1: ClosureOp Pred C1] [inst2: ClosureOp Pred C2]
  {P: Relation A}: C1 P sub_rel C2 P
where
  inclusion := by
    intros a b
    let sub := @inst1.least P (C2 P) inst2.pred inst2.sub
    apply sub.inclusion

instance cl_mono {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl]
  {P Q: Relation A} [r1: P sub_rel Q]: Cl P sub_rel Cl Q
where
  inclusion := by
    have r2: Q sub_rel Cl Q := inst.sub
    have r3: P sub_rel Cl Q := Relation.trans r1 r2
    let H := @inst.least P (Cl Q) inst.pred r3
    intros a b
    apply H.inclusion

end Closure


/-!
Then, the reflexive transitive relation
-/
def RTPred {A: Type} (P: Relation A) := Reflexive P ∧ Transitive P

/--
Reflexive Transitive relation Closure
-/
inductive RTCl {A} (P: Relation A): Relation A where
  | refl {a}: RTCl P a a
  | step {a b c}: P a b -> RTCl P b c -> RTCl P a c


instance {A} {P: Relation A}: Transitive (RTCl P) where
  trans := by
    intros a b c Hab
    induction Hab with
    | refl => solve_by_elim
    | @step a t b Hat Htb IHtb =>
      intros Hbc
      specialize (IHtb Hbc)
      constructor
      . apply Hat
      . apply IHtb


theorem RTCl.inclusion {A} {P: Relation A}: forall {a b},
  P a b -> RTCl P a b
:= by
  intro a b H
  apply RTCl.step H
  apply RTCl.refl


macro "rtcl_incl": tactic => `(tactic| apply RTCl.inclusion)
macro "rtcl_step": tactic => `(tactic| apply RTCl.step)


instance RTCl.close {A} (P: Relation A): Closure RTPred P (RTCl P) where
  sub := SubRel.mk $ by
    intros a b H
    apply RTCl.step H .refl
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk RTCl.refl
    . /- Transitive -/
      constructor
      intros a b c
      apply Relation.trans
  least := by
    intros Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right
    apply SubRel.mk
    intros a b H
    induction H with
    | refl =>
      apply Q.refl
    | @step a t b Hat Htb IH =>
      apply Q.trans
      . apply sub.inclusion Hat
      . apply IH


instance rtcl_cl_op {A: Type}: ClosureOp RTPred RTCl (A := A) where
  close := RTCl.close

instance {A} {P: Relation A}: Reflexive (RTCl P) where
  refl := RTCl.refl


instance {A} {P: Relation A}: KeepCong P (RTCl P) where
  keep_cong := by
    intros f HP a b HC
    induction HC with
    | @refl =>
      apply RTCl.refl
    | @step a b c Hab Hbc IHbc =>
      specialize (HP Hab)
      apply RTCl.step HP IHbc


/-!
Then, the equivalence relation
-/
def EPred {A: Type} (P: Relation A) := Reflexive P ∧ Transitive P ∧ Symmetric P

/--
Equivalence Closure
-/
inductive ECl {A} (P: Relation A): Relation A where
  | inclusion {a b}: P a b -> ECl P a b
  | refl {a}: ECl P a a
  | trans {a b c}: ECl P a b -> ECl P b c -> ECl P a c
  | symm {a b}: ECl P a b -> ECl P b a


instance ECl.close {A} (P: Relation A): Closure EPred P (ECl P) where
  sub := SubRel.mk ECl.inclusion
  pred := by
    constructor
    . /- Reflexive -/
      apply Reflexive.mk ECl.refl
    constructor
    . /- Transitive -/
      apply Transitive.mk ECl.trans
    . /- Symmetric -/
      apply Symmetric.mk ECl.symm
  least := by
    intros Q inst sub
    let inst_refl := inst.left
    let inst_trans := inst.right.left
    let inst_symm := inst.right.right
    apply SubRel.mk
    intros a b H
    induction H
    case inclusion a b Hab =>
      apply sub.inclusion
      apply Hab
    case refl a =>
      apply Q.refl
    case trans Hab Hbc =>
      apply Q.trans Hab Hbc
    case symm Hab =>
      apply Q.symm Hab

instance ecl_cl_op {A: Type}: ClosureOp EPred ECl (A := A) where
  close := ECl.close

instance {A} {P: Relation A}: Reflexive (ECl P) where
  refl := ECl.refl

instance {A} {P: Relation A}: Transitive (ECl P) where
  trans := ECl.trans

instance {A} {P: Relation A}: Symmetric (ECl P) where
  symm := ECl.symm


instance {A} {P: Relation A}: KeepCong P (ECl P) where
  keep_cong := by
    intros f HP a b HC
    induction HC with
    | @inclusion a b H =>
      apply ECl.inclusion (HP H)
    | @refl =>
      apply ECl.refl
    | @trans a b c Hab Hac IHab IHac =>
      apply ECl.trans IHab IHac
    | @symm a b Hab IHab =>
      apply ECl.symm IHab


/-!
Now, we prove Church-Rosser property implies the uniqueness of normal forms.
-/


/--
Normal terms with respect to a reduction
-/
def Relation.Normal {A: Type} (R: Relation A) (x: A) := Not (exists y, R x y)
/--
Normal terms with respect to multi step reduction
-/
def Relation.MNormal {A: Type} (R: Relation A) (x: A) := forall {y}, RTCl R x y -> x = y


def Relation.Normal.MNormal {A: Type} {R: Relation A}:
  forall {x: A}, R.Normal x -> R.MNormal x
:= by
  intros n HR m HMR
  induction HMR with
  | @refl x =>
    eq_refl
  | @step a b c Hab Hbc Hbc =>
    exfalso
    apply HR
    constructor
    apply Hab


theorem Relation.MNormal.Normal {A: Type} {R: Relation A} [Irreflexive R]:
  forall {x: A}, R.MNormal x -> R.Normal x
:= by
  intros n HMR Hx
  let ⟨x, Hx⟩ := Hx
  have E: n = x := by
    apply HMR
    apply R.super
    exact Hx
  rewrite [E] at Hx
  apply R.irrefl Hx



/-!
# Uniqueness of reduction
Semi-confluence, confluence, and Church-Rosser
-/

class SemiConfluent {A: Type} (P: Relation A) where
  semi_confl: forall {m1 m2 m3: A}, P m1 m2 -> RTCl P m1 m3 -> exists m4, RTCl P m2 m4 /\ RTCl P m3 m4


def Relation.semi_confl {A: Type} (P: Relation A) [inst: SemiConfluent P]
  {m1 m2 m3: A} := inst.semi_confl (m1 := m1) (m2 := m2) (m3 := m3)


class Confluent {A: Type} (P: Relation A) where
  confl: forall {m1 m2 m3: A},
    RTCl P m1 m2 -> RTCl P m1 m3 -> exists m4, RTCl P m2 m4 /\ RTCl P m3 m4


def Relation.confl {A: Type} (P: Relation A) [inst: Confluent P]
  {m1 m2 m3: A} := inst.confl (m1 := m1) (m2 := m2) (m3 := m3)


class ChurchRosser {A: Type} (P: Relation A) where
  church_rosser: forall {m2 m3: A},
    ECl P m2 m3 -> exists m4, RTCl P m2 m4 /\ RTCl P m3 m4

def Relation.church_rosser {A: Type} (P: Relation A) [inst: ChurchRosser P]
  {m2 m3: A} := inst.church_rosser (m2 := m2) (m3 := m3)


instance Relation.semi_confl_to_confl {A: Type} (P: Relation A)
  [inst: SemiConfluent P]: Confluent P where
  confl := by
    intros m1 m2 m3
    intros H12
    revert m3
    induction H12 with
    | @refl x =>
      intros m3 H13
      exists m3
      apply And.intro
      . apply H13
      . apply RTCl.refl
    | @step m1 b m2 H1b Hb2 IH =>
      intros m3 H13
      let ⟨x, ⟨Hbx, H3x⟩⟩ := inst.semi_confl H1b H13
      let ⟨m4, ⟨H24, Hx4⟩⟩ := IH Hbx
      exists m4
      apply And.intro
      . apply H24
      . apply Relation.trans H3x Hx4


instance Relation.confl_to_ChRo {A: Type} (P: Relation A)
  [inst: Confluent P]: ChurchRosser P where
  church_rosser := by
    intros m2 m3 H
    induction H with
    | @inclusion a b Hab =>
      apply inst.confl
      . apply RTCl.refl
      . apply P.super Hab
    | @refl x =>
      exists x
      apply And.intro
      . apply RTCl.refl
      . apply RTCl.refl
    | @trans a b c Hab Hbc IHab IHbc =>
      let ⟨x, ⟨Hax, Hbx⟩⟩ := IHab
      let ⟨y, ⟨Hby, Hcy⟩⟩ := IHbc
      let ⟨m4, ⟨Hxm4, Hym4⟩⟩ := inst.confl Hbx Hby
      exists m4
      apply And.intro
      . apply Relation.trans Hax Hxm4
      . apply Relation.trans Hcy Hym4
    | @symm a b Hab IHab =>
      let ⟨m4, ⟨H1, H2⟩⟩ := IHab
      exists m4


class Relation.NormalFormUnique {A} (R: Relation A) where
  normal_formal_unique: forall {n m1 m2: A},
    RTCl R n m1 -> RTCl R n m2 ->
    R.Normal m1 -> R.Normal m2 ->
    m1 = m2


instance Relation.ChRo_normal_form_unique
  {A: Type}
  {R: Relation A}
  [inst: Confluent R]
: R.NormalFormUnique where
  normal_formal_unique := by
    intros n m1 m2
    intros r1 r2 N1 N2
    have ⟨m4, ⟨H14, H24⟩⟩ := inst.confl r1 r2
    have E1 := N1.MNormal H14
    have E2 := N2.MNormal H24
    subst_eqs
    eq_refl
