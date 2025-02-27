abbrev Relation (A: Type) := A -> A -> Prop


class Reflexive {A} (P: Relation A) where
  refl: forall {a: A}, P a a

def Relation.refl {A: Type} {P: Relation A} [inst: Reflexive P]:
  forall {a: A}, P a a := inst.refl


class Antisymmetric {A} (P: Relation A) where
  anti: forall {a b: A}, P a b -> P b a -> a = b

def Relation.anti {A} {P: Relation A} [inst: Antisymmetric P]:
  forall {a b: A}, P a b -> P b a -> a = b := inst.anti


class Transitive {A} (P: Relation A) where
  trans: forall {a b c: A}, P a b -> P b c -> P a c

def Relation.trans {A: Type} {P: Relation A} [inst: Transitive P]:
  forall {a b c: A}, P a b -> P b c -> P a c := inst.trans


class Symmetric {A} (P: Relation A) where
  symm: forall {a b: A}, P a b -> P b a

def Relation.symm {A} {P: Relation A} [inst: Symmetric P]:
  forall {a b: A}, P a b -> P b a := inst.symm


class SubRel {A} (P: Relation A) (Q: Relation A): Prop where
  inclusion: forall {a b: A}, P a b -> Q a b

notation: 60 P " sub_rel " Q => SubRel P Q

def Relation.super {A: Type} {P: Relation A} {Super: Relation A}
  [inst: P sub_rel Super]: forall {a b: A}, P a b -> Super a b :=
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
  (P sub_rel Q) -> (Q sub_rel P) -> forall {a b: A}, P a b <-> Q a b := by
  intros A P Q s1 s2
  intros a b
  constructor
  . apply s1.inclusion
  . apply s2.inclusion

theorem rel_eq: forall {A: Type} {P Q: Relation A}, (forall x y: A, P x y <-> Q x y) -> P = Q := by
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
  [inst1: Closure Pred P C1] [inst2: Closure Pred P C2]: C1 sub_rel C2 where
    inclusion := by
      intros a b
      let sub := @inst1.least C2 inst2.pred inst2.sub
      apply sub.inclusion


class ClosureOp {A: Type} (Pred: outParam (RelationPred A)) (Cl: outParam (RelationOp A)) where
  close (P: Relation A): Closure Pred P (Cl P)
  sub {P: Relation A} := (close P).sub (P := P)
  pred {P: Relation A} := (close P).pred (P := P)
  least {P Q: Relation A} := (close P).least (P := P) (Q := Q)


def RelationOp.close {A: Type} (Cl: RelationOp A) (P: Relation A) {Pred: RelationPred A}
  [inst: ClosureOp Pred Cl] := inst.close P


instance {A: Type} {Pred: RelationPred A} (Cl: RelationOp A) [inst: ClosureOp Pred Cl]
  (P: Relation A): Closure Pred P (Cl P) := inst.close P


instance {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl] {P: Relation A}:
  P sub_rel (Cl P) := (inst.close P).sub

instance cl_op_cl_op_sub {A: Type} {Pred: RelationPred A} {C1 C2: RelationOp A}
  [inst1: ClosureOp Pred C1] [inst2: ClosureOp Pred C2] {P: Relation A}: C1 P sub_rel C2 P where
    inclusion := by
      intros a b
      let sub := @inst1.least P (C2 P) inst2.pred inst2.sub
      apply sub.inclusion

instance cl_mono {A: Type} {Pred: RelationPred A} {Cl: RelationOp A} [inst: ClosureOp Pred Cl]
  {P Q: Relation A} [r1: P sub_rel Q]: Cl P sub_rel Cl Q where
  inclusion := by
    have r2: Q sub_rel Cl Q := inst.sub
    have r3: P sub_rel Cl Q := Relation.trans r1 r2
    let H := @inst.least P (Cl Q) inst.pred r3
    intros a b
    apply H.inclusion

end Closure

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
