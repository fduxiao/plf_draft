def TotalMap (A: Type) := String -> A
abbrev PartialMap (A: Type) := TotalMap (Option A)

@[simp]
def TotalMap.empty {A: Type} (v: A): TotalMap A := fun _ => v
@[simp]
def PartialMap.empty {A: Type}: PartialMap A := TotalMap.empty .none

@[simp]
def TotalMap.update {A: Type} (m: TotalMap A) (x: String) (v: A): TotalMap A
  := fun x' => if x' == x then v else m x'

@[simp]
def PartialMap.update {A: Type} (m: PartialMap A) (x: String) (v: A): PartialMap A
  := TotalMap.update m x (Option.some v)

@[simp]
def PartialMap.merge {A: Type} (m1 m2: PartialMap A): PartialMap A :=
  fun x => match m1 x with
    | .some y => y
    | .none => m2 x


declare_syntax_cat lfp_total_map
syntax term: lfp_total_map
syntax "map![" "]": term
syntax "map![" lfp_total_map "]": term
syntax "_" "=>" term: lfp_total_map
syntax term "=>" term ";" lfp_total_map: lfp_total_map
syntax term "=>" term: lfp_total_map

macro_rules
  | `(map![ ]) =>`(PartialMap.empty)
  | `(map![ $m:term ]) =>`($m)
  | `(map![ _ => $v:term ]) => `(TotalMap.empty $v)
  | `(map![ $x:term => $v:term ; $m:lfp_total_map ]) => `(map![$m].update $x $v)
  | `(map![ $x:term => $v:term ]) => `(TotalMap.update PartialMap.empty $x (Option.some $v))


theorem TotalMap.apply_empty {A: Type} {x: String} {v: A}:
  map![_ => v] x = v := by
    simp[empty]



theorem TotalMap.update_eq {A: Type} {m : TotalMap A} {x v}:
  map![x => v ; m] x = v := by
    simp[update]


theorem TotalMap.update_neq {A: Type} {m: TotalMap A} {x1 x2 v}:
  x1 ≠ x2 -> map![x1 => v; m] x2 = m x2 := by
    intros H
    simp [update]
    intros K
    symm at K
    contradiction


theorem TotalMap.update_shadow {A: Type} {m : TotalMap A} {x v1 v2}:
  map![x => v2 ; x => v1 ; m] = map![x => v2 ; m]
:= by
  apply funext
  intros y
  cases (y.decEq x) with
  | isTrue E =>
    simp [update, E]
  | isFalse NE =>
    simp [update, NE]


theorem TotalMap.update_same {A : Type} {m : TotalMap A} {x}:
  map![x => m x ; m] = m
:= by
  apply funext
  intros y
  cases (y.decEq x) with
  | isTrue E =>
    simp [update, E]
  | isFalse NE =>
    simp [update, NE]


theorem TotalMap.update_permute {A: Type} {m : TotalMap A} {x1 x2 v1 v2}:
  x1 ≠ x2 ->
  map![x1 => v1 ; x2 => v2 ; m] =  map![x2 => v2 ; x1 => v1 ; m]
:= by
  intros H
  apply funext
  intros y
  simp [update]
  cases y.decEq x1 with
  | isTrue E =>
    subst E
    simp [H]
  | isFalse NE =>
    simp [NE]


theorem PartialMap.apply_empty {A: Type} {x: String}:
  @PartialMap.empty A x = .none
:= by
  apply TotalMap.apply_empty


theorem PartialMap.update_eq {A: Type} {m : PartialMap A} {x} {v: A}:
  map![x => v ; m] x = .some v
:= by
  apply TotalMap.update_eq


theorem PartialMap.update_neq {A: Type} {m: TotalMap A} {x1 x2 v}:
  x1 ≠ x2 -> map![x1 => v; m] x2 = m x2
:= by
  apply TotalMap.update_neq


theorem PartialMap.update_same {A : Type} {m : PartialMap A} {x} {v: A}:
  m x = .some v ->
  map![x => v ; m] = m
:= by
  intros H
  unfold update
  rewrite [<-H]
  apply TotalMap.update_same


theorem PartialMap.update_shadow {A: Type} {m : PartialMap A} {x v1 v2}:
  map![x => v2 ; x => v1 ; m] = map![x => v2 ; m]
:= by
  apply TotalMap.update_shadow


theorem PartialMap.update_permute {A: Type} {m : PartialMap A} {x1 x2 v1 v2}:
  x1 ≠ x2 ->
  map![x1 => v1 ; x2 => v2 ; m] =  map![x2 => v2 ; x1 => v1 ; m]
:= by
  apply TotalMap.update_permute


@[simp]
def PartialMap.included_in {A: Type} (m m': PartialMap A) :=
  forall x v, m x = .some v -> m' x = .some v


@[refl]
theorem PartialMap.included_in_refl {A} {m: PartialMap A}:
  m.included_in m
:= by
  intro x v H
  exact H


theorem PartialMap.included_in_update {A: Type} {m m' : PartialMap A}
  {x : String} {vx : A}:
  m.included_in m' ->
  (map![x => vx ; m]).included_in map![x => vx ; m']
:= by
  intros H
  intros y vy
  cases y.decEq x with
  | isTrue Hxy =>
    simp [TotalMap.update, Hxy]
  | isFalse Hxy =>
    simp [TotalMap.update, Hxy]
    apply H


theorem PartialMap.empty_merge {A: Type} {m: PartialMap A}
:
  PartialMap.empty.merge m = m
:= by
  apply funext
  intros x
  simp


theorem PartialMap.merge_empty {A: Type} {m: PartialMap A}
:
  m.merge .empty = m
:= by
  apply funext
  intros x
  unfold merge
  split
  . symm
    assumption
  . simp
    symm
    assumption


theorem PartialMap.empty_update_merge {A: Type} {m: PartialMap A}
  {x: String} {v: A}
:
  (PartialMap.empty.update x v).merge m = m.update x v
:= by
  apply funext
  intros y
  simp
  cases y.decEq x with
  | _ H => simp [H]
