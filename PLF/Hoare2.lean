import PLF.Hoare

inductive DImp : Type where
  | Skip (Q: State.Assertion)
  | Seq (d1 d2: DImp)
  | Asgn (X: String) (a: AExp) (Q: State.Assertion)
  | If (b: BExp) (P1: State.Assertion) (d1: DImp)
    (P2: State.Assertion) (d2: DImp) (Q: State.Assertion)
  | While (b: BExp) (P: State.Assertion) (d: DImp) (Q: State.Assertion)
  | Pre (P: State.Assertion) (d: DImp)
  | Post (d: DImp) (Q: State.Assertion)


structure Decorated : Type where
  pre_cond: State.Assertion
  dimp: DImp



declare_syntax_cat lfp_dimp
-- skip
syntax:100 "skip" "{{" lfp_assertion "}}": lfp_dimp
-- assignment
syntax:100 ident ":=" lfp_aexp:15 "{{" lfp_assertion "}}": lfp_dimp
-- assignment using a predefined term
syntax:100 "[" term "]" ":=" lfp_aexp:15 "{{" lfp_assertion "}}": lfp_dimp
-- we still need brackets for priority
syntax:100 "(" lfp_dimp ")" : lfp_dimp

-- while
syntax:11 "while" lfp_bexp:5 "do" "{{" lfp_assertion "}}"
  lfp_dimp
  "end" "{{" lfp_assertion"}}": lfp_dimp

-- if
syntax:11 "if" lfp_bexp:5 "then"
  "{{" lfp_assertion "}}" lfp_dimp
  "else" "{{" lfp_assertion "}}" lfp_dimp
  "end" "{{" lfp_assertion "}}": lfp_dimp

-- pre-condition
syntax:88 "->>" "{{" lfp_assertion "}}" lfp_dimp: lfp_dimp
-- post-condition
syntax:90 lfp_dimp "->>" "{{" lfp_assertion "}}": lfp_dimp
-- sequence
syntax:10 lfp_dimp ";" lfp_dimp : lfp_dimp
-- initial condition
syntax:9 "{{" lfp_assertion "}}" lfp_dimp: lfp_dimp
-- a term can be used directly as a dimp
syntax term: lfp_dimp
-- finally the evaluation
syntax "<d{" lfp_dimp "}>": term


macro_rules
  | `(<d{ skip {{ P }} }>) => `(DImp.Skip P)
  | `(<d{ $v:ident := $a {{ $P }} }>) => `(
    DImp.Asgn $(Lean.quote (toString v.getId)) [AExp| $a ] {{ $P }}
  )
  | `(<d{ [ $t:term ] := $a {{ $P }} }>) => `(
    DImp.Asgn $t [AExp| $a ] {{ $P }}
  )
  | `(<d{ ( $d:lfp_dimp ) }>) => `(<d{ $d }>)
  | `(<d{ while $b do {{ $P }} $d end {{$Q}} }>) =>`(
    DImp.While [BExp| $b ] {{ $P }} <d{$d}> {{ $Q }}
  )
  | `(<d{ if $b then {{ $P1 }} $d1 else {{ $P2 }} $d2 end {{ $Q }} }>) =>`(
    DImp.If [BExp| $b ] {{ $P1 }} <d{ $d1 }> {{ $P2 }} <d{ $d2 }> {{ $Q }}
  )
  | `(<d{ ->> {{ $P }} $d }>) => `(DImp.Pre {{ $P }} <d{ $d }>)
  | `(<d{ $d ->> {{ $Q }} }>) => `(DImp.Post <d{ $d }> {{ $Q }})
  | `(<d{ $d1; $d2 }>) => `(DImp.Seq <d{ $d1 }> <d{ $d2 }>)
  | `(<d{ {{ $P }} $d:lfp_dimp }>) => `(Decorated.mk {{ $P }} <d{ $d }>)
  | `(<d{ $t:term }>) => `($t)


def dec_while: Decorated :=
  <d{
  {{ True }}
    while ~X == 0
    do {{ True ∧ ~X = 0 }}
      X := X - 1 {{ True }}
    end
  {{ True ∧ X = 0}} ->>
  {{ X = 0 }}
  }>


@[simp]
def DImp.erase (d: DImp): Imp :=
  match d with
  | .Skip _ => .Skip
  | .Asgn x e _ => .Asgn x e
  | .Seq d1 d2 => .Seq d1.erase d2.erase
  | .If b _ d1 _ d2 _ => .If b d1.erase d2.erase
  | .While b _ d _ => .While b d.erase
  | .Pre _ d => d.erase
  | .Post d _ => d.erase


@[simp]
def DImp.post_cond (d: DImp): State.Assertion :=
  match d with
  | .Skip Q => Q
  | .Asgn _ _ Q => Q
  | .Seq _ d2 => d2.post_cond
  | .If _ _ _ _ _ Q => Q
  | .While _ _ _ Q => Q
  | .Pre _ d => d.post_cond
  | .Post _ Q => Q


abbrev Decorated.erase (d: Decorated): Imp := d.dimp.erase
abbrev Decorated.post_cond (d: Decorated): State.Assertion := d.dimp.post_cond


example : dec_while.erase = <{while ~X == 0 do X := X - 1 end}> := by
  eq_refl

example : dec_while.pre_cond = True := by eq_refl
example : dec_while.post_cond = {{ X = 0 }} := by eq_refl


@[simp]
def Decorated.outer_triple_valid (d: Decorated) :=
  {{ [d.pre_cond] }}< d.erase >{{ [d.post_cond] }}


example: dec_while.outer_triple_valid =
  {{ True }}<
    while ~X == 0 do X := X - 1 end
  >{{ X = 0 }}
:= by
  eq_refl


@[simp]
def DImp.verifcation_conds (P: State.Assertion) (d: DImp): Prop :=
  match d with
  | .Skip Q => P ->> Q
  | .Seq d1 d2 => d1.verifcation_conds P ∧ d2.verifcation_conds d1.post_cond
  | .Asgn x a Q => P ->> {{ Q ![[x] => [a]] }}
  | .If b P1 d1 P2 d2 Q =>
    ({{ P ∧ b }} ->> P1)
    ∧ ({{ P ∧ ~b }} ->> P2)
    ∧ (d1.post_cond ->> Q) ∧ (d2.post_cond ->> Q)
    ∧ d1.verifcation_conds P1
    ∧ d2.verifcation_conds P2
  | .While b Q d R =>
    -- d.post_cond is the loop-invariant
    (P ->> d.post_cond)
    ∧ ({{ [d.post_cond] ∧ b }} ->> Q)
    ∧ ({{ [d.post_cond] ∧ ¬ b }} ->> R)
    ∧ (d.verifcation_conds Q)
  | .Pre P' d =>
    (P ->> P')
    ∧ d.verifcation_conds P'
  | .Post d Q =>
    d.verifcation_conds P
    ∧ (d.post_cond ->> Q)


theorem DImp.verifcation_conds_correct (d: DImp) P:
  d.verifcation_conds P -> {{ P }}< d.erase >{{ [d.post_cond] }}
:= by
  revert P
  induction d with
  | Skip Q =>
    intros P HPre
    simp
    apply HoareTriple.consequence_pre <;> try solve_by_elim
    . apply HoareTriple.skip
  | Seq d1 d2 IHd1 IHd2 =>
    simp
    intros P HPd1 HPd2
    apply HoareTriple.seq <;> try solve_by_elim
  | Asgn x a Q =>
    intros P HPre
    simp
    apply HoareTriple.consequence_pre
    . apply HoareTriple.asgn
    . exact HPre
  | If b p1 d1 p2 d2 Q IHd1 IHd2 =>
    intros P HPre
    simp; simp at HPre
    let ⟨HT, ⟨HF, ⟨Hd1Q, ⟨Hd2Q, ⟨HThen, HElse⟩⟩⟩⟩⟩ := HPre
    specialize (IHd1 _ HThen)
    specialize (IHd2 _ HElse)
    apply HoareTriple.if
    . -- case true
      apply HoareTriple.consequence <;> (try simp) <;> trivial
    . -- case false
      apply HoareTriple.consequence <;> (try simp) <;> trivial
  | While b Q d R IHd =>
    intros P HPre
    simp; simp at HPre
    let ⟨HP, ⟨HBody, ⟨HPost, Hd⟩⟩⟩ := HPre
    specialize (IHd _ Hd)
    apply HoareTriple.consequence
    . apply HoareTriple.while
      apply HoareTriple.consequence_pre
      . apply IHd
      . simp
        apply HBody
    . apply HP
    . simp
      apply HPost
  | Pre R d IHd =>
    intros P HPre
    let ⟨HP, HD⟩ := HPre
    simp
    apply HoareTriple.consequence_pre <;> solve_by_elim
  | Post d Q IHd =>
    intros P HPre
    let ⟨HP, HD⟩ := HPre
    apply HoareTriple.consequence_post <;> solve_by_elim


@[simp]
def Decorated.verifcation_conds (dec: Decorated): Prop :=
  dec.dimp.verifcation_conds dec.pre_cond


def Decorated.verifcation_conds_correct {dec: Decorated} :
  dec.verifcation_conds -> dec.outer_triple_valid
:= dec.dimp.verifcation_conds_correct _


macro "verify_one_assn": tactic => `(tactic|
  (try simp at *) <;>
  subst_vars <;>
  (try simp at *) <;>
  (try rewrite [
    Nat.eq_of_beq,
    Nat.beq_eq_true_eq,
    Nat.eq_of_beq_eq_true
  ] at *) <;>
  (try eq_refl) <;>
  (try intros <;>
    (try constructor) <;>
    (try omega) <;>
    solve_by_elim [
    Nat.ne_of_beq_eq_false
  ])
)

macro "verify_assn": tactic => `(tactic|
  try (repeat constructor <;> verify_one_assn) <;>
  try verify_one_assn
)

example: 1 + 1 = 2 := by
  verify_assn

example: 1 + 1 = 2 /\ 2 * 4 < 10 := by
  verify_assn

example: 1 + 1 = 2 /\ 2 * 4 < 10 /\ 4 + 4 * 5 < 25 := by
  verify_assn


macro "verify": tactic => `(tactic|
  (try simp) <;>
  intros <;>
  (try simp) <;>
  intros <;>
  apply Decorated.verifcation_conds_correct <;>
  simp <;>
  intros <;>
  verify_assn
)

namespace Playground

def swap_dec (m n:Nat) : Decorated :=
  <d{
    {{ X = [m] ∧ Y = [n]}} ->>
        {{ (X + Y) - ((X + Y) - Y) = [n] ∧ (X + Y) - Y = [m] }}
    X := X + Y
        {{ X - (X - Y) = [n] ∧ X - Y = [m] }};
    Y := X - Y
        {{ X - Y = [n] ∧ Y = [m] }};
    X := X - Y {{ X = [n] ∧ Y = [m]}}
  }>


theorem swap_correct m n: (swap_dec m n).outer_triple_valid := by
  unfold swap_dec
  verify


def if_minus_plus_dec :=
  <d{
  {{True}}
  if (X <= Y) then
              {{ X <= Y }} (->>
              {{ X <= Y }}
    Z := Y - X
              {{ Z = Y - X ∧ Y - X + X = Y }})
  else
              {{ True }} (->>
              {{ True }}
    Y := X + Z
              {{ Y = X + Z }})
  end
  {{ Y = X + Z}} }>

theorem if_minus_plus_correct :
  if_minus_plus_dec.outer_triple_valid
:= by
  unfold if_minus_plus_dec
  verify

def div_mod_dec (a b : Nat) : Decorated :=
  <d{
  {{ True }} ->>
  {{ True }}
    X := [a]
              {{ X = [a] }};
    Y := 0
              {{ X = [a] /\ Y = 0 }};
    while [b] <= X do
              {{ [a] = [b] * Y + X /\ [b] <= X}} ->>
              {{ [a] = [b] * Y + X /\ [b] <= X }}
      X := X - [b]
              {{ [a] = [b] * Y + X + [b] }};
      Y := Y + 1
              {{ [a] = [b] * Y + X }}
    end
  {{ [a] = [b] * Y + X /\ X < [b] }} ->>
  {{ [a] = [b] * Y + X /\ X < [b] }} }>

theorem div_mod_outer_triple_valid a b:
  (div_mod_dec a b).outer_triple_valid
:= by
  verify
  . intros st E1 E2
    rewrite [E1, E2]
    omega
  . verify_assn
    intros st E
    {calc
      a = b * st "Y" + st "X" + b := E
      _ = b * st "Y" + b + st "X" := by omega
      _ = b * st "Y" + b * 1 + st "X" := by omega
      _ = b * (st "Y" + 1) + st "X" := by
        rewrite [Nat.mul_add]
        eq_refl
    }

end Playground
