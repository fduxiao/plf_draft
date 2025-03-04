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
