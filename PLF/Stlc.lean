import PLF.SmallStep

namespace STLC

inductive ty : Type where
  | B : ty
  | To : ty -> ty -> ty
  deriving Repr


inductive tm : Type where
  | tm_var: String -> tm
  | tm_app: tm -> tm -> tm
  | tm_abs: String -> ty -> tm -> tm
  | tm_true: tm
  | tm_false: tm
  | tm_if: tm -> tm -> tm -> tm



declare_syntax_cat plf_stlc (behavior := symbol)

syntax:100 term: plf_stlc
syntax "<{{" plf_stlc "}}>": term
syntax:100 "(" plf_stlc ")": plf_stlc
syntax:1 plf_stlc "->" plf_stlc : plf_stlc
syntax:100 "$(" term ")": plf_stlc
syntax "Bool": plf_stlc
syntax "if" plf_stlc "then" plf_stlc "else" plf_stlc: plf_stlc
syntax "true": plf_stlc
syntax "false": plf_stlc


end STLC
