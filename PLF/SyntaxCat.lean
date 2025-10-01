declare_syntax_cat my_ident
syntax ident: my_ident
syntax "[" term "]": my_ident
syntax "[ident|" my_ident "]": term
macro_rules
  | `([ident| $x:ident ]) => `($(Lean.quote (toString x.getId)))
  | `([ident| [$x:term] ]) => `($x)
