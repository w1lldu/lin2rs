import Lean

import Lin2rs.Types


open Lean

open Lin2rs


declare_syntax_cat expr_qual

syntax "lin" : expr_qual


declare_syntax_cat expr_pt

syntax "Nat" : expr_pt


declare_syntax_cat expr_ty

syntax expr_qual expr_pt : expr_ty


declare_syntax_cat surface_expr

syntax num : surface_expr
syntax ident : surface_expr
syntax surface_expr "+" surface_expr : surface_expr
syntax "if" surface_expr "then" surface_expr "else" surface_expr : surface_expr
syntax "let" ident ":" expr_ty "=" surface_expr "in" surface_expr : surface_expr
