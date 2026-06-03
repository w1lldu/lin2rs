import Lean

import Lin2rs.Types
import Lin2rs.Lang


open Lean Elab Meta Command

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


def elabQual (stx: TSyntax `expr_qual) : TermElabM Qual :=
  match stx with
  | `(expr_qual| lin) => return .Lin
  | _ => throwUnsupportedSyntax

def elabPt (stx : TSyntax `expr_pt) : TermElabM Pt :=
  match stx with
  | `(expr_pt| Nat) => return .Nat
  | _ => throwUnsupportedSyntax

def elabTy (stx : TSyntax `expr_ty) : TermElabM Ty :=
  match stx with
  | `(expr_ty| $q:expr_qual $pt:expr_pt) => return (<- elabQual q, <- elabPt pt)
  | _ => throwUnsupportedSyntax

partial def elabExpr (stx : TSyntax `surface_expr) : TermElabM Tm :=
  match stx with
  | `(surface_expr| $n:num) =>  return .Num n.getNat
  | `(surface_expr| $id:ident) =>  return .Id id.getId.toString
  | `(surface_expr| $e1:surface_expr + $e2:surface_expr) =>
    return .Add (<- elabExpr e1) (<- elabExpr e2)
  | `(surface_expr| if $cond:surface_expr then $thn:surface_expr else $els:surface_expr) =>
    return .If (<- elabExpr cond) (<- elabExpr thn) (<- elabExpr els)
  | `(surface_expr| let $id:ident : $ty:expr_ty = $assn:surface_expr in $body:surface_expr) =>
    return .Let id.getId.toString (<- elabTy ty) (<- elabExpr assn) (<- elabExpr body)
  | _ => throwUnsupportedSyntax


def evalQual (q : Qual) :=
  match q with
  | .Lin => mkAppM ``Qual.Lin #[]

def evalPt (pt : Pt) :=
  match pt with
  | .Nat => mkAppM ``Pt.Nat #[]

def evalTy (ty : Ty) := do
  mkAppM ``Prod.mk #[<- evalQual ty.fst, <- evalPt ty.snd]

def evalExpr (tm : Tm) :=
  match tm with
  | .Num n => mkAppM ``Tm.Num #[mkNatLit n]
  | .Id id => mkAppM ``Tm.Id #[mkStrLit id]
  | .Add tm1 tm2 => do
    mkAppM ``Tm.Add #[<- evalExpr tm1, <- evalExpr tm2]
  | .If cond thn els => do
    mkAppM ``Tm.If #[<- evalExpr cond, <- evalExpr thn, <- evalExpr els]
  | .Let id ty assn body => do
    mkAppM ``Tm.Let #[mkStrLit id, <- evalTy ty, <- evalExpr assn, <- evalExpr body]


elab "[lin2rs" e:surface_expr "]" : term => do
  evalExpr (<- elabExpr e)

elab "#typ" e:surface_expr : command => do
  if iwt (<- liftTermElabM (elabExpr e))
  then throwError "not yet implemented"
  else throwError "not yet implemented"

elab "#tc" e:surface_expr ":" pt:expr_pt : command => do
  if tc (<- liftTermElabM (elabExpr e)) (<- liftTermElabM (elabPt pt))
  then throwError "not yet implemented"
  else throwError "not yet implemented"
