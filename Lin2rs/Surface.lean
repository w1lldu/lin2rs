import Lean

import Lin2rs.Types
import Lin2rs.Lang.Tc


open Lean Elab Meta Command

open Lin2rs


declare_syntax_cat expr_qual

syntax "un" : expr_qual
syntax "lin" : expr_qual

def elabQual (stx: TSyntax `expr_qual) : TermElabM Qual :=
  match stx with
  | `(expr_qual| un) => return .Un
  | `(expr_qual| lin) => return .Lin
  | _ => throwUnsupportedSyntax

declare_syntax_cat expr_pt
declare_syntax_cat expr_ty

syntax "Nat" : expr_pt
syntax "Bool" : expr_pt
syntax "(" expr_ty "×" expr_ty ")" : expr_pt
syntax "(" expr_ty "->" expr_ty ")" : expr_pt

syntax expr_qual expr_pt : expr_ty

mutual
  partial def elabPt (stx : TSyntax `expr_pt) : TermElabM Pt :=
    match stx with
    | `(expr_pt| Nat) => return .Nat
    | `(expr_pt| Bool) => return .Bool
    | `(expr_pt| ($tyl × $tyr)) => return .Prod (<- elabTy tyl) (<- elabTy tyr)
    | `(expr_pt| ($tya -> $tyb)) => return .Lam (<- elabTy tya) (<- elabTy tyb)
    | _ => throwUnsupportedSyntax
    -- termination_by sizeOf stx

  partial def elabTy (stx : TSyntax `expr_ty) : TermElabM Ty :=
    match stx with
    | `(expr_ty| $q:expr_qual $pt:expr_pt) => return .mk (<- elabQual q) (<- elabPt pt)
    | _ => throwUnsupportedSyntax
    -- termination_by sizeOf stx
end

declare_syntax_cat surface_expr

syntax "(" surface_expr ")" : surface_expr
syntax num : surface_expr
syntax &"true" : surface_expr
syntax &"false" : surface_expr
syntax expr_qual "(" surface_expr "," surface_expr ")" : surface_expr
syntax expr_qual "(" ident ":" expr_ty "=>" surface_expr ")" : surface_expr
syntax ident : surface_expr
syntax surface_expr "+" surface_expr : surface_expr
syntax "if" surface_expr "then" surface_expr "else" surface_expr : surface_expr
syntax "split" surface_expr "as" ident "," ident "in" surface_expr : surface_expr
syntax "(" surface_expr surface_expr")" : surface_expr
syntax "let" ident ":" expr_ty "=" surface_expr "in" surface_expr : surface_expr

partial def elabExp (stx : TSyntax `surface_expr) : TermElabM Exp :=
  match stx with
  | `(surface_expr| ($e:surface_expr)) => return (<- elabExp e)
  | `(surface_expr| $n:num) => return .Num n.getNat
  | `(surface_expr| true) => return (.Bool true)
  | `(surface_expr| false) => return (.Bool false)
  | `(surface_expr| $q:expr_qual ($el:surface_expr, $er:surface_expr)) =>
    return .Prod (<- elabQual q) (<- elabExp el) (<- elabExp er)
  | `(surface_expr| $q:expr_qual ($id:ident : $ty:expr_ty => $body:surface_expr)) => return .Lam (<- elabQual q) id.getId.toString (<- elabTy ty) (<- elabExp body)
  | `(surface_expr| $id:ident) => return .Id id.getId.toString
  | `(surface_expr| $e1:surface_expr + $e2:surface_expr) =>
    return .Add (<- elabExp e1) (<- elabExp e2)
  | `(surface_expr| if $cond:surface_expr then $thn:surface_expr else $els:surface_expr) =>
    return .If (<- elabExp cond) (<- elabExp thn) (<- elabExp els)
  | `(surface_expr| split $ep:surface_expr as $l:ident, $r:ident in $body:surface_expr) =>
    return .Split (<- elabExp ep) l.getId.toString r.getId.toString (<- elabExp body)
  | `(surface_expr| ($e1:surface_expr $e2:surface_expr)) =>
    return .App (<- elabExp e1) (<- elabExp e2)
  | `(surface_expr| let $id:ident : $ty:expr_ty = $assn:surface_expr in $body:surface_expr) =>
    return .Let id.getId.toString (<- elabTy ty) (<- elabExp assn) (<- elabExp body)
  | _ => throwUnsupportedSyntax
  -- termination_by sizeOf stx


def Exp.toTm' (e : Exp) (ids : List String) : Tm ids.length :=
  match e with
  | .Num n => .Num n
  | .Bool b => .Bool b
  | .Prod q l r => .Prod q (Exp.toTm' l ids) (Exp.toTm' r ids)
  | .Lam q id ty body => .Lam q id ty (Exp.toTm' body (id :: ids))
  | .Id id =>
    match ids.findFinIdx? (· == id) with
    | .none => .FVar id
    | .some idx => .BVar id idx
  | .Add e1 e2 => .Add (Exp.toTm' e1 ids) (Exp.toTm' e2 ids)
  | .If cond thn els => .If (Exp.toTm' cond ids) (Exp.toTm' thn ids) (Exp.toTm' els ids)
  | .Split ep l r body => .Split (Exp.toTm' ep ids) l r (Exp.toTm' body (l :: r :: ids))
  | .App e1 e2 => .App (Exp.toTm' e1 ids) (Exp.toTm' e2 ids)
  | .Let id ty assn body => .Let id ty (Exp.toTm' assn ids) (Exp.toTm' body (id :: ids))

def Exp.toTm (e : Exp) : Tm 0 :=
  Exp.toTm' e []


def evalQual (q : Qual) :=
  match q with
  | .Un => mkAppM ``Qual.Un #[]
  | .Lin => mkAppM ``Qual.Lin #[]

mutual
  def evalPt (pt : Pt) := do
    match pt with
    | .Nat => mkAppM ``Pt.Nat #[]
    | .Bool => mkAppM ``Pt.Bool #[]
    | .Prod ty1 ty2 => mkAppM ``Pt.Prod #[<- evalTy ty1, <- evalTy ty2]
    | .Lam ty1 ty2 => mkAppM ``Pt.Lam #[<- evalTy ty1, <- evalTy ty2]

  def evalTy (ty : Ty) := do
    let .mk q pt := ty
    mkAppM ``Ty.mk #[<- evalQual q, <- evalPt pt]
end

def evalBool b :=
  match b with
  | true => mkAppM ``true #[]
  | false => mkAppM ``false #[]

def evalFin (f : Fin n) : MetaM Expr := do
  mkAppM ``Fin.mk #[mkNatLit f, <- mkDecideProof (<- mkAppM ``LT.lt #[mkNatLit f, mkNatLit n])]

def evalTm (tm : Tm n) : MetaM Expr := do
  let n := mkNatLit n
  match tm with
  | .Num num => mkAppOptM ``Tm.Num #[n, mkNatLit num]
  | .Bool b => mkAppOptM ``Tm.Bool #[n, <- evalBool b]
  | .Prod q l r =>
    mkAppOptM ``Tm.Prod #[n, <- evalQual q, <- evalTm l, <- evalTm r]
  | .Lam q id ty body =>
    mkAppOptM ``Tm.Lam #[n, <- evalQual q, mkStrLit id, <- evalTy ty, <- evalTm body]
  | .BVar id idx => mkAppOptM ``Tm.BVar #[n, mkStrLit id, <- evalFin idx]
  | .FVar id => mkAppOptM ``Tm.FVar #[n, mkStrLit id]
  | .Add tm1 tm2 => mkAppOptM ``Tm.Add #[n, <- evalTm tm1, <- evalTm tm2]
  | .If cond thn els =>
    mkAppOptM ``Tm.If #[n, <- evalTm cond, <- evalTm thn, <- evalTm els]
  | .Split tmp l r body =>
    mkAppOptM ``Tm.Split #[n, <- evalTm tmp, mkStrLit l, mkStrLit r, <- evalTm body]
  | .App tm1 tm2 => mkAppOptM ``Tm.App #[n, <- evalTm tm1, <- evalTm tm2]
  | .Let id ty assn body =>
    mkAppOptM ``Tm.Let #[n, mkStrLit id, <- evalTy ty, <- evalTm assn, <- evalTm body]
  -- | _ => mkAppOptM ``Tm.Num #[mkNatLit 0] -- TODO


elab "[lin2rs" e:surface_expr "]" : term => do
  evalTm (Exp.toTm (<- elabExp e))

elab "#ts" e:surface_expr : command => do
  match ts (Exp.toTm (<- liftTermElabM (elabExp e))) with
  | .some ty => logInfo (<- liftTermElabM (evalTy ty))
  | .none => logError "not well typed"

elab "#tc" e:surface_expr ":" ty:expr_ty : command => do
  match tc (Exp.toTm (<- liftTermElabM (elabExp e))) (<- liftTermElabM (elabTy ty)) with
  | .none => logError "not well typed"
  | .some b =>
    if b
    then logInfo "types match"
    else logError "types do not match"

elab "#iwt" e:surface_expr : command => do
  if iwt (Exp.toTm (<- liftTermElabM (elabExp e)))
  then logInfo "well typed"
  else logInfo "not well typed"

#check [lin2rs 1]

#check [lin2rs 1] == Tm.Num 1

#ts let x : lin Nat = 1 in x + 2

#eval ts [lin2rs let x : lin Nat = 1 in x + 2]

#tc let x : lin Nat = 1 in x + 2 : un Nat
