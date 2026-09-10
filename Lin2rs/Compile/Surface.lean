import Lean

import Lin2rs.Compile.Types
import Lin2rs.Compile.Tc
import Lin2rs.Compile.Compile


open Lean Elab Meta Command

open Compile


-- declare_syntax_cat expr_qual

-- syntax "un" : expr_qual
-- syntax "lin" : expr_qual

-- def elabQual (stx: TSyntax `expr_qual) : TermElabM Qual :=
--   match stx with
--   | `(expr_qual| un) => return .Un
--   | `(expr_qual| lin) => return .Lin
--   | _ => throwUnsupportedSyntax

-- declare_syntax_cat expr_pt
declare_syntax_cat expr_ty (behavior := both)

syntax &"Nat" : expr_ty
syntax &"Bool" : expr_ty
syntax "Bytes" : expr_ty
syntax "(" expr_ty "×" expr_ty ")" : expr_ty
-- syntax "(" expr_ty "->" expr_ty ")" : expr_pt

-- syntax expr_qual expr_pt : expr_ty

-- mutual
--   partial def elabPt (stx : TSyntax `expr_pt) : TermElabM Pt :=
--     match stx with
--     | `(expr_pt| Nat) => return .Nat
--     | `(expr_pt| Bool) => return .Bool
--     | `(expr_pt| Bytes) => return .Bool
--     | `(expr_pt| ($tyl × $tyr)) => return .Prod (<- elabTy tyl) (<- elabTy tyr)
--     -- | `(expr_pt| ($tya -> $tyb)) => return .Lam (<- elabTy tya) (<- elabTy tyb)
--     | _ => throwUnsupportedSyntax
--     -- termination_by sizeOf stx

--   partial def elabTy (stx : TSyntax `expr_ty) : TermElabM Ty :=
--     match stx with
--     | `(expr_ty| $q:expr_qual $pt:expr_pt) => return .mk (<- elabQual q) (<- elabPt pt)
--     | _ => throwUnsupportedSyntax
--     -- termination_by sizeOf stx
-- end

partial def elabTy (stx : TSyntax `expr_ty) : TermElabM Ty :=
  match stx with
  | `(expr_ty| Nat) => return .Nat
  | `(expr_ty| Bool) => return .Bool
  | `(expr_ty| Bytes) => return .Bytes
  | `(expr_ty| ($tyl × $tyr)) => return .Prod (<- elabTy tyl) (<- elabTy tyr)
  -- | `(expr_pt| ($tya -> $tyb)) => return .Lam (<- elabTy tya) (<- elabTy tyb)
  | _ => throwUnsupportedSyntax
  -- termination_by sizeOf stx


declare_syntax_cat builtin

syntax "alloc" : builtin
syntax "drop" : builtin
syntax "fill_rnd" : builtin
syntax "memcpy" : builtin


declare_syntax_cat builtin_args
declare_syntax_cat surface_expr

syntax surface_expr : builtin_args
syntax surface_expr "," builtin_args : builtin_args

syntax "(" surface_expr ")" : surface_expr
syntax num : surface_expr
syntax &"true" : surface_expr
syntax &"false" : surface_expr
syntax "(" surface_expr "," surface_expr ")" : surface_expr
-- syntax expr_qual "(" ident ":" expr_ty "=>" surface_expr ")" : surface_expr
syntax ident : surface_expr
syntax "if" surface_expr "then" surface_expr "else" surface_expr : surface_expr
syntax "split" surface_expr "as" ident "," ident "in" surface_expr : surface_expr
-- syntax "(" surface_expr surface_expr")" : surface_expr
syntax "let" ident ":" expr_ty "=" surface_expr "in" surface_expr : surface_expr
syntax surface_expr "+" surface_expr : surface_expr
syntax builtin "(" ")" : surface_expr
syntax builtin "(" builtin_args ")" : surface_expr

partial def elabBuiltin (stx : TSyntax `builtin) : TermElabM (Σ n, Builtin n) :=
  match stx with
  | `(builtin| alloc) => return ⟨_, .Alloc⟩
  | `(builtin| drop)  => return ⟨_, .Drop⟩
  | `(builtin| fill_rnd) => return ⟨_, .Fill_rnd⟩
  | `(builtin| memcpy)   => return ⟨_, .Memcpy⟩
  | _ => throwUnsupportedSyntax

mutual
  partial def elabBArgs (stx : TSyntax `builtin_args) : TermElabM (List Exp) :=
    match stx with
    | `(builtin_args| $e:surface_expr) => return [(<- elabExp e)]
    | `(builtin_args| $e:surface_expr , $es:builtin_args) => return (<- elabExp e) :: (<- elabBArgs es)
    | _ => throwUnsupportedSyntax

  partial def elabExp (stx : TSyntax `surface_expr) : TermElabM Exp :=
    match stx with
    | `(surface_expr| ($e:surface_expr)) => return (<- elabExp e)
    | `(surface_expr| $n:num) => return .Num n.getNat
    | `(surface_expr| true) => return (.Bool true)
    | `(surface_expr| false) => return (.Bool false)
    | `(surface_expr| ($el:surface_expr, $er:surface_expr)) =>
      return .Prod (<- elabExp el) (<- elabExp er)
    -- | `(surface_expr| $q:expr_qual ($id:ident : $ty:expr_ty => $body:surface_expr)) =>
    -- return .Lam (<- elabQual q) id.getId.toString (<- elabTy ty) (<- elabExp body)
    | `(surface_expr| $id:ident) => return .Id id.getId.toString
    | `(surface_expr| if $cond:surface_expr then $thn:surface_expr else $els:surface_expr) =>
      return .If (<- elabExp cond) (<- elabExp thn) (<- elabExp els)
    | `(surface_expr| split $ep:surface_expr as $l:ident, $r:ident in $body:surface_expr) =>
      return .Split (<- elabExp ep) l.getId.toString r.getId.toString (<- elabExp body)
    -- | `(surface_expr| ($e1:surface_expr $e2:surface_expr)) =>
    --   return .App (<- elabExp e1) (<- elabExp e2)
    | `(surface_expr| let $id:ident : $ty:expr_ty = $assn:surface_expr in $body:surface_expr) =>
      return .Let id.getId.toString (<- elabTy ty) (<- elabExp assn) (<- elabExp body)
    | `(surface_expr| $e1:surface_expr + $e2:surface_expr) =>
      return .Builtin .Add [(<- elabExp e1), (<- elabExp e2)]
    | `(surface_expr| $b:builtin ( )) => return .Builtin (<- elabBuiltin b).snd []
    | `(surface_expr| $b:builtin ( $bs:builtin_args )) => return .Builtin (<- elabBuiltin b).snd (<- elabBArgs bs)
    | _ => throwUnsupportedSyntax
    -- termination_by sizeOf stx
end


mutual
  def Exp.toTm' (e : Exp) (ids : List String) : Option (Tm ids.length Unit) :=
    match e with
    | .Num n => return .Num n ()
    | .Bool b => return .Bool b ()
    | .Prod l r => return .Prod (<- Exp.toTm' l ids) (<- Exp.toTm' r ids) ()
    -- | .Lam q id ty body => .Lam q id ty (Exp.toTm' body (id :: ids))
    | .Id id =>
      match ids.findFinIdx? (· == id) with
      | .none => return .FVar id ()
      | .some idx => return .BVar id idx ()
    | .If cond thn els => return .If (<- Exp.toTm' cond ids) (<- Exp.toTm' thn ids) (<- Exp.toTm' els ids) ()
    | .Split p l r body => return .Split (<- Exp.toTm' p ids) l r (<- Exp.toTm' body (l :: r :: ids)) ()
    -- | .App e1 e2 => .App (Exp.toTm' e1 ids) (Exp.toTm' e2 ids)
    | .Let id ty assn body => return .Let id ty (<- Exp.toTm' assn ids) (<- Exp.toTm' body (id :: ids)) ()
    | @Exp.Builtin m b args => return .Builtin m b (<- toTmVec m args ids) ()

    def toTmVec (n : Nat) (es : List Exp) (ids : List String) : Option (TmVec n ids.length Unit) :=
      match n, es with
      | 0, [] => .some .nil
      | n + 1, e :: es' => return .cons (<- Exp.toTm' e ids) (<- toTmVec n es' ids)
      | _, _ => .none
end

def Exp.toTm (e : Exp) : Option (Tm 0 Unit) :=
  Exp.toTm' e []


-- def evalQual (q : Qual) :=
--   match q with
--   | .Un => mkAppM ``Qual.Un #[]
--   | .Lin => mkAppM ``Qual.Lin #[]

-- mutual
--   def evalPt (pt : Pt) := do
--     match pt with
--     | .Nat => mkAppM ``Pt.Nat #[]
--     | .Bool => mkAppM ``Pt.Bool #[]
--     | .Bytes n => mkAppM ``Pt.Bytes #[mkNatLit n]
--     | .Prod ty1 ty2 => mkAppM ``Pt.Prod #[<- evalTy ty1, <- evalTy ty2]
--     -- | .Lam ty1 ty2 => mkAppM ``Pt.Lam #[<- evalTy ty1, <- evalTy ty2]

--   def evalTy (ty : Ty) := do
--     let .mk q pt := ty
--     mkAppM ``Ty.mk #[<- evalQual q, <- evalPt pt]
-- end

def evalTy (ty : Ty) := do
  match ty with
  | .Nat => mkAppM ``Ty.Nat #[]
  | .Bool => mkAppM ``Ty.Bool #[]
  | .Bytes => mkAppM ``Ty.Bytes #[]
  | .Prod ty1 ty2 => mkAppM ``Ty.Prod #[<- evalTy ty1, <- evalTy ty2]
  -- | .Lam ty1 ty2 => mkAppM ``Pt.Lam #[<- evalTy ty1, <- evalTy ty2]

def evalBool b :=
  match b with
  | true => mkAppM ``true #[]
  | false => mkAppM ``false #[]

def evalFin (f : Fin n) : MetaM Expr := do
  mkAppM ``Fin.mk #[mkNatLit f, <- mkDecideProof (<- mkAppM ``LT.lt #[mkNatLit f, mkNatLit n])]

def evalBuiltin (b : Builtin n) : MetaM Expr := do
  match b with
  | .Add => mkAppM ``Builtin.Add #[]
  | .Alloc => mkAppM ``Builtin.Alloc #[]
  | .Drop => mkAppM ``Builtin.Drop #[]
  | .Fill_rnd => mkAppM ``Builtin.Fill_rnd #[]
  | .Memcpy => mkAppM ``Builtin.Memcpy #[]

mutual
  def evalTmVec (tv : TmVec l n Unit) : MetaM Expr := do
    let n := mkNatLit n
    let U := mkConst ``Unit
    match tv with
    | .nil => mkAppOptM ``TmVec.nil #[n, U]
    | .cons tm tv' => mkAppOptM ``TmVec.cons #[n, U, mkNatLit (l - 1), <- evalTm tm, <- evalTmVec tv']

  def evalTm (tm : Tm n Unit) : MetaM Expr := do
    let n := mkNatLit n
    let U := mkConst ``Unit
    let u := mkConst ``Unit.unit
    match tm with
    | .Num num _ => mkAppOptM ``Tm.Num #[n, U, mkNatLit num, u]
    | .Bool b _ => mkAppOptM ``Tm.Bool #[n, U, <- evalBool b, u]
    | .Prod l r _ =>
      mkAppOptM ``Tm.Prod #[n, U, <- evalTm l, <- evalTm r, u]
    -- | .Lam q id ty body _ =>
      -- mkAppOptM ``Tm.Lam #[n, <- evalQual q, mkStrLit id, <- evalTy ty, <- evalTm body]
    | .BVar id idx _ => mkAppOptM ``Tm.BVar #[n, U, mkStrLit id, <- evalFin idx, u]
    | .FVar id _ => mkAppOptM ``Tm.FVar #[n, U, mkStrLit id, u]
    | .If cond thn els _ =>
      mkAppOptM ``Tm.If #[n, U, <- evalTm cond, <- evalTm thn, <- evalTm els, u]
    | .Split tmp l r body _ =>
      mkAppOptM ``Tm.Split #[n, U, <- evalTm tmp, mkStrLit l, mkStrLit r, <- evalTm body, u]
    -- | .App tm1 tm2 => mkAppOptM ``Tm.App #[n, <- evalTm tm1, <- evalTm tm2]
    | .Let id ty assn body _ =>
      mkAppOptM ``Tm.Let #[n, U, mkStrLit id, <- evalTy ty, <- evalTm assn, <- evalTm body, u]
    | .Builtin l b args _ =>
      mkAppOptM ``Tm.Builtin #[n, U, mkNatLit l, <- evalBuiltin b, <- evalTmVec args, u]
    -- | _ => mkAppOptM ``Tm.Num #[mkNatLit 0]
end

elab "[lin2rs" e:surface_expr "]" : term => do
  let some tm := Exp.toTm (<- elabExp e) | throwError "lin2rs: unable to convert expression to tm"
  evalTm tm

elab "#ts" e:surface_expr : command => do
  let some tm := (Exp.toTm (<- liftTermElabM (elabExp e))) | throwError "lin2rs: unable to convert expression to tm"
  match ts tm with
  | .some tm' => logInfo (<- liftTermElabM (evalTy tm'.tag))
  | .none => logError "not well typed"

elab "#tc" e:surface_expr ":" ty:expr_ty : command => do
  let some tm := (Exp.toTm (<- liftTermElabM (elabExp e))) | throwError "lin2rs: unable to convert expression to tm"
  match tc tm (<- liftTermElabM (elabTy ty)) with
  | .none => logError "not well typed"
  | .some b =>
    if b
    then logInfo "types match"
    else logError "types do not match"

elab "#iwt" e:surface_expr : command => do
  let some tm := (Exp.toTm (<- liftTermElabM (elabExp e))) | throwError "lin2rs: unable to convert expression to tm"
  if iwt tm
  then logInfo "well typed"
  else logInfo "not well typed"

elab "#compile" e:surface_expr : command => do
  let some tm := (Exp.toTm (<- liftTermElabM (elabExp e))) | throwError "lin2rs: unable to convert expression to tm"
  let some tm' := ts tm | throwError "lin2rs: not well typed"
  logInfo (compile_to_string tm')

#eval [lin2rs true]

#check [lin2rs 1] == Tm.Num 1 ()

#ts let x : Nat = 1 in x + 2

#eval ts [lin2rs let x : Nat = 1 in x + 2]

#tc let x : Nat = 1 in x + 2 : Nat

#compile let x : Nat = 1 in x + 2

#compile (let x : Nat = 1 in x, 2)

#compile let x : Bool = false in if x then 2 else 1

def a := (ts [lin2rs if true then 2 else 1])

#eval [lin2rs if true then 2 else 1]
#eval (ts [lin2rs if true then 2 else 1])

#eval a.map (fun tm => (compile_tm (tag_tm tm 0).fst #v[]))

#ts drop(memcpy(alloc(5), fill_rnd(alloc(4)), 3))
