import Lean

import Lin2rs.Compile.Types

open Lean

open Compile


inductive Usage where
  | Zero : Usage
  | One : Usage
  | Many : Usage
  deriving BEq

def TyCtx n := Vector (Ty × Usage) n
  deriving BEq


def TyCtx.approx (tc1 tc2 : TyCtx n) :=
  (tc1.zip tc2).all
    (fun ((.mk q _, u), (.mk _ _, u')) =>
      match q with
      | .Un => true
      | .Lin => u == u')


def use (u : Usage) : Usage :=
  match u with
  | .Zero => .One
  | _ => .Many

-- instead of none, return an error?
-- maybe multiple?
def ts' (tm : Tm n Unit) (ctx : TyCtx n) : Option (Ty × TyCtx n) := do
  sorry
  -- match tm with
  -- | .Num _ => .some (.mk .Un .Nat, ctx)
  -- | .Bool _ => .some (.mk .Un .Bool, ctx)
  -- | .Prod q l r =>
  --   let (tyl, ctx') <- ts' l ctx
  --   let (tyr, ctx'') <- ts' r ctx'
  --   let .mk ql _ := tyl
  --   let .mk qr _ := tyr
  --   if ql ≤ q && qr ≤ q
  --   then .some (.mk q (.Prod tyl tyr), ctx'')
  --   else .none
  -- | .Lam q id ty body =>
  --   let (ty', ctx') <- ts' body (ctx.push (ty, .Zero))
  --   if (match q with
  --     | .Un =>
  --       (ctx.zip (ctx'.pop)).any
  --         (fun (b, b') =>
  --           let .mk (.mk qv _) u := b
  --           let .mk _ u' := b'
  --           -- if a linear variable gets used in an unrestricted lambda, the usage changes.
  --           -- if the usage is .Many, it will fail elsewhere
  --           (qv == Qual.Lin) && (u != u'))
  --     | .Lin => false)
  --   then failure
  --   else
  --     let .mk qt _ := ty
  --     bif (match qt with
  --       | .Un => false
  --       | .Lin => ctx'.back.snd != .One)
  --     then failure
  --     else .some (.mk q (.Lam ty ty'), ctx'.pop)
  -- | .BVar _ idx =>
  --   -- vector pushes to the back
  --   let idx' : Fin n := .mk (n - 1 - idx) (by omega)
  --   let (ty, u) := ctx.get idx'
  --   .some (ty, ctx.set idx' (ty, use u))
  -- | .FVar _ => .none
  -- | .Add e1 e2 =>
  --   let (ty1, ctx') <- ts' e1 ctx
  --   let .mk _ pt1 := ty1
  --   if pt1 == .Nat
  --   then
  --     let (ty2, ctx'') <- ts' e2 ctx'
  --     let .mk _ pt2 := ty2
  --     if pt2 == .Nat
  --     then .some (.mk .Un .Nat, ctx'')
  --     else .none
  --   else .none
  -- | .If cond thn els =>
  --   let (tyc, ctx') <- ts' cond ctx
  --   let .mk _ ptc := tyc
  --   if ptc == .Bool
  --   then
  --     let (tyt, ctxt) <- ts' thn ctx'
  --     let (tye, ctxe) <- ts' els ctx'
  --     -- loosen this for unrestricted vars
  --     if tyt == tye && ctxt.approx ctxe
  --     then .some (tyt, ctxt)
  --     else .none
  --   else .none
  -- | .Split ep l r body =>
  --   let (typ, ctx') <- ts' ep ctx
  --   let .mk _ ptt := typ
  --   match ptt with
  --   | .Prod tyl tyr =>
  --     let (ty, ctx'') <- ts' body ((ctx'.push (tyr, .Zero)).push (tyl, .Zero))
  --     let .mk qtl _ := tyl
  --     bif (match qtl with
  --       | .Un => false
  --       | .Lin =>
  --         ctx''.back.snd != .One)
  --     then failure
  --     else
  --       let .mk qtr _ := tyr
  --       haveI : NeZero (n + 2 - 1) := by
  --         apply NeZero.mk
  --         simp
  --       bif (match qtr with
  --         | .Un => false
  --         | .Lin => (ctx''.pop).back.snd != .One)
  --       then failure
  --       else .some (ty, ctx''.pop.pop)
  --   | _ => .none
  -- | .App e1 e2 =>
  --   let (ty1, ctx') <- ts' e1 ctx
  --   let .mk _ pt1 := ty1
  --   match pt1 with
  --   | .Lam tya tyb =>
  --     let (ty2, ctx'') <- ts' e2 ctx'
  --     if ty2 ≤ tya
  --     then .some (tyb, ctx'')
  --     else .none
  --   | _ => .none
  -- | .Let id ty assn body =>
  --   let (tya, ctx') <- ts' assn ctx
  --   if tya ≤ ty
  --   then
  --     let (tyb, ctx'') <- ts' body (ctx'.push (ty, .Zero))
  --     let .mk qt _ := ty
  --     bif (match qt with
  --       | .Un => false
  --       | .Lin => ctx''.back.snd != .One)
  --     then failure
  --     else .some (tyb, ctx''.pop)
  --   else .none

def ts (tm : Tm n Unit) : Option (Tm n Ty) :=
  sorry
  -- (ts' tm #v[]).map Prod.fst

-- def tc (tm : Tm 0) (ty : Ty) : Option Bool :=
--   (ts tm).map (· == ty)

-- def iwt (tm : Tm 0) : Bool :=
--   (ts tm).isSome

-- write tests
