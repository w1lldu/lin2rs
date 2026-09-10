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


-- def TyCtx.approx (tc1 tc2 : TyCtx n) :=
--   (tc1.zip tc2).all
--     (fun ((.mk q _, u), (.mk _ _, u')) =>
--       match q with
--       | .Un => true
--       | .Lin => u == u')


def use (u : Usage) : Usage :=
  match u with
  | .Zero => .One
  | _ => .Many

-- instead of none, return an error?
-- maybe multiple?
def ts' (tm : Tm n Unit) (ctx : TyCtx n) : Option (Tm n Ty × TyCtx n) := do
  -- sorry
  match tm with
  | .Num num _ => .some (.Num num .Nat, ctx)
  | .Bool b _ => .some (.Bool b .Bool, ctx)
  | .Prod l r _ =>
    let (tml, ctx') <- ts' l ctx
    let (tmr, ctx'') <- ts' r ctx'
    let tyl := tml.tag
    let tyr := tmr.tag
    -- let .mk ql _ := tyl
    -- let .mk qr _ := tyr
    -- if ql ≤ q && qr ≤ q
    .some (.Prod tml tmr (.Prod tyl tyr), ctx'')
    -- else .none
  | .BVar id idx _ =>
    -- vector pushes to the back
    let idx' : Fin n := .mk (n - 1 - idx) (by omega)
    let (ty, u) := ctx.get idx'
    .some (.BVar id idx ty, ctx.set idx' (ty, use u))
  | .FVar _ _ => .none
  | .If cond thn els _ =>
    let (tmc, ctx') <- ts' cond ctx
    let (tmt, ctxt) <- ts' thn ctx'
    let (tme, ctxe) <- ts' els ctx'
    if tmc.tag == .Bool && tmt.tag == tme.tag && ctxt == ctxe
    -- loosen this for unrestricted vars
    then .some (.If tmc tmt tme tmt.tag, ctxt)
    else .none
  | .Split p l r body _ =>
    let (tmp, ctx') <- ts' p ctx
    let tyt := tmp.tag
    match tyt with
    | .Prod tyl tyr =>
      let (tmb, ctx'') <- ts' body ((ctx'.push (tyr, .Zero)).push (tyl, .Zero))
      -- let .mk qtl _ := tyl
      -- bif (match qtl with
      --   | .Un => false
      --   | .Lin =>
      --     ctx''.back.snd != .One)
      bif ctx''.back.snd != .One
      then failure
      else
        haveI : NeZero (n + 2 - 1) := by
          apply NeZero.mk
          simp
        -- let .mk qtr _ := tyr
        -- bif (match qtr with
        --   | .Un => false
        --   | .Lin => (ctx''.pop).back.snd != .One)
        bif (ctx''.pop).back.snd != .One
        then failure
        else .some (.Split tmp l r tmb tmb.tag, ctx''.pop.pop)
    | _ => .none
  | .Let id ty assn body _ =>
    let (tma, ctx') <- ts' assn ctx
    -- if tma.tag ≤ ty
    -- then
    let (tmb, ctx'') <- ts' body (ctx'.push (ty, .Zero))
    -- let .mk qt _ := ty
    -- bif (match qt with
    --   | .Un => false
    --   | .Lin => ctx''.back.snd != .One)
    bif ctx''.back.snd != .One
    then failure
    else .some (.Let id ty tma tmb tmb.tag, ctx''.pop)
    -- else .none
  | .Builtin l b tv _ =>
    match b, tv with
    | .Add, .cons tm1 (.cons tm2 .nil) =>
      let (tm1', ctx') <- ts' tm1 ctx
      let (tm2', ctx'') <- ts' tm2 ctx'
      if tm1'.tag == .Nat && tm2'.tag == .Nat
      then .some (.Builtin 2 .Add (.cons tm1' (.cons tm2' .nil)) .Nat, ctx'')
      else .none
    | .Alloc, .cons tm .nil =>
      let (tm', ctx') <- ts' tm ctx
      if tm'.tag == .Nat
      then .some (.Builtin 1 .Alloc (.cons tm' .nil) .Bytes, ctx')
      else .none
    | .Drop, .cons tm .nil =>
      let (tm', ctx') <- ts' tm ctx
      .some (.Builtin 1 .Drop (.cons tm' .nil) .Nat, ctx')
    | .Fill_rnd, .cons tm .nil =>
      let (tm', ctx') <- ts' tm ctx
      if tm'.tag == .Bytes
      then .some (.Builtin 1 .Fill_rnd (.cons tm' .nil) .Bytes, ctx')
      else .none
    | .Memcpy, tv =>
      let .cons tm1 (.cons tm2 (.cons tm3 .nil)) := tv
      let (tm1', ctx') <- ts' tm1 ctx
      let (tm2', ctx'') <- ts' tm2 ctx'
      let (tm3', ctx''') <- ts' tm3 ctx''
      if tm1'.tag == .Bytes && tm2'.tag == .Nat && tm3'.tag == .Bytes
      then
        .some (.Builtin 3 .Memcpy (.cons tm1' (.cons tm2' (.cons tm3' .nil))) (.Prod .Bytes .Bytes), ctx''')
      else .none

def ts (tm : Tm 0 Unit) : Option (Tm 0 Ty) :=
  (ts' tm #v[]).map Prod.fst

def tc (tm : Tm 0 Unit) (ty : Ty) : Option Bool :=
  (ts tm).map (fun tm' => tm'.tag == ty)

def iwt (tm : Tm 0 Unit) : Bool :=
  (ts tm).isSome

-- write tests
