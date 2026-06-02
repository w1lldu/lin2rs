import Lean

import Lin2rs.Types


open Lin2rs


def Ctx := Std.HashMap String Ty
  deriving BEq


def tc (e : Tm) (ctx : Ctx) : Option (Pt × Ctx) :=
  match e with
  | .Num _ => .some (Pt.PNat, ctx)
  | .Id id =>
    match ctx.get? id with
    | none => .none
    | some (q, t) =>
      match q with
      | .lin => .some (t, ctx.erase id)
  | .Add tm1 tm2 =>
    match tc tm1 ctx with
    | .none => .none
    | .some (pt1, ctx') =>
      if pt1 == .PNat
      then
        match tc tm2 ctx' with
        | .none => .none
        | .some (pt2, ctx'') =>
          if pt2 == .PNat
          then .some (.PNat, ctx'')
          else .none
      else .none
  | .If cond thn els =>
    match tc cond ctx with
    | .none => .none
    | .some (ptc, ctx') =>
      if ptc == .PNat
      then
        match tc thn ctx' with
        | .none => .none
        | .some (ptt, ctxt) =>
          match tc els ctx' with
          | .none => .none
          | .some (pte, ctxe) =>
            if ptt == pte && ctxt == ctxe
            then (ptt, ctxt)
            else .none
      else .none
  | .Let id ty assn body =>
    match tc assn ctx with
    | .none => .none
    | .some (pta, ctx') =>
      -- check-type
      if ty.snd == pta
      then
        match tc body (ctx'.insert id ty) with
        | .none => .none
        | .some (ptb, ctx'') =>
          match ty.fst with
          | .lin =>
            if (ctx''.contains id)
            then .none
            else (ptb, ctx'')
      else .none

-- def check-type t1 t2 thunk : Option (Pt × Ctx)
-- isn't this halfway to continuations
-- continuations do not solve the problem of nesting,
-- they are just nested in a different way

-- write tests
