import Lean

import Lin2rs.Types


open Lin2rs


def Ctx := Std.HashMap String Ty
  deriving BEq


-- well-formedness check?

def typ (e : Tm) (ctx : Ctx) : Option (Pt × Ctx) :=
  match e with
  | .Num _ => .some (.Nat, ctx)
  | .Id id =>
    match ctx.get? id with
    | none => .none
    | some (q, t) =>
      match q with
      | .Lin => .some (t, ctx.erase id)
  | .Add tm1 tm2 =>
    match typ tm1 ctx with
    | .none => .none
    | .some (pt1, ctx') =>
      if pt1 == .Nat
      then
        match typ tm2 ctx' with
        | .none => .none
        | .some (pt2, ctx'') =>
          if pt2 == .Nat
          then .some (.Nat, ctx'')
          else .none
      else .none
  | .If cond thn els =>
    match typ cond ctx with
    | .none => .none
    | .some (ptc, ctx') =>
      if ptc == .Nat
      then
        match typ thn ctx' with
        | .none => .none
        | .some (ptt, ctxt) =>
          match typ els ctx' with
          | .none => .none
          | .some (pte, ctxe) =>
            if ptt == pte && ctxt == ctxe
            then (ptt, ctxt)
            else .none
      else .none
  | .Let id ty assn body =>
    match typ assn ctx with
    | .none => .none
    | .some (pta, ctx') =>
      if ty.snd == pta
      then
        match typ body (ctx'.insert id ty) with
        | .none => .none
        | .some (ptb, ctx'') =>
          match ty.fst with
          | .Lin =>
            if (ctx''.contains id)
            then .none
            else (ptb, ctx'')
      else .none

def typeof (e : Tm) : Option (Pt × Ctx) :=
  typ e Std.HashMap.emptyWithCapacity

def tc (e : Tm) (pt : Pt) : Bool :=
  match typeof e with
  | .none => false
  | .some (pt', _) => pt == pt'

def iwt (e : Tm) : Bool :=
  Option.isSome (typeof e)

-- def check-type t1 t2 thunk : Option (Pt × Ctx)
-- isn't this halfway to continuations
-- continuations do not solve the problem of nesting,
-- they are just nested in a different way

-- write tests
