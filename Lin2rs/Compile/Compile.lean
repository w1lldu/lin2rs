import Lean

import Lin2rs.Compile.Types
import Lin2rs.Compile.Tc

open Lean

open Compile

namespace Compile

-- insert m new vars
-- def Tm.shift (tm : Tm n α) (m : Nat) : Tm (n + m) α :=
-- sorry


mutual
def tag_tm (tm : Tm n α) (tag : Nat) : Tm n (α × Nat) × Nat :=
  match tm with
  | .Num num t => (.Num num (t, tag), tag + 1)
  | .Bool b t => (.Bool b (t, tag), tag + 1)
  | .Prod l r t =>
    let (lt, tag') := tag_tm l (tag + 1)
    let (rt, tag'') := tag_tm r tag'
    (.Prod lt rt (t, tag), tag'')
  | .BVar id idx t => (.BVar id idx (t, tag), tag + 1)
  | .FVar id t => (.FVar id (t, tag), tag + 1)
  | .If cond thn els t =>
    let (condt, tag') := tag_tm cond (tag + 1)
    let (thnt, tag'') := tag_tm thn tag'
    let (elst, tag''') := tag_tm els tag''
    (.If condt thnt elst (t, tag), tag''')
  | .Split p l r body t =>
    let (pt, tag') := tag_tm p (tag + 1)
    let (bodyt, tag'') := tag_tm body tag'
    (.Split pt l r bodyt (t, tag), tag'')
  | .Let id ty assn body t =>
    let (assnt, tag') := tag_tm assn (tag + 1)
    let (bodyt, tag'') := tag_tm body tag'
    (.Let id ty assnt bodyt (t, tag), tag'')
  | .Builtin l b tv t =>
    let (tvt, tag') := tag_tv tv (tag + 1)
    (.Builtin l b tvt (t, tag), tag')

  def tag_tv (tv : TmVec l n α) (tag : Nat) : TmVec l n (α × Nat) × Nat :=
    match tv with
    | .nil => (.nil, tag)
    | .cons t ts =>
      let (tt, tag') := tag_tm t tag
      let (tst, tag'') := tag_tv ts tag'
      (.cons tt tst, tag'')
end

mutual
  def collapse_args (args : List RVal) :=
    match args with
    | .nil => ""
    | .cons arg .nil => arg.to_c
    | .cons arg args' => arg.to_c ++ ", " ++ (collapse_args args')

  def RVal.to_c (i : RVal) : String :=
    match i with
    | .RNum n => s!"(void *)(intptr_t){n.repr}"
    | .RVar id => id
    | .RCall cf args => s!"{cf.repr}({collapse_args args})"
    | .RDeref s o => s!"*(void **)({s} + {o.repr} * ptr_size)"
end

mutual
  def CExpr.to_c (ce : CExpr) : String :=
    match ce with
    | .CDecl id => s!"void *{id}"
    | .CIf cond thn els iname =>
      s!"if ({cond.to_c}) " ++ "{\n" ++ (thn.to_c_set iname) ++ ";\n} else {\n" ++ (els.to_c_set iname) ++ ";\n}"
    | .CLet id assn => s!"void *{id} = {assn.to_c}"
    | .CSet id assn => s!"{id} = {assn.to_c}"
    | .CAssn id o assn => s!"*(void **)({id} + {o.repr} * ptr_size) = {assn.to_c}"
    | .CCall cf args => s!"{cf.repr}({collapse_args args})"

  def Seq.to_c (s : Seq) : String :=
    match s with
    | .mk .nil i => i.to_c
    | .mk (.cons ce .nil) i => ce.to_c ++ ";\n" ++ i.to_c
    | .mk (.cons ce ces) i => ce.to_c ++ ";\n" ++ (Seq.mk ces i).to_c

  def Seq.to_c_set (s : Seq) (var : String) : String :=
    match s with
    | .mk .nil i => s!"{var} = {i.to_c}"
    | .mk (.cons ce .nil) i => ce.to_c ++ ";\n" ++ s!"{var} = {i.to_c}"
    | .mk (.cons ce ces) i => ce.to_c ++ ";\n" ++ (Seq.mk ces i).to_c
end

def compile_drop (rv : RVal) (ty : Ty) (n : Nat) (t : Nat) : List CExpr × Nat :=
  match ty with
  | .Nat | .Bool => ([], t)
  | .Bytes => ([.CCall .Free [rv]], t)
  | .Prod l r =>
    let pname := s!"drop_{n}_{t}"
    let pl := s!"drop_l_{n}_{t}"
    let pr := s!"drop_r_{n}_{t}"
    let (ls, t') := compile_drop (.RVar pl) l n (t + 1)
    let (rs, t'') := compile_drop (.RVar pr) r n t'
    ([
        .CLet pname rv,
        .CLet pl (.RDeref pname 0),
        .CLet pr (.RDeref pname 1)
      ] ++ ls ++ rs ++ [
        .CCall .Free [.RVar pname]
      ],
      t'')

mutual
  def compile_tm (tm : Tm n (Ty × Nat)) (env : Vector String n) : Seq :=
    match tm with
    | .Num num _ => .mk [] (.RNum num)
    | .Bool b _ => .mk [] (.RNum (if b then 1 else 0))
    | .Prod l r t =>
      let pname := "prod_" ++ t.snd.repr
      let .mk ls l' := compile_tm l env
      let .mk rs r' := compile_tm r env
      .mk (ls ++ rs ++ [
        .CLet pname (.RCall .Malloc [.RCall .Mul [(.RNum 2), (.RVar "ptr_size")]]),
        .CAssn pname 0 l',
        .CAssn pname 1 r'
      ]) (.RVar pname)
    | .BVar _ idx _ =>
      let idx' : Fin n := .mk (n - 1 - idx) (by omega)
      .mk [] (.RVar (env.reverse.get idx'))
    | .FVar id _ => .mk [] (.RVar id)
    | .If cond thn els t =>
      let iname := "if_" ++ t.snd.repr
      let .mk conds cond' := compile_tm cond env
      let thn' := compile_tm thn env
      let els' := compile_tm els env
      .mk (conds ++ [
        .CDecl iname,
        .CIf cond' thn' els' iname
      ]) (.RVar iname)
    | .Split p l r body t =>
      let pname' := "prod_" ++ t.snd.repr
      let pl := "l" ++ t.snd.repr ++ l
      let pr := "r" ++ t.snd.repr ++ r
      let .mk ps p' := compile_tm p env
      let .mk bodys body' := compile_tm body ((env.push r).push l)
      .mk (ps ++ [
        -- p' is always a CVar but Lean doesn't know that
        .CLet pname' p',
        .CLet pl (.RDeref pname' 0),
        .CLet pr (.RDeref pname' 1)
      ] ++ bodys) body'
    | .Let id _ assn body t =>
      let id' := "var_" ++ t.snd.repr ++ "_" ++ id
      let .mk assns assn' := compile_tm assn env
      let .mk bodys body' := compile_tm body (env.push id')
      .mk (assns ++ [.CLet id' assn'] ++ bodys) body'
--       let id := "var" ++ t.snd.repr ++ id
--       define_result (compile_ctm assn env) id ++
--       compile_atm body (env.push id)
    | .Builtin l b tv t =>
      match b, tv with
      | .Drop, .cons tm .nil =>
        let .mk arg arg' := compile_tm tm env
        -- t is split for easier termination proving
        let .mk drop _ := compile_drop arg' t.fst t.snd 0
        .mk (arg ++ drop) (.RNum 0)
      -- should be implemented in c
      -- | .Fill_rnd, .cons tm .nil =>
      --   let bytes' := s!"bytes_{t.snd}"
      --   let len := s!"len_{t.snd}"
      --   let .mk arg arg' := compile_tm tm env
      --   .mk (arg ++ [
      --       .CLet bytes' arg',
      --       .CLet len (.RDeref bytes' 0)
      --     ]) (.RCall .Fill_rnd [arg', (.RVar len)])
      | .Alloc, .cons tm .nil =>
        let .mk arg arg' := compile_tm tm env
        let bytes := s!"alloc_{t.snd}"
        .mk (arg ++ [
            .CLet bytes (.RCall .Malloc [.RCall .Add [arg', .RNum 1]]),
            .CAssn bytes 0 arg'
          ]) (.RVar bytes)
      | _, tv =>
        let cf := match b with
        | .Add => .Add
        | .Memcpy => .Memcpy
        | .Fill_rnd => .Fill_rnd
        | .Alloc => .NoOp
        | .Drop => .NoOp
        let (tms, args) := ((compile_tv tv env).map (fun (.mk tms tm) => (tms, tm))).unzip
        .mk (tms.foldr (· ++ ·) []) (.RCall cf args)

  def compile_tv (tv : TmVec l n (Ty × Nat)) (env : Vector String n) : List Seq :=
    match tv with
    | .nil => .nil
    | .cons tm tms => (compile_tm tm env) :: (compile_tv tms env)
end


-- add stuff at beginning (see test.c)
-- todo: add indentation (or autoformat?)
-- why does it need .{0}?
def compile_to_string (tm : Tm 0 Ty) : String :=
  (compile_tm (tag_tm tm 0).fst #v[]).to_c
