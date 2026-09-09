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
  | .Prod q l r t =>
    let (lt, tag') := tag_tm l (tag + 1)
    let (rt, tag'') := tag_tm r tag'
    (.Prod q lt rt (t, tag), tag'')
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

-- def compile_imm (imm : Imm n (Ty × Nat)) (env : Vector String n) : String :=
--   match imm with
--   | .Num num _ => num.repr
--   | .Bool b _ => b.toNat.repr
--   | .BVar _ idx _ =>
--       -- vector pushes to the back
--       let idx' : Fin n := .mk (n - 1 - idx) (by omega)
--       env.reverse.get idx
--   | .FVar id => id

-- def set (var : String) (val : String) :=
--   var ++ " = " ++ val

-- -- TODO: figure out types and casting
-- def define (var : String) (val : String) :=
--   "LL " ++ var ++ " = " ++ val

-- def set_result (exprs : List String) (var : String) : List String :=
--   exprs.foldr (fun expr exprs => (if exprs == [] then set var expr else expr) :: exprs) []

-- def define_result (exprs : List String) (var : String) : List String :=
--   exprs.foldr (fun expr exprs => (if exprs == [] then define var expr else expr) :: exprs) []

-- def collapse (exprs : List String) :=
--   exprs.foldr (fun expr exprs => expr ++ ";" ++ exprs) ""

-- mutual
--   -- todo: take into account qualifiers?
--   def compile_ctm (ctm : CTm n (Ty × Nat)) (env : Vector String n) : List String :=
--     match ctm with
--     | .Prod _ l r t =>
--       let prod := "prod" ++ t.snd.repr
--       let prodp := "prodp" ++ t.snd.repr
--       [
--         "struct prod " ++ prod ++ " = { " ++ compile_imm l env ++ ", " ++ compile_imm r env ++ " }",
--         "LL " ++ prodp ++ " == (LL) &" ++ prod,
--         prodp
--       ]
--     | .Add i1 i2 _ => [ compile_imm i1 env ++ " + " ++ compile_imm i2 env ]
--     | .If cond thn els t =>
--       let res := "if" ++ t.snd.repr
--       [
--         "LL " ++ res,
--         -- if (...) {...}; is valid
--         "if (" ++ compile_imm cond env ++ ") {" ++
--       collapse (set_result (compile_atm thn env) res) ++ "} else {" ++
--       collapse (set_result (compile_atm els env) res) ++ "}",
--         res
--       ]
--     | .Builtin1 b1 i _ => [ b1.repr ++ "(" ++ compile_imm i env ++ ")" ]
--     | .Builtin3 b3 i1 i2 i3 _ => [ b3.repr ++ "(" ++ compile_imm i1 env ++ ", " ++ compile_imm i2 env ++ ", " ++ compile_imm i3 env ++ ")" ]
--     | .Imm imm => [ compile_imm imm env ]

--   def compile_atm (atm : ATm n (Ty × Nat)) (env : Vector String n) :=
--     -- TODO: figure out types and casting
--     match atm with
--     | .Split p l r body t =>
--       let prod := "p" ++ t.snd.repr
--       let prodl := "l" ++ t.snd.repr ++ l
--       let prodr := "r" ++ t.snd.repr ++ r
--       ("struct prod " ++ prod ++ " = *(struct prod *) " ++ (compile_imm p env)) ::
--       define prodl (prod ++ ".l") ::
--       define prodr (prod ++ ".r") ::
--       compile_atm body ((env.push prodr).push prodl)
--     | .Let id _ assn body t =>
--       let id := "var" ++ t.snd.repr ++ id
--       define_result (compile_ctm assn env) id ++
--       compile_atm body (env.push id)
--     | .CTm ctm => compile_ctm ctm env
-- end

mutual
  def collapse_args (args : List Imm) :=
    match args with
    | .nil => ""
    | .cons arg .nil => arg.to_c
    | .cons arg args' => arg.to_c ++ ", " ++ (collapse_args args')

  def Imm.to_c (i : Imm) : String :=
    match i with
    | .CNum n => s!"(void *)(intptr_t){n.repr}"
    | .CVar id => id
    | .CCall b args => s!"{b.repr}({collapse_args args})"
    | .CMalloc n => s!"malloc({n.repr})"
    | .CDeref s o => s!"*(void **)({s} + {o.repr} * ptr_size)"
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
    | .CDrop var => s!"drop({var.to_c})"

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

mutual
  def compile_tm (tm : Tm n (Ty × Nat)) (env : Vector String n) : Seq :=
    match tm with
    | .Num num _ => .mk [] (.CNum num)
    | .Bool b _ => .mk [] (.CNum (if b then 1 else 0))
    | .Prod _ l r t =>
      let pname := "prod_" ++ t.snd.repr
      let .mk ls l' := compile_tm l env
      let .mk rs r' := compile_tm r env
      .mk (ls ++ rs ++ [
        .CLet pname (.CMalloc 2),
        .CAssn pname 0 l',
        .CAssn pname 1 r'
      ]) (.CVar pname)
    | .BVar _ idx _ =>
      let idx' : Fin n := .mk (n - 1 - idx) (by omega)
      .mk [] (.CVar (env.reverse.get idx'))
    | .FVar id _ => .mk [] (.CVar id)
    | .If cond thn els t =>
      let iname := "if_" ++ t.snd.repr
      let .mk conds cond' := compile_tm cond env
      let thn' := compile_tm thn env
      let els' := compile_tm els env
      .mk (conds ++ [
        .CDecl iname,
        .CIf cond' thn' els' iname
      ]) (.CVar iname)
    | .Split p l r body t =>
      let pname' := "prod_" ++ t.snd.repr
      let pl := "l" ++ t.snd.repr ++ l
      let pr := "r" ++ t.snd.repr ++ r
      let .mk ps p' := compile_tm p env
      let .mk bodys body' := compile_tm body ((env.push r).push l)
      .mk (ps ++ [
        -- p' is always a CVar but Lean doesn't know that
        .CLet pname' p',
        .CLet pl (.CDeref pname' 0),
        .CLet pr (.CDeref pname' 1)
      ] ++ bodys) body'
    | .Let id _ assn body t =>
      let id' := "var_" ++ t.snd.repr ++ "_" ++ id
      let .mk assns assn' := compile_tm assn env
      let .mk bodys body' := compile_tm body (env.push id')
      .mk (assns ++ [.CLet id' assn'] ++ bodys) body'
--       let id := "var" ++ t.snd.repr ++ id
--       define_result (compile_ctm assn env) id ++
--       compile_atm body (env.push id)
    | .Builtin l b tv _ =>
      let (tms, args) := ((compile_tv tv env).map (fun (.mk tms tm) => (tms, tm))).unzip
      .mk (tms.foldr (· ++ ·) []) (.CCall b args)

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
