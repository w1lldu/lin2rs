import Lean

import Lin2rs.Compile.Types

open Lean

open Compile

namespace Compile

inductive Bind : Nat -> Nat -> Type 1 where
  | Let : String -> Ty -> CTm n Unit -> Bind n (n + 1)
  | Split : Imm n -> String -> String -> Bind n (n + 2)

def Bind.bind (b : Bind n m) (atm : ATm m Unit) : ATm n Unit :=
  match b with
  | .Let id ty ctm => .Let id ty ctm atm ()
  | .Split p l r => .Split p l r atm ()

inductive Binds : Nat -> Nat -> Type 1 where
  | nil : Binds n n
  | cons : Bind n m -> Binds m p -> Binds n p

def Binds.bind (bs : Binds n m) (atm : ATm m Unit) : ATm n Unit :=
  match bs with
  | .nil => atm
  | .cons b bs => b.bind (bs.bind atm)

mutual
  def anfA (tm : Tm n) : ATm n Unit :=
    let ⟨_, res, binds⟩ := anfC tm
    binds.bind (.CTm res)

  def anfC (tm : Tm n) : Σ m, CTm m Unit × Binds n m :=
    match tm with
    | _ =>
      let ⟨m, imm, binds⟩ := anfI tm
      ⟨m, .Imm imm, binds⟩

  def anfI (tm : Tm n) : Σ m, Imm m × Binds n m :=
    match tm with
    | _ => sorry
end

def anf (tm : Tm n) : ATm n Unit :=
  anfA tm

mutual
  def tag_ctm (ctm : CTm n Unit) (n : Nat) : CTm n Nat × Nat :=
    (.Imm (.Num 0), 0)

  -- tagging split should increase by 1, use multiple var names
  def tag_atm (atm : ATm n Unit) (n : Nat) : ATm n Nat × Nat :=
    (.CTm (.Imm (.Num 0)), 0)
end

def compile_imm (imm : Imm n) (env : Vector String n) : String :=
  match imm with
  | .Num n => n.repr
  -- TODO: figure out types and casting
  | .Bool b => b.toNat.repr
  | .BVar _ idx =>
      -- vector pushes to the back
      let idx' : Fin n := .mk (n - 1 - idx) (by omega)
      env.reverse.get idx
  | .FVar id => id

def set (var : String) (val : String) :=
  var ++ " = " ++ val

-- TODO: figure out types and casting
def define (var : String) (val : String) :=
  "int " ++ var ++ " = " ++ val

def set_result (exprs : List String) (var : String) : List String :=
  exprs.foldr (fun expr exprs => (if exprs == [] then set var expr else expr) :: exprs) []

def define_result (exprs : List String) (var : String) : List String :=
  exprs.foldr (fun expr exprs => (if exprs == [] then define var expr else expr) :: exprs) []

def collapse (exprs : List String) :=
  exprs.foldr (fun expr exprs => expr ++ ";" ++ exprs) ""

mutual
  -- todo: take into account qualifiers?
  def compile_ctm (ctm : CTm n Nat) (env : Vector String n) : List String :=
    match ctm with
    | .Prod _ l r t =>
      let prod := "prod" ++ t.repr
      let prodp := "prodp" ++ t.repr
      [
        "struct prod " ++ prod ++ " = { " ++ compile_imm l env ++ ", " ++ compile_imm r env ++ " }",
        "LL " ++ prodp ++ " == (LL) &" ++ prod,
        prodp
      ]
    | .Add i1 i2 => [ compile_imm i1 env ++ " + " ++ compile_imm i2 env ]
    | .If cond thn els t =>
      let res := "if" ++ t.repr
      [
        "int " ++ res,
        -- if (...) {...}; is valid
        "if (" ++ compile_imm cond env ++ ") {" ++
      collapse (set_result (compile_atm thn env) res) ++ "} else {" ++
      collapse (set_result (compile_atm els env) res) ++ "}",
        res
      ]
    | .Builtin1 b1 i => [ b1.repr ++ "(" ++ compile_imm i env ++ ")" ]
    | .Builtin3 b3 i1 i2 i3 => [ b3.repr ++ "(" ++ compile_imm i1 env ++ ", " ++ compile_imm i2 env ++ ", " ++ compile_imm i3 env ++ ")" ]
    | .Imm imm => [ compile_imm imm env ]

  def compile_atm (atm : ATm n Nat) (env : Vector String n) :=
    -- TODO: figure out types and casting
    match atm with
    | .Split p l r body t =>
      let prod := "p" ++ t.repr
      let prodl := "l" ++ t.repr ++ l
      let prodr := "r" ++ t.repr ++ r
      ("struct prod " ++ prod ++ " = *(struct prod *) " ++ (compile_imm p env)) ::
      define prodl (prod ++ ".l") ::
      define prodr (prod ++ ".r") ::
      compile_atm body ((env.push prodr).push prodl)
    | .Let id _ assn body t =>
      let id := "var" ++ t.repr ++ id
      define_result (compile_ctm assn env) id ++
      compile_atm body (env.push id)
    | .CTm ctm => compile_ctm ctm env
end

-- struct prod { int l ; int r };

-- add stuff at beginning (see test.c)
-- todo: add indentation (or autoformat?)
def compile_to_string (tm : Tm n) : String :=
  collapse (compile_atm (tag_atm (anf tm) 0).fst #v[])
