import Lean

import Lin2rs.Compile.Types
import Lin2rs.Compile.Tc

open Lean

open Compile

namespace Compile

-- insert m new vars
def Tm.shift (tm : Tm n α) (m : Nat) : Tm (n + m) α :=
sorry

def Imm.shift (imm : Imm n α) (m : Nat) : Imm (n + m) α :=
  sorry

def CTm.shift (ctm : CTm n α) (m : Nat): CTm (n + m) α :=
  sorry

def ATm.shift (atm : ATm n α) (m : Nat): ATm (n + m) α :=
  sorry

inductive Bind : Nat -> Nat -> Type 1 where
  | Let : String -> Ty -> CTm n Ty -> Bind n (n + 1)
  | Split : Imm n Ty -> String -> String -> Bind n (n + 2)

def Bind.bind (b : Bind n m) (atm : ATm m Ty) : ATm n Ty :=
  match b with
  | .Let id ty ctm => .Let id ty ctm atm atm.tag
  | .Split p l r => .Split p l r atm atm.tag

inductive Binds : Nat -> Nat -> Type 1 where
  | nil : Binds n n
  | cons : Bind n m -> Binds m p -> Binds n p

def Binds.bind (bs : Binds n m) (atm : ATm m Ty) : ATm n Ty :=
  match bs with
  | .nil => atm
  | .cons b bs => b.bind (bs.bind atm)

def Binds.append (bs1 : Binds n m) (bs2 : Binds m p) : Binds n p :=
  sorry

def Binds.snoc (bs : Binds n m) (b' : Bind m p) : Binds n p :=
  match bs with
  | .nil => .cons b' .nil
  | .cons b bs => .cons b (bs.snoc b')

mutual
  def anfA (tm : Tm n Ty) : ATm n Ty :=
    let ⟨_, res, binds, _⟩ := anfC tm
    binds.bind (.CTm res)

  def anfC (tm : Tm n Ty) : Σ' m, CTm m Ty ×' Binds n m ×' n ≤ m :=
    match tm with
    | .Num _ _ | .Bool _ _ | .BVar _ _ _ | .FVar _ =>
      let ⟨n', imm, setup⟩ := anfI tm
      ⟨n', .Imm imm, setup⟩
    | .Prod q l r ty =>
      let ⟨m, limm, ls, nm⟩ := anfI l
      let ⟨p, rimm, rs, mp⟩ := anfI (r.shift (m - n))
      haveI : (n + (m - n)) = m := by
        omega
      let rs' : Binds m p := cast (by rw [this]) rs
      haveI : (m + (p - m)) = p := by
        omega
      let limm' : Imm p Ty := cast (by rw [this]) (limm.shift (p - m))
      haveI : n ≤ p := by
        omega
      ⟨p, .Prod q limm' rimm ty, ls.append rs', this⟩
    | _ =>
      let ⟨m, imm, binds⟩ := anfI tm
      ⟨m, .Imm imm, binds⟩

  def anfI (tm : Tm n Ty) : Σ' m, Imm m Ty ×' Binds n m ×' (n ≤ m) :=
    match tm with
    | .Num num ty => ⟨n, .Num num ty, .nil, Nat.le_refl n⟩
    | .Bool b ty => ⟨n, .Bool b ty, .nil, Nat.le_refl n⟩
    | .Prod q l r ty =>
      let ⟨n', anfed, setup, _⟩ := anfC tm
      ⟨n' + 1, .BVar "" 0 ty, setup.snoc (.Let "" ty anfed), by omega⟩
    | _ => sorry
end

def anf (tm : Tm n Ty) : ATm n Ty :=
  anfA tm

mutual
  def tag_ctm (ctm : CTm n α) (t : Nat) : CTm n (α × Nat) × Nat :=
    (.Imm (.Num 0 (ctm.tag, 0)), 0)

  -- tagging split should increase by 1, use multiple var names
  def tag_atm (atm : ATm n α) (t : Nat) : ATm n (α × Nat) × Nat :=
    (.CTm (.Imm (.Num 0 (atm.tag, 0))), 0)
end

def compile_imm (imm : Imm n (Ty × Nat)) (env : Vector String n) : String :=
  match imm with
  | .Num num _ => num.repr
  | .Bool b _ => b.toNat.repr
  | .BVar _ idx _ =>
      -- vector pushes to the back
      let idx' : Fin n := .mk (n - 1 - idx) (by omega)
      env.reverse.get idx
  | .FVar id => id

def set (var : String) (val : String) :=
  var ++ " = " ++ val

-- TODO: figure out types and casting
def define (var : String) (val : String) :=
  "LL " ++ var ++ " = " ++ val

def set_result (exprs : List String) (var : String) : List String :=
  exprs.foldr (fun expr exprs => (if exprs == [] then set var expr else expr) :: exprs) []

def define_result (exprs : List String) (var : String) : List String :=
  exprs.foldr (fun expr exprs => (if exprs == [] then define var expr else expr) :: exprs) []

def collapse (exprs : List String) :=
  exprs.foldr (fun expr exprs => expr ++ ";" ++ exprs) ""

mutual
  -- todo: take into account qualifiers?
  def compile_ctm (ctm : CTm n (Ty × Nat)) (env : Vector String n) : List String :=
    match ctm with
    | .Prod _ l r t =>
      let prod := "prod" ++ t.snd.repr
      let prodp := "prodp" ++ t.snd.repr
      [
        "struct prod " ++ prod ++ " = { " ++ compile_imm l env ++ ", " ++ compile_imm r env ++ " }",
        "LL " ++ prodp ++ " == (LL) &" ++ prod,
        prodp
      ]
    | .Add i1 i2 _ => [ compile_imm i1 env ++ " + " ++ compile_imm i2 env ]
    | .If cond thn els t =>
      let res := "if" ++ t.snd.repr
      [
        "LL " ++ res,
        -- if (...) {...}; is valid
        "if (" ++ compile_imm cond env ++ ") {" ++
      collapse (set_result (compile_atm thn env) res) ++ "} else {" ++
      collapse (set_result (compile_atm els env) res) ++ "}",
        res
      ]
    | .Builtin1 b1 i _ => [ b1.repr ++ "(" ++ compile_imm i env ++ ")" ]
    | .Builtin3 b3 i1 i2 i3 _ => [ b3.repr ++ "(" ++ compile_imm i1 env ++ ", " ++ compile_imm i2 env ++ ", " ++ compile_imm i3 env ++ ")" ]
    | .Imm imm => [ compile_imm imm env ]

  def compile_atm (atm : ATm n (Ty × Nat)) (env : Vector String n) :=
    -- TODO: figure out types and casting
    match atm with
    | .Split p l r body t =>
      let prod := "p" ++ t.snd.repr
      let prodl := "l" ++ t.snd.repr ++ l
      let prodr := "r" ++ t.snd.repr ++ r
      ("struct prod " ++ prod ++ " = *(struct prod *) " ++ (compile_imm p env)) ::
      define prodl (prod ++ ".l") ::
      define prodr (prod ++ ".r") ::
      compile_atm body ((env.push prodr).push prodl)
    | .Let id _ assn body t =>
      let id := "var" ++ t.snd.repr ++ id
      define_result (compile_ctm assn env) id ++
      compile_atm body (env.push id)
    | .CTm ctm => compile_ctm ctm env
end

-- struct prod { LL l ; LL r };

-- add stuff at beginning (see test.c)
-- todo: add indentation (or autoformat?)
-- why does it need .{0}?
def compile_to_string (tm : Tm 0 Ty) : String :=
  collapse (compile_atm (tag_atm.{0} (anf tm) 0).fst #v[])
