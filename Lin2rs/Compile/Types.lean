import Lean

open Lean

namespace Compile

-- a ≤ b => a is a subtype of b (a can cast to b)

-- inductive Qual where
--   | Un : Qual
--   -- | Aff : Qual
--   | Lin : Qual
--   deriving Repr, BEq, DecidableEq

-- def Qual.le (q1 q2 : Qual) : Bool:=
--   match q1, q2 with
--   | Un, Lin => true
--   | Lin, Un => false
--   | _, _ => true

-- instance : LE Qual where
--   le q1 q2 := Qual.le q1 q2 = true

-- instance : LT Qual where
--   lt q1 q2 := q1 ≤ q2 ∧ q1 ≠ q2

-- instance {q1 q2 : Qual} : Decidable (q1 ≤ q2) := by
--   simp [LE.le]
--   infer_instance

-- instance (q1 q2 : Qual) : Decidable (q1 < q2) := by
--   simp [LT.lt]
--   infer_instance

inductive Ty where
  | Nat : Ty
  | Bool : Ty
  | Bytes : Ty
  | Prod : Ty -> Ty -> Ty
  deriving Repr, BEq

-- mutual
--   inductive Pt where
--     | Nat : Pt
--     | Bool : Pt
--     | Bytes : Nat -> Pt
--     | Prod : Ty -> Ty -> Pt
--     deriving Repr, BEq

--   -- cannot prove termination with structure
--   -- doesnt matter since we ended up making everything partial?
--   -- structure Ty where
--   --   qual : Qual
--   --   pt : Pt
--   --   deriving BEq, Repr, DecidableEq
--   inductive Ty where
--     | mk : Qual -> Pt -> Ty
--     deriving Repr, BEq, DecidableEq
-- end

-- def Ty.le (ty1 ty2 : Ty) : Bool :=
--   match ty1, ty2 with
--     | (mk q1 .Nat), (mk q2 .Nat) | (mk q1 .Bool), (mk q2 .Bool) => q1 ≤ q2
--     | (mk q1 (.Prod ty1l ty1r)), (mk q2 (.Prod ty2l ty2r)) => q1 ≤ q2 ∧ Ty.le ty1l ty2l ∧ Ty.le ty1r ty2r
--     | _, _ => false
--   termination_by sizeOf ty1 + sizeOf ty2

-- instance : LE Ty where
--   le ty1 ty2 := Ty.le ty1 ty2 = true

-- instance : LT Ty where
--   lt ty1 ty2 := ty1 ≤ ty2 ∧ ty1 ≠ ty2

-- instance (ty1 ty2 : Ty) : Decidable (ty1 ≤ ty2) := by
--   simp [LE.le]
--   infer_instance

-- instance (ty1 ty2 : Ty) : Decidable (ty1 < ty2) := by
--   simp [LT.lt]
--   infer_instance

inductive Builtin : Nat -> Type
  | Add : Builtin 2
  | Alloc : Builtin 1
  | Drop : Builtin 1
  | Fill_rnd : Builtin 1
  | Memcpy : Builtin 3
  deriving Repr, BEq

def Builtin.repr (b : Builtin n) :=
  match b with
  | Add => "add"
  | Alloc => "alloc"
  | Drop => "drop"
  | Fill_rnd => "fill_rnd"
  | Memcpy => "memcpy"

inductive Exp where
  | Num : Nat -> Exp
  | Bool : Bool -> Exp
  | Prod : Exp -> Exp -> Exp
  | Id : String -> Exp
  | If : Exp -> Exp -> Exp -> Exp
  | Split : Exp -> String -> String -> Exp -> Exp
  | Let : String -> Ty -> Exp -> Exp -> Exp
  | Builtin : Builtin n -> List Exp -> Exp
  deriving Repr, BEq

-- keep the names for printing
mutual
  inductive TmVec : Nat -> Nat -> Type u -> Type (u + 1) where
    | nil : TmVec 0 n α
    | cons : Tm n α -> TmVec l n α -> TmVec (l + 1) n α
  -- deriving Repr, BEq

  inductive Tm : Nat -> Type u -> Type (u + 1)
    | Num {n α} : Nat -> α -> Tm n α
    | Bool {n α} : Bool -> α -> Tm n α
    | Prod {n α} : Tm n α -> Tm n α -> α -> Tm n α
    | BVar {n α} : String -> Fin n -> α -> Tm n α
    | FVar {n α} : String -> α -> Tm n α
    | If {n α} : Tm n α -> Tm n α -> Tm n α -> α -> Tm n α
    | Split {n α} : Tm n α -> String -> String -> Tm (n + 2) α -> α -> Tm n α
    | Let {n α} : String -> Ty -> Tm n α -> Tm (n + 1) α -> α -> Tm n α
    | Builtin {n α} (l) : Builtin l -> TmVec l n α -> α -> Tm n α
  -- deriving Repr, BEq
end

mutual
  def beqTmVec [BEq α] : TmVec l n α -> TmVec l n α -> Bool
    | .nil, .nil => true
    | .cons t ts, .cons t' ts' =>
      beqTm t t' && beqTmVec ts ts'
    | _, _ => false

  def beqTm [BEq α] : Tm n α -> Tm n α -> Bool
    | .Num num a, .Num num' a' =>
      num == num' && a == a'
    | .Bool b a, .Bool b' a' =>
      b == b' && a == a'
    | .Prod l r a, .Prod l' r' a' =>
      beqTm l l' && beqTm r r' && a == a'
    | .BVar id idx a, .BVar id' idx' a' =>
      id == id' && idx == idx' && a == a'
    | .FVar id a, .FVar id' a' =>
      id == id' && a == a'
    | .If cond thn els a, .If cond' thn' els' a' =>
      beqTm cond cond' && beqTm thn thn' && beqTm els els' && a == a'
    | .Split p l r body a, .Split p' l' r' body' a' =>
      beqTm p p' && l == l' && r == r' && beqTm body body' && a == a'
    | .Let id ty assn body a, .Let id' ty' assn' body' a' =>
      id == id' && ty == ty' && beqTm assn assn' && beqTm body body' && a == a'
    | .Builtin l b tv a, .Builtin l' b' tv' a' =>
      if h : l = l' then
        -- thanks LLM
        match h with
        | rfl => b == b' && beqTmVec tv tv' && a == a'
      else
        false
    | _, _ => false
end

instance [BEq α] : BEq (TmVec l n α) where
  beq := beqTmVec

instance [BEq α] : BEq (Tm n α) where
  beq := beqTm

mutual
  def reprTmVec [Repr α] (tv : TmVec l n α) (prec : Nat) : Format :=
    match tv with
      | .nil => "TmVec.nil"
      | .cons t ts => s!"(TmVec.cons {reprTm t (prec + 1)} {reprTmVec ts (prec + 1)})"

  def reprTm [Repr α] (tm : Tm n α) (prec : Nat) : Format :=
    match tm with
      | .Num num a => s!"(Tm.Num {num} {reprPrec a prec})"
      | .Bool b a => s!"(Tm.Bool {b} {reprPrec a prec})"
      | .Prod l r a => s!"(Tm.Prod {reprTm l 0} {reprTm r 0} {reprPrec a prec})"
      | .BVar id idx a => s!"(Tm.BVar {id} {repr idx} {reprPrec a prec})"
      | .FVar id a => s!"(Tm.FVar {id} {reprPrec a prec})"
      | .If c t e a => s!"(Tm.If {reprTm c 0} {reprTm t 0} {reprTm e 0} {reprPrec a prec}"
      | .Split p l r body a => s!"Tm.Split {reprTm p 0} {l} {r} {reprTm body 0} {reprPrec a prec})"
      | .Let id ty assn body a => s!"(Tm.Let {id} {repr ty} {reprTm assn 0} {reprTm body 0} {reprPrec a prec})"
      | .Builtin l b tv a => s!"(Tm.Builtin {repr l} {repr b} {reprTmVec tv (prec + 1)} {reprPrec a prec})"
end

instance [Repr α] : Repr (TmVec l n α) where
  reprPrec := reprTmVec

instance [Repr α] : Repr (Tm n α) where
  reprPrec := reprTm


def Tm.tag (tm : Tm n α) : α :=
  match tm with
  | Num _ t
  | Bool _ t
  | Prod _ _ t
  | BVar _ _ t
  | FVar _ t
  | If _ _ _ t
  | Split _ _ _ _ t
  | Let _ _ _ _ t
  | Builtin _ _ _ t
  => t

def TmVec.get (tv : TmVec l n α) (f : Fin l) : Tm n α :=
  match tv, f with
  | .nil, n => Fin.elim0 n
  | .cons tm tv', 0 => tm
  | .cons _ tv', ⟨j + 1, h⟩ => tv'.get ⟨j, Nat.lt_of_succ_lt_succ h⟩

inductive CFun where
  | Add : CFun
  | Mul : CFun
  | Malloc : CFun
  | Free : CFun
  | Fill_rnd : CFun
  | Memcpy : CFun
  | NoOp : CFun
  deriving Repr

def CFun.repr (cf : CFun) :=
  match cf with
  | Add => "add"
  | Mul => "mul"
  | Malloc => "malloc"
  | Free => "free" -- should be drop
  | Fill_rnd => "fill_rnd"
  | Memcpy => "memcpy"
  | NoOp => "no_op"

inductive RVal where
  | RNum : Nat -> RVal
  | RVar : String -> RVal
  | RCall : CFun -> List RVal -> RVal
  | RDeref : String -> Nat -> RVal
  deriving Repr

mutual
  inductive CExpr where
    -- compile if to seq cond if ...
    -- the if branches cannot run before the conditional
    | CDecl : String -> CExpr
    | CIf : RVal -> Seq -> Seq -> String -> CExpr
    | CLet : String -> RVal -> CExpr
    | CSet : String -> RVal -> CExpr -- offset
    | CAssn : String -> Nat -> RVal -> CExpr -- offset
    | CCall : CFun -> List RVal -> CExpr
    -- | CBuiltin : Builtin n -> List CExpr -> CExpr
    deriving Repr

  inductive Seq where
    | mk : List CExpr -> RVal -> Seq
    deriving Repr
end

end Compile
