
namespace Compile

-- a ≤ b => a is a subtype of b (a can cast to b)

inductive Qual where
  | Un : Qual
  -- | Aff : Qual
  | Lin : Qual
  deriving Repr, BEq, DecidableEq

-- def Qual.le (q1 q2 : Qual) : Bool:=
--   match q1, q2 with
--   | .Un, .Lin => true
--   | .Lin, .Un => false
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

mutual
  inductive Pt where
    | Nat : Pt
    | Bool : Pt
    | Bytes : Nat -> Pt
    | Prod : Ty -> Ty -> Pt
    deriving Repr, BEq

  -- cannot prove termination with structure
  -- doesnt matter since we ended up making everything partial?
  -- structure Ty where
  --   qual : Qual
  --   pt : Pt
  --   deriving BEq, Repr, DecidableEq
  inductive Ty where
    | mk : Qual -> Pt -> Ty
    deriving Repr, BEq, DecidableEq
end

-- def Ty.le (ty1 ty2 : Ty) : Bool :=
--   match ty1, ty2 with
--     | (.mk q1 .Nat), (.mk q2 .Nat) | (.mk q1 .Bool), (.mk q2 .Bool) => q1 ≤ q2
--     | (.mk q1 (.Prod ty1l ty1r)), (.mk q2 (.Prod ty2l ty2r)) => q1 ≤ q2 ∧ Ty.le ty1l ty2l ∧ Ty.le ty1r ty2r
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

inductive Builtin1 where
  | Alloc : Builtin1
  | Free : Builtin1
  | Fill_rnd : Builtin1
  deriving Repr, BEq

def Builtin1.repr (b1 : Builtin1) :=
  match b1 with
  | Alloc => "alloc"
  | Free => "free"
  | Fill_rnd => "fill_rnd"

inductive Builtin3 where
  | Memcpy : Builtin3
  deriving Repr, BEq

def Builtin3.repr (b3 : Builtin3) :=
  match b3 with
  | Memcpy => "memcpy"

-- add tag to hold types, so that ts is able to provide the type for compilation
-- keep the names for printing
inductive Tm : Nat -> Type u -> Type (u + 1)
  | Num : Nat -> α -> Tm n α
  | Bool : Bool -> α -> Tm n α
  | Prod : Qual -> Tm n α -> Tm n α -> α -> Tm n α
  | BVar : String -> Fin n -> α -> Tm n α
  | FVar : String -> Tm n α
  | Add : Tm n α -> Tm n α -> α -> Tm n α
  | If : Tm n α -> Tm n α -> Tm n α -> α -> Tm n α
  | Split : Tm n α -> String -> String -> Tm (n + 2) α -> α -> Tm n α
  | Let : String -> Ty -> Tm n α -> Tm (n + 1) α -> α -> Tm n α
  | Builtin1 : Builtin1 -> Tm n α -> α -> Tm n α
  | Builtin3 : Builtin3 -> Tm n α -> Tm n α -> Tm n α -> α -> Tm n α

-- rename?
inductive Imm : Nat -> Type u -> Type (u + 1)
  | Num : Nat -> α -> Imm n α
  | Bool : Bool -> α -> Imm n α
  | BVar : String -> Fin n -> α -> Imm n α
  | FVar : String -> Imm n α

mutual
  inductive CTm : Nat -> Type u -> Type (u + 1) where
    | Prod : Qual -> Imm n α -> Imm n α -> α -> CTm n α
    | Add : Imm n α -> Imm n α -> α -> CTm n α
    -- If needs a tag to unify the two branches
    | If : Imm n α -> ATm n α -> ATm n α -> α -> CTm n α
    | Builtin1 : Builtin1 -> Imm n α -> α -> CTm n α
    | Builtin3 : Builtin3 -> Imm n α -> Imm n α -> Imm n α -> α -> CTm n α
    | Imm : Imm n α -> CTm n α

  inductive ATm : Nat -> Type u -> Type (u + 1) where
    -- use Imm bc decreases overlap in compilation (compile_imm vs set_result_to compile_ctm)
    | Split : Imm n α -> String -> String -> ATm (n + 2) α -> α -> ATm n α
    | Let : String -> Ty -> CTm n α -> ATm (n + 1) α -> α -> ATm n α
    | CTm : CTm n α -> ATm n α
end

def Imm.tag (imm : Imm n α) : α :=
  sorry

def CTm.tag (ctm : CTm n α) : α :=
  sorry

def ATm.tag (atm : ATm n α) : α :=
  sorry

end Compile
