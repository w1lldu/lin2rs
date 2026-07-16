
namespace Lin2rs

-- a ≤ b => a is a subtype of b (a can cast to b)

inductive Qual where
  | Un : Qual
  -- | Aff : Qual
  | Lin : Qual
  deriving Repr, BEq, DecidableEq

def Qual.le (q1 q2 : Qual) : Bool:=
  match q1, q2 with
  | .Un, .Lin => true
  | .Lin, .Un => false
  | _, _ => true

instance : LE Qual where
  le q1 q2 := Qual.le q1 q2 = true

instance : LT Qual where
  lt q1 q2 := q1 ≤ q2 ∧ q1 ≠ q2

instance {q1 q2 : Qual} : Decidable (q1 ≤ q2) := by
  simp [LE.le]
  infer_instance

instance (q1 q2 : Qual) : Decidable (q1 < q2) := by
  simp [LT.lt]
  infer_instance

mutual
  inductive Pt where
    | Nat : Pt
    | Bool : Pt
    | Prod : Ty -> Ty -> Pt
    | Lam : Ty -> Ty -> Pt
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

def Ty.le (ty1 ty2 : Ty) : Bool :=
  match ty1, ty2 with
    | (.mk q1 .Nat), (.mk q2 .Nat) | (.mk q1 .Bool), (.mk q2 .Bool) => q1 ≤ q2
    | (.mk q1 (.Prod ty1l ty1r)), (.mk q2 (.Prod ty2l ty2r)) => q1 ≤ q2 ∧ Ty.le ty1l ty2l ∧ Ty.le ty1r ty2r
    | (.mk q1 (.Lam ty1a ty1b)), (.mk q2 (.Lam ty2a ty2b)) => q1 ≤ q2 ∧ Ty.le ty2a ty1a ∧ Ty.le ty1b ty2b
    | _, _ => false
  termination_by sizeOf ty1 + sizeOf ty2

instance : LE Ty where
  le ty1 ty2 := Ty.le ty1 ty2 = true

instance : LT Ty where
  lt ty1 ty2 := ty1 ≤ ty2 ∧ ty1 ≠ ty2

instance (ty1 ty2 : Ty) : Decidable (ty1 ≤ ty2) := by
  simp [LE.le]
  infer_instance

instance (ty1 ty2 : Ty) : Decidable (ty1 < ty2) := by
  simp [LT.lt]
  infer_instance

inductive Exp where
  | Num : Nat -> Exp
  | Bool : Bool -> Exp
  | Prod : Qual -> Exp -> Exp -> Exp
  | Lam : Qual -> String -> Ty -> Exp -> Exp
  | Id : String -> Exp
  | Add : Exp -> Exp -> Exp
  | If : Exp -> Exp -> Exp -> Exp
  | Split : Exp -> String -> String -> Exp -> Exp
  | App : Exp -> Exp -> Exp
  | Let : String -> Ty -> Exp -> Exp -> Exp
  deriving Repr, BEq

-- keep the names for printing
inductive Tm : Nat -> Type where
  | Num : Nat -> Tm n
  | Bool : Bool -> Tm n
  | Prod : Qual -> Tm n -> Tm n -> Tm n
  -- | Prod : Qual -> Tm n -> Tm m -> Tm (max n m)
  | Lam : Qual -> String -> Ty -> Tm (n + 1) -> Tm n
  | BVar : String -> Fin n -> Tm n
  | FVar : String -> Tm n
  | Add : Tm n -> Tm n -> Tm n
  -- | Add : Tm n -> Tm m -> Tm (max n m)
  | If : Tm n -> Tm n -> Tm n -> Tm n
  -- | If : Tm n -> Tm m -> Tm o -> Tm (max n (max m o))
  | Split : Tm n -> String -> String -> Tm (n + 2) -> Tm n
  | App : Tm n -> Tm n -> Tm n
  -- | App : Tm n -> Tm m -> Tm (max n m)
  | Let : String -> Ty -> Tm n -> Tm (n + 1) -> Tm n
  deriving Repr, BEq

end Lin2rs
