
namespace Lin2rs

inductive Qual where
  -- | un : Qual
  -- | aff : Qual
  | lin : Qual
  deriving BEq

inductive Pt where
  | PNat : Pt
  deriving DecidableEq

def Ty := Qual × Pt
  deriving BEq

-- inductive Ty where
--   | Qp : Qual -> Pt -> Ty

inductive Tm where
  | Num : Nat -> Tm
  | Id : String -> Tm
  | Add : Tm -> Tm -> Tm
  | If : Tm -> Tm -> Tm -> Tm
  | Let : String -> Ty -> Tm -> Tm -> Tm

end Lin2rs
