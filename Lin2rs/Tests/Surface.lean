import Lin2rs.Types
import Lin2rs.Surface

open Lin2rs

-- ============================================================
-- Surface [lin2rs ...] tests
-- ============================================================

-- Elaboration sanity checks
#check [lin2rs 1] == Tm.Num 1

#check [lin2rs true] == Tm.Bool true
#check [lin2rs false] == Tm.Bool false

#check [lin2rs un (1, 2)] == Tm.Prod Qual.Un (Tm.Num 1) (Tm.Num 2)
#check [lin2rs lin (1, 2)] == Tm.Prod Qual.Lin (Tm.Num 1) (Tm.Num 2)

-- Typechecking via [lin2rs ...]
#eval ts [lin2rs 1]
#eval ts [lin2rs let x : lin Nat = 1 in x + 2]
#eval ts [lin2rs un (1, 2)]
#eval ts [lin2rs un (x : un Nat => x + 1)]
#eval ts [lin2rs (un (x : un Nat => x + 1) 2)]

-- #ts works directly on surface syntax; [lin2rs ...] is a term
#ts let x : lin Nat = 1 in x + 2
#tc let x : lin Nat = 1 in x + 2 : un Nat
