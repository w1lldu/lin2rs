import Lin2rs.Surface


-- ============================================================
-- Positive #tc tests
-- ============================================================

#tc 1 : un Nat
#tc true : un Bool
#tc false : un Bool

-- Linear variable used exactly once
#tc let x : lin Nat = 1 in x + 2 : un Nat

-- Unrestricted variable used many times
#tc let x : un Nat = 1 in x + x : un Nat
#tc let x : un Nat = 1 in x + x + x : un Nat

-- Products
#tc un (1, 2) : un (un Nat × un Nat)
#tc lin (1, 2) : lin (un Nat × un Nat)
#tc lin (let x : lin Nat = 1 in x, let y : lin Nat = 2 in y)
      : lin (lin Nat × lin Nat)

-- Functions
#tc un (x : un Nat => x + 1) : un (un Nat -> un Nat)
#tc lin (x : un Nat => x + 1) : lin (un Nat -> un Nat)

-- Application
#tc (un (x : un Nat => x + 1) 2) : un Nat

-- Subtyping: unrestricted argument to linear parameter
#tc (lin (x : lin Nat => x) 1) : lin Nat

-- If
#tc if true then 1 else 2 : un Nat
#tc let x : un Nat = 1 in if true then x else 1 : un Nat
#tc let x : lin Nat = 1 in if true then x else x : lin Nat

-- Higher-order
#tc let f : un (un Nat -> un Nat) = un (x : un Nat => x + 1) in (f 2) : un Nat


-- ============================================================
-- Negative #ts tests (should report "not well typed")
-- ============================================================

-- Linear variable used twice
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let x : lin Nat = 1 in x + x

-- Linear variable unused
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let x : lin Nat = 1 in 2

-- Linear variable used in only one branch
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let x : lin Nat = 1 in if true then x else 2

-- Split: linear component unused
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let p : lin (lin Nat × lin Nat) = lin (let x : lin Nat = 1 in x, let y : lin Nat = 2 in y) in
    split p as a, b in a

-- Split: linear component used twice
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let p : lin (lin Nat × lin Nat) = lin (let x : lin Nat = 1 in x, let y : lin Nat = 2 in y) in
    split p as a, b in a + a

-- Product quality too low for linear component
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts un (let x : lin Nat = 1 in x, 2)

-- Application: linear argument to unrestricted parameter
/-- error: not well typed -/
#guard_msgs (error, drop all) in
#ts let f : un (un Nat -> un Nat) = un (x : un Nat => x) in
    let y : lin Nat = 1 in (f y)
