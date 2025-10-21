/-
Test file with valid Lean code.
This should pass all CI checks.
-/

theorem add_comm (a b : Nat) : a + b = b + a := Nat.add_comm a b

theorem zero_mul (n : Nat) : 0 * n = 0 := Nat.zero_mul n
