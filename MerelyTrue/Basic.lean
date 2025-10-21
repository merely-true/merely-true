/-
Basic theorems for testing CI validation.
-/

theorem one_plus_one : 1 + 1 = 2 := rfl

theorem nat_zero_add (n : Nat) : 0 + n = n := Nat.zero_add n
