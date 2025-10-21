/-
Invalid Lean syntax - should fail build.
-/

theorem broken : 1 + 1 = 2 := by
  not a valid tactic
