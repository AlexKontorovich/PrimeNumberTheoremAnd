import Mathlib.Data.Real.Basic

example (x : ℕ) : 0 ≤ (x : ℝ) := by exact Nat.cast_nonneg x
