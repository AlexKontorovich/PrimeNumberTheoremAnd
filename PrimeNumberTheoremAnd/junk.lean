import Mathlib.Data.Real.Basic

theorem extracted_1 (x : ℝ) (hx : 0 ≤ x) (hxx : x ≠ 0) : 0 < x := by
  exact lt_of_le_of_ne hx (id (Ne.symm hxx))
  sorry
