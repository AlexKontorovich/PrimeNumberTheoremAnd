import Mathlib.Algebra.Order.BigOperators.Group.Finset

example (a : ℤ) (i j : ℕ) (h : i ≤ j) : a + (i : ℤ) ≤ a + (j : ℤ) := by
  have hij' : (i : ℤ) ≤ (j : ℤ) := Int.ofNat_le.mpr h
  have : (i : ℤ) + a ≤ (j : ℤ) + a := add_le_add_right hij' a
  -- now commute
  simpa [add_comm, add_left_comm, add_assoc] using this
