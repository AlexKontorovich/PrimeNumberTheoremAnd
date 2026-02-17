import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators

example (a : ℤ) (i j : ℕ) (h : i ≤ j) : a + (i : ℤ) ≤ a + (j : ℤ) := by
  have hij' : (i : ℤ) ≤ (j : ℤ) := Int.ofNat_le.mpr h
  have : a + (i : ℤ) ≤ a + (j : ℤ) := add_le_add_left hij' a
  simpa using this
