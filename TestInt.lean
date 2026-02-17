import Mathlib.Data.Int.Basic

example (a : Int) (i j : Nat) (h : i ≤ j) : a + (i : Int) ≤ a + (j : Int) := by
  have hij' : (i : Int) ≤ (j : Int) := Int.ofNat_le.mpr h
  exact add_le_add_left hij' a
