import Mathlib.Algebra.Order.BigOperators.Group.Finset

example {x a b : ℝ} (h : a ≤ b) : x + a ≤ x + b := by
  -- see which lemma works
  have := add_le_add_right h x
  -- this yields ?
  simpa [add_comm, add_left_comm, add_assoc] using this
