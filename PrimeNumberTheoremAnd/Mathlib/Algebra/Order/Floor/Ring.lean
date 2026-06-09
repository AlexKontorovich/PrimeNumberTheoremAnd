module

public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Floor and fractional-part estimates

Small floor-ring lemmas used by summation and Abel-continuation arguments.
-/

@[expose] public section

namespace Int

variable {R : Type*} [Ring R] [LinearOrder R] [IsOrderedRing R] [FloorRing R]

theorem fract_abs_le_one (a : R) : |fract a| ≤ 1 := by
  rw [abs_fract]
  exact (fract_lt_one a).le

end Int
