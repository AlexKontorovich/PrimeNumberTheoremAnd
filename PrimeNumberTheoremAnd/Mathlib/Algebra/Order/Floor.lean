import Mathlib.Algebra.Order.Floor

variable {α : Type*} [LinearOrderedRing α] [FloorRing α]

theorem Nat.self_sub_floor {a : α} (ha : 0 ≤ a) : a - ⌊a⌋₊ = Int.fract a := by
  rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add', Int.self_sub_fract]
  exact (natCast_floor_eq_intCast_floor ha).symm
