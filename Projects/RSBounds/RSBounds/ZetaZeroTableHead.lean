import RSBounds.ZetaZeroTable
import Mathlib.Data.Rat.BigOperators

/-!
# A reciprocal-norm bound for the certified first 29 zeros

The numerical step is only an exact rational sum over the already certified
lower bracket endpoints. The analytic comparison uses `Im z ≤ ‖z‖` and the
open brackets from `ZetaZeroTable.first29`; no additional zero certificates or
Riemann-hypothesis assumption are needed.
-/

open Complex

namespace TernaryGoldbach.RSBounds.ZetaZeroTableHead
open BacklundLowCount ZetaZeroTable

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- All lower endpoints in the certified table are positive rationals. -/
theorem bracketLower_pos (i : Fin 29) : 0 < bracketLower i := by
  have h : ∀ i : Fin 29, 0 < bracketLower i := by decide +kernel
  exact h i

/-- Exact rational upper bound, usable independently of the real ordinates. -/
theorem sum_reciprocal_lower_lt :
    (∑ i : Fin 29, (1 : ℚ) / bracketLower i) < 0.592316 := by
  decide +kernel

/-- The certified 29-zero head is bounded using only its lower brackets. -/
theorem first29_reciprocal_norm_sum_lt :
    (∑ i : Fin 29, 1 / ‖(1 / 2 : ℂ) + first29.ordinate i * I‖) < 0.592316 := by
  have hsum : (∑ i : Fin 29, (1 : ℝ) / (bracketLower i : ℝ)) < 0.592316 := by
    have hcast := (Rat.cast_lt (K := ℝ)).mpr sum_reciprocal_lower_lt
    simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_one, Rat.cast_ofScientific] using hcast
  apply lt_of_le_of_lt _ hsum
  apply Finset.sum_le_sum
  intro i _
  have hlo : (0 : ℝ) < (bracketLower i : ℝ) := by
    exact_mod_cast bracketLower_pos i
  have hnorm : first29.ordinate i ≤ ‖(1 / 2 : ℂ) + first29.ordinate i * I‖ := by
    simpa using Complex.im_le_norm ((1 / 2 : ℂ) + first29.ordinate i * I)
  exact one_div_le_one_div_of_le hlo ((first29_bracket i).1.le.trans hnorm)

/-- Non-strict form of the certified reciprocal-norm head bound. -/
theorem first29_reciprocal_norm_sum_le :
    (∑ i : Fin 29, 1 / ‖(1 / 2 : ℂ) + first29.ordinate i * I‖) ≤ 0.592316 :=
  first29_reciprocal_norm_sum_lt.le

end TernaryGoldbach.RSBounds.ZetaZeroTableHead
