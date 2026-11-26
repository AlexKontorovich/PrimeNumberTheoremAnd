import RSBounds.BacklundHighCount
import RSBounds.RosserCountDefinition
import RSBounds.BacklundLowCount

/-!
# Rosser's unconditional zero-count bound

The public count is defined directly from Mathlib's zeta function and its
analytic zero orders, with `0 < Im rho <= T`. It has no finite-RH parameter.
The proof uses the analytic argument from height 100 and the separately
replayed finite zero certificates below that height.
-/

open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.Rosser1941
open BacklundCountIdentity

/-- Rosser (1941), Theorem 19, with the original constants and full range.
No RH, zero-count, numerical certificate, or analytic estimate is a premise. -/
theorem zero_count_bounds (T : ℝ) (hT : 2 ≤ T) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  rw [positiveZeroCount_eq (by linarith)]
  by_cases h100 : 100 ≤ T
  · exact rosser_bound_high h100
  · exact BacklundLowCount.rosser_bound_low hT (le_of_not_ge h100)

end TernaryGoldbach.RSBounds.Rosser1941
