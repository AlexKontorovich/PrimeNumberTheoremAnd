import RSBounds.BacklundCircleCount
import RSBounds.BacklundCountEndpoint
import RSBounds.RosserCountDefinition

/-! The unconditional analytic zero-count estimate for every `T >= 100`,
including zero ordinates. No finite zero certificate is imported here. -/

open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

lemma continuous_roundedEnvelope {T : ℝ} (hT : 100 ≤ T) :
    ContinuousAt BacklundFinalScalar.roundedEnvelope T := by
  have hT0 : 0 < T := by linarith
  have hTr : 0 < T - 33 / 25 := by linarith
  have hD : 0 < (T - 33 / 25) ^ 2 - 4 := by nlinarith
  have hL : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
  unfold BacklundFinalScalar.roundedEnvelope
  fun_prop (disch := positivity)

/-- Analytic range, including heights equal to zero ordinates. -/
theorem rosser_bound_high {T : ℝ} (hT : 100 ≤ T) :
    |(N_le T : ℝ) - mainTerm T| < rosserR 1.588 T := by
  have hT0 : 0 < T := by linarith
  apply closed_count_abs_lt_of_good_height_bound hT0
    (M := mainTerm) (B := BacklundFinalScalar.roundedEnvelope)
  · change ContinuousAt rosserF T
    exact (hasDerivAt_rosserF hT0).continuousAt
  · exact continuous_roundedEnvelope hT
  · intro S hTS hg
    exact BacklundCircleMajorant.count_le_roundedEnvelope (hT.trans hTS.le) hg
  · exact BacklundFinalScalar.roundedEnvelope_lt_rosser hT

end TernaryGoldbach.RSBounds.BacklundCountIdentity

namespace TernaryGoldbach.RSBounds.Rosser1941

/-- Rosser's original constants in the analytic range, for the actual zeta
zero count with the inclusive upper endpoint. No finite RH certificate or
zero-count hypothesis is used. -/
theorem zero_count_bounds_high (T : ℝ) (hT : 100 ≤ T) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by
  rw [positiveZeroCount_eq (by linarith)]
  exact BacklundCountIdentity.rosser_bound_high hT

end TernaryGoldbach.RSBounds.Rosser1941
