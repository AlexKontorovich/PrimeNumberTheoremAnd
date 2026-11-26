import RSBounds.BacklundCircleMajorantBounds
import RSBounds.BacklundCircleSymmetry
import RSBounds.BacklundAngularAssembly
import RSBounds.BacklundAngularNumerics
import RSBounds.BacklundCountJensen
import RSBounds.BacklundFinalScalar

/-!
# Discharging the actual circle majorant in Rosser's zero count

Every analytic input is an imported theorem.  The only remaining height
hypothesis is the zero-avoidance condition needed by the exact contour count.
-/

open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

theorem majorant_circleIntegrable (T : ℝ) :
    CircleIntegrable (majorant T) (5 / 4 : ℂ) radius := by
  have hi : IntervalIntegrable
      (fun θ => scalar (heightLog T) (powerLog T) (stripLog T)
        ((5 / 4 : ℝ) + radius * Real.cos θ)) volume 0 Real.pi := by
    have hi' := BacklundAngularAssembly.intervalIntegrable_scalar_arc
      (heightLog T) (powerLog T) (stripLog T)
    unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
      BacklundAngularCoefficients.radius at hi'
    simpa only [radius] using hi'
  unfold majorant
  simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using circleIntegrable_re_of_upper hi

theorem majorant_average_le (T : ℝ) :
    circleAverage (majorant T) (5 / 4 : ℂ) radius /
        (2 * BacklundAngularCoefficients.q) ≤
      0.1361 / BacklundAngularCoefficients.q +
        BacklundAngularCoefficients.slopeA * powerLog T +
        BacklundAngularCoefficients.slopeB * heightLog T +
        (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
          (2 * Real.pi * BacklundAngularCoefficients.q) := by
  have hi := BacklundAngularAssembly.intervalIntegrable_scalar_arc
    (heightLog T) (powerLog T) (stripLog T)
  unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
    BacklundAngularCoefficients.radius at hi
  have he := circleAverage_re_eq_upper (c := 5 / 4) (r := radius)
    (f := scalar (heightLog T) (powerLog T) (stripLog T)) (by
      simpa only [radius] using hi)
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he
  change circleAverage (majorant T) (5 / 4 : ℂ) radius = _ at he
  rw [he]
  have hb := BacklundAngularAssembly.scalar_arc_integral_le
    (heightLog T) (powerLog T) (stripLog T)
  unfold BacklundAngularAssembly.arc BacklundAngularAssembly.sigma
    BacklundAngularCoefficients.radius at hb
  convert hb using 1
  dsimp [radius]
  field_simp [BacklundAngularCoefficients.q_pos.ne', Real.pi_ne_zero]

theorem correction_coefficient_le_one :
    (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) /
      (2 * Real.pi * BacklundAngularCoefficients.q) ≤ 1 := by
  have hq := BacklundAngularCoefficients.q_bounds.1
  have hα : 0 ≤ BacklundAngularCoefficients.alpha := Real.arccos_nonneg _
  have hβ : BacklundAngularCoefficients.beta ≤ Real.pi := Real.arccos_le_pi _
  have hm := mul_nonneg Real.pi_pos.le
    (show 0 ≤ 2 * BacklundAngularCoefficients.q - 1 by linarith)
  rw [div_le_one (by positivity [BacklundAngularCoefficients.q_pos])]
  nlinarith [Real.pi_pos]

theorem count_le_roundedEnvelope {T : ℝ} (hT : 100 ≤ T)
    (hgood : BacklundCountIdentity.zetaGoodHeight T) :
    |(BacklundCountIdentity.N T : ℝ) - BacklundCountIdentity.mainTerm T| ≤
      BacklundFinalScalar.roundedEnvelope T := by
  have hh := BacklundCountIdentity.count_le_circle_majorant
    (T := T) (R := radius) (B := majorant T) (by linarith) hgood
    (by norm_num [radius]) (by dsimp [radius]; linarith)
    (majorant_circleIntegrable T) (fun z _ => majorant_nonneg hT z)
    (fun _ hz => zeta_plus_le_exp_majorant hT hz)
    (fun _ hz => zeta_minus_le_exp_majorant hT hz)
  have hq : Real.log (radius / (3 / 4)) = BacklundAngularCoefficients.q := by
    unfold radius BacklundAngularCoefficients.q
    norm_num
  rw [hq, add_div] at hh
  have hmean := majorant_average_le T
  have hp : powerLog T = Real.log (T + radius) - Real.log (2 * Real.pi) := by
    unfold powerLog
    rw [Real.log_div (by dsimp [radius]; linarith) (by positivity)]
  have hraw : |(BacklundCountIdentity.N T : ℝ) - BacklundCountIdentity.mainTerm T| ≤
      BacklundAngularCoefficients.slopeA * Real.log (T + radius) +
      BacklundAngularCoefficients.slopeB * heightLog T +
      BacklundAngularCoefficients.intercept 0.1361 +
      (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
        (2 * Real.pi * BacklundAngularCoefficients.q) +
      2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
    rw [hp] at hmean
    unfold BacklundAngularCoefficients.intercept
    linarith
  have hA := mul_le_mul_of_nonneg_right BacklundAngularCoefficients.slopeA_bounds.2
    (log_height_pos hT).le
  have hB := mul_le_mul_of_nonneg_right BacklundAngularCoefficients.slopeB_le
    (heightLog_nonneg hT)
  have hK := BacklundAngularCoefficients.intercept_le_strong
  have hV := mul_le_mul_of_nonneg_right correction_coefficient_le_one (stripLog_nonneg hT)
  have hVe : ((BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) /
      (2 * Real.pi * BacklundAngularCoefficients.q)) * stripLog T =
      (BacklundAngularCoefficients.beta - BacklundAngularCoefficients.alpha) * stripLog T /
        (2 * Real.pi * BacklundAngularCoefficients.q) := by ring
  rw [hVe, one_mul] at hV
  change _ ≤ 0.1361 * Real.log (T + radius) + 0.4423 * heightLog T + 1.5803 +
    stripLog T + 2 / (Real.pi * T) + 1 / (4 * Real.pi * T)
  linarith

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
