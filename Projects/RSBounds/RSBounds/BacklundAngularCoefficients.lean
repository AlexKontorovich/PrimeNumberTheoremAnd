import RSBounds.BacklundRightArcNumericsBase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-! Exact angular coefficients in Backlund's circle integral, with radius 1.32. -/

open Real MeasureTheory

namespace TernaryGoldbach.RSBounds.BacklundAngularCoefficients

noncomputable def radius : ℝ := 33 / 25
noncomputable def q : ℝ := Real.log (44 / 25)
noncomputable def alpha : ℝ := Real.arccos (-(25 / 132))
noncomputable def beta : ℝ := Real.arccos (-(125 / 132))
noncomputable def slopeA : ℝ :=
  (radius * Real.sin alpha - (Real.pi - alpha) / 4 +
    radius * Real.sin beta - 5 * (Real.pi - beta) / 4) / (4 * Real.pi * q)
noncomputable def slopeB : ℝ := 1 / (4 * q)
noncomputable def intercept (C : ℝ) : ℝ :=
  C / q - slopeA * Real.log (2 * Real.pi) + Real.log (3.426 : ℝ) / (2 * q) + 1 / 2

lemma q_pos : 0 < q := Real.log_pos (by norm_num)

lemma first_cos_integral :
    (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) =
      -radius * Real.sin alpha + (Real.pi - alpha) / 4 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

lemma second_cos_integral :
    (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) =
      -radius * Real.sin beta + 5 * (Real.pi - beta) / 4 := by
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

/-- Exact assembly of the four angular sectors before inserting scalar
estimates. `J` is the right-arc integral divided by `2π`, and `V` the strip
correction. No numerical integral bound is assumed by this identity. -/
lemma angular_integrals_eq (J L H V : ℝ) :
    (2 * Real.pi * J + Real.pi / 2 * H -
      L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
      L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) +
      (beta - alpha) * V) / (2 * Real.pi * q) =
      J / q + slopeA * L + slopeB * H + (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [first_cos_integral, second_cos_integral]
  unfold slopeA slopeB
  field_simp [q_pos.ne', Real.pi_ne_zero]
  ring

end TernaryGoldbach.RSBounds.BacklundAngularCoefficients
