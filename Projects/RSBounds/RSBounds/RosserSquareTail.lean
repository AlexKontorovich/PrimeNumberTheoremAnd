import RSBounds.RosserWeightedBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A reciprocal-square tail for actual zeta zeros

This extends the proved Rosser partial-summation interface with weight `t⁻²`.
The finite sums count actual zeta zeros with their analytic multiplicities,
on the interval `(a,b]`. The estimate is unconditional and holds at every height at least seven.
No finite RH, zero-free region, or PNT estimate is an assumption here.

The counting input is `Rosser1941.zero_count_bounds`, through
`WeightedZetaZeros.weightedSum_le_decreasing_head`. The elementary integral
calculation follows the same partial-summation method as RS75, Section 3.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.RosserSquareTail

open Rosser1941 WeightedZetaZeros RosserWeightedBounds RosserTailIntegrals

/-- The antiderivative allowance for the frozen Rosser density and `t⁻²`. -/
noncomputable def squarePrimitive (c t : ℝ) : ℝ :=
  (Real.log (t / (2 * Real.pi)) + 1) / (2 * Real.pi * t) +
    c / (2 * t ^ 2)

noncomputable def squareAllowance (a : ℝ) : ℝ :=
  squarePrimitive (coefficient a) a + 2 * rosserR 1.588 a / a ^ 2

theorem hasDerivAt_reciprocal_square {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-2 / t ^ 3) t := by
  have hp : (fun t : ℝ => t ^ 2) t ≠ 0 := pow_ne_zero 2 ht.ne'
  have hh := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 2) hp
  convert hh using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [ht.ne']
    <;> ring

theorem hasDerivAt_neg_squarePrimitive (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -squarePrimitive c t)
      ((Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + c / t) / t ^ 2) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn : t ≠ 0 := ht.ne'
  have hi := hasDerivAt_id t
  have hl := (hi.div_const (2 * Real.pi)).log (div_ne_zero hn hp)
  have h₁ := (hl.add_const (1 : ℝ)).div
    (hi.const_mul (2 * Real.pi)) (by
      simpa only [id_eq] using mul_ne_zero hp hn)
  have h₂ := (hasDerivAt_const t c).div ((hi.pow 2).const_mul 2) (by
    simpa only [Pi.pow_apply, id_eq] using
      mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) (pow_ne_zero 2 hn))
  convert (h₁.add h₂).neg using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [hp, hn]
    <;> ring

theorem squarePrimitive_nonneg {c t : ℝ} (hc : 0 ≤ c) (ht : 7 ≤ t) :
    0 ≤ squarePrimitive c t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht0 : 0 < t := by linarith
  have hpt : 2 * Real.pi ≤ t := by linarith [Real.pi_lt_d4]
  have hlog : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hpt))
  unfold squarePrimitive
  positivity

theorem integral_upperDensity_div_square {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, upperDensity a t / t ^ 2) =
      squarePrimitive (coefficient a) a - squarePrimitive (coefficient a) b := by
  have hc : ContinuousOn (fun t => upperDensity a t / t ^ 2) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div
      (continuousAt_id.pow 2) (by
        simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 2 ht0.ne')).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_neg_squarePrimitive (coefficient a)
      (ha.trans_le (by rw [uIcc_of_le hab] at ht; exact ht.1))) hc.intervalIntegrable
  simpa only [upperDensity, neg_sub_neg] using h

theorem integral_density_div_square_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, density t / t ^ 2) ≤ squarePrimitive (coefficient a) a := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t => density t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    have ht0 : 0 < t := by linarith
    exact ((continuousAt_density ht1).div (continuousAt_id.pow 2)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 2 ht0.ne')).continuousWithinAt
  have hu : IntervalIntegrable (fun t => upperDensity a t / t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div (continuousAt_id.pow 2)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 2 ht0.ne')).continuousWithinAt
  have hle := intervalIntegral.integral_mono_on hab hi hu (fun t ht =>
    div_le_div_of_nonneg_right (density_le_upperDensity ha1 ht.1)
      (by have ht0 : 0 ≤ t := ha0.le.trans ht.1; positivity))
  rw [integral_upperDensity_div_square ha0 hab] at hle
  exact hle.trans (sub_le_self _
    (squarePrimitive_nonneg (coefficient_nonneg ha1) (ha.trans hab)))

/-- A uniform finite square-weight estimate, retaining the lower count correction. -/
theorem square_sum_le_head {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 2) ≤
      squarePrimitive (coefficient a) a + (G a - positiveZeroCount a) / a ^ 2 := by
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => -2 / t ^ 3) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have he := weightedSum_le_decreasing_head (by linarith : 2 ≤ a) hab
    (fun t ht => hasDerivAt_reciprocal_square (ha0.trans_le ht.1)) hi
    (fun t ht => div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (by have ht0 : 0 ≤ t := ha0.le.trans ht.1.le; positivity))
    (by have hb : 0 ≤ b := ha0.le.trans hab; positivity)
  have he' : weightedSum a b (fun t => 1 / t ^ 2) ≤
      (∫ t in a..b, density t / t ^ 2) +
      (G a - positiveZeroCount a) / a ^ 2 := by
    convert he using 1 <;> simp only [density, G, mul_one_div]
  exact he'.trans (add_le_add (integral_density_div_square_le ha hab) le_rfl)

/-- The count input is already proved for actual zeros, so this has no RH premise. -/
theorem square_sum_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 2) ≤ squareAllowance a := by
  have hc : (G a - positiveZeroCount a) / a ^ 2 ≤
      2 * rosserR 1.588 a / a ^ 2 :=
    div_le_div_of_nonneg_right (head_correction_le (by linarith : 2 ≤ a))
      (by
        have ha0 : 0 ≤ a := by linarith
        positivity)
  exact (square_sum_le_head ha hab).trans (add_le_add le_rfl hc)


end TernaryGoldbach.RSBounds.RosserSquareTail
