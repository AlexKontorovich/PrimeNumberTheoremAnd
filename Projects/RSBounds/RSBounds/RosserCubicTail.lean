import RSBounds.RosserWeightedBounds
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# A reciprocal-cube tail for actual zeta zeros

This extends the proved Rosser partial-summation interface with weight `t⁻³`.
The finite sums count actual zeta zeros with their analytic multiplicities,
on the interval `(a,b]`. The final height-1894439 bound is unconditional.
No finite RH, zero-free region, or PNT estimate is an assumption here.

The counting input is `Rosser1941.zero_count_bounds`, through
`WeightedZetaZeros.weightedSum_le_decreasing_head`. The elementary integral
calculation follows the same partial-summation method as RS75, Section 3.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.RosserCubicTail

open Rosser1941 WeightedZetaZeros RosserWeightedBounds RosserTailIntegrals

/-- The antiderivative allowance for the frozen Rosser density and `t⁻³`. -/
noncomputable def cubicPrimitive (c t : ℝ) : ℝ :=
  (Real.log (t / (2 * Real.pi)) / 2 + 1 / 4) / (2 * Real.pi * t ^ 2) +
    c / (3 * t ^ 3)

noncomputable def cubicAllowance (a : ℝ) : ℝ :=
  cubicPrimitive (coefficient a) a + 2 * rosserR 1.588 a / a ^ 3

theorem hasDerivAt_reciprocal_cube {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 3) (-3 / t ^ 4) t := by
  have hp : (fun t : ℝ => t ^ 3) t ≠ 0 := pow_ne_zero 3 ht.ne'
  have hh := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 3) hp
  convert hh using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [ht.ne']
    <;> ring

theorem hasDerivAt_neg_cubicPrimitive (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -cubicPrimitive c t)
      ((Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + c / t) / t ^ 3) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn : t ≠ 0 := ht.ne'
  have hi := hasDerivAt_id t
  have hl := (hi.div_const (2 * Real.pi)).log (div_ne_zero hn hp)
  have h₁ := ((hl.div_const 2).add_const (1 / 4 : ℝ)).div
    ((hi.pow 2).const_mul (2 * Real.pi)) (by
      simpa only [Pi.pow_apply, id_eq] using mul_ne_zero hp (pow_ne_zero 2 hn))
  have h₂ := (hasDerivAt_const t c).div ((hi.pow 3).const_mul 3) (by
    simpa only [Pi.pow_apply, id_eq] using
      mul_ne_zero (by norm_num : (3 : ℝ) ≠ 0) (pow_ne_zero 3 hn))
  convert (h₁.add h₂).neg using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [hp, hn]
    <;> ring

theorem cubicPrimitive_nonneg {c t : ℝ} (hc : 0 ≤ c) (ht : 7 ≤ t) :
    0 ≤ cubicPrimitive c t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht0 : 0 < t := by linarith
  have hpt : 2 * Real.pi ≤ t := by linarith [Real.pi_lt_d4]
  have hlog : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hpt))
  unfold cubicPrimitive
  positivity

theorem integral_upperDensity_div_cube {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, upperDensity a t / t ^ 3) =
      cubicPrimitive (coefficient a) a - cubicPrimitive (coefficient a) b := by
  have hc : ContinuousOn (fun t => upperDensity a t / t ^ 3) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div
      (continuousAt_id.pow 3) (by
        simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 3 ht0.ne')).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_neg_cubicPrimitive (coefficient a)
      (ha.trans_le (by rw [uIcc_of_le hab] at ht; exact ht.1))) hc.intervalIntegrable
  simpa only [upperDensity, neg_sub_neg] using h

theorem integral_density_div_cube_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, density t / t ^ 3) ≤ cubicPrimitive (coefficient a) a := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t => density t / t ^ 3) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    have ht0 : 0 < t := by linarith
    exact ((continuousAt_density ht1).div (continuousAt_id.pow 3)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 3 ht0.ne')).continuousWithinAt
  have hu : IntervalIntegrable (fun t => upperDensity a t / t ^ 3) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div (continuousAt_id.pow 3)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 3 ht0.ne')).continuousWithinAt
  have hle := intervalIntegral.integral_mono_on hab hi hu (fun t ht =>
    div_le_div_of_nonneg_right (density_le_upperDensity ha1 ht.1)
      (by have ht0 : 0 ≤ t := ha0.le.trans ht.1; positivity))
  rw [integral_upperDensity_div_cube ha0 hab] at hle
  exact hle.trans (sub_le_self _
    (cubicPrimitive_nonneg (coefficient_nonneg ha1) (ha.trans hab)))

/-- A uniform finite cube-weight estimate, retaining the lower count correction. -/
theorem cubic_sum_le_head {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 3) ≤
      cubicPrimitive (coefficient a) a + (G a - positiveZeroCount a) / a ^ 3 := by
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => -3 / t ^ 4) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have he := weightedSum_le_decreasing_head (by linarith : 2 ≤ a) hab
    (fun t ht => hasDerivAt_reciprocal_cube (ha0.trans_le ht.1)) hi
    (fun t _ => div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
    (by have hb : 0 ≤ b := ha0.le.trans hab; positivity)
  have he' : weightedSum a b (fun t => 1 / t ^ 3) ≤
      (∫ t in a..b, density t / t ^ 3) +
      (G a - positiveZeroCount a) / a ^ 3 := by
    convert he using 1 <;> simp only [density, G, mul_one_div]
  exact he'.trans (add_le_add (integral_density_div_cube_le ha hab) le_rfl)

/-- The count input is already proved for actual zeros, so this has no RH premise. -/
theorem cubic_sum_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 3) ≤ cubicAllowance a := by
  have hc : (G a - positiveZeroCount a) / a ^ 3 ≤
      2 * rosserR 1.588 a / a ^ 3 :=
    div_le_div_of_nonneg_right (head_correction_le (by linarith : 2 ≤ a))
      (by
        have ha0 : 0 ≤ a := by linarith
        positivity)
  exact (cubic_sum_le_head ha hab).trans (add_le_add le_rfl hc)

private theorem rational_pow_le_exp_nat (n : ℕ) : (2.7 : ℝ) ^ n ≤ Real.exp n := by
  calc
    (2.7 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by
      gcongr
      linarith [Real.exp_one_gt_d9]
    _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp

private theorem log_A_bounds : 1 ≤ Real.log 1894439 ∧ Real.log 1894439 ≤ 15 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1894439)).mpr
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1894439)).mpr
    exact (by norm_num : (1894439 : ℝ) ≤ 2.7 ^ 15).trans (rational_pow_le_exp_nat 15)

private theorem log_A_div_two_pi_le : Real.log (1894439 / (2 * Real.pi)) ≤ 13 := by
  apply (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 1894439 / (2 * Real.pi))).mpr
  calc
    (1894439 : ℝ) / (2 * Real.pi) ≤ 1894439 / 6 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [Real.pi_gt_three]
    _ ≤ (2.7 : ℝ) ^ 13 := by norm_num
    _ ≤ Real.exp 13 := rational_pow_le_exp_nat 13

private theorem rosserR_A_le : rosserR 1.588 1894439 ≤ 6 := by
  have hloglog : Real.log (Real.log 1894439) ≤ 3 := by
    apply (Real.log_le_iff_le_exp (by linarith [log_A_bounds.1])).mpr
    exact log_A_bounds.2.trans
      ((by norm_num : (15 : ℝ) ≤ 2.7 ^ 3).trans (rational_pow_le_exp_nat 3))
  unfold rosserR
  linarith [log_A_bounds.2]

/-- Closed scalar certificate using only proved elementary exp and pi bounds. -/
theorem cubicAllowance_A_lt : cubicAllowance 1894439 < 3e-13 := by
  have hc : coefficient 1894439 ≤ 0.58 := by
    have hh : (0.443 : ℝ) / Real.log 1894439 ≤ 0.443 := by
      rw [div_le_iff₀ (by linarith [log_A_bounds.1])]
      nlinarith [log_A_bounds.1]
    unfold coefficient
    linarith
  have hfirst :
      (Real.log (1894439 / (2 * Real.pi)) / 2 + 1 / 4) /
          (2 * Real.pi * (1894439 : ℝ) ^ 2) ≤
        (27 / 4 : ℝ) / (6.28 * (1894439 : ℝ) ^ 2) := by
    calc
      _ ≤ (27 / 4 : ℝ) / (2 * Real.pi * (1894439 : ℝ) ^ 2) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [log_A_div_two_pi_le]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [Real.pi_gt_d2]
  have hsecond : coefficient 1894439 / (3 * (1894439 : ℝ) ^ 3) ≤
      (0.58 : ℝ) / (3 * (1894439 : ℝ) ^ 3) := by gcongr
  have hthird : 2 * rosserR 1.588 1894439 / (1894439 : ℝ) ^ 3 ≤
      (12 : ℝ) / (1894439 : ℝ) ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [rosserR_A_le]
  unfold cubicAllowance cubicPrimitive
  have hrat : (27 / 4 : ℝ) / (6.28 * (1894439 : ℝ) ^ 2) +
      (0.58 : ℝ) / (3 * (1894439 : ℝ) ^ 3) +
      (12 : ℝ) / (1894439 : ℝ) ^ 3 < 3e-13 := by norm_num
  linarith

/-- The actual positive-ordinate reciprocal-cube tail, with analytic multiplicities.
The lower endpoint is excluded, the upper endpoint included, and no RH is assumed. -/
theorem cubic_sum_A_lt {T : ℝ} (hT : 1894439 ≤ T) :
    weightedSum 1894439 T (fun t => 1 / t ^ 3) < 3e-13 :=
  (cubic_sum_le (by norm_num : (7 : ℝ) ≤ 1894439) hT).trans_lt cubicAllowance_A_lt

end TernaryGoldbach.RSBounds.RosserCubicTail
