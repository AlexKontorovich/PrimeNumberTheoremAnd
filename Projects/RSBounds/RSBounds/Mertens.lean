/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact finite-interval identities for the weighted prime sum

These identities are an unconditional foundation for Rosser--Schoenfeld (1962),
Theorem 6, equation (3.21). They do **not** establish that theorem's sharp error
bound. In particular, this file imports neither a finite-RH hypothesis nor a
numerical prime-number estimate.

The finite-anchor identity keeps the analytic task explicit: bounds on
`theta t - t` must still control the two endpoints and the signed integral.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds

/-- The prime sum in Rosser--Schoenfeld (1962), equation (3.21). -/
noncomputable def primeWeightedSum (x : ℝ) : ℝ :=
  ∑ p ∈ (Icc 0 ⌊x⌋₊).filter Nat.Prime, Real.log p / p

private noncomputable def primeLog (n : ℕ) : ℝ :=
  if n.Prime then Real.log n else 0

private theorem theta_eq_sum_primeLog (x : ℝ) :
    Chebyshev.theta x = ∑ n ∈ Icc 0 ⌊x⌋₊, primeLog n := by
  simp [Chebyshev.theta_eq_sum_Icc, primeLog, sum_filter]

/-- Abel summation for `sum_{p ≤ x} log p / p`, valid down to `x = 1`. -/
theorem primeWeightedSum_eq_theta_div_add_integral {x : ℝ} (hx : 1 ≤ x) :
    primeWeightedSum x = Chebyshev.theta x / x +
      ∫ t in 1..x, Chebyshev.theta t / t ^ 2 := by
  have hsum : primeWeightedSum x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * primeLog n := by
    unfold primeWeightedSum
    rw [sum_filter]
    apply sum_congr rfl
    intro n hn
    by_cases hp : n.Prime <;> simp [primeLog, hp, div_eq_mul_inv, mul_comm]
  rw [hsum, sum_mul_eq_sub_integral_mul₀ primeLog (f := fun t : ℝ => t⁻¹)
    (by simp [primeLog]) x]
  · rw [← intervalIntegral.integral_of_le hx]
    simp_rw [deriv_inv, ← theta_eq_sum_primeLog]
    have hneg : (fun t : ℝ => -(t ^ 2)⁻¹ * Chebyshev.theta t) =
        fun t => -(Chebyshev.theta t / t ^ 2) := by
      funext t
      simp [div_eq_mul_inv, mul_comm]
    rw [hneg, intervalIntegral.integral_neg]
    simp [div_eq_mul_inv, mul_comm]
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop
  · rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg

private theorem intervalIntegrable_theta_div_sq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.theta t / t ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hi : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) :=
    ContinuousOn.integrableOn_Icc ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1])))
  have hs := integrableOn_mul_sum_Icc primeLog (m := 0) (by linarith : 0 ≤ a) hi
  simpa only [← theta_eq_sum_primeLog, div_eq_mul_inv, mul_comm] using hs

/-- A finite-anchor Abel identity. No asymptotic or numerical estimate is assumed. -/
theorem primeWeightedSum_sub_eq_theta_div_sub_add_integral
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    primeWeightedSum b - primeWeightedSum a =
      Chebyshev.theta b / b - Chebyshev.theta a / a +
        ∫ t in a..b, Chebyshev.theta t / t ^ 2 := by
  rw [primeWeightedSum_eq_theta_div_add_integral (ha.trans hab),
    primeWeightedSum_eq_theta_div_add_integral ha]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_theta_div_sq (a := 1) le_rfl ha)
    (intervalIntegrable_theta_div_sq ha hab)
  linarith

/-- The integral of the centered theta error on a finite interval. -/
theorem integral_theta_error_div_sq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (Chebyshev.theta t - t) / t ^ 2) =
      (∫ t in a..b, Chebyshev.theta t / t ^ 2) - (Real.log b - Real.log a) := by
  have hne : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have heq : (∫ t in a..b, (Chebyshev.theta t - t) / t ^ 2) =
      ∫ t in a..b, (Chebyshev.theta t / t ^ 2 - t⁻¹) := by
    apply intervalIntegral.integral_congr
    intro t ht
    field_simp [hne t ht]
  rw [heq, intervalIntegral.integral_sub
    (intervalIntegrable_theta_div_sq ha hab)
    (ContinuousOn.intervalIntegrable (by fun_prop (disch := grind [hne])))]
  congr 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => Real.hasDerivAt_log (hne t ht))
    (ContinuousOn.intervalIntegrable (by fun_prop (disch := grind [hne])))

/-- Centered finite-anchor form, isolating precisely the analytic error terms
needed in a quantitative Mertens estimate. -/
theorem primeWeightedSum_sub_log_eq_anchor
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    primeWeightedSum b - Real.log b =
      primeWeightedSum a - Real.log a +
        (Chebyshev.theta b - b) / b - (Chebyshev.theta a - a) / a +
        ∫ t in a..b, (Chebyshev.theta t - t) / t ^ 2 := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [integral_theta_error_div_sq ha hab]
  have hs := primeWeightedSum_sub_eq_theta_div_sub_add_integral ha hab
  rw [sub_div, sub_div, div_self ha0, div_self hb0]
  linarith

/-- The corresponding weighted sum over all prime powers. -/
noncomputable def mangoldtWeightedSum (x : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, (Λ n : ℝ) / n

/-- Abel summation for the weighted von Mangoldt sum. -/
theorem mangoldtWeightedSum_eq_psi_div_add_integral {x : ℝ} (hx : 1 ≤ x) :
    mangoldtWeightedSum x = Chebyshev.psi x / x +
      ∫ t in 1..x, Chebyshev.psi t / t ^ 2 := by
  have hsum : mangoldtWeightedSum x =
      ∑ n ∈ Icc 0 ⌊x⌋₊, (n : ℝ)⁻¹ * (Λ n : ℝ) := by
    simp [mangoldtWeightedSum, div_eq_mul_inv, mul_comm]
  rw [hsum, sum_mul_eq_sub_integral_mul₀ (fun n => (Λ n : ℝ))
    (f := fun t : ℝ => t⁻¹) (by simp) x]
  · rw [← intervalIntegral.integral_of_le hx]
    simp_rw [deriv_inv, ← Chebyshev.psi_eq_sum_Icc]
    have hneg : (fun t : ℝ => -(t ^ 2)⁻¹ * Chebyshev.psi t) =
        fun t => -(Chebyshev.psi t / t ^ 2) := by
      funext t
      simp [div_eq_mul_inv, mul_comm]
    rw [hneg, intervalIntegral.integral_neg]
    simp [div_eq_mul_inv, mul_comm]
  · intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    fun_prop
  · rw [deriv_inv']
    apply ContinuousOn.integrableOn_Icc
    exact ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1]))).neg

private theorem intervalIntegrable_psi_div_sq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Chebyshev.psi t / t ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hi : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) :=
    ContinuousOn.integrableOn_Icc ((continuousOn_id.pow 2).inv₀ (fun t ht =>
      pow_ne_zero 2 (by change t ≠ 0; linarith [ht.1])))
  have hs := integrableOn_mul_sum_Icc (fun n => (Λ n : ℝ)) (m := 0)
    (by linarith : 0 ≤ a) hi
  simpa only [← Chebyshev.psi_eq_sum_Icc, div_eq_mul_inv, mul_comm] using hs

/-- The centered psi integral on a finite interval. -/
theorem integral_psi_error_div_sq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2) =
      (∫ t in a..b, Chebyshev.psi t / t ^ 2) - (Real.log b - Real.log a) := by
  have hne : ∀ t ∈ Set.uIcc a b, t ≠ 0 := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    linarith [ht.1]
  have heq : (∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2) =
      ∫ t in a..b, (Chebyshev.psi t / t ^ 2 - t⁻¹) := by
    apply intervalIntegral.integral_congr
    intro t ht
    field_simp [hne t ht]
  rw [heq, intervalIntegral.integral_sub
    (intervalIntegrable_psi_div_sq ha hab)
    (ContinuousOn.intervalIntegrable (by fun_prop (disch := grind [hne])))]
  congr 1
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => Real.hasDerivAt_log (hne t ht))
    (ContinuousOn.intervalIntegrable (by fun_prop (disch := grind [hne])))

/-- A finite anchor avoids introducing a limiting Mertens constant. In contrast
to the centered-at-infinity formula, the integral has a positive sign, so a
lower bound for psi gives a lower bound for this weighted sum. -/
theorem mangoldtWeightedSum_sub_log_eq_anchor
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    mangoldtWeightedSum b - Real.log b =
      mangoldtWeightedSum a - Real.log a +
        (Chebyshev.psi b - b) / b - (Chebyshev.psi a - a) / a +
        ∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 := by
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [integral_psi_error_div_sq ha hab,
    mangoldtWeightedSum_eq_psi_div_add_integral ha,
    mangoldtWeightedSum_eq_psi_div_add_integral (ha.trans hab)]
  have hi := intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_psi_div_sq (a := 1) le_rfl ha)
    (intervalIntegrable_psi_div_sq ha hab)
  rw [sub_div, sub_div, div_self ha0, div_self hb0]
  linarith

end TernaryGoldbach.RSBounds
