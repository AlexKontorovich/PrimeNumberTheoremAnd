/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# The exact trigonometric polynomial in the RS75 zero-free-region proof

Rosser and Schoenfeld (1975), p. 250, immediately before Theorem 1,
use `8*(a + cos theta)^2*(b + cos theta)^2`, with `a = 0.9126`
and `b = 0.2766`. All displayed decimals here are exact rational numbers.

Source: https://doi.org/10.1090/S0025-5718-1975-0457373-7

This module proves the polynomial identities and positivity. It does not
assert the zero-free region or any logarithmic-derivative estimate.
-/

namespace TernaryGoldbach.RSBounds.RS75Polynomial

noncomputable def a : ℝ := 0.9126

noncomputable def b : ℝ := 0.2766

/-- The exact expanded cosine polynomial used by Rosser and Schoenfeld. -/
noncomputable def P (θ : ℝ) : ℝ :=
  11.1859355312082048 + 19.073344004352 * Real.cos θ +
    11.67618784 * Real.cos (2 * θ) + 4.7568 * Real.cos (3 * θ) +
    Real.cos (4 * θ)

/-- The coefficients, extended by zero beyond degree four. -/
noncomputable def coeff (k : ℕ) : ℝ :=
  if k = 0 then 11.1859355312082048
  else if k = 1 then 19.073344004352
  else if k = 2 then 11.67618784
  else if k = 3 then 4.7568
  else if k = 4 then 1
  else 0

/-- Exact factorization; no floating-point approximation occurs. -/
theorem factorization (θ : ℝ) :
    P θ = 8 * (a + Real.cos θ) ^ 2 * (b + Real.cos θ) ^ 2 := by
  unfold P a b
  rw [show 4 * θ = 2 * (2 * θ) by ring]
  simp only [Real.cos_two_mul, Real.cos_three_mul]
  ring

/-- Positivity for every real argument, supplied by the square factorization. -/
theorem P_nonneg (θ : ℝ) : 0 ≤ P θ := by
  rw [factorization]
  positivity

theorem coeff_nonneg (k : ℕ) : 0 ≤ coeff k := by
  unfold coeff
  split_ifs <;> norm_num

theorem coeff_pos_of_le_four {k : ℕ} (hk : k ≤ 4) : 0 < coeff k := by
  interval_cases k <;> norm_num [coeff]

/-- Finite-sum form for later logarithmic-derivative arguments. -/
theorem P_eq_sum (θ : ℝ) :
    P θ = ∑ k ∈ Finset.range 5, coeff k * Real.cos ((k : ℝ) * θ) := by
  norm_num [P, coeff, Finset.sum_range_succ]

/-- The sum of the four nonconstant coefficients in the RS75 proof. -/
theorem sum_positive_coefficients :
    (∑ k ∈ Finset.range 4, coeff (k + 1)) = 36.506331844352 := by
  norm_num [coeff, Finset.sum_range_succ]

theorem sum_positive_coefficients_Icc :
    (∑ k ∈ Finset.Icc 1 4, coeff k) = 36.506331844352 := by
  norm_num [coeff, Finset.sum_Icc_succ_top]

end TernaryGoldbach.RSBounds.RS75Polynomial
