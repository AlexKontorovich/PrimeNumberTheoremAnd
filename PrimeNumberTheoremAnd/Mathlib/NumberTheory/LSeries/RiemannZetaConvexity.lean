/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecificLimits.Normed
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaAbelContinuation
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Bounds for the Riemann zeta function

Strip bounds for `riemannZeta`, used in `ZetaFiniteOrder`. Euler-product input is in
`PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta`.

## Main results

* `norm_riemannZeta_le`, `norm_riemannZeta_shift_le` : strip bounds for the Λ₀ pipeline
* `norm_riemannZeta_ratio_le_on_verticalLine`, `norm_riemannZeta_ratio_le_on_vertical_line` :
  convexity input on vertical lines
* `norm_riemannZeta_lt_linear_im_on_strip` : linear bound in the strip `1/2 ≤ re < 3`
-/

@[expose] public section

open scoped BigOperators Topology
open Real Set Filter Topology MeasureTheory Complex

/-!
### Vertical-line ratio bound
-/

/-- For `σ > 1`, the Euler product at `re s = 2σ` controls `‖ζ(2σ) / ζ σ‖` on the line `σ + it`. -/
theorem norm_riemannZeta_ratio_le_on_verticalLine (σ t : ℝ) (hσ : 1 < σ) :
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖ ≤ ‖riemannZeta (verticalLine σ t)‖ := by
  have hs : 1 < (verticalLine σ t).re := by rw [verticalLine_re]; exact hσ
  calc
    ‖riemannZeta (2 * (σ : ℂ)) / riemannZeta (σ : ℂ)‖
        = ∏' p : Nat.Primes, (1 + ((p : ℕ) : ℝ) ^ (-σ))⁻¹ :=
          norm_riemannZeta_div_riemannZeta σ hσ
    _ ≤ ∏' p : Nat.Primes, (‖1 - ((p : ℕ) : ℂ) ^ (-verticalLine σ t)‖)⁻¹ :=
        tprod_inv_one_add_real_le_riemannZeta_norm_on_verticalLine σ t hσ
    _ = ‖riemannZeta (verticalLine σ t)‖ := by
      simpa [verticalLine] using (norm_riemannZeta_eulerProduct (verticalLine σ t) hs).symm

/-- Convexity input at `σ = 3/2`: `‖ζ 3 / ζ (3/2)‖ ≤ ‖ζ (3/2 + it)‖`. -/
theorem norm_riemannZeta_ratio_le_on_vertical_line (t : ℝ) :
    ‖riemannZeta 3 / riemannZeta ((3 : ℝ) / 2)‖ ≤ ‖riemannZeta (verticalLine (3 / 2 : ℝ) t)‖ := by
  have hσ : 1 < (3 / 2 : ℝ) := by norm_num
  have h2 : (2 : ℂ) * ((3 / 2 : ℝ) : ℂ) = (3 : ℂ) := by norm_num
  simpa [h2, div_eq_mul_inv, mul_comm] using
    norm_riemannZeta_ratio_le_on_verticalLine (3 / 2 : ℝ) t hσ

/-!
### Abel strip bounds
-/

/-- On `zetaAbelContinuationDomain`, `‖ζ s‖ ≤ 1 + ‖(s - 1)⁻¹‖ + ‖s‖ / re s`. -/
theorem norm_riemannZeta_le (s : ℂ) (hs : s ∈ zetaAbelContinuationDomain) :
    ‖riemannZeta s‖ ≤ 1 + ‖1 / (s - 1)‖ + ‖s‖ / s.re := by
  rw [riemannZeta_eq_zetaAbelContinuationFormula s hs]
  exact norm_zetaAbelContinuationFormula_le s hs

namespace StripBounds

private lemma three_sq_add_sq_le_sq_add_abs (t : ℝ) :
    (3 : ℝ) ^ 2 + t ^ 2 ≤ (3 + |t|) ^ 2 := by
  nlinarith [abs_nonneg t, sq_abs t, sq_nonneg (3 + |t|)]

private lemma norm_lt_three_add_abs_im (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    ‖s‖ < (3 : ℝ) + |s.im| := by
  have hneg : (-(3 : ℝ)) < s.re := by linarith [hs.1]
  have hre : s.re ^ 2 < (3 : ℝ) ^ 2 := sq_lt_sq' hneg hs.2
  have hsum : s.re ^ 2 + s.im ^ 2 < (3 : ℝ) ^ 2 + s.im ^ 2 := (add_lt_add_iff_right _).mpr hre
  have hsq : Complex.normSq s < (3 + |s.im|) ^ 2 := by
    have := lt_of_lt_of_le hsum (three_sq_add_sq_le_sq_add_abs s.im)
    simpa [Complex.normSq_apply, pow_two] using this
  exact (sq_lt_sq₀ (norm_nonneg s) (by positivity)).1 (by rwa [Complex.sq_norm])

private lemma one_div_re_le_two (s : ℂ) (hs : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ)) :
    1 / s.re ≤ (2 : ℝ) := by
  have hpos : 0 < s.re := by linarith [hs.1]
  calc
    1 / s.re ≤ 1 / (1 / 2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hs.1
    _ = 2 := by norm_num

private lemma one_le_norm_sub_one (s : ℂ) (hs_im : (1 : ℝ) ≤ |s.im|) :
    (1 : ℝ) ≤ ‖s - 1‖ := by
  have : |s.im| ≤ ‖s - 1‖ := by
    simpa [Complex.sub_im, Complex.one_im] using Complex.abs_im_le_norm (s - 1)
  exact le_trans hs_im this

private lemma norm_lt_linear_im (s : ℂ) (hs_re : (1 / 2 : ℝ) ≤ s.re ∧ s.re < (3 : ℝ))
    (hs_im : (1 : ℝ) ≤ |s.im|) :
    ‖riemannZeta s‖ < (1 : ℝ) + 1 + ((3 : ℝ) + |s.im|) * 2 := by
  have hs_ne : s ≠ 1 := by
    intro h; rw [h] at hs_im; simp [Complex.one_im] at hs_im; linarith
  have hσ : zetaAbelContinuationReLower < s.re :=
    lt_of_lt_of_le zetaAbelContinuationReLower_lt_half (by simpa using hs_re.1)
  calc
    ‖riemannZeta s‖
        ≤ 1 + 1 / ‖s - 1‖ + ‖s‖ / s.re := by
          simpa [one_div] using norm_riemannZeta_le s (mem_zetaAbelContinuationDomain_of_re hs_ne hσ)
    _ ≤ 1 + 1 + ‖s‖ / s.re := by
      gcongr
      simpa [one_div] using inv_le_one_of_one_le₀ (one_le_norm_sub_one s hs_im)
    _ ≤ 1 + 1 + ‖s‖ * 2 := by
      gcongr
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (one_div_re_le_two s hs_re) (norm_nonneg s)
    _ < 1 + 1 + ((3 : ℝ) + |s.im|) * 2 := by
      gcongr
      exact norm_lt_three_add_abs_im s hs_re

end StripBounds

open StripBounds

/-- In the strip `1/2 ≤ re z < 3` with `1 ≤ |im z|`, `‖ζ z‖ < 8 + 2|im z|`. -/
theorem norm_riemannZeta_lt_linear_im_on_strip (z : ℂ)
    (hz_re : z.re ∈ Ico (1 / 2 : ℝ) (3 : ℝ)) (hz_im : (1 : ℝ) ≤ |z.im|) :
    ‖riemannZeta z‖ < (8 : ℝ) + 2 * |z.im| := by
  have hz_re' : (1 / 2 : ℝ) ≤ z.re ∧ z.re < (3 : ℝ) := by simpa [Ico] using hz_re
  calc
    ‖riemannZeta z‖
        < (1 : ℝ) + 1 + ((3 : ℝ) + |z.im|) * 2 := norm_lt_linear_im z hz_re' hz_im
    _ = (8 : ℝ) + 2 * |z.im| := by ring

private lemma shift_mem_strip (s : ℂ) (t : ℝ) (hs : ‖s‖ ≤ 1) (ht : (2 : ℝ) < |t|) :
    let z := verticalLine (s.re + (3 / 2 : ℝ)) (s.im + t)
    z.re ∈ Ico (1 / 2 : ℝ) (3 : ℝ) ∧ (1 : ℝ) ≤ |z.im| := by
  simp only [verticalLine_re, verticalLine_im, Set.mem_Ico]
  constructor
  · have h := (Complex.abs_re_le_norm s).trans hs
    rw [abs_le] at h
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · have h := (Complex.abs_im_le_norm s).trans hs
    rw [abs_le] at h
    by_cases ht₀ : 0 ≤ t
    · have ht' : (2 : ℝ) < t := by rwa [abs_of_nonneg ht₀] at ht
      rw [abs_of_nonneg (by linarith : 0 ≤ s.im + t)]
      linarith [h.1, ht']
    · push Not at ht₀
      have ht' : t < (-2 : ℝ) := by
        rw [abs_of_neg ht₀] at ht
        linarith
      have hneg : s.im + t < 0 := by linarith [h.2, ht']
      rw [abs_of_neg hneg]
      linarith [h.2, ht']

/-- If `‖s‖ ≤ 1` and `2 < |t|`, then `‖ζ (s + 3/2 + it)‖ < 10 + 2|t|`. -/
theorem norm_riemannZeta_shift_le (t : ℝ) (s : ℂ) (hs : ‖s‖ ≤ 1) (ht : 2 < |t|) :
    ‖riemannZeta (s + (3 / 2 : ℝ) + Complex.I * t)‖ < 10 + 2 * |t| := by
  set z := verticalLine (s.re + (3 / 2 : ℝ)) (s.im + t)
  have hz : s + (3 / 2 : ℝ) + Complex.I * t = z := by
    simp only [z]
    conv_lhs => rw [mul_comm Complex.I t]
    exact verticalLine_add_const s (3 / 2) t
  have ⟨hz_re, hz_im⟩ := shift_mem_strip s t hs ht
  have hz_im_le : |z.im| ≤ 1 + |t| := by
    simp only [z, verticalLine_im]
    linarith [abs_add_le s.im t, (Complex.abs_im_le_norm s).trans hs]
  calc
    ‖riemannZeta (s + (3 / 2 : ℝ) + Complex.I * t)‖ = ‖riemannZeta z‖ := by rw [hz]
    _ < (8 : ℝ) + 2 * |z.im| := norm_riemannZeta_lt_linear_im_on_strip z hz_re hz_im
    _ ≤ (8 : ℝ) + 2 * (1 + |t|) := by gcongr
    _ = (10 : ℝ) + 2 * |t| := by ring
