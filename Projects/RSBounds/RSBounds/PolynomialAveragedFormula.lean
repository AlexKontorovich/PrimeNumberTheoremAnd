/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.PolynomialZetaFormula
import RSBounds.PolynomialZeroKernel

/-!
# Assembling the fourfold averaged explicit formula

All five primitive formulas use one sequence of good contour heights. Their
fourth finite difference gives the upper polynomial smoothing of psi, with
main term `x + 2*h`, constant `-log(2*pi)`, and an explicit left remainder.
No estimate for the zero sum or remainder is assumed or asserted here.
-/

open Complex Finset Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.PolynomialAveraged

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialZeroKernel
open PolynomialZeta PolynomialPsi

/-- The zero coefficient after fourfold averaging and normalization. -/
noncomputable def zeroCoefficient (x h : ℝ) (ρ : ℂ) : ℂ :=
  forwardDiff h 4 (antiderivative ρ 4) x / (h : ℂ) ^ 4

/-- The left contour remainder after the same averaging operation. -/
noncomputable def leftRemainder (x h : ℝ) : ℂ :=
  forwardDiff h 4 psi4LeftRemainder x / (h : ℂ) ^ 4

private theorem antiderivative_four_eq (ρ : ℂ) (x : ℝ) :
    antiderivative ρ 4 x =
      (x : ℂ) ^ (ρ + 4) / (ρ * (ρ + 1) * (ρ + 2) * (ρ + 3) * (ρ + 4)) := by
  norm_num [antiderivative, rising]

private theorem forwardDiff_four_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 4 (fun t => ∑ i ∈ s, f i t) x =
      ∑ i ∈ s, forwardDiff h 4 (f i) x := by
  simp only [forwardDiff_four, sum_add_distrib, sum_sub_distrib, mul_sum]

private theorem forwardDiff_four_mul (c : ℂ) (f : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 4 (fun t => c * f t) x = c * forwardDiff h 4 f x := by
  simp only [forwardDiff_four]
  ring

private theorem forwardDiff_four_sub (f g : ℝ → ℂ) (x h : ℝ) :
    forwardDiff h 4 (fun t => f t - g t) x =
      forwardDiff h 4 f x - forwardDiff h 4 g x := by
  simp only [forwardDiff_four]
  ring

/-- The finite difference of the integrated main term. -/
theorem normalized_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    forwardDiff h 4 (fun t : ℝ => (t : ℂ) ^ 5 / 120) x / (h : ℂ) ^ 4 =
      ((x + 2 * h : ℝ) : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (PolynomialSmoothing.fourth_difference_main_term hh x)
  push_cast at hc
  rw [forwardDiff_four]
  push_cast
  convert hc using 1 <;> ring

/-- Fourfold averaging leaves the constant at the zero pole unchanged. -/
theorem normalized_zero_pole {h : ℝ} (hh : h ≠ 0) (x : ℝ) (c : ℂ) :
    forwardDiff h 4 (fun t : ℝ => (t : ℂ) ^ 4 * c / 24) x / (h : ℂ) ^ 4 = c := by
  have hh0 : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  rw [forwardDiff_four]
  push_cast
  field_simp [hh0]
  ring

/-- Casting the finite arithmetic smoothing identity into the complex formula. -/
theorem normalized_Psi4 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N) :
    forwardDiff h 4 (fun t => (Psi4 t : ℂ)) x / (h : ℂ) ^ 4 =
      (psiUpper N x h : ℂ) := by
  have hc := congrArg (fun t : ℝ => (t : ℂ))
    (fourthDifference_Psi4 hx hh hN)
  simpa only [forwardDiff_four, fourthDifference, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_ofNat] using hc

private theorem tendsto_normalized_forwardDiff_four
    {F : ℕ → ℝ → ℂ} {G : ℝ → ℂ} (x h : ℝ)
    (h0 : Tendsto (fun k => F k x) atTop (𝓝 (G x)))
    (h1 : Tendsto (fun k => F k (x + h)) atTop (𝓝 (G (x + h))))
    (h2 : Tendsto (fun k => F k (x + 2 * h)) atTop (𝓝 (G (x + 2 * h))))
    (h3 : Tendsto (fun k => F k (x + 3 * h)) atTop (𝓝 (G (x + 3 * h))))
    (h4 : Tendsto (fun k => F k (x + 4 * h)) atTop (𝓝 (G (x + 4 * h)))) :
    Tendsto (fun k => forwardDiff h 4 (F k) x / (h : ℂ) ^ 4) atTop
      (𝓝 (forwardDiff h 4 G x / (h : ℂ) ^ 4)) := by
  simpa only [forwardDiff_four] using
    ((((h4.sub (h3.const_mul 4)).add (h2.const_mul 6)).sub
      (h1.const_mul 4)).add h0).div_const ((h : ℂ) ^ 4)

/-- The upper fourfold averaged explicit formula along a common sequence
of good heights. The left contour remainder is retained explicitly. -/
theorem explicit_formula_upper_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
      (𝓝 (((x + 2 * h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi))) := by
  let F : ℕ → ℝ → ℂ := fun k t => ∑ ρ ∈ zerosRectD zetaF (T k),
    (multRectD zetaF (T k) ρ : ℂ) * antiderivative ρ 4 t
  let G : ℝ → ℂ := fun t => (t : ℂ) ^ 5 / 120 - (Psi4 t : ℂ) -
    psi4LeftRemainder t - (t : ℂ) ^ 4 * Complex.log (2 * Real.pi) / 24
  have hlim (t : ℝ) (ht : 0 < t) : Tendsto (fun k => F k t) atTop (𝓝 (G t)) := by
    simpa only [F, G, antiderivative_four_eq] using
      explicit_formula_Psi4_at_heights hT ht
  have havg := tendsto_normalized_forwardDiff_four x h (hlim x hx)
    (hlim (x + h) (by linarith)) (hlim (x + 2 * h) (by linarith))
    (hlim (x + 3 * h) (by linarith)) (hlim (x + 4 * h) (by linarith))
  have hsum (k : ℕ) : forwardDiff h 4 (F k) x / (h : ℂ) ^ 4 =
      ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ := by
    dsimp only [F]
    rw [forwardDiff_four_sum, sum_div]
    apply sum_congr rfl
    intro ρ _
    rw [forwardDiff_four_mul, mul_div_assoc]
    rfl
  have hvalue : forwardDiff h 4 G x / (h : ℂ) ^ 4 =
      ((x + 2 * h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
        leftRemainder x h - Complex.log (2 * Real.pi) := by
    dsimp only [G]
    rw [forwardDiff_four_sub, forwardDiff_four_sub, forwardDiff_four_sub,
      sub_div, sub_div, sub_div, normalized_main_term hh.ne',
      normalized_Psi4 hx.le hh hN, normalized_zero_pole hh.ne']
    rfl
  simpa only [hsum, hvalue] using havg

/-- Existence form of the upper averaged formula; no zero-location premise. -/
theorem explicit_formula_upper {x h : ℝ} (hx : 0 < x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient x h ρ) atTop
        (𝓝 (((x + 2 * h : ℝ) : ℂ) - (psiUpper N x h : ℂ) -
          leftRemainder x h - Complex.log (2 * Real.pi))) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  exact ⟨T, hT.mem, explicit_formula_upper_at_heights hT hx hh hN⟩

/-- The same formula shifted to give the lower polynomial smoothing. -/
theorem explicit_formula_lower_at_heights {T : ℕ → ℝ}
    (hT : GoodHeights zetaF Bz T) {x h : ℝ} (hx : 4 * h < x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) :
    Tendsto (fun k => ∑ ρ ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) ρ : ℂ) * zeroCoefficient (x - 4 * h) h ρ) atTop
      (𝓝 (((x - 2 * h : ℝ) : ℂ) - (psiLower N x h : ℂ) -
        leftRemainder (x - 4 * h) h - Complex.log (2 * Real.pi))) := by
  have hv := explicit_formula_upper_at_heights hT (x := x - 4 * h)
    (by linarith) hh (show x - 4 * h + 4 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel,
    show x - 4 * h + 2 * h = x - 2 * h by ring] using hv

end TernaryGoldbach.RSBounds.PolynomialAveraged
