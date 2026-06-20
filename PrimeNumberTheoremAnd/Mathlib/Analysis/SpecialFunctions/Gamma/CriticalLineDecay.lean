import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Critical-line Gamma decay

This file records the exact norm of `Γ` on the critical line `Re s = 1/2`
together with the resulting exponential decay bound:

* `Complex.gamma_half_vertical_norm_sq`:
  `‖Γ(1/2 + iτ)‖² = π / cosh(πτ)`.
* `Complex.gamma_half_vertical_norm_le_exp`:
  `‖Γ(1/2 + iτ)‖ ≤ √(2π) · exp(-π|τ|/2)`.

Both follow from Euler's reflection formula `Gamma_mul_Gamma_one_sub`,
the conjugation symmetry `Gamma_conj`, and the elementary `sin → cosh`
chain along the line `Re s = 1/2`.
-/

open Real

namespace Complex

private lemma sin_pi_half_add_mul_I (τ : ℝ) :
    Complex.sin (Real.pi * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)) =
      (Real.cosh (Real.pi * τ) : ℂ) := by
  have harg : (Real.pi : ℂ) * (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)
      = (Real.pi / 2 : ℂ) + ((Real.pi * τ : ℝ) : ℂ) * I := by
    norm_num [Complex.ofReal_div, Complex.ofReal_mul]
    ring_nf
  rw [harg]
  simp [Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.cos_mul_I,
    Complex.sin_mul_I, Complex.ofReal_cosh]

/-- Exact critical-line identity:
`‖Γ(1/2+iτ)‖² = π / cosh(πτ)`. -/
theorem gamma_half_vertical_norm_sq (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * τ) := by
  let z : ℂ := ((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I
  have hconj : (starRingEnd ℂ) z = 1 - z := by
    apply Complex.ext <;> norm_num [z, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im]
  have hleft :
      Complex.Gamma z * Complex.Gamma (1 - z) = ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) := by
    rw [← hconj, Complex.Gamma_conj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hsin : Complex.sin (Real.pi * z) = (Real.cosh (Real.pi * τ) : ℂ) := by
    simpa [z] using sin_pi_half_add_mul_I τ
  have hcomplex :
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ) =
        ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 : ℝ) : ℂ)
          = Complex.Gamma z * Complex.Gamma (1 - z) := hleft.symm
      _ = (Real.pi : ℂ) / Complex.sin (Real.pi * z) := Complex.Gamma_mul_Gamma_one_sub z
      _ = ((Real.pi / Real.cosh (Real.pi * τ) : ℝ) : ℂ) := by
        simp [hsin, Complex.ofReal_div]
  simpa [z] using Complex.ofReal_injective hcomplex

private lemma exp_abs_div_two_le_cosh (x : ℝ) : Real.exp |x| / 2 ≤ Real.cosh x := by
  rw [Real.cosh_eq]
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]
  · rw [abs_of_neg (lt_of_not_ge hx)]
    nlinarith [Real.exp_pos x, Real.exp_pos (-x)]

private lemma gamma_half_vertical_norm_sq_le_exp (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ^ 2 ≤
      2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
  rw [gamma_half_vertical_norm_sq]
  have hxabs : |Real.pi * τ| = Real.pi * |τ| := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
  have hcosh_lower : Real.exp (Real.pi * |τ|) / 2 ≤ Real.cosh (Real.pi * τ) := by
    simpa [hxabs] using exp_abs_div_two_le_cosh (Real.pi * τ)
  have hden_pos : 0 < Real.exp (Real.pi * |τ|) / 2 := by positivity
  have hinv : (Real.cosh (Real.pi * τ))⁻¹ ≤ (Real.exp (Real.pi * |τ|) / 2)⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hden_pos hcosh_lower
  have hinv_eval : (Real.exp (Real.pi * |τ|) / 2)⁻¹ =
      2 * Real.exp (-(Real.pi * |τ|)) := by
    rw [div_eq_mul_inv, mul_inv_rev]
    rw [inv_inv, ← Real.exp_neg]
  calc
    Real.pi / Real.cosh (Real.pi * τ) = Real.pi * (Real.cosh (Real.pi * τ))⁻¹ := by ring
    _ ≤ Real.pi * (Real.exp (Real.pi * |τ|) / 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv Real.pi_pos.le
    _ = 2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
      rw [hinv_eval]
      ring

/-- Critical-line Gamma decay:
`‖Γ(1/2+iτ)‖ ≤ √(2π) exp(-π|τ|/2)`. -/
theorem gamma_half_vertical_norm_le_exp (τ : ℝ) :
    ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + (τ : ℂ) * I)‖ ≤
      Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2)) := by
  refine (sq_le_sq₀ (norm_nonneg _) ?_).mp ?_
  · positivity
  have hrhs_sq :
      (Real.sqrt (2 * Real.pi) * Real.exp (-(Real.pi * |τ| / 2))) ^ 2 =
        2 * Real.pi * Real.exp (-(Real.pi * |τ|)) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    rw [sq, ← Real.exp_add]
    ring_nf
  rw [hrhs_sq]
  exact gamma_half_vertical_norm_sq_le_exp τ

end Complex
