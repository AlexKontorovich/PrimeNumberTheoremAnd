import RSBounds.BacklundGammaBaseline
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier

noncomputable def multiplier (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-(1 - s)) * Complex.Gamma (1 - s) *
    Complex.cos ((Real.pi : ℂ) * (1 - s) / 2)

theorem functional_equation {s : ℂ} (hs : s.im ≠ 0) :
    riemannZeta s = multiplier s * riemannZeta (1 - s) := by
  have hn : ∀ n : ℕ, 1 - s ≠ -(n : ℂ) := by
    intro n he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.neg_im, Complex.natCast_im,
      neg_zero, zero_sub] at hh
    exact hs (neg_eq_zero.mp hh)
  have hone : 1 - s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, zero_sub] at hh
    exact hs (neg_eq_zero.mp hh)
  have hh := riemannZeta_one_sub hn hone
  simpa [multiplier, sub_sub_cancel] using hh

theorem norm_multiplier_imaginary {t : ℝ} (ht : 0 < t) :
    ‖multiplier ((t : ℂ) * I)‖ =
      ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.sinh (Real.pi * t / 2) / Real.pi := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hpow : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - (t : ℂ) * I))‖ = (2 * Real.pi)⁻¹ := by
    have he : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp [Real.rpow_neg_one]
  have hcos : ‖Complex.cos ((Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2)‖ =
      Real.sinh (Real.pi * t / 2) := by
    have he : (Real.pi : ℂ) * (1 - (t : ℂ) * I) / 2 =
        (Real.pi : ℂ) / 2 - ((Real.pi * t / 2 : ℝ) : ℂ) * I := by
      push_cast
      ring
    have hs : 0 < Real.sinh (Real.pi * t / 2) := Real.sinh_pos_iff.mpr (by positivity)
    rw [he, Complex.cos_pi_div_two_sub, Complex.sin_mul_I,
      ← Complex.ofReal_sinh (Real.pi * t / 2), norm_mul, norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  unfold multiplier
  rw [norm_mul, norm_mul, norm_mul, hpow, hcos,
    BacklundGammaBaseline.norm_Gamma_one_sub_mul_I]
  norm_num
  field_simp

theorem norm_multiplier_imaginary_le {t : ℝ} (ht : 0 < t) :
    ‖multiplier ((t : ℂ) * I)‖ ≤ Real.sqrt (t / (2 * Real.pi)) := by
  have hs : 0 < Real.sinh (Real.pi * t / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  have hd : Real.sinh (Real.pi * t) =
      2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    convert Real.sinh_two_mul (x := Real.pi * t / 2) using 1 <;> ring
  have he : ‖multiplier ((t : ℂ) * I)‖ ^ 2 =
      t / (2 * Real.pi) * (Real.sinh (Real.pi * t / 2) / Real.cosh (Real.pi * t / 2)) := by
    rw [norm_multiplier_imaginary ht, div_pow, mul_pow,
      BacklundGammaBaseline.norm_Gamma_one_add_mul_I_sq ht, hd]
    field_simp
  have hratio : Real.sinh (Real.pi * t / 2) / Real.cosh (Real.pi * t / 2) ≤ 1 := by
    rw [div_le_one hc]
    exact (Real.sinh_lt_cosh (x := Real.pi * t / 2)).le
  have hsq : ‖multiplier ((t : ℂ) * I)‖ ^ 2 ≤ t / (2 * Real.pi) := by
    rw [he]
    simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ t / (2 * Real.pi))
  have hroot := Real.sq_sqrt (by positivity : 0 ≤ t / (2 * Real.pi))
  nlinarith [norm_nonneg (multiplier ((t : ℂ) * I)), Real.sqrt_nonneg (t / (2 * Real.pi))]

/-- The exact left-edge estimate needed in the strip argument. -/
theorem norm_zeta_imaginary_le {t : ℝ} (ht : 0 < t) :
    ‖riemannZeta ((t : ℂ) * I)‖ ≤
      Real.sqrt (t / (2 * Real.pi)) * ‖riemannZeta (1 + (t : ℂ) * I)‖ := by
  rw [functional_equation (by simpa using ht.ne'), norm_mul]
  have he : 1 - (t : ℂ) * I = conj (1 + (t : ℂ) * I) := by simp [sub_eq_add_neg]
  rw [he, riemannZeta_conj, norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_multiplier_imaginary_le ht) (norm_nonneg _)

end TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier
