import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundGammaBaseline

theorem norm_Gamma_one_sub_mul_I (t : ℝ) :
    ‖Complex.Gamma (1 - (t : ℂ) * I)‖ = ‖Complex.Gamma (1 + (t : ℂ) * I)‖ := by
  have he : 1 - (t : ℂ) * I = conj (1 + (t : ℂ) * I) := by simp [sub_eq_add_neg]
  rw [he, Complex.Gamma_conj, norm_conj]

/-- Exact Gamma modulus at real part one, from Mathlib's reflection and
recurrence formulae. -/
theorem norm_Gamma_one_add_mul_I_sq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 =
      Real.pi * t / Real.sinh (Real.pi * t) := by
  have htC : (t : ℂ) * I ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne') I_ne_zero
  have hs : 0 < Real.sinh (Real.pi * t) := Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos ht)
  have hsin : ‖Complex.sin ((Real.pi : ℂ) * ((t : ℂ) * I))‖ = Real.sinh (Real.pi * t) := by
    have he : (Real.pi : ℂ) * ((t : ℂ) * I) = ((Real.pi * t : ℝ) : ℂ) * I := by
      push_cast
      ring
    rw [he, Complex.sin_mul_I, ← Complex.ofReal_sinh (Real.pi * t), norm_mul,
      norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs]
  have hr := congrArg norm (Complex.Gamma_mul_Gamma_one_sub ((t : ℂ) * I))
  rw [norm_mul, norm_div, norm_Gamma_one_sub_mul_I, hsin] at hr
  have hpi : ‖(Real.pi : ℂ)‖ = Real.pi := by simp [Real.pi_pos.le]
  rw [hpi] at hr
  have hc := congrArg norm (Complex.Gamma_add_one ((t : ℂ) * I) htC)
  rw [norm_mul, norm_mul] at hc
  have harg : (t : ℂ) * I + 1 = 1 + (t : ℂ) * I := add_comm _ _
  rw [harg] at hc
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, norm_I, mul_one] at hc
  calc
    _ = t * (‖Complex.Gamma ((t : ℂ) * I)‖ * ‖Complex.Gamma (1 + (t : ℂ) * I)‖) := by
      rw [pow_two, hc]
      ring
    _ = t * (Real.pi / Real.sinh (Real.pi * t)) := by rw [hr]
    _ = _ := by ring

theorem norm_Gamma_one_add_mul_I_sq_exp {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ ^ 2 =
      2 * Real.pi * t * Real.exp (-Real.pi * t) /
        (1 - Real.exp (-2 * Real.pi * t)) := by
  rw [norm_Gamma_one_add_mul_I_sq ht, Real.sinh_eq]
  have hp : 0 < Real.pi * t := mul_pos Real.pi_pos ht
  have he : Real.exp (-2 * Real.pi * t) = Real.exp (-(Real.pi * t)) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have he' : Real.exp (-Real.pi * t) = Real.exp (-(Real.pi * t)) := by congr 1; ring
  rw [he, he', Real.exp_neg]
  have hexp : Real.exp (Real.pi * t) ≠ 0 := (Real.exp_pos _).ne'
  have hlt : 1 < Real.exp (Real.pi * t) := Real.one_lt_exp_iff.mpr hp
  field_simp

end TernaryGoldbach.RSBounds.BacklundGammaBaseline
