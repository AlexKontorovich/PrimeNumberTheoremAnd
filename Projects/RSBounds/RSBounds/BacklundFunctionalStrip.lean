import RSBounds.BacklundFunctionalMultiplier
import RSBounds.BacklundHyperbolicFactor
import RSBounds.BacklundGammaModulusHorizontal

open Complex Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier

theorem norm_cos_le_cosh_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos, norm_div, Complex.norm_ofNat]
  calc
    _ ≤ (‖Complex.exp (z * I)‖ + ‖Complex.exp (-z * I)‖) / 2 := by
      gcongr
      exact norm_add_le _ _
    _ = Real.cosh z.im := by
      rw [Complex.norm_exp_mul_I, Complex.norm_exp_mul_I, Complex.neg_im, neg_neg,
        Real.cosh_eq]
      ring

theorem cosh_div_sinh_half_eq {t : ℝ} (ht : 0 < t) :
    Real.cosh (Real.pi * t / 2) / Real.sinh (Real.pi * t / 2) =
      (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
  have h : 0 < Real.pi * t / 2 := by positivity
  have he : Real.exp (-Real.pi * t) = (Real.exp (Real.pi * t / 2))⁻¹ ^ 2 := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul]
    congr 1
    ring
  have hp : 1 < Real.exp (Real.pi * t / 2) := Real.one_lt_exp_iff.mpr h
  have hn : Real.exp (Real.pi * t / 2) ≠ 0 := (Real.exp_pos _).ne'
  rw [he, Real.cosh_eq, Real.sinh_eq, Real.exp_neg]
  field_simp <;> ring

theorem gamma_cosh_ratio_eq {t : ℝ} (ht : 0 < t) :
    ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi =
      Real.sqrt (t / (2 * Real.pi)) *
        Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
  have hs : 0 < Real.sinh (Real.pi * t / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hc : 0 < Real.cosh (Real.pi * t / 2) := Real.cosh_pos _
  have hd : Real.sinh (Real.pi * t) =
      2 * Real.sinh (Real.pi * t / 2) * Real.cosh (Real.pi * t / 2) := by
    convert Real.sinh_two_mul (x := Real.pi * t / 2) using 1 <;> ring
  have hq : 0 ≤ (1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)) := by
    rw [← cosh_div_sinh_half_eq ht]
    positivity
  have he : (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) ^ 2 =
      t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
    rw [div_pow, mul_pow, BacklundGammaBaseline.norm_Gamma_one_add_mul_I_sq ht,
      ← cosh_div_sinh_half_eq ht, hd]
    field_simp <;> ring
  have hs1 := Real.sq_sqrt (by positivity : 0 ≤ t / (2 * Real.pi))
  have hs2 := Real.sq_sqrt hq
  have hprod : (Real.sqrt (t / (2 * Real.pi)) *
      Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t)))) ^ 2 =
      t / (2 * Real.pi) * ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by
    rw [mul_pow, hs1, hs2]
  have hL : 0 ≤ ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi := by positivity
  have hR : 0 ≤ Real.sqrt (t / (2 * Real.pi)) *
      Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) := by positivity
  nlinarith

theorem power_normalization {t : ℝ} (ht : 0 < t) (σ : ℝ) :
    (2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi)) =
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hd : 0 < t / (2 * Real.pi) := div_pos ht hp
  rw [Real.sqrt_eq_rpow]
  simp only [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos hd]
  rw [← Real.exp_add, ← Real.exp_add, Real.log_div ht.ne' hp.ne']
  congr 1
  ring

/-- Quantitative functional-equation multiplier on the whole reflected
half-strip. The only height restriction is `t >= 50`. -/
theorem norm_multiplier_strip_le {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
    ‖multiplier ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < 2 * Real.pi := by positivity
  have hG : ‖Complex.Gamma (1 - ((σ : ℂ) + t * I))‖ ≤
      ‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2)) := by
    have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
      simp
      push_cast
      ring
    rw [he, Complex.Gamma_conj, norm_conj]
    convert BacklundGammaModulus.norm_Gamma_horizontal_le
      (a := 1 - σ) (t := t) (by linarith) (by linarith) ht using 1 <;> ring
  have hP : ‖(2 * (Real.pi : ℂ)) ^ (-(1 - ((σ : ℂ) + t * I)))‖ =
      (2 * Real.pi) ^ (σ - 1) := by
    have he : 2 * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [he, Complex.norm_cpow_eq_rpow_re_of_pos hp]
    congr 1
    simp <;> ring
  have hC : ‖Complex.cos ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)‖ ≤
      Real.cosh (Real.pi * t / 2) := by
    have he : (((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)).im = -(Real.pi * t / 2) := by
      simp [Complex.div_ofNat_im, Complex.mul_im] <;> ring
    simpa [he, Real.cosh_neg] using norm_cos_le_cosh_im
      ((Real.pi : ℂ) * (1 - ((σ : ℂ) + t * I)) / 2)
  have hpow : 2 * (2 * Real.pi) ^ (σ - 1) = (2 * Real.pi) ^ σ / Real.pi := by
    rw [Real.rpow_sub hp, Real.rpow_one]
    field_simp
  unfold multiplier
  rw [norm_mul, norm_mul, norm_mul, hP, Complex.norm_ofNat]
  calc
    _ ≤ 2 * (2 * Real.pi) ^ (σ - 1) *
        (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * t ^ (-σ) * Real.exp (9 / (4 * t ^ 2))) *
        Real.cosh (Real.pi * t / 2) := by gcongr
    _ = ((2 * Real.pi) ^ σ * t ^ (-σ) * Real.sqrt (t / (2 * Real.pi))) *
        Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) *
        Real.exp (9 / (4 * t ^ 2)) := by
      rw [hpow]
      have he := gamma_cosh_ratio_eq ht0
      calc
        _ = ((2 * Real.pi) ^ σ * t ^ (-σ)) *
            (‖Complex.Gamma (1 + (t : ℂ) * I)‖ * Real.cosh (Real.pi * t / 2) / Real.pi) *
            Real.exp (9 / (4 * t ^ 2)) := by ring
        _ = _ := by rw [he]; ring
    _ ≤ (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (1 / (4 * t ^ 2)) *
        Real.exp (9 / (4 * t ^ 2)) := by
      rw [power_normalization ht0]
      gcongr
      exact BacklundHyperbolicFactor.sqrt_exp_ratio_le ht
    _ = _ := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem norm_zeta_reflected_strip_le {σ t : ℝ}
    (hσ : -(1 / 2 : ℝ) ≤ σ) (hσ' : σ ≤ 1 / 2) (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ := by
  have ht0 : 0 < t := by linarith
  rw [functional_equation (by simpa using ht0.ne'), norm_mul]
  have he : 1 - ((σ : ℂ) + t * I) = conj (((1 - σ : ℝ) : ℂ) + t * I) := by
    simp
    push_cast
    ring
  rw [he, riemannZeta_conj, norm_conj]
  exact mul_le_mul_of_nonneg_right (norm_multiplier_strip_le hσ hσ' ht) (norm_nonneg _)

end TernaryGoldbach.RSBounds.BacklundFunctionalMultiplier
