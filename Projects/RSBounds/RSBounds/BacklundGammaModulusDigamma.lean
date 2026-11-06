import RSBounds.BacklundDigammaStirling

/-!
# The real digamma estimate used for Gamma modulus bounds

This quantitative estimate is unconditional: its series input is the proved
IEANTN Gauss formula, and the vertical estimate is adapted from Zeta23.
-/

open Complex Real

namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem abs_digamma_re_sub_log_le {a t : ℝ}
    (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 50 ≤ t) :
    |(Complex.digamma ((a : ℂ) + t * I)).re - Real.log t| ≤ 9 / (2 * t ^ 2) := by
  let w : ℂ := (a : ℂ) + t * I
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := by linarith
  have hre : w.re = a := by simp [w]
  have him : w.im = t := by simp [w]
  have hw : 0 < w.re := by simpa [hre] using ha0
  have hD : 0 < a ^ 2 + t ^ 2 := by positivity
  have hmain := TernaryGoldbach.RSBounds.BacklundZeta23.StirlingVert.digamma_stirling hw
    (by rw [him, abs_of_pos ht0]; linarith)
  rw [him] at hmain
  have hlogre : (Complex.log w).re = Real.log (a ^ 2 + t ^ 2) / 2 := by
    rw [Complex.log_re, show ‖w‖ = Real.sqrt (a ^ 2 + t ^ 2) by
      rw [Complex.norm_eq_sqrt_sq_add_sq, hre, him], Real.log_sqrt hD.le]
  have hinvre : ((1 / 2 : ℂ) / w).re = a / (2 * (a ^ 2 + t ^ 2)) := by
    rw [show (1 / 2 : ℂ) / w = ((1 / 2 : ℝ) : ℂ) * w⁻¹ by push_cast; ring,
      Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply, hre, him]
    field_simp
  have hR : |(Complex.digamma w).re - Real.log (a ^ 2 + t ^ 2) / 2 +
      a / (2 * (a ^ 2 + t ^ 2))| ≤ 3 / t ^ 2 := by
    have h := (Complex.abs_re_le_norm _).trans hmain
    simpa only [Complex.add_re, Complex.sub_re, hlogre, hinvre] using h
  have hlog : 0 ≤ Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ∧
      Real.log (a ^ 2 + t ^ 2) / 2 - Real.log t ≤ 9 / (8 * t ^ 2) := by
    have he : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by
      field_simp
      ring
    rw [he, Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have hl0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) :=
      Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    have hl1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 ≤ 9 / 4 := by nlinarith
    have hq : a ^ 2 / t ^ 2 ≤ (9 / 4) / t ^ 2 :=
      div_le_div_of_nonneg_right ha2 (sq_nonneg t)
    ring_nf at hq hl0 hl1 ⊢
    constructor <;> linarith
  have hi : 0 ≤ a / (2 * (a ^ 2 + t ^ 2)) ∧
      a / (2 * (a ^ 2 + t ^ 2)) ≤ 3 / (4 * t ^ 2) := by
    constructor
    · positivity
    · rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 3 / 2 - a) (sq_nonneg t)]
  rw [abs_le] at hR ⊢
  change -(9 / (2 * t ^ 2)) ≤ (Complex.digamma w).re - Real.log t ∧
    (Complex.digamma w).re - Real.log t ≤ 9 / (2 * t ^ 2)
  have ht2 : 0 < t ^ 2 := by positivity
  ring_nf at hR hlog hi ⊢
  constructor <;> nlinarith [hR.1, hR.2, hlog.1, hlog.2, hi.1, hi.2,
    sq_nonneg t⁻¹]

end TernaryGoldbach.RSBounds.BacklundGammaModulus
