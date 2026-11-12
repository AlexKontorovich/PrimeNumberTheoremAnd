import RSBounds.BacklundCircleMajorantGeometry
import RSBounds.BacklundStrip

open Complex Real Set

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

/-- The piecewise majorant bounds the actual zeta function at every ordinate
in the vertical range swept out by the circle. -/
theorem zeta_norm_le_exp_scalar {T σ t : ℝ} (hT : 100 ≤ T)
    (hσ : -(1 / 2 : ℝ) ≤ σ) (ht0 : T - radius ≤ t) (ht1 : t ≤ T + radius) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      Real.exp (scalar (heightLog T) (powerLog T) (stripLog T) σ) := by
  have ht50 := height_bounds hT ht0
  have htpos : 0 < t := by linarith
  by_cases hright : 5 / 4 ≤ σ
  · rw [scalar_right hright, Real.exp_log]
    · simpa using BacklundZetaBoundary.zeta_norm_le_real_axis
        (s := (σ : ℂ) + t * I) (by simp; linarith)
    · apply norm_pos_iff.mpr
      exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hright' : σ < 5 / 4 := lt_of_not_ge hright
  by_cases hone : 1 ≤ σ
  · rw [scalar_one hone hright', exp_heightLog hT]
    have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
      (s := (σ : ℂ) + t * I) (by simpa using hone) (by simpa using ht50)
    have hl := Real.log_le_log htpos ht1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul,
      zero_add, add_zero] at hz
    linarith
  have hone' : σ < 1 := lt_of_not_ge hone
  by_cases hzero : 0 ≤ σ
  · rw [scalar_middle hzero hone', exp_height_power_strip hT]
    have hz := BacklundStrip.norm_zeta_strip_le hzero hone'.le ht50
    have hratio := strip_ratio_antitone hT ht0
    have hpower := power_log_mono hT ht0 ht1 (show 0 ≤ (1 - σ) / 2 by linarith)
    have hp0 : 0 ≤ (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
      exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.log_nonneg (by linarith))
    have hc0 : 0 ≤ (T - radius) ^ 2 / ((T - radius) ^ 2 - 4) := by
      exact div_nonneg (sq_nonneg _) (strip_den_pos hT).le
    have hm := mul_le_mul hratio hpower hp0 hc0
    have he : t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t =
        (t ^ 2 / (t ^ 2 - 4)) * ((t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) := by ring
    rw [he] at hz
    exact hz.trans (by convert hm using 1; ring)
  have hzero' : σ < 0 := lt_of_not_ge hzero
  rw [scalar_left hzero', exp_height_power hT]
  have hz := BacklundLeftZetaBoundary.norm_zeta_left_strip_lt hσ hzero'.le ht50
  have hm := power_log_mono hT ht0 ht1 (show 0 ≤ 1 / 2 - σ by linarith)
  exact hz.le.trans (by simpa only [mul_comm] using hm)

theorem zeta_plus_le_exp_majorant {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    ‖riemannZeta (z + T * I)‖ ≤ Real.exp (majorant T z) := by
  have hheights := (sphere_heights (T := T) hz).1
  have hh := zeta_norm_le_exp_scalar hT (sphere_coordinates hz).1 hheights.1 hheights.2
  have he : z + T * I = (z.re : ℂ) + ((T + z.im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [add_comm]
  simpa only [majorant, he] using hh

theorem zeta_minus_le_exp_majorant {T : ℝ} (hT : 100 ≤ T) {z : ℂ}
    (hz : z ∈ Metric.sphere (5 / 4 : ℂ) radius) :
    ‖riemannZeta (z - T * I)‖ ≤ Real.exp (majorant T z) := by
  have hheights := (sphere_heights (T := T) hz).2
  have hh := zeta_norm_le_exp_scalar hT (sphere_coordinates hz).1 hheights.1 hheights.2
  have he : z - T * I = (starRingEnd ℂ)
      ((z.re : ℂ) + ((T - z.im : ℝ) : ℂ) * I) := by
    apply Complex.ext <;> simp
  rw [he, riemannZeta_conj, norm_conj]
  exact hh

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
