import RSBounds.BacklundHalfStrip
import RSBounds.BacklundStripNormalizer
import RSBounds.BacklundBottomFiniteSum
import RSBounds.BacklundFunctionalStrip
import RSBounds.BacklundGammaModulusAbsorption
import TernaryGoldbach.Explicit.ZetaGrowth

/-! # Backlund's explicit bound in the critical strip, equation (56)

This assembles actual right-edge, reflected-edge, finite bottom-edge, and
polynomial-growth estimates with the proved upper half-strip maximum principle.
-/

open Complex Real Set
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundStrip
open BacklundStripNormalizer

private theorem base_ge_one {t : ℝ} (ht : 50 ≤ t) : 1 ≤ t / (2 * Real.pi) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
  linarith [Real.pi_lt_four]

private theorem norm_le_raw {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤
      (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
  rw [norm_normalizedZeta_horizontal (by linarith : 1 < t)]
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  exact mul_le_of_le_one_right (by positivity)
    (correction_le_one hσ0 hσ1 (by linarith))

private theorem norm_le_zeta_div_log {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hP : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one ht) (by linarith)
  exact (norm_le_raw hσ0 hσ1 ht).trans
    (div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hP) hL.le)

private theorem norm_le_reflected {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1 / 2)
    (ht : 50 ≤ t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ Real.exp (5 / (2 * t ^ 2)) *
      ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖ / Real.log t := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hP : (t / (2 * Real.pi)) ^ (-σ / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (base_ge_one ht) (by linarith)
  have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t / (2 * Real.pi)) ^ (1 / 2 - σ) = (t / (2 * Real.pi)) ^ (-σ / 2) := by
    rw [← Real.rpow_add hp]
    congr 1
    ring
  calc
    _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t :=
        norm_le_raw hσ0 (by linarith) ht
    _ ≤ (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ((t / (2 * Real.pi)) ^ (1 / 2 - σ) * Real.exp (5 / (2 * t ^ 2)) *
        ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) / Real.log t := by
      gcongr
      exact BacklundFunctionalMultiplier.norm_zeta_reflected_strip_le (by linarith) hσ1 ht
    _ = (t / (2 * Real.pi)) ^ (-σ / 2) *
      (Real.exp (5 / (2 * t ^ 2)) * ‖riemannZeta (((1 - σ : ℝ) : ℂ) + t * I)‖) /
        Real.log t := by rw [← hab]; ring
    _ ≤ _ := div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity) hP) hL.le

private theorem norm_right_edge {t : ℝ} (ht : 50 ≤ t) :
    ‖normalizedZeta (1 + (t : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
    (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
  have hraw := norm_le_zeta_div_log (σ := 1) (by norm_num) le_rfl ht
  simp only [Complex.ofReal_one] at hraw
  refine hraw.trans ?_
  apply (div_le_one hL).mpr
  simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add] at hz
  linarith

private theorem norm_left_edge {t : ℝ} (ht : 50 ≤ t) :
    ‖normalizedZeta ((t : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hz := BacklundZetaBoundary.zeta_norm_le_log_sub
    (s := 1 + (t : ℂ) * I) (by simp) (by simpa using ht)
  simp only [Complex.add_im, Complex.one_im, Complex.mul_I_im, Complex.ofReal_re,
    zero_add] at hz
  have hraw := norm_le_reflected (σ := 0) le_rfl (by norm_num) ht
  norm_num at hraw
  refine hraw.trans ?_
  apply (div_le_one hL).mpr
  have hb : ‖riemannZeta (1 + (t : ℂ) * I)‖ ≤ Real.log t - 6 / 125 := by
    convert hz using 1 <;> norm_num
  exact (mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le).trans
    (BacklundGammaModulus.exp_mul_log_saving_lt ht).le

private theorem bottom_budget : (3.75 : ℝ) ≤ Real.log 50 - 6 / 125 := by
  have h48 : Real.log (48 : ℝ) = 4 * Real.log 2 + Real.log 3 := by
    rw [show (48 : ℝ) = 2 ^ 4 * 3 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have hle := Real.log_le_log (by norm_num : (0 : ℝ) < 48) (by norm_num : (48 : ℝ) ≤ 50)
  rw [h48] at hle
  linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]

private theorem norm_bottom_edge {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖normalizedZeta ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 1 := by
  have hL : 0 < Real.log (50 : ℝ) := Real.log_pos (by norm_num)
  by_cases hh : 1 / 2 ≤ σ
  · refine (norm_le_zeta_div_log hσ0 hσ1 (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
    apply (div_le_one hL).mpr
    have h := BacklundBottomCertificates.norm_zeta_height_fifty_le hh hσ1
    norm_num at h ⊢
    linarith [bottom_budget]
  · have href := BacklundBottomCertificates.norm_zeta_height_fifty_le
      (σ := 1 - σ) (by linarith) (by linarith)
    refine (norm_le_reflected hσ0 (by linarith) (by norm_num : (50 : ℝ) ≤ 50)).trans ?_
    apply (div_le_one hL).mpr
    have hbound : ‖riemannZeta (((1 - σ : ℝ) : ℂ) + (50 : ℂ) * I)‖ ≤
        Real.log 50 - 6 / 125 := href.trans bottom_budget
    exact (mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le).trans
      (BacklundGammaModulus.exp_mul_log_saving_lt (by norm_num : (50 : ℝ) ≤ 50)).le

/-- A coarse growth estimate reusing calr3's already-proved Abel continuation. -/
private theorem zeta_growth_right {σ t : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤ 5 * t := by
  let s : ℂ := (σ : ℂ) + t * I
  have hs : 0 < s.re := by simp [s]; linarith
  have ht0 : 0 < t := by linarith
  have hp : s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp [s] at hh
    linarith
  have hsn : ‖s‖ ≤ 2 * t := by
    have hh := norm_add_le (σ : ℂ) ((t : ℂ) * I)
    simp only [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at hh
    rw [abs_of_nonneg (by linarith : 0 ≤ σ), abs_of_pos ht0] at hh
    change ‖(σ : ℂ) + t * I‖ ≤ 2 * t
    linarith
  have hdn : t ≤ ‖s - 1‖ := by
    have hh := Complex.abs_im_le_norm (s - 1)
    simpa [s, abs_of_pos ht0] using hh
  have hdpos : 0 < ‖s - 1‖ := ht0.trans_le hdn
  have hh := TernaryGoldbach.Explicit.norm_zetaF_le hs
  rw [TernaryGoldbach.Explicit.zetaF_of_ne hp, norm_mul] at hh
  have hdiv : ‖s‖ * ‖s - 1‖ / s.re ≤ 2 * ‖s‖ * ‖s - 1‖ := by
    apply (div_le_iff₀ hs).mpr
    have hsr : 1 / 2 ≤ s.re := by simpa [s] using hσ0
    have hm := mul_nonneg (mul_nonneg (norm_nonneg s) (norm_nonneg (s - 1)))
      (show 0 ≤ 2 * s.re - 1 by linarith)
    nlinarith
  have hprod : ‖s - 1‖ * ‖riemannZeta s‖ ≤ 2 * t + 4 * t * ‖s - 1‖ := by
    have hm := mul_le_mul_of_nonneg_right hsn (norm_nonneg (s - 1))
    nlinarith
  apply (mul_le_mul_iff_right₀ hdpos).mp
  change ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (5 * t)
  refine hprod.trans ?_
  have hm := mul_nonneg ht0.le (show 0 ≤ ‖s - 1‖ - 2 by linarith)
  nlinarith

private theorem norm_growth {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hL : 1 ≤ Real.log t := one_le_log_of_three_le (by linarith)
  have hL0 : 0 < Real.log t := by linarith
  by_cases hh : 1 / 2 ≤ σ
  · refine (norm_le_zeta_div_log hσ0 hσ1 ht).trans ?_
    have hz := zeta_growth_right hh hσ1 ht
    apply (div_le_iff₀ hL0).mpr
    have hm := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
    nlinarith
  · refine (norm_le_reflected hσ0 (by linarith) ht).trans ?_
    have hz := zeta_growth_right (σ := 1 - σ) (by linarith) (by linarith) ht
    have he : Real.exp (5 / (2 * t ^ 2)) ≤ 3 := by
      apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
      apply (div_le_one (by positivity : (0 : ℝ) < 2 * t ^ 2)).mpr
      nlinarith
    have hm := mul_le_mul he hz (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3)
    apply (div_le_iff₀ hL0).mpr
    have hmul := mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hL)
    nlinarith

/-- The actual analytic normalized zeta is bounded on the entire upper
half-strip. The finite bottom certificate is used here. -/
theorem norm_normalizedZeta_le_one {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ 1 := by
  have hd : DiffContOnCl ℂ normalizedZeta (Ioo (0 : ℝ) 1 ×ℂ Ioi (50 : ℝ)) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    rw [closure_reProdIm, closure_Ioo (by norm_num : (0 : ℝ) ≠ 1), closure_Ioi] at hz
    have hzim : (50 : ℝ) ≤ z.im := hz.2
    exact (analyticAt_normalizedZeta (by linarith)).differentiableAt.differentiableWithinAt
  apply BacklundHalfStrip.norm_le_one (a := 50) (by norm_num) hd
  · intro z hre hzt
    have he : z = (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
    rw [he]
    exact norm_left_edge hzt
  · intro z hre hzt
    have he : z = 1 + (z.im : ℂ) * I := by apply Complex.ext <;> simp [hre]
    rw [he]
    exact norm_right_edge hzt
  · intro z hz0 hz1 hzt
    have he : z = (z.re : ℂ) + (50 : ℂ) * I := by apply Complex.ext <;> simp [hzt]
    rw [he]
    exact norm_bottom_edge hz0 hz1
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz0 hz1 hzt
    simpa only [Complex.re_add_im, one_mul] using norm_growth hz0 hz1 hzt
  · simpa using hσ0
  · simpa using hσ1
  · simpa using ht

/-- Backlund (1918), equation (56), with its original threshold and factor. -/
theorem norm_zeta_strip_le {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 50 ≤ t) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t :=
  zeta_norm_le_of_normalized_le hσ0 hσ1 (by linarith)
    (norm_normalizedZeta_le_one hσ0 hσ1 ht)

end TernaryGoldbach.RSBounds.BacklundStrip
