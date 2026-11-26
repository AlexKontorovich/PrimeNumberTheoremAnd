import RSBounds.PolynomialKernelScaling
import RSBounds.PolynomialLowerKernel

/-! Common kernel bounds on Re(s) = -1/2, for both additive smoothings. -/

open Complex Set

namespace TernaryGoldbach.RSBounds.PolynomialLeftKernel

open PolynomialZeroKernel PolynomialLowerKernel PolynomialAveraged PolynomialKernelScaling

theorem norm_difference_left_low {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) {ρ : ℂ} (hρ : ρ.re = -1 / 2) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) y / (δ : ℂ) ^ 4‖ ≤ 1.1 / ‖ρ‖ := by
  have hy : 0 < y := by linarith
  have hy24 : (24 / 25 : ℝ) ≤ y := by linarith
  have hn : ρ ≠ 0 := by intro h; rw [h] at hρ; norm_num at hρ
  have hp : y ^ ρ.re ≤ (25 / 24 : ℝ) := by
    rw [hρ]
    have hh := Real.rpow_le_rpow_of_exponent_ge hy hy1 (by norm_num : (-1 : ℝ) ≤ -1 / 2)
    rw [Real.rpow_neg_one] at hh
    refine hh.trans ?_
    rw [inv_eq_one_div, div_le_iff₀ hy]
    nlinarith
  have hf : 1 + 2 * δ / y ≤ (49 / 48 : ℝ) := by
    have hh : 2 * δ / y ≤ (1 / 48 : ℝ) := by
      rw [div_le_iff₀ hy]
      nlinarith
    linarith
  have hm := norm_normalized_fourth_difference_le_low_of_neg_one_lt
    (by rw [hρ]; norm_num) hn (by rw [hρ]; norm_num) hy hδ
  refine hm.trans ?_
  calc
    (y ^ ρ.re / ‖ρ‖) * (1 + 2 * δ / y) ≤
        ((25 / 24 : ℝ) / ‖ρ‖) * (49 / 48) := by
      apply mul_le_mul
      · exact div_le_div_of_nonneg_right hp (norm_nonneg _)
      · exact hf
      · positivity
      · positivity
    _ = ((25 / 24 : ℝ) * (49 / 48)) / ‖ρ‖ := by ring
    _ ≤ 1.1 / ‖ρ‖ := div_le_div_of_nonneg_right (by norm_num) (norm_nonneg _)

theorem norm_difference_left_high {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) {ρ : ℂ} (hρ : ρ.re = -1 / 2) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) y / (δ : ℂ) ^ 4‖ ≤
      19 / (δ ^ 4 * ‖rising ρ 4‖) := by
  have hy : 0 < y := by linarith
  have hm := norm_forwardDiff_le_const_on hδ.le (antiderivative ρ 4)
    (((26 / 25 : ℝ) ^ 4) / ‖rising ρ 4‖) 4 y (by
      intro t ht
      have ht0 : 0 < t := hy.trans_le ht.1
      have ht26 : t ≤ (26 / 25 : ℝ) := by norm_num at ht; linarith [ht.2]
      rw [antiderivative, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      have hre : (ρ + (4 : ℕ)).re = (7 / 2 : ℝ) := by simp [hρ]; norm_num
      rw [hre]
      rcases le_or_gt t 1 with ht1 | ht1
      · exact (Real.rpow_le_one ht0.le ht1 (by norm_num : (0 : ℝ) ≤ 7 / 2)).trans
          (by norm_num)
      · calc
          t ^ (7 / 2 : ℝ) ≤ t ^ (4 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num)
          _ = t ^ (4 : ℕ) := by rw [Real.rpow_ofNat]
          _ ≤ (26 / 25 : ℝ) ^ (4 : ℕ) := pow_le_pow_left₀ ht0.le ht26 4)
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc
    ‖forwardDiff δ 4 (antiderivative ρ 4) y‖ / δ ^ 4 ≤
        (2 ^ 4 * (((26 / 25 : ℝ) ^ 4) / ‖rising ρ 4‖)) / δ ^ 4 := by gcongr
    _ = (16 * (26 / 25 : ℝ) ^ 4) / (δ ^ 4 * ‖rising ρ 4‖) := by ring
    _ ≤ 19 / (δ ^ 4 * ‖rising ρ 4‖) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)

theorem abs_im_pow_le_norm_rising_four (ρ : ℂ) :
    |ρ.im| ^ 5 ≤ ‖rising ρ 4‖ := by
  have hn (n : ℕ) : |ρ.im| ≤ ‖ρ + n‖ := by
    simpa only [Complex.add_im, Complex.natCast_im, add_zero] using
      Complex.abs_im_le_norm (ρ + n)
  have h0 : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  norm_num [rising, norm_mul]
  calc
    |ρ.im| ^ 5 = |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| * |ρ.im| := by ring
    _ ≤ ‖ρ‖ * ‖ρ + 1‖ * ‖ρ + 2‖ * ‖ρ + 3‖ * ‖ρ + 4‖ := by
      gcongr
      · simpa using hn 1
      · simpa using hn 2
      · simpa using hn 3
      · simpa using hn 4

theorem norm_difference_left_high_im {δ y : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) {ρ : ℂ}
    (hρ : ρ.re = -1 / 2) (him : ρ.im ≠ 0) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) y / (δ : ℂ) ^ 4‖ ≤
      19 / (δ ^ 4 * |ρ.im| ^ 5) := by
  apply (norm_difference_left_high hδ hδ1 hy0 hy1 hρ).trans
  exact div_le_div_of_nonneg_left (by norm_num)
    (mul_pos (pow_pos hδ 4) (pow_pos (abs_pos.mpr him) 5))
    (mul_le_mul_of_nonneg_left (abs_im_pow_le_norm_rising_four ρ) (by positivity))

theorem norm_zeroCoefficient_left_low {x δ y : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) {ρ : ℂ} (hρ : ρ.re = -1 / 2) :
    ‖zeroCoefficient (x * y) (δ * x) ρ‖ ≤ x ^ (-1 / 2 : ℝ) * (1.1 / ‖ρ‖) := by
  rw [norm_zeroCoefficient_dilate hx (by linarith) hδ, hρ]
  exact mul_le_mul_of_nonneg_left (norm_difference_left_low hδ hδ1 hy0 hy1 hρ)
    (Real.rpow_nonneg hx.le _)

theorem norm_zeroCoefficient_left_high {x δ y : ℝ}
    (hx : 0 < x) (hδ : 0 < δ) (hδ1 : δ ≤ 0.01)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) {ρ : ℂ}
    (hρ : ρ.re = -1 / 2) (him : ρ.im ≠ 0) :
    ‖zeroCoefficient (x * y) (δ * x) ρ‖ ≤
      x ^ (-1 / 2 : ℝ) * (19 / (δ ^ 4 * |ρ.im| ^ 5)) := by
  rw [norm_zeroCoefficient_dilate hx (by linarith) hδ, hρ]
  exact mul_le_mul_of_nonneg_left (norm_difference_left_high_im hδ hδ1 hy0 hy1 hρ him)
    (Real.rpow_nonneg hx.le _)

end TernaryGoldbach.RSBounds.PolynomialLeftKernel
