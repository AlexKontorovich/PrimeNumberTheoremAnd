import RSBounds.PolynomialRemainderIntegral
import RSBounds.PolynomialLeftKernel
import RSBounds.PolynomialRemainderMajorant

/-!
# A numerical bound for the actual averaged left remainder

The historical step `delta = 0.0000211` is retained. The theorem bounds
the remainder for both additive smoothing directions, not merely the
integrand. No RH or zero-count estimate is assumed.
-/

open Complex Set MeasureTheory
open scoped Real

namespace TernaryGoldbach.RSBounds.PolynomialRemainderBound

open TernaryGoldbach.Explicit PolynomialAveraged PolynomialLeftRemainder
open PolynomialRemainderIntegral PolynomialLeftKernel PolynomialRemainderMajorant

theorem norm_averagedIntegrand_le_majorant {x y : ℝ} (hx : 0 < x)
    (hy0 : 1 - 4 * (0.0000211 : ℝ) ≤ y) (hy1 : y ≤ 1) (t : ℝ) :
    ‖logDeriv riemannZeta (leftLine t) *
        zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * majorant t := by
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hlo := norm_zeroCoefficient_left_low hx
    (by norm_num : (0 : ℝ) < 0.0000211) (by norm_num : (0.0000211 : ℝ) ≤ 0.01)
    hy0 hy1 (leftLine_re t)
  have hld := norm_logDeriv_zeta_left_log t
  change ‖logDeriv riemannZeta (leftLine t)‖ ≤
    340 + 80 * Real.log (max 1 |t|) at hld
  have hn0 : 0 < ‖leftLine t‖ := by
    have hh := Complex.abs_re_le_norm (leftLine t)
    rw [leftLine_re] at hh
    norm_num at hh
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ ‖leftLine t‖ := by
    have hh := Complex.abs_re_le_norm (leftLine t)
    rw [leftLine_re] at hh
    norm_num at hh
    exact hh
  have htNorm : |t| ≤ ‖leftLine t‖ := by
    simpa [leftLine] using Complex.abs_im_le_norm (leftLine t)
  rw [norm_mul]
  by_cases ht1 : |t| ≤ 1
  · have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 := by
      simpa only [max_eq_left ht1, Real.log_one, mul_zero, add_zero] using hld
    have hk : ‖zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ ≤
        x ^ (-1 / 2 : ℝ) * 2.2 := by
      refine hlo.trans (mul_le_mul_of_nonneg_left ?_ hxp)
      rw [div_le_iff₀ hn0]
      nlinarith
    have he : majorant t = 748 := by simp [majorant, positiveMajorant, ht1]
    rw [he]
    calc
      _ ≤ 340 * (x ^ (-1 / 2 : ℝ) * 2.2) :=
        mul_le_mul hd hk (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  · have htpos : 0 < |t| := by linarith
    have htgt : 1 < |t| := lt_of_not_ge ht1
    rw [max_eq_right htgt.le] at hld
    by_cases htD : |t| ≤ cutoff
    · have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 1300 := by
        have hl := (Real.log_le_log htpos htD).trans log_cutoff_le
        linarith
      have hk : ‖zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ ≤
          x ^ (-1 / 2 : ℝ) * (1.1 / |t|) := by
        exact hlo.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) htpos htNorm) hxp)
      have he : majorant t = 1430 / |t| := by
        simp [majorant, positiveMajorant, ht1, htD]
      rw [he]
      calc
        _ ≤ 1300 * (x ^ (-1 / 2 : ℝ) * (1.1 / |t|)) :=
          mul_le_mul hd hk (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · have hD : (0 : ℝ) < cutoff := by norm_num [cutoff]
      have hratio : 0 < |t| / cutoff := div_pos htpos hD
      have hl : Real.log |t| ≤ 12 + |t| / cutoff := by
        have he := Real.log_div htpos.ne' hD.ne'
        have hh := Real.log_le_sub_one_of_pos hratio
        linarith [log_cutoff_le]
      have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 1300 + 80 * |t| / cutoff := by
        calc
          _ ≤ 340 + 80 * (12 + |t| / cutoff) := by linarith
          _ = _ := by ring
      have htim : (leftLine t).im ≠ 0 := by
        simpa [leftLine] using (abs_pos.mp htpos)
      have hi := norm_zeroCoefficient_left_high hx
        (by norm_num : (0 : ℝ) < 0.0000211) (by norm_num : (0.0000211 : ℝ) ≤ 0.01)
        hy0 hy1 (leftLine_re t) htim
      have hi' : ‖zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ ≤
          x ^ (-1 / 2 : ℝ) * (19 * cutoff ^ 4 / |t| ^ 5) := by
        have hc : (1 : ℝ) / (0.0000211 : ℝ) ^ 4 ≤ cutoff ^ 4 := by norm_num [cutoff]
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ hxp)
        simp only [leftLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, zero_mul,
          add_zero, zero_add]
        calc
          19 / ((0.0000211 : ℝ) ^ 4 * |t| ^ 5) =
              19 * (1 / (0.0000211 : ℝ) ^ 4) / |t| ^ 5 := by ring
          _ ≤ 19 * cutoff ^ 4 / |t| ^ 5 := by gcongr
      have he : majorant t =
          19 * cutoff ^ 4 * (1300 + 80 * |t| / cutoff) / |t| ^ 5 := by
        simp [majorant, positiveMajorant, tail, ht1, htD]
      rw [he]
      calc
        _ ≤ (1300 + 80 * |t| / cutoff) *
            (x ^ (-1 / 2 : ℝ) * (19 * cutoff ^ 4 / |t| ^ 5)) :=
          mul_le_mul hd hi' (norm_nonneg _) (by positivity)
        _ = _ := by ring

theorem norm_leftRemainder_le {x y : ℝ} (hx : 0 < x)
    (hy0 : 1 - 4 * (0.0000211 : ℝ) ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (0.0000211 * x)‖ ≤
      25000 / (Real.pi * x ^ (1 / 2 : ℝ)) := by
  have hy : 0 < y := by linarith
  have hh : 0 < (0.0000211 : ℝ) * x := mul_pos (by norm_num) hx
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hi := integrable_averagedIntegrand (mul_pos hx hy) hh
  have hmaj := integrable_majorant.const_mul (x ^ (-1 / 2 : ℝ))
  have hnorm : ‖∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
      zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * 50000 := by
    calc
      _ ≤ ∫ t : ℝ, ‖logDeriv riemannZeta (leftLine t) *
          zeroCoefficient (x * y) (0.0000211 * x) (leftLine t)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, x ^ (-1 / 2 : ℝ) * majorant t :=
        integral_mono hi.norm hmaj (norm_averagedIntegrand_le_majorant hx hy0 hy1)
      _ = x ^ (-1 / 2 : ℝ) * ∫ t : ℝ, majorant t := integral_const_mul _ _
      _ ≤ x ^ (-1 / 2 : ℝ) * 50000 := mul_le_mul_of_nonneg_left integral_majorant_le hxp
  rw [leftRemainder_eq_integral (mul_pos hx hy) hh, norm_mul]
  have hfac : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-1 / 2 : ℝ) * 50000) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 25000 / (Real.pi * x ^ (1 / 2 : ℝ)) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le]
      ring

theorem norm_leftRemainder_lt {x y : ℝ} (hx : Real.exp 23 ≤ x)
    (hy0 : 1 - 4 * (0.0000211 : ℝ) ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (0.0000211 * x)‖ < 0.1 := by
  have hx0 := (Real.exp_pos 23).trans_le hx
  exact (norm_leftRemainder_le hx0 hy0 hy1).trans_lt (scaled_majorant_lt hx)

theorem norm_upper_leftRemainder_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    ‖leftRemainder x (0.0000211 * x)‖ < 0.1 := by
  simpa only [mul_one] using norm_leftRemainder_lt (y := 1) hx (by norm_num) le_rfl

theorem norm_lower_leftRemainder_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    ‖leftRemainder (x - 4 * (0.0000211 * x)) (0.0000211 * x)‖ < 0.1 := by
  rw [show x - 4 * (0.0000211 * x) = x * (1 - 4 * (0.0000211 : ℝ)) by ring]
  exact norm_leftRemainder_lt hx le_rfl (by norm_num)

end TernaryGoldbach.RSBounds.PolynomialRemainderBound
