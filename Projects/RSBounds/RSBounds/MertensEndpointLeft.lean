import RSBounds.MertensIntervalLeftBound

/-!
# Endpoint form of the signed-integral left remainder

The finite remainder is the difference of two convergent endpoint
integrals. Each endpoint integral is bounded by an explicit multiple of
`c^(-3/2)`, and therefore vanishes at infinity. No RH is used.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.MertensEndpointLeft

open TernaryGoldbach.Explicit PolynomialExplicit MertensIntervalKernel
  MertensSignedInterval MertensIntervalLeftBound

noncomputable def endpointKernel (c : ℝ) (s : ℂ) : ℂ :=
  (c : ℂ) ^ (s - 1) / (s * (s - 1))

noncomputable def endpointIntegrand (c t : ℝ) : ℂ :=
  contourIntegrand riemannZeta (endpointKernel c) 1
    (((-1 / 2 : ℝ) : ℂ) + t * I)

/-- The actual endpoint left vertical integral. -/
noncomputable def F (c : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t : ℝ, endpointIntegrand c t

theorem norm_endpointKernel_left_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖endpointKernel c (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (16 * c ^ (-3 / 2 : ℝ)) / (1 + |t|) ^ 2 := by
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  have hre : s.re = -1 / 2 := by simp [s]
  have him : s.im = t := by simp [s]
  have hnorm : (1 + |t|) / 4 ≤ ‖s‖ := by
    have hr := Complex.abs_re_le_norm s
    have hi := Complex.abs_im_le_norm s
    rw [hre] at hr
    rw [him] at hi
    norm_num at hr
    linarith
  have hnorm1 : (1 + |t|) / 4 ≤ ‖s - 1‖ := by
    have hr := Complex.abs_re_le_norm (s - 1)
    have hi := Complex.abs_im_le_norm (s - 1)
    simp only [sub_re, one_re, hre] at hr
    simp only [sub_im, one_im, sub_zero, him] at hi
    norm_num at hr
    linarith
  have ht : 0 < (1 + |t|) / 4 := by positivity
  change ‖endpointKernel c s‖ ≤ _
  rw [endpointKernel, norm_div, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc]
  have he : (s - 1).re = -3 / 2 := by simp only [sub_re, hre, one_re]; norm_num
  rw [he]
  calc
    c ^ (-3 / 2 : ℝ) / (‖s‖ * ‖s - 1‖) ≤
        c ^ (-3 / 2 : ℝ) / (((1 + |t|) / 4) * ((1 + |t|) / 4)) := by gcongr
    _ = _ := by field_simp <;> ring

theorem norm_endpointIntegrand_le {c : ℝ} (hc : 0 < c) (t : ℝ) :
    ‖endpointIntegrand c t‖ ≤
      (8000 * c ^ (-3 / 2 : ℝ)) * (1 + |t|) ^ (-3 / 2 : ℝ) := by
  have hp : 0 < 1 + |t| := by positivity
  rw [endpointIntegrand, contourIntegrand, Complex.ofReal_one, Complex.one_cpow,
    mul_one, norm_mul]
  calc
    _ ≤ (500 * (1 + |t|) ^ (1 / 2 : ℝ)) *
        ((16 * c ^ (-3 / 2 : ℝ)) / (1 + |t|) ^ 2) := by
      exact mul_le_mul (norm_logDeriv_zeta_left_le_sqrt t)
        (norm_endpointKernel_left_le hc t) (norm_nonneg _) (by positivity)
    _ = (8000 * c ^ (-3 / 2 : ℝ)) *
        ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ = _ := by rw [← Real.rpow_sub hp]; norm_num

theorem continuous_endpointIntegrand {c : ℝ} (hc : 0 < c) :
    Continuous (endpointIntegrand c) := by
  have hs0 (t : ℝ) : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 (t : ℝ) : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hz (t : ℝ) : riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I) ≠ 0 :=
    zeta_ne_zero_of_zetaF (hs1 t)
      (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have hld : Continuous (fun t : ℝ =>
      logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    have hf := continuous_logDeriv_lineD ldatum_zeta2 (-1 / 2) (fun t =>
      ldatum_zeta2.nz_strip _ (by simp; norm_num) (by simp; norm_num))
    have hp := continuous_logDeriv_lineD ldatum_sub_one (-1 / 2) (fun t =>
      ldatum_sub_one.nz_strip _ (by simp; norm_num) (by simp; norm_num))
    convert hf.sub hp using 1
    ext t
    rw [Pi.sub_apply, logDeriv_zetaF_eq (hs1 t) (hz t), logDeriv_sub_one]
    ring
  have hn : Continuous (fun t : ℝ =>
      (c : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1)) := by
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hc.ne')).comp (by fun_prop)
  have hd : Continuous (fun t : ℝ =>
      endpointKernel c (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    exact hn.div (by fun_prop) (fun t => mul_ne_zero (hs0 t) (sub_ne_zero.mpr (hs1 t)))
  have heq : endpointIntegrand c = fun t : ℝ =>
      logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I) *
        endpointKernel c (((-1 / 2 : ℝ) : ℂ) + t * I) := by
    funext t
    simp only [endpointIntegrand, contourIntegrand, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
  rw [heq]
  exact hld.mul hd

theorem integrable_endpointIntegrand {c : ℝ} (hc : 0 < c) :
    Integrable (endpointIntegrand c) :=
  (integrable_one_add_abs_neg_three_halves.const_mul (8000 * c ^ (-3 / 2 : ℝ))).mono'
    (continuous_endpointIntegrand hc).aestronglyMeasurable
    (Eventually.of_forall (norm_endpointIntegrand_le hc))

theorem norm_F_le {c : ℝ} (hc : 0 < c) :
    ‖F c‖ ≤ 6000 * c ^ (-3 / 2 : ℝ) := by
  have hpow : 0 ≤ c ^ (-3 / 2 : ℝ) := by positivity
  have hint : ‖∫ t : ℝ, endpointIntegrand c t‖ ≤ 32000 * c ^ (-3 / 2 : ℝ) := by
    calc
      _ ≤ ∫ t : ℝ, ‖endpointIntegrand c t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (8000 * c ^ (-3 / 2 : ℝ)) * (1 + |t|) ^ (-3 / 2 : ℝ) :=
        integral_mono (integrable_endpointIntegrand hc).norm
          (integrable_one_add_abs_neg_three_halves.const_mul _)
          (norm_endpointIntegrand_le hc)
      _ = _ := by rw [integral_const_mul, integral_one_add_abs_neg_three_halves]; ring
  rw [F, norm_mul]
  have hconst : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Real.pi_pos.le]
  rw [hconst]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (32000 * c ^ (-3 / 2 : ℝ)) := by gcongr
    _ ≤ 6000 * c ^ (-3 / 2 : ℝ) := by
      have hπ : 3 < Real.pi := Real.pi_gt_three
      have hcoeff : (1 / (2 * Real.pi)) * 32000 ≤ 6000 := by
        rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith
      calc
        _ = ((1 / (2 * Real.pi)) * 32000) * c ^ (-3 / 2 : ℝ) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hpow

theorem leftRemainder_eq_sub_F {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    leftRemainder a b = F b - F a := by
  rw [leftRemainder, F, F, ← mul_sub, ← integral_sub
    (integrable_endpointIntegrand hb) (integrable_endpointIntegrand ha)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have hs1 : ((-1 / 2 : ℝ) : ℂ) + t * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  simp only [endpointIntegrand, contourIntegrand, Complex.ofReal_one,
    Complex.one_cpow, mul_one, kernel_eq hs1, numerator, endpointKernel]
  ring

/-- Explicit error in the endpoint limit, before taking any filter limit. -/
theorem norm_leftRemainder_add_F_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖leftRemainder a b + F a‖ ≤ 6000 * b ^ (-3 / 2 : ℝ) := by
  rw [leftRemainder_eq_sub_F ha hb, sub_add_cancel]
  exact norm_F_le hb

theorem leftRemainder_add {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    leftRemainder a b + leftRemainder b c = leftRemainder a c := by
  rw [leftRemainder_eq_sub_F ha hb, leftRemainder_eq_sub_F hb hc,
    leftRemainder_eq_sub_F ha hc]
  ring

theorem tendsto_F_atTop : Tendsto F atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun c : ℝ => 6000 * c ^ (-3 / 2 : ℝ))
    (Eventually.of_forall fun _ => norm_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact norm_F_le hc
  · have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 2)).const_mul 6000
    simpa only [neg_div, mul_zero] using h

theorem tendsto_leftRemainder_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (leftRemainder a) atTop (𝓝 (-F a)) := by
  have h : Tendsto (fun b : ℝ => F b - F a) atTop (𝓝 (-F a)) := by
    simpa only [zero_sub] using tendsto_F_atTop.sub_const (F a)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  exact (leftRemainder_eq_sub_F ha hb).symm

end TernaryGoldbach.RSBounds.MertensEndpointLeft
