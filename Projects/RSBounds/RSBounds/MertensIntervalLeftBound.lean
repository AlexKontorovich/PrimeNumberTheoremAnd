import RSBounds.MertensSignedInterval
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# A quantitative bound for the signed-interval left remainder

The actual logarithmic derivative bound on `Re s = -1/2`, together with
the two denominator factors of the interval kernel, gives an explicit
integrable majorant. Its integral is evaluated, not assumed. No RH or
zero-free hypothesis is needed.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.MertensIntervalLeftBound

open TernaryGoldbach.Explicit PolynomialExplicit PolynomialLeftRemainder
  MertensIntervalKernel MertensSignedInterval

/-- The shifted power integral, including its exact endpoint value. -/
theorem integral_Ioi_add_rpow_of_lt {r c m : ℝ} (hr : r < -1) (hc : -m < c) :
    (∫ t : ℝ in Ioi c, (t + m) ^ r) = -(c + m) ^ (r + 1) / (r + 1) := by
  have hd : ∀ x ∈ Ici c,
      HasDerivAt (fun t : ℝ => (t + m) ^ (r + 1) / (r + 1)) ((x + m) ^ r) x := by
    intro x hx
    convert! (((hasDerivAt_id _).add_const _).rpow_const _).div_const _ using 1
    · simp [show r + 1 ≠ 0 by linarith]
    left
    linarith [mem_Ici.mp hx, id_eq x]
  have ht : Tendsto (fun t : ℝ => (t + m) ^ (r + 1) / (r + 1))
      atTop (𝓝 (0 / (r + 1))) := by
    rw [← neg_neg (r + 1)]
    exact ((tendsto_rpow_neg_atTop (by linarith : 0 < -(r + 1))).comp
      (tendsto_atTop_add_const_right _ m tendsto_id)).div_const _
  convert integral_Ioi_of_hasDerivAt_of_tendsto' hd
    (integrableOn_add_rpow_Ioi_of_lt hr hc) ht using 1
  simp only [zero_div, zero_sub, neg_div]

theorem integral_one_add_abs_neg_three_halves :
    (∫ t : ℝ, (1 + |t|) ^ (-3 / 2 : ℝ)) = 4 := by
  rw [integral_comp_abs (f := fun t : ℝ => (1 + t) ^ (-3 / 2 : ℝ))]
  have h := integral_Ioi_add_rpow_of_lt
    (r := (-3 / 2 : ℝ)) (c := 0) (m := 1) (by norm_num) (by norm_num)
  simp_rw [add_comm (1 : ℝ)]
  rw [h]
  norm_num

theorem integrable_one_add_abs_neg_three_halves :
    Integrable (fun t : ℝ => (1 + |t|) ^ (-3 / 2 : ℝ)) := by
  simpa only [Real.norm_eq_abs, neg_div] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3 / 2) (by norm_num))

/-- On the left line both endpoint powers have negative exponent. -/
theorem norm_numerator_left_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖numerator a b (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ) := by
  calc
    _ ≤ ‖(b : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1)‖ +
        ‖(a : ℂ) ^ ((((-1 / 2 : ℝ) : ℂ) + t * I) - 1)‖ := norm_sub_le _ _
    _ = _ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb,
        Complex.norm_cpow_eq_rpow_re_of_pos ha]
      norm_num
      ring

theorem norm_kernel_left_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖kernel a b (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (16 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) / (1 + |t|) ^ 2 := by
  let s : ℂ := ((-1 / 2 : ℝ) : ℂ) + t * I
  have hre : s.re = -1 / 2 := by simp [s]
  have him : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have h0 := congrArg Complex.re h
    rw [hre] at h0
    norm_num at h0
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
  change ‖kernel a b s‖ ≤ _
  rw [kernel_eq hs1, norm_div, norm_mul]
  calc
    ‖numerator a b s‖ / (‖s‖ * ‖s - 1‖) ≤
        (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) / (‖s‖ * ‖s - 1‖) := by
      gcongr
      exact norm_numerator_left_le ha hb t
    _ ≤ (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) /
        (((1 + |t|) / 4) * ((1 + |t|) / 4)) := by gcongr
    _ = _ := by field_simp <;> ring

/-- The envelope used for the actual zeta logarithmic derivative. -/
theorem norm_logDeriv_zeta_left_le_sqrt (t : ℝ) :
    ‖logDeriv riemannZeta (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      500 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hp : 0 < 1 + |t| := by positivity
  have hm : 0 < max 1 |t| := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hlog : Real.log (max 1 |t|) ≤ 2 * (1 + |t|) ^ (1 / 2 : ℝ) := by
    have h1 := Real.log_le_log hm (show max 1 |t| ≤ 1 + |t| by
      exact max_le (by linarith [abs_nonneg t]) (by linarith))
    have h2 := Real.log_le_rpow_div hp.le (by norm_num : (0 : ℝ) < 1 / 2)
    linarith
  have hpow : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg t]) (by norm_num)
  have h := norm_logDeriv_zeta_left_log t
  linarith

/-- A completely explicit integrable majorant for the actual left integrand. -/
theorem norm_left_integrand_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    ‖contourIntegrand riemannZeta (kernel a b) 1
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      (8000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) *
        (1 + |t|) ^ (-3 / 2 : ℝ) := by
  have hp : 0 < 1 + |t| := by positivity
  rw [contourIntegrand, Complex.ofReal_one, Complex.one_cpow, mul_one, norm_mul]
  calc
    _ ≤ (500 * (1 + |t|) ^ (1 / 2 : ℝ)) *
        ((16 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) / (1 + |t|) ^ 2) := by
      exact mul_le_mul (norm_logDeriv_zeta_left_le_sqrt t) (norm_kernel_left_le ha hb t)
        (norm_nonneg _) (by positivity)
    _ = (8000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) *
        ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (2 : ℝ)) := by
      rw [Real.rpow_two]
      ring
    _ = _ := by rw [← Real.rpow_sub hp]; norm_num

/-- Explicit finite-interval left-remainder estimate, with no RH premise. -/
theorem norm_leftRemainder_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ‖leftRemainder a b‖ ≤ 6000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) := by
  have hA : 0 ≤ a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ) := by positivity
  have hnormInt : ‖∫ t : ℝ, contourIntegrand riemannZeta (kernel a b) 1
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      32000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) := by
    calc
      _ ≤ ∫ t : ℝ, ‖contourIntegrand riemannZeta (kernel a b) 1
          (((-1 / 2 : ℝ) : ℂ) + t * I)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, (8000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) *
          (1 + |t|) ^ (-3 / 2 : ℝ) :=
        integral_mono (integrable_leftRemainder ha hb).norm
          (integrable_one_add_abs_neg_three_halves.const_mul _)
          (norm_left_integrand_le ha hb)
      _ = _ := by rw [integral_const_mul, integral_one_add_abs_neg_three_halves]; ring
  rw [leftRemainder, norm_mul]
  have hc : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Real.pi_pos.le]
  rw [hc]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (32000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ))) := by gcongr
    _ ≤ 6000 * (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) := by
      have hπ : 3 < Real.pi := Real.pi_gt_three
      have hcoeff : (1 / (2 * Real.pi)) * 32000 ≤ 6000 := by
        rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
        linarith
      calc
        _ = ((1 / (2 * Real.pi)) * 32000) *
          (a ^ (-3 / 2 : ℝ) + b ^ (-3 / 2 : ℝ)) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hcoeff hA

end TernaryGoldbach.RSBounds.MertensIntervalLeftBound
