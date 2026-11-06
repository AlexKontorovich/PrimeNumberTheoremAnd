import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Tactic

/-!
# An elementary normalization for Backlund's critical-strip estimate

The multiplier uses the principal logarithm in the right half-plane. It
replaces the completed-zeta square-root-sine normalization in Backlund (1918),
pp. 363–368, with an elementary analytic factor having an `O(t⁻²)` modulus
correction. The target loss remains `t²/(t²−4)` at the original threshold 50.
-/

open Complex Real MeasureTheory Set
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundStripNormalizer

noncomputable def exponent (s : ℂ) : ℂ :=
  (s - 1) / 2 * Complex.log (-s * I / (2 * Real.pi)) - s / 2

noncomputable def normalizedZeta (s : ℂ) : ℂ :=
  riemannZeta s * Complex.exp (exponent s) / Complex.log (-s * I)

/-- On the right half-plane, the argument is the real inverse tangent. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    z.arg = Real.arctan (z.im / z.re) := by
  rw [← Complex.tan_arg]
  exact (Real.arctan_tan
    (Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz))
    (Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz))).symm

/-- Cubic lower approximation to inverse tangent; the bound is global on
nonnegative arguments. -/
theorem arctan_cubic_lower {x : ℝ} (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x := by
  have hf : Continuous (fun u : ℝ => 1 - u ^ 2) := by fun_prop
  have hg : Continuous (fun u : ℝ => 1 / (1 + u ^ 2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro u
    positivity
  have hi := intervalIntegral.integral_mono_on (μ := volume) hx
    (hf.intervalIntegrable 0 x) (hg.intervalIntegrable 0 x)
    (fun u _ => by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + u ^ 2)).mpr
      nlinarith [sq_nonneg (u ^ 2)])
  rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
    ((show Continuous (fun u : ℝ => u ^ 2) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_const, integral_pow, integral_one_div_one_add_sq] at hi
  norm_num at hi ⊢
  exact hi

/-- The logarithm of the elementary multiplier's modulus, after removing
`(t/(2π))^((σ−1)/2)`. -/
noncomputable def correctionExponent (σ t : ℝ) : ℝ :=
  (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) +
    t / 2 * Real.arctan (σ / t) - σ / 2

/-- The correction exponent is nonpositive throughout the critical strip. -/
theorem correctionExponent_nonpos {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 < t) : correctionExponent σ t ≤ 0 := by
  have hlog : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  have ha := Real.arctan_le_self (div_nonneg hσ0 ht.le)
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
  have he : t / 2 * (σ / t) = σ / 2 := by field_simp
  rw [he] at hm
  unfold correctionExponent
  have hn : (σ - 1) / 4 * Real.log (1 + (σ / t) ^ 2) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
  linarith

/-- A deliberately generous quadratic lower error, enough for the historical
`4/t²` loss. -/
theorem correctionExponent_lower {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 0 < t) : -(1 / t ^ 2) ≤ correctionExponent σ t := by
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  have hu : 0 ≤ σ / t := div_nonneg hσ0 ht.le
  have hl : Real.log (1 + (σ / t) ^ 2) ≤ (σ / t) ^ 2 := by
    simpa using Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
  have ha := arctan_cubic_lower hu
  have hm := mul_le_mul_of_nonneg_left ha (show 0 ≤ t / 2 by positivity)
  have hml := mul_le_mul_of_nonpos_left hl (show (σ - 1) / 4 ≤ 0 by linarith)
  have hs2 : σ ^ 2 ≤ 1 := pow_le_one₀ hσ0 hσ1
  have hs3 : σ ^ 3 ≤ 1 := pow_le_one₀ hσ0 hσ1
  have he : (σ - 1) / 4 * (σ / t) ^ 2 +
      t / 2 * (σ / t - (σ / t) ^ 3 / 3) - σ / 2 =
      (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 := by
    field_simp
    ring
  have hlo : (σ ^ 3 / 12 - σ ^ 2 / 4) / t ^ 2 ≤ correctionExponent σ t := by
    rw [← he]
    unfold correctionExponent
    linarith
  refine le_trans ?_ hlo
  rw [← neg_div, div_le_div_iff_of_pos_right ht2]
  nlinarith [pow_nonneg hσ0 3]

/-- Modulus of `log(t−iσ)`, expressed in real elementary functions. -/
noncomputable def logModulus (σ t : ℝ) : ℝ :=
  Real.sqrt ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 +
    (Real.arctan (σ / t)) ^ 2)

noncomputable def correction (σ t : ℝ) : ℝ :=
  Real.exp (correctionExponent σ t) * Real.log t / logModulus σ t

/-- The complex logarithm's modulus is at least the real logarithm. -/
theorem log_le_logModulus {σ t : ℝ} (ht : 1 ≤ t) :
    Real.log t ≤ logModulus σ t := by
  have ht0 : 0 < t := by linarith
  have hL : 0 ≤ Real.log t := Real.log_nonneg ht
  have hl : 0 ≤ Real.log (1 + (σ / t) ^ 2) := Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  unfold logModulus
  apply (Real.le_sqrt (by positivity) (by positivity)).mpr
  nlinarith [sq_nonneg (Real.arctan (σ / t))]

/-- On the critical strip the elementary correction can only decrease the
normalized zeta modulus. -/
theorem correction_le_one {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 1 < t) : correction σ t ≤ 1 := by
  have hL : 0 < Real.log t := Real.log_pos ht
  have hD := log_le_logModulus (σ := σ) ht.le
  have he : Real.exp (correctionExponent σ t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (correctionExponent_nonpos hσ0 hσ1 (by linarith))
  unfold correction
  apply (div_le_one (hL.trans_le hD)).mpr
  exact (mul_le_of_le_one_left hL.le he).trans hD

theorem one_le_log_of_three_le {t : ℝ} (ht : 3 ≤ t) : 1 ≤ Real.log t := by
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht
  linarith [Real.log_three_gt_d9]

/-- The logarithm denominator loses at most `1/t²` relative to `log t`. -/
theorem logModulus_upper {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) : logModulus σ t ≤ Real.log t + 1 / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hL := one_le_log_of_three_le ht
  have hd : 0 ≤ 1 / t ^ 2 := by positivity
  have hu2 : (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right (pow_le_one₀ hσ0 hσ1) (sq_nonneg t)
  have hl0 : 0 ≤ Real.log (1 + (σ / t) ^ 2) :=
    Real.log_nonneg (by nlinarith [sq_nonneg (σ / t)])
  have hl1 : Real.log (1 + (σ / t) ^ 2) ≤ 1 / t ^ 2 := by
    have h := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (σ / t) ^ 2)
    linarith
  have ha0 : 0 ≤ Real.arctan (σ / t) := Real.arctan_nonneg.mpr (by positivity)
  have ha1 : Real.arctan (σ / t) ≤ 1 / t :=
    (Real.arctan_le_self (by positivity)).trans
      (div_le_div_of_nonneg_right hσ1 ht0.le)
  have ha2 : Real.arctan (σ / t) ^ 2 ≤ 1 / t ^ 2 := by
    have hsq : Real.arctan (σ / t) ^ 2 ≤ (1 / t) ^ 2 := by nlinarith
    simpa [div_pow] using hsq
  have hlsq : (Real.log t + Real.log (1 + (σ / t) ^ 2) / 2) ^ 2 ≤
      (Real.log t + (1 / t ^ 2) / 2) ^ 2 := by gcongr
  unfold logModulus
  apply Real.sqrt_le_iff.mpr
  constructor
  · linarith
  · have hm := mul_nonneg (sub_nonneg.mpr hL) hd
    nlinarith

/-- The elementary normalizer retains Backlund's exact historical loss. -/
theorem correction_lower {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) : 1 - 4 / t ^ 2 ≤ correction σ t := by
  have ht0 : 0 < t := by linarith
  have hL := one_le_log_of_three_le ht
  have hD := log_le_logModulus (σ := σ) (by linarith : 1 ≤ t)
  have hDpos : 0 < logModulus σ t := by linarith
  have hd : 0 ≤ 1 / t ^ 2 := by positivity
  have hdsmall : 1 / t ^ 2 ≤ 1 / 9 := by
    apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 9)
    nlinarith
  have hcoef : 0 ≤ 1 - 4 / t ^ 2 := by
    rw [show 4 / t ^ 2 = 4 * (1 / t ^ 2) by ring]
    linarith
  have hDupper : logModulus σ t ≤ Real.log t * (1 + 1 / t ^ 2) := by
    refine (logModulus_upper hσ0 hσ1 ht).trans ?_
    have hm := mul_nonneg (sub_nonneg.mpr hL) hd
    nlinarith
  have he : 1 - 1 / t ^ 2 ≤ Real.exp (correctionExponent σ t) := by
    have he0 := correctionExponent_lower hσ0 hσ1 ht0
    have he1 := Real.add_one_le_exp (correctionExponent σ t)
    linarith
  unfold correction
  apply (le_div_iff₀ hDpos).mpr
  calc
    _ ≤ (1 - 4 / t ^ 2) * (Real.log t * (1 + 1 / t ^ 2)) :=
      mul_le_mul_of_nonneg_left hDupper hcoef
    _ ≤ (1 - 1 / t ^ 2) * Real.log t := by
      have h1 := mul_nonneg (show 0 ≤ Real.log t by linarith) hd
      have h2 := mul_nonneg (show 0 ≤ Real.log t by linarith) (sq_nonneg (1 / t ^ 2))
      linear_combination 2 * h1 + 4 * h2
    _ ≤ Real.exp (correctionExponent σ t) * Real.log t :=
      mul_le_mul_of_nonneg_right he (by linarith)

/-- Exact logarithmic modulus of a point on a horizontal line. -/
theorem log_norm_horizontal {σ t : ℝ} (ht : 0 < t) :
    Real.log ‖(t : ℂ) - σ * I‖ =
      Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 := by
  have hq : 0 < 1 + (σ / t) ^ 2 := by positivity
  have hn : ‖(t : ℂ) - σ * I‖ = t * Real.sqrt (1 + (σ / t) ^ 2) := by
    apply (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [mul_pow, Real.sq_sqrt hq.le, Complex.sq_norm, Complex.normSq_apply]
    simp
    field_simp
  rw [hn, Real.log_mul ht.ne' (Real.sqrt_pos.mpr hq).ne', Real.log_sqrt hq.le]

/-- Exact elementary real and imaginary parts of `log(t−iσ)`. -/
theorem log_horizontal {σ t : ℝ} (ht : 0 < t) :
    Complex.log ((t : ℂ) - σ * I) =
      ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
        (Real.arctan (σ / t) : ℂ) * I := by
  apply Complex.ext
  · simpa [Complex.log_re] using log_norm_horizontal (σ := σ) ht
  · rw [Complex.log_im, arg_eq_arctan_of_re_pos (by simpa using ht)]
    simp [neg_div, Real.arctan_neg]

/-- The denominator in the analytic normalizer has exactly the real modulus
used above. -/
theorem norm_log_horizontal {σ t : ℝ} (ht : 0 < t) :
    ‖Complex.log ((t : ℂ) - σ * I)‖ = logModulus σ t := by
  rw [log_horizontal ht, Complex.norm_def]
  simp [logModulus, Complex.normSq_apply, pow_two]

/-- The chosen normalization is holomorphic on the whole upper half-plane
above height one. In particular it has no unmentioned branch obstruction in
the half-strip. -/
theorem analyticAt_normalizedZeta {s : ℂ} (hs : 1 < s.im) :
    AnalyticAt ℂ normalizedZeta s := by
  have ht : 0 < s.im := by linarith
  have hp : s ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp at hh
    linarith
  have hw : -s * I ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simpa using ht
  have hw' : -s * I / (2 * Real.pi) ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    rw [show (2 : ℂ) * Real.pi = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_re]
    simpa using div_pos ht (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos)
  have hnorm : 1 < ‖-s * I‖ := by
    have h := Complex.re_le_norm (-s * I)
    have hr : (-s * I).re = s.im := by simp
    rw [hr] at h
    linarith
  have hn : Complex.log (-s * I) ≠ 0 := by
    intro he
    have h := congrArg Complex.re he
    rw [Complex.log_re, Complex.zero_re] at h
    have hp := Real.log_pos hnorm
    linarith
  have hd : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I)) s :=
    (analyticAt_id.neg.mul analyticAt_const).clog hw
  have hc : AnalyticAt ℂ (fun z : ℂ => Complex.log (-z * I / (2 * Real.pi))) s :=
    ((analyticAt_id.neg.mul analyticAt_const).div_const).clog hw'
  have he : AnalyticAt ℂ exponent s := by
    unfold exponent
    exact (((analyticAt_id.sub analyticAt_const).div_const).mul hc).sub
      analyticAt_id.div_const
  have hz : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s (by simpa using hp)
  exact (hz.mul he.cexp).div hd hn

/-- Exact real part of the analytic exponent; no asymptotic equivalence is
used in the strip estimate. -/
theorem exponent_re_horizontal {σ t : ℝ} (ht : 0 < t) :
    (exponent ((σ : ℂ) + t * I)).re =
      (σ - 1) / 2 * Real.log (t / (2 * Real.pi)) + correctionExponent σ t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have hw : (t : ℂ) - σ * I ≠ 0 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
    exact ht.ne' hh
  have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
    ring_nf
    simp
  have hdiv : ((t : ℂ) - σ * I) / (2 * Real.pi) =
      ((t : ℂ) - σ * I) * (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by
    push_cast
    rfl
  have hl : Complex.log (((t : ℂ) - σ * I) / (2 * Real.pi)) =
      -(Real.log (2 * Real.pi) : ℂ) +
      ((Real.log t + Real.log (1 + (σ / t) ^ 2) / 2 : ℝ) : ℂ) -
        (Real.arctan (σ / t) : ℂ) * I := by
    rw [hdiv, Complex.log_mul_ofReal _ (inv_pos.mpr hp) _ hw,
      Real.log_inv, log_horizontal ht]
    push_cast
    ring
  unfold exponent
  rw [hrot, hl, Real.log_div ht.ne' hp.ne']
  simp [correctionExponent, Complex.mul_re, Complex.mul_im, div_ofNat_re, div_ofNat_im]
  ring

/-- Exact modulus factorization of the analytic normalizer. -/
theorem norm_normalizedZeta_horizontal {σ t : ℝ} (ht : 1 < t) :
    ‖normalizedZeta ((σ : ℂ) + t * I)‖ =
      (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
        ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * correction σ t := by
  have ht0 : 0 < t := by linarith
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hlog : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hD : logModulus σ t ≠ 0 := ne_of_gt
    ((Real.log_pos ht).trans_le (log_le_logModulus ht.le))
  have hrot : -((σ : ℂ) + t * I) * I = (t : ℂ) - σ * I := by
    ring_nf
    simp
  rw [normalizedZeta, norm_div, norm_mul, Complex.norm_exp,
    exponent_re_horizontal ht0, Real.exp_add, hrot, norm_log_horizontal ht0]
  rw [Real.rpow_def_of_pos hp]
  unfold correction
  field_simp

/-- Undo the normalizer with the exact `t²/(t²−4)` factor from Backlund (56). -/
theorem zeta_norm_le_of_normalized_le {σ t : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (ht : 3 ≤ t) (hφ : ‖normalizedZeta ((σ : ℂ) + t * I)‖ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
      t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 - 4 := by nlinarith
  have hp : 0 < t / (2 * Real.pi) := by positivity
  have hL : 0 < Real.log t := Real.log_pos (by linarith)
  have hA : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) := Real.rpow_pos_of_pos hp _
  have hq0 : 0 < 1 - 4 / t ^ 2 := by
    apply sub_pos.mpr
    apply (div_lt_one (sq_pos_of_pos ht0)).mpr
    nlinarith
  have hq := correction_lower hσ0 hσ1 ht
  rw [norm_normalizedZeta_horizontal (by linarith : 1 < t)] at hφ
  have hprod : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      ‖riemannZeta ((σ : ℂ) + t * I)‖ / Real.log t * (1 - 4 / t ^ 2) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hq (by positivity)).trans hφ
  have hab : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t / (2 * Real.pi)) ^ ((1 - σ) / 2) = 1 := by
    rw [← Real.rpow_add hp, show (σ - 1) / 2 + (1 - σ) / 2 = 0 by ring,
      Real.rpow_zero]
  have htarget : (t / (2 * Real.pi)) ^ ((σ - 1) / 2) *
      (t ^ 2 / (t ^ 2 - 4) * (t / (2 * Real.pi)) ^ ((1 - σ) / 2) * Real.log t) /
        Real.log t * (1 - 4 / t ^ 2) = 1 := by
    have he : 1 - 4 / t ^ 2 = (t ^ 2 - 4) / t ^ 2 := by field_simp
    rw [he]
    field_simp
    nlinarith [hab]
  have hm : 0 < (t / (2 * Real.pi)) ^ ((σ - 1) / 2) / Real.log t *
      (1 - 4 / t ^ 2) := by positivity
  apply (mul_le_mul_iff_right₀ hm).mp
  convert hprod.trans_eq htarget.symm using 1 <;> ring

end TernaryGoldbach.RSBounds.BacklundStripNormalizer
