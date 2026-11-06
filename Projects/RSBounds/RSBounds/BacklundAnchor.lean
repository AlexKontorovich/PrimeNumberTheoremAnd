import RSBounds.BacklundCenterNumerics
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The logarithm branch at Rosser's anchor

The Euler logarithm satisfies `‖L(σ+it)‖ ≤ log ζ(σ)` for `σ>1`.
The certified bound `ζ(5/4)<23/5<exp(π/2)` therefore puts the whole
vertical line image in the right half-plane. This justifies use of the
principal argument in the zero-count identity; a lower bound for the
norm of zeta alone would not justify the branch choice.

The real Euler-log conversion follows the proved argument in
`TernaryGoldbach.Prelim.PNTMertens.log_zeta_eq_sum`. The final vertical
FTC step adapts the argument in Gersh's `BacklundArgVarVertical.lean`
from anchor 2 to anchor 5/4; see THIRD_PARTY_NOTICES.md.
-/

open Complex Filter MeasureTheory
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundAnchor

noncomputable def eulerLog (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))

lemma norm_neg_log_one_sub_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖-Complex.log (1 - z)‖ ≤ -Real.log (1 - ‖z‖) := by
  apply (Complex.hasSum_taylorSeries_neg_log' hz).norm_le_of_bounded
    (Real.hasSum_pow_div_log_of_abs_lt_one (by simpa using hz))
  intro n
  have hd : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Complex.norm_natCast (n + 1)
  simp only [norm_div, norm_pow, hd, le_refl]

lemma real_eulerLog {σ : ℝ} (hσ : 1 < σ) :
    eulerLog (σ : ℂ) =
      ((∑' p : Nat.Primes, -Real.log (1 - (p : ℝ) ^ (-σ)) : ℝ) : ℂ) := by
  rw [eulerLog, Complex.ofReal_tsum]
  apply tsum_congr
  intro p
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hpow : (p : ℂ) ^ (-(σ : ℂ)) = (((p : ℝ) ^ (-σ) : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_neg, Complex.ofReal_natCast] using
      (Complex.ofReal_cpow hp0.le (-σ)).symm
  have hlt : (p : ℝ) ^ (-σ) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  rw [hpow, ← Complex.ofReal_one, ← Complex.ofReal_sub,
    ← Complex.ofReal_log (by linarith)]
  simp

lemma norm_eulerLog_le {s : ℂ} (hs : 1 < s.re) :
    ‖eulerLog s‖ ≤ Real.log ‖riemannZeta (s.re : ℂ)‖ := by
  let r : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s.re)
  have hrs : Summable r := Nat.Primes.summable_rpow.mpr (by linarith)
  have hlogs : Summable (fun p => -Real.log (1 - r p)) := by
    simpa only [sub_eq_add_neg] using
      (Real.summable_log_one_add_of_summable hrs.neg).neg
  have he : Real.log ‖riemannZeta (s.re : ℂ)‖ =
      ∑' p : Nat.Primes, -Real.log (1 - r p) := by
    rw [← riemannZeta_eulerProduct_exp_log (by simpa using hs),
      show (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s.re : ℂ)))) =
        eulerLog (s.re : ℂ) from rfl,
      real_eulerLog hs, Complex.norm_exp, Complex.ofReal_re, Real.log_exp]
  rw [he]
  apply tsum_of_norm_bounded hlogs.hasSum
  intro p
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith
  have hn : ‖(p : ℂ) ^ (-s)‖ = r p := by
    simpa only [r, Complex.neg_re, Complex.ofReal_natCast] using
      Complex.norm_cpow_eq_rpow_re_of_pos hp0 (-s)
  have hlt : r p < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  simpa only [hn] using norm_neg_log_one_sub_le (z := (p : ℂ) ^ (-s)) (hn ▸ hlt)

lemma log_zeta_five_fourths_lt_half_pi :
    Real.log ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < Real.pi / 2 := by
  have he := Real.sum_le_exp_of_nonneg (x := (31 / 20 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ] at he
  have hπ : (31 / 20 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_d2]
  have hz : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  apply (Real.log_lt_iff_lt_exp hz).mpr
  exact zeta_five_fourths_upper.trans
    ((show (23 / 5 : ℝ) < Real.exp (31 / 20) by linarith).trans
      (Real.exp_lt_exp.mpr hπ))

lemma re_zeta_anchor_pos (t : ℝ) :
    0 < (riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
  let s : ℂ := (5 / 4 : ℂ) + t * I
  have hs : 1 < s.re := by simp [s]; norm_num
  have hb : ‖eulerLog s‖ < Real.pi / 2 :=
    (norm_eulerLog_le hs).trans_lt (by simpa [s] using log_zeta_five_fourths_lt_half_pi)
  have hi : |(eulerLog s).im| < Real.pi / 2 :=
    (Complex.abs_im_le_norm _).trans_lt hb
  have hc : 0 < Real.cos (eulerLog s).im := Real.cos_pos_of_mem_Ioo (abs_lt.mp hi)
  change 0 < (riemannZeta s).re
  rw [← riemannZeta_eulerProduct_exp_log hs, show
    (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-s))) = eulerLog s from rfl,
    Complex.exp_re]
  exact mul_pos (Real.exp_pos _) hc

private lemma anchor_ne_one (t : ℝ) : (5 / 4 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  norm_num at this

private lemma anchor_ne_zero (t : ℝ) : riemannZeta ((5 / 4 : ℂ) + t * I) ≠ 0 :=
  riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)

lemma hasDerivAt_log_anchor (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I)))
      (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I) * I) t := by
  have hl : HasDerivAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) I t := by
    convert ((Complex.ofRealCLM.hasFDerivAt).hasDerivAt.mul_const I).const_add (5 / 4) using 1 <;> simp
  have hz := (differentiableAt_riemannZeta (anchor_ne_one t)).hasDerivAt.scomp t hl
  have h := hz.clog_real (Complex.mem_slitPlane_iff.mpr (Or.inl (re_zeta_anchor_pos t)))
  simp only [Function.comp_def, smul_eq_mul] at h
  convert h using 1 <;> simp only [logDeriv_apply] <;> ring

lemma continuous_vertical_integrand :
    Continuous (fun t : ℝ => (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hl : ContinuousAt (fun u : ℝ => (5 / 4 : ℂ) + u * I) t := by fun_prop
  have ha : AnalyticAt ℂ riemannZeta ((5 / 4 : ℂ) + t * I) := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds (anchor_ne_one t)] with z hz
    exact differentiableAt_riemannZeta hz
  have hc : ContinuousAt (fun u : ℝ =>
      deriv riemannZeta ((5 / 4 : ℂ) + u * I) /
        riemannZeta ((5 / 4 : ℂ) + u * I)) t :=
    ContinuousAt.comp (g := fun s : ℂ => deriv riemannZeta s / riemannZeta s)
      (f := fun u : ℝ => (5 / 4 : ℂ) + u * I)
      (ha.deriv.continuousAt.div ha.continuousAt (anchor_ne_zero t)) hl
  simpa only [logDeriv_apply, Function.comp_def] using Complex.continuous_re.continuousAt.comp hc

lemma vertical_integral_eq_arg (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) =
      (riemannZeta ((5 / 4 : ℂ) + T * I)).arg := by
  have hd (t : ℝ) :
      HasDerivAt (fun u : ℝ => (Complex.log (riemannZeta ((5 / 4 : ℂ) + u * I))).im)
        (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re t := by
    convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_log_anchor t) using 1 <;>
      simp [Function.comp_def]
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hd t) (continuous_vertical_integrand.intervalIntegrable 0 T)
  rw [he]
  simp only [Complex.log_im, Complex.ofReal_zero, zero_mul, add_zero]
  have hs := real_eulerLog (σ := (5 / 4 : ℝ)) (by norm_num)
  have he' := riemannZeta_eulerProduct_exp_log (s := ((5 / 4 : ℝ) : ℂ)) (by norm_num)
  change Complex.exp (eulerLog ((5 / 4 : ℝ) : ℂ)) = _ at he'
  rw [hs] at he'
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at he'
  have harg : (riemannZeta (5 / 4 : ℂ)).arg = 0 := by
    rw [← he', ← Complex.ofReal_exp]
    exact Complex.arg_ofReal_of_nonneg (Real.exp_nonneg _)
  rw [harg, sub_zero]

lemma abs_vertical_integral_le (T : ℝ) :
    |∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re| ≤ Real.pi / 2 := by
  rw [vertical_integral_eq_arg]
  exact (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (re_zeta_anchor_pos T))).le

end TernaryGoldbach.RSBounds.BacklundAnchor
