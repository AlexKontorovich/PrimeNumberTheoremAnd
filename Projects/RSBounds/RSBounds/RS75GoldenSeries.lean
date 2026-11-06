import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-!
# Actual real log-moment and von Mangoldt series for the RS75 constants

The underlying Dirichlet-series identities and differentiation are reused
from Mathlib. This module binds the actual logarithmic derivative of zeta
to its moments and proves the monotonicity used by rational-point checks.
No numerical or zero-free-region premise occurs here.
-/

open Complex LSeries ArithmeticFunction Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.RS75GoldenSeries

noncomputable def coeff (f : ℕ → ℝ) (j : ℕ) : ℕ → ℂ :=
  (LSeries.logMul^[j]) (fun n => (f n : ℂ))

noncomputable def series (f : ℕ → ℝ) (j : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, Real.log (n : ℝ) ^ j * f n * (n : ℝ) ^ (-s)

noncomputable def moment (s : ℝ) (j : ℕ) : ℝ :=
  ∑' n : ℕ, Real.log (n : ℝ) ^ j * (n : ℝ) ^ (-s)

noncomputable def logDerivative (s : ℝ) : ℝ :=
  (logDeriv riemannZeta (s : ℂ)).re

noncomputable def slope (s : ℝ) : ℝ := series (fun n => Λ n) 1 s

lemma coeff_apply (f : ℕ → ℝ) (j n : ℕ) :
    coeff f j n = ((Real.log (n : ℝ) ^ j * f n : ℝ) : ℂ) := by
  induction j with
  | zero => simp [coeff]
  | succ j ih =>
      rw [coeff, Function.iterate_succ_apply', LSeries.logMul]
      change Complex.log n * coeff f j n = _
      rw [ih, ← Complex.natCast_log]
      push_cast
      rw [pow_succ]
      ring

lemma coeff_succ (f : ℕ → ℝ) (j : ℕ) :
    LSeries.logMul (coeff f j) = coeff f (j + 1) := by
  simp only [coeff, Function.iterate_succ_apply']

lemma coeff_abscissa (f : ℕ → ℝ) (j : ℕ) :
    abscissaOfAbsConv (coeff f j) = abscissaOfAbsConv (fun n => (f n : ℂ)) := by
  simp [coeff]

lemma coeff_term {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j n : ℕ) :
    LSeries.term (coeff f j) (s : ℂ) n =
      ((Real.log (n : ℝ) ^ j * f n * (n : ℝ) ^ (-s) : ℝ) : ℂ) := by
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -s ≠ 0)]
  · simp only [LSeries.term_of_ne_zero hn, coeff_apply, Complex.ofReal_mul,
      Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_neg,
      Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]

lemma coeff_summable {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    LSeriesSummable (coeff f j) (s : ℂ) := by
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  rw [coeff_abscissa, Complex.ofReal_re]
  exact hc.trans_lt (by exact_mod_cast hs)

lemma hasSum_series {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    HasSum (fun n : ℕ => Real.log (n : ℝ) ^ j * f n * (n : ℝ) ^ (-s))
      (LSeries (coeff f j) (s : ℂ)).re := by
  have h := Complex.hasSum_re (coeff_summable hs f j hc).hasSum
  change HasSum (fun n => (LSeries.term (coeff f j) (s : ℂ) n).re)
    (LSeries (coeff f j) (s : ℂ)).re at h
  simpa only [coeff_term hs, Complex.ofReal_re] using h

lemma summable_series {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ j * f n * (n : ℝ) ^ (-s)) :=
  (hasSum_series hs f j hc).summable

lemma series_eq_re {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    series f j s = (LSeries (coeff f j) (s : ℂ)).re :=
  (hasSum_series hs f j hc).tsum_eq

lemma complexSeries_eq {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    LSeries (coeff f j) (s : ℂ) = (series f j s : ℂ) := by
  rw [LSeries, series, Complex.ofReal_tsum]
  exact tsum_congr (coeff_term hs f j)

lemma hasDerivAt_series {s : ℝ} (hs : 1 < s) (f : ℕ → ℝ) (j : ℕ)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    HasDerivAt (series f j) (-series f (j + 1) s) s := by
  have ha : abscissaOfAbsConv (coeff f j) < (s : ℂ).re := by
    rw [coeff_abscissa, Complex.ofReal_re]
    exact hc.trans_lt (by exact_mod_cast hs)
  have h := (LSeries_hasDerivAt ha).real_of_complex
  rw [coeff_succ, Complex.neg_re, ← series_eq_re hs f (j + 1) hc] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hs] with t ht
  exact series_eq_re ht f j hc

lemma antitoneOn_series (f : ℕ → ℝ) (j : ℕ) (hf : ∀ n, 0 ≤ f n)
    (hc : abscissaOfAbsConv (fun n => (f n : ℂ)) ≤ 1) :
    AntitoneOn (series f j) (Ioi 1) := by
  intro x hx y hy hxy
  change 1 < x at hx
  change 1 < y at hy
  apply (summable_series hy f j hc).tsum_le_tsum _ (summable_series hx f j hc)
  intro n
  by_cases hn : n = 0
  · subst n
    simp [Real.zero_rpow (by linarith : -x ≠ 0), Real.zero_rpow (by linarith : -y ≠ 0)]
  · apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) _) (hf n))
    exact Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn) (by linarith)

private lemma one_eq_const : (1 : ℕ → ℂ) = fun _ => (1 : ℂ) := by
  funext n
  exact Pi.one_apply n

lemma one_abscissa : abscissaOfAbsConv (fun _ : ℕ => ((1 : ℝ) : ℂ)) ≤ 1 := by
  simpa only [Complex.ofReal_one, one_eq_const] using
    (show abscissaOfAbsConv (1 : ℕ → ℂ) ≤ 1 by
      simpa only [abscissaOfAbsConv_one] using (le_refl (1 : EReal)))

lemma series_one_eq_moment (s : ℝ) (j : ℕ) :
    series (fun _ => 1) j s = moment s j := by simp [series, moment]

lemma summable_moment {s : ℝ} (hs : 1 < s) (j : ℕ) :
    Summable (fun n : ℕ => Real.log (n : ℝ) ^ j * (n : ℝ) ^ (-s)) := by
  simpa using summable_series hs (fun _ => 1) j one_abscissa

lemma hasDerivAt_moment {s : ℝ} (hs : 1 < s) (j : ℕ) :
    HasDerivAt (fun t => moment t j) (-moment s (j + 1)) s := by
  have h := hasDerivAt_series hs (fun _ => 1) j one_abscissa
  have hf : series (fun _ => 1) j = fun t => moment t j := by
    funext t
    exact series_one_eq_moment t j
  rw [hf, series_one_eq_moment] at h
  exact h

lemma zeta_eq_moment_zero {s : ℝ} (hs : 1 < s) :
    riemannZeta (s : ℂ) = (moment s 0 : ℂ) := by
  rw [← LSeries_one_eq_riemannZeta (by simpa using hs), one_eq_const]
  simpa only [coeff, Function.iterate_zero_apply, Complex.ofReal_one, series_one_eq_moment]
    using complexSeries_eq hs (fun _ => 1) 0 one_abscissa

lemma moment_zero_pos {s : ℝ} (hs : 1 < s) : 0 < moment s 0 := by
  have h := riemannZeta_re_pos_of_one_lt hs
  rwa [zeta_eq_moment_zero hs, Complex.ofReal_re] at h

lemma zeta_hasDerivAt {s : ℝ} (hs : 1 < s) :
    HasDerivAt riemannZeta (-(moment s 1 : ℂ)) (s : ℂ) := by
  have ha : abscissaOfAbsConv (1 : ℕ → ℂ) < (s : ℂ).re := by
    rw [abscissaOfAbsConv_one, Complex.ofReal_re]
    exact_mod_cast hs
  have h := LSeries_hasDerivAt ha
  have he : LSeries.logMul (1 : ℕ → ℂ) = coeff (fun _ => 1) 1 := by
    simp [coeff, one_eq_const]
  rw [he, complexSeries_eq hs (fun _ => 1) 1 one_abscissa, series_one_eq_moment] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show 1 < (s : ℂ).re by simpa using hs)] with z hz
  exact (LSeries_one_eq_riemannZeta hz).symm

lemma logDerivative_eq_moments {s : ℝ} (hs : 1 < s) :
    logDerivative s = -moment s 1 / moment s 0 := by
  rw [logDerivative, logDeriv_apply, (zeta_hasDerivAt hs).deriv, zeta_eq_moment_zero hs]
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_div, Complex.ofReal_re]

lemma hasDerivAt_logDerivative_moments {s : ℝ} (hs : 1 < s) :
    HasDerivAt logDerivative
      (moment s 2 / moment s 0 - (moment s 1 / moment s 0) ^ 2) s := by
  have h := ((hasDerivAt_moment hs 1).neg).div (hasDerivAt_moment hs 0)
    (moment_zero_pos hs).ne'
  have hv : ((- -moment s (1 + 1)) * moment s 0 -
      (-moment s 1) * (-moment s (0 + 1))) / moment s 0 ^ 2 =
      moment s 2 / moment s 0 - (moment s 1 / moment s 0)^2 := by
    norm_num only [Nat.reduceAdd, neg_neg]
    field_simp [(moment_zero_pos hs).ne']
  simp only [Pi.neg_apply] at h
  rw [hv] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hs] with t ht
  exact logDerivative_eq_moments ht

lemma vonMangoldt_abscissa :
    abscissaOfAbsConv (fun n : ℕ => (Λ n : ℂ)) ≤ 1 := by
  apply abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (x := 1)
  intro y hy
  exact LSeriesSummable_vonMangoldt (by simpa using hy)

lemma logDerivative_eq_vonMangoldt {s : ℝ} (hs : 1 < s) :
    logDerivative s = -series (fun n => Λ n) 0 s := by
  rw [series_eq_re hs (fun n => Λ n) 0 vonMangoldt_abscissa]
  simp only [coeff, Function.iterate_zero_apply]
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs), neg_div,
    Complex.neg_re, neg_neg, logDerivative, logDeriv_apply]

lemma hasDerivAt_logDerivative {s : ℝ} (hs : 1 < s) :
    HasDerivAt logDerivative (slope s) s := by
  have h := (hasDerivAt_series hs (fun n => Λ n) 0 vonMangoldt_abscissa).neg
  simp only [Nat.zero_add, neg_neg] at h
  apply h.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const continuous_id).mem_nhds hs] with t ht
  exact logDerivative_eq_vonMangoldt ht

lemma slope_eq_moments {s : ℝ} (hs : 1 < s) :
    slope s = moment s 2 / moment s 0 - (moment s 1 / moment s 0)^2 :=
  (hasDerivAt_logDerivative hs).unique (hasDerivAt_logDerivative_moments hs)

lemma monotoneOn_logDerivative : MonotoneOn logDerivative (Ioi 1) := by
  intro x hx y hy hxy
  rw [logDerivative_eq_vonMangoldt hx, logDerivative_eq_vonMangoldt hy]
  exact neg_le_neg (antitoneOn_series (fun n => Λ n) 0
    (fun _ => vonMangoldt_nonneg) vonMangoldt_abscissa hx hy hxy)

lemma antitoneOn_slope : AntitoneOn slope (Ioi 1) :=
  antitoneOn_series (fun n => Λ n) 1 (fun _ => vonMangoldt_nonneg) vonMangoldt_abscissa

end TernaryGoldbach.RSBounds.RS75GoldenSeries
