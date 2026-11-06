/-
Portions adapted from Mathlib.Analysis.Complex.JensenFormula.
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0; see licenses/PrimeNumberTheoremAnd-LICENSE.
Modifications and power-limit extension: 2026 OpenAI.
-/
import Mathlib.Analysis.Complex.JensenFormula
import RSBounds.BacklundPhase
import Mathlib.Tactic

/-!
# Jensen's inequality for Backlund's power functions

This module retains a circle-average boundary majorant, rather than replacing
it by its supremum. It supplies the Jensen and phase-limit part of Rosser's
power argument. It does not supply the argument-variation/zero-count bridge
or the numerical zeta boundary estimates.

The divisor comparison below follows the geometric comparison in Mathlib's
`AnalyticOnNhd.sum_divisor_le`; Jensen's formula itself is reused directly.
-/

open Filter MeromorphicAt MeasureTheory MeromorphicOn Metric Real Set Topology Complex
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundJensen

/-- Number of zeros in the closed disk, with analytic multiplicities. -/
noncomputable def zeroCount (f : ℂ → ℂ) (c : ℂ) (r : ℝ) : ℝ :=
  ∑ᶠ u, (divisor f (closedBall c r) u : ℝ)

/-- Geometric part of Jensen's zero-count inequality, with the exact
circle average retained. -/
theorem zeroCount_mul_log_le_circleAverage {c : ℂ} {r R : ℝ} {f : ℂ → ℂ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) :
    zeroCount f c r * Real.log (R / r) ≤
      circleAverage (fun z => Real.log ‖f z‖) c R - Real.log ‖f c‖ := by
  have hR : 0 < R := hr.trans hrR
  have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
  have hJ := hfa.circleAverage_log_norm hR.ne' hfc
  rw [abs_of_pos hR] at hJ
  rw [hJ, add_sub_cancel_right, zeroCount, finsum_mul]
  refine finsum_le_finsum ?_ ?_ fun u => ?_
  · exact (divisor f (closedBall c r)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ => (by simp_all)
  · exact (divisor f (closedBall c R)).finiteSupport (isCompact_closedBall ..) |>.subset
      fun _ _ => (by simp_all)
  · by_cases hbig : u ∈ closedBall c R
    · by_cases hsmall : u ∈ closedBall c r
      · simp only [hf.mono (closedBall_subset_closedBall hrR.le), hsmall,
          AnalyticOnNhd.divisor_apply, hf, hbig]
        by_cases huc : u = c
        · rw [huc, (hf c (by simp; positivity)).analyticOrderAt_eq_zero.mpr hfc]
          simp
        have hdist : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        have hdistR : ‖c - u‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm'] using hsmall
        apply mul_le_mul_of_nonneg_left ?_ (by simp)
        apply Real.log_le_log (div_pos hR hr)
        rw [← div_eq_mul_inv]
        exact div_le_div_of_nonneg_left hR.le hdist hdistR
      · simp only [hsmall, not_false_eq_true,
          Function.locallyFinsuppWithin.apply_eq_zero_of_notMem, Int.cast_zero, zero_mul]
        refine mul_nonneg (mod_cast hf.divisor_nonneg ..) ?_
        have hdist : 0 < ‖c - u‖ := by
          have : r < ‖c - u‖ := by simpa [mem_closedBall, dist_eq_norm', not_le] using hsmall
          linarith
        apply Real.log_nonneg
        rw [← div_eq_mul_inv, one_le_div hdist]
        simpa [mem_closedBall, dist_eq_norm'] using hbig
    · have hsmall : u ∉ closedBall c r := fun hu =>
        hbig (closedBall_subset_closedBall hrR.le hu)
      simp [hbig, hsmall]

/-- Jensen's inequality with an integrable angular logarithmic majorant. -/
theorem zeroCount_le_of_log_majorant {c : ℂ} {r R : ℝ} {f : ℂ → ℂ} {B : ℂ → ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0)
    (hB : CircleIntegrable B c R)
    (hbound : ∀ z ∈ sphere c R, Real.log ‖f z‖ ≤ B z) :
    zeroCount f c r ≤
      (circleAverage B c R - Real.log ‖f c‖) / Real.log (R / r) := by
  have hR : 0 < R := hr.trans hrR
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hfa : AnalyticOnNhd ℂ f (closedBall c |R|) := by simpa [abs_of_pos hR] using hf
  have hi := (hfa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hc := circleAverage_mono hi hB (by simpa [abs_of_pos hR] using hbound)
  apply (le_div_iff₀ hlog).mpr
  exact (zeroCount_mul_log_le_circleAverage hr hrR hf hfc).trans (sub_le_sub_right hc _)

/-- Backlund's average of two powers. At a real-symmetry center this is
exactly the real part of a power. -/
noncomputable def powerAverage (f g : ℂ → ℂ) (n : ℕ) (s : ℂ) : ℂ :=
  (f s ^ n + g s ^ n) / 2

theorem powerAverage_center {f g : ℂ → ℂ} {c : ℂ}
    (hc : g c = conj (f c)) (n : ℕ) :
    powerAverage f g n c = ((f c ^ n).re : ℂ) := by
  unfold powerAverage
  rw [hc, ← map_pow]
  rw [Complex.add_conj]
  push_cast
  ring

theorem analyticOnNhd_powerAverage {f g : ℂ → ℂ} {s : Set ℂ}
    (hf : AnalyticOnNhd ℂ f s) (hg : AnalyticOnNhd ℂ g s) (n : ℕ) :
    AnalyticOnNhd ℂ (powerAverage f g n) s := by
  intro z hz
  unfold powerAverage
  exact ((hf z hz).pow n |>.add ((hg z hz).pow n)).div_const (c := 2)

theorem norm_powerAverage_le {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
    (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
    ‖powerAverage f g n s‖ ≤ Real.exp ((n : ℝ) * B) := by
  rw [powerAverage, norm_div, Complex.norm_ofNat]
  have h1 := norm_add_le (f s ^ n) (g s ^ n)
  rw [norm_pow, norm_pow] at h1
  have hp1 := pow_le_pow_left₀ (norm_nonneg (f s)) hf n
  have hp2 := pow_le_pow_left₀ (norm_nonneg (g s)) hg n
  rw [Real.exp_nat_mul]
  linarith

theorem log_norm_powerAverage_le {f g : ℂ → ℂ} {s : ℂ} {B : ℝ}
    (hB : 0 ≤ B) (hf : ‖f s‖ ≤ Real.exp B) (hg : ‖g s‖ ≤ Real.exp B) (n : ℕ) :
    Real.log ‖powerAverage f g n s‖ ≤ (n : ℝ) * B := by
  by_cases hz : powerAverage f g n s = 0
  · simp [hz]
    positivity
  · have h := Real.log_le_log (norm_pos_iff.mpr hz) (norm_powerAverage_le hf hg n)
    simpa using h

/-- Normalized Jensen estimate for one nonvanishing Backlund power. -/
theorem normalized_power_zeroCount_le {c : ℂ} {r R : ℝ} {f g : ℂ → ℂ}
    {B : ℂ → ℝ} (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hB : CircleIntegrable B c R)
    (hB0 : ∀ z ∈ sphere c R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere c R, ‖g z‖ ≤ Real.exp (B z))
    {n : ℕ} (hn : 0 < n) (hfc : powerAverage f g n c ≠ 0) :
    zeroCount (powerAverage f g n) c r / n ≤
      (circleAverage B c R - Real.log ‖powerAverage f g n c‖ / n) /
        Real.log (R / r) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 < Real.log (R / r) := Real.log_pos ((one_lt_div hr).mpr hrR)
  have hi : CircleIntegrable (fun z => (n : ℝ) * B z) c R := by
    unfold CircleIntegrable at hB ⊢
    exact hB.const_mul (n : ℝ)
  have h := zeroCount_le_of_log_majorant hr hrR
    (analyticOnNhd_powerAverage hf hg n) hfc hi (fun z hz =>
      log_norm_powerAverage_le (hB0 z hz) (hfb z hz) (hgb z hz) n)
  rw [show circleAverage (fun z => (n : ℝ) * B z) c R =
      (n : ℝ) * circleAverage B c R by
        simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (n : ℝ))
          (f := B) (c := c) (R := R))] at h
  apply (div_le_iff₀ hn0).mpr
  convert h using 1
  field_simp


/-- Backlund's power limit in Jensen's inequality. The angular majorant is
retained exactly, and the center contributes `log ‖f c‖` in the limit. The
result is an eventual bound along a proved strictly increasing sequence. -/
theorem exists_power_sequence_zeroCount_bound {c : ℂ} {r R : ℝ}
    {f g : ℂ → ℂ} {B : ℂ → ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hfc : f c ≠ 0) (hconj : g c = conj (f c))
    (hB : CircleIntegrable B c R)
    (hB0 : ∀ z ∈ sphere c R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere c R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere c R, ‖g z‖ ≤ Real.exp (B z)) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
        zeroCount (powerAverage f g (n j)) c r / (n j : ℝ) ≤
          (circleAverage B c R - Real.log ‖f c‖) / Real.log (R / r) + ε := by
  obtain ⟨n, hn, hp, hl⟩ := exists_backlund_phase_sequence hfc
  refine ⟨n, hn, ?_⟩
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hnpos : ∀ᶠ j in atTop, 0 < n j := by
    filter_upwards [hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    exact_mod_cast hj
  have hratio := real_power_ratio_tendsto hp
  have hnonzero : ∀ᶠ j in atTop, powerAverage f g (n j) c ≠ 0 := by
    filter_upwards [hratio.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with j hj
    rw [powerAverage_center hconj]
    apply Complex.ofReal_ne_zero.mpr
    intro hz
    rw [hz, zero_div] at hj
    exact lt_irrefl _ hj
  have hnorm (j : ℕ) : ‖powerAverage f g (n j) c‖ = |(f c ^ n j).re| := by
    rw [powerAverage_center hconj, Complex.norm_real, Real.norm_eq_abs]
  have hlim : Tendsto
      (fun j => (circleAverage B c R -
        Real.log ‖powerAverage f g (n j) c‖ / (n j : ℝ)) / Real.log (R / r))
      atTop (𝓝 ((circleAverage B c R - Real.log ‖f c‖) / Real.log (R / r))) := by
    simp_rw [hnorm]
    exact (tendsto_const_nhds.sub hl).div_const _
  intro ε hε
  filter_upwards [hnpos, hnonzero,
    hlim.eventually (gt_mem_nhds (show
      (circleAverage B c R - Real.log ‖f c‖) / Real.log (R / r) <
      (circleAverage B c R - Real.log ‖f c‖) / Real.log (R / r) + ε by linarith))]
    with j hj hnz hlt
  exact (normalized_power_zeroCount_le hr hrR hf hg hB hB0 hfb hgb hj hnz).trans hlt.le

end TernaryGoldbach.RSBounds.BacklundJensen
