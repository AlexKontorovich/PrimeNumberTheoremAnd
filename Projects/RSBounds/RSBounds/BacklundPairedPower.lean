import RSBounds.BacklundPairedCrossing

/-!
# Rosser's power limit with reflected Jensen pairs

This result combines constructive crossings, their near/far Jensen weights,
and the proved Backlund phase subsequence. No zero pairing or zero count is
assumed. The inputs are an analytic conjugate pair, a continuous argument,
a reflection-error bound, and a circle-integrable boundary majorant.
-/

open Filter Real Complex Metric MeasureTheory MeromorphicOn Set Topology
open scoped ComplexConjugate
open TernaryGoldbach.RSBounds.BacklundJensen
open TernaryGoldbach.RSBounds.BacklundPairedCrossing

namespace TernaryGoldbach.RSBounds.BacklundPairedPower

/-- The sharp doubled Jensen budget for a single power. -/
theorem normalized_power_argument_le {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ}
    {R E : ℝ} {n : ℕ} (hR : 3 / 4 < R) (hE : 0 < E) (hn : 0 < n)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
    (hfc : powerAverage f g n (5 / 4 : ℂ) ≠ 0)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
    (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hzero : ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos ((n : ℝ) * θ x) = 0 → powerAverage f g n (x : ℂ) = 0)
    (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
    |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g n (5 / 4 : ℂ)‖ / n) / (2 * Real.log (R / (3 / 4))) +
        2 / n + E / (2 * Real.pi) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hR0 : 0 < R := by linarith
  have hlog : 0 < Real.log (R / (3 / 4)) := Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hpow := analyticOnNhd_powerAverage hf hg n
  have hpowa : AnalyticOnNhd ℂ (powerAverage f g n) (closedBall (5 / 4 : ℂ) |R|) := by
    simpa only [abs_of_pos hR0] using hpow
  have hi := (hpowa.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hiB : CircleIntegrable (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R := by
    unfold CircleIntegrable at hB ⊢
    exact hB.const_mul (n : ℝ)
  have havg := circleAverage_mono hi hiB (by
    rw [abs_of_pos hR0]
    exact fun z hz => log_norm_powerAverage_le (hB0 z hz) (hfb z hz) (hgb z hz) n)
  rw [show circleAverage (fun z => (n : ℝ) * B z) (5 / 4 : ℂ) R =
    (n : ℝ) * circleAverage B (5 / 4 : ℂ) R by
      simpa only [smul_eq_mul] using (circleAverage_fun_smul (a := (n : ℝ))
        (f := B) (c := (5 / 4 : ℂ)) (R := R))] at havg
  have hh := abs_argument_le hR (mul_pos hn0 hE) hpow hfc (hθ.const_mul (n : ℝ)) hzero
    (fun δ hδ0 hδ1 => by
      rw [show ((n : ℝ) * θ (1 / 2 + δ) - n * θ (1 / 2)) -
        (n * θ (1 / 2) - n * θ (1 / 2 - δ)) =
        n * ((θ (1 / 2 + δ) - θ (1 / 2)) -
          (θ (1 / 2) - θ (1 / 2 - δ))) by ring, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_left (hdelta δ hδ0 hδ1) hn0.le)
  rw [show (n : ℝ) * θ (5 / 4) - n * θ (1 / 2) =
    n * (θ (5 / 4) - θ (1 / 2)) by ring, abs_mul, Nat.abs_cast] at hh
  have hh' : (n : ℝ) * |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      ((n : ℝ) * circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g n (5 / 4 : ℂ)‖) / (2 * Real.log (R / (3 / 4))) +
        2 + (n : ℝ) * E / (2 * Real.pi) := by
    exact hh.trans (by gcongr)
  have hh'' := div_le_div_of_nonneg_right hh' hn0.le
  convert hh'' using 1 <;> field_simp [hn0.ne', hlog.ne', Real.pi_ne_zero]

/-- Rosser's limiting reflected Jensen argument bound. The additive crossing
cost disappears along the explicitly proved power subsequence. -/
theorem argument_bound {f g : ℂ → ℂ} {B : ℂ → ℝ} {θ : ℝ → ℝ} {R E : ℝ}
    (hR : 3 / 4 < R) (hE : 0 < E)
    (hf : AnalyticOnNhd ℂ f (closedBall (5 / 4 : ℂ) R))
    (hg : AnalyticOnNhd ℂ g (closedBall (5 / 4 : ℂ) R))
    (hfc : f (5 / 4 : ℂ) ≠ 0) (hconj : g (5 / 4 : ℂ) = conj (f (5 / 4 : ℂ)))
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖f z‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ sphere (5 / 4 : ℂ) R, ‖g z‖ ≤ Real.exp (B z))
    (hθ : ContinuousOn θ (Icc (-1 / 4 : ℝ) (5 / 4 : ℝ)))
    (hzero : ∀ n : ℕ, ∀ x ∈ Icc (-1 / 4 : ℝ) (5 / 4 : ℝ),
      Real.cos ((n : ℝ) * θ x) = 0 → powerAverage f g n (x : ℂ) = 0)
    (hdelta : ∀ δ : ℝ, 0 < δ → δ ≤ 3 / 4 →
      |(θ (1 / 2 + δ) - θ (1 / 2)) - (θ (1 / 2) - θ (1 / 2 - δ))| ≤ E) :
    |θ (5 / 4) - θ (1 / 2)| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
        (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi) := by
  obtain ⟨n, hn, hp, hl⟩ := TernaryGoldbach.RSBounds.exists_backlund_phase_sequence hfc
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hnpos : ∀ᶠ j in atTop, 0 < n j := by
    filter_upwards [hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    exact_mod_cast hj
  have hratio := TernaryGoldbach.RSBounds.real_power_ratio_tendsto hp
  have hnonzero : ∀ᶠ j in atTop, powerAverage f g (n j) (5 / 4 : ℂ) ≠ 0 := by
    filter_upwards [hratio.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with j hj
    rw [powerAverage_center hconj]
    apply Complex.ofReal_ne_zero.mpr
    intro hz
    rw [hz, zero_div] at hj
    exact lt_irrefl _ hj
  have hnorm (j : ℕ) : ‖powerAverage f g (n j) (5 / 4 : ℂ)‖ =
      |(f (5 / 4 : ℂ) ^ n j).re| := by
    rw [powerAverage_center hconj, Complex.norm_real, Real.norm_eq_abs]
  have hlim : Tendsto
      (fun j => (circleAverage B (5 / 4 : ℂ) R -
        Real.log ‖powerAverage f g (n j) (5 / 4 : ℂ)‖ / (n j : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (n j : ℝ) + E / (2 * Real.pi))
      atTop (𝓝 ((circleAverage B (5 / 4 : ℂ) R - Real.log ‖f (5 / 4 : ℂ)‖) /
        (2 * Real.log (R / (3 / 4))) + E / (2 * Real.pi))) := by
    simp_rw [hnorm]
    have hz : Tendsto (fun j => (2 : ℝ) / (n j : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hnTop
    simpa using (((tendsto_const_nhds.sub hl).div_const _).add hz).add_const (E / (2 * Real.pi))
  apply ge_of_tendsto hlim
  filter_upwards [hnpos, hnonzero] with j hj hnz
  exact normalized_power_argument_le hR hE hj hf hg hnz hB hB0 hfb hgb hθ (hzero (n j)) hdelta

end TernaryGoldbach.RSBounds.BacklundPairedPower
