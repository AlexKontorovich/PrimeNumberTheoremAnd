module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Analytic/Stirling.lean — shared Stirling/digamma asymptotics.

This is the shared home for complex Stirling-type asymptotics of Γ, log Γ and ψ = Γ'/Γ.
Consumers:
  • Zeta23/GammaFacts/Mu.lean: ψ on the vertical line Re = 1/4, error O(1/τ²);
    the trigamma series for the μ′ bound;
  • the Riemann–von Mangoldt argument: Im log Γ(1/4 + iT/2) main term; |Γ| growth
    in strips;
  • the explicit-formula argument: digamma growth on vertical strips.
Builds on Zeta23.GammaFacts.Series: digamma_series, hasSum_digamma_series,
summable_digamma_series, inv_gamma_eq_prod (Weierstrass product for 1/Γ).
-/
public import Zeta23.GammaFacts.Series

@[expose] public section

noncomputable section

namespace Zeta23
namespace Stirling

open Complex Filter Topology

/-- ψ is differentiable on the integer complement (Γ is analytic and nonvanishing there). -/
theorem differentiableAt_digamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  have hΓan : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopenZ.mem_nhds hz] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact hw ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hψan.differentiableAt

/-- Trigamma termwise series (used in Zeta23/GammaFacts/Mu.lean, deriv_bound).
ψ′(z) = Σ_{n≥0} 1/(z+n)², differentiating the digamma series termwise.   -/
theorem hasSum_trigamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    HasSum (fun n : ℕ => 1 / (z + n) ^ 2) (deriv Complex.digamma z) := by
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  obtain ⟨ε, hε0, hball⟩ := Metric.isOpen_iff.mp hopenZ z hz
  have hr0 : 0 < ε / 2 := by positivity
  set U : Set ℂ := Metric.ball z (ε / 2) with hU
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hzU : z ∈ U := Metric.mem_ball_self hr0
  have hUsub : U ⊆ Complex.integerComplement :=
    subset_trans (Metric.ball_subset_ball (by linarith)) hball
  have hδ : ∀ n : ℕ, ε / 2 < ‖z + ((n : ℂ) + 1)‖ := by
    intro n
    by_contra hle
    push Not at hle
    have hmem : (-(((n : ℂ)) + 1)) ∈ Metric.ball z ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      calc ‖-((n : ℂ) + 1) - z‖ = ‖z + ((n : ℂ) + 1)‖ := by
            rw [show -((n : ℂ) + 1) - z = -(z + ((n : ℂ) + 1)) by ring, norm_neg]
        _ ≤ ε / 2 := hle
        _ < ε := by linarith
    exact (hball hmem) ⟨-((n : ℤ) + 1), by push_cast; ring⟩
  set F : ℕ → ℂ → ℂ := fun n w => 1 / ((n : ℂ) + 1) - 1 / (w + n + 1) with hF
  set u : ℕ → ℝ := fun n =>
    (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2)) with hu
  have hnormn1 : ∀ n : ℕ, ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
    intro n
    rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hterm_ne : ∀ (n : ℕ) (w : ℂ), w ∈ U → w + ((n : ℂ) + 1) ≠ 0 := by
    intro n w hw h0
    have hwz : ‖w - z‖ < ε / 2 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ = ‖z - w‖ := by
      rw [show z + ((n : ℂ) + 1) = (z - w) + (w + ((n : ℂ) + 1)) by ring, h0, add_zero]
    rw [norm_sub_rev] at h1
    have := hδ n
    linarith
  have hlow : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖z + ((n : ℂ) + 1)‖ - ε / 2 ≤ ‖w + ((n : ℂ) + 1)‖ := by
    intro n w hw
    have hwz : ‖z - w‖ < ε / 2 := by
      rw [norm_sub_rev, ← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    have h1 : ‖z + ((n : ℂ) + 1)‖ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := by
      calc ‖z + ((n : ℂ) + 1)‖ = ‖(w + ((n : ℂ) + 1)) + (z - w)‖ := by ring_nf
        _ ≤ ‖w + ((n : ℂ) + 1)‖ + ‖z - w‖ := norm_add_le _ _
    linarith
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ U → ‖F n w‖ ≤ u n := by
    intro n w hw
    have hn1 : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
    have hw0 := hterm_ne n w hw
    have hw0' : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hw0
    have hident : F n w = w / (((n : ℂ) + 1) * (w + ((n : ℂ) + 1))) := by
      rw [hF]
      simp only
      rw [show w + ((n : ℂ) + 1) = w + (n : ℂ) + 1 by ring]
      field_simp
      ring
    have hwb : ‖w‖ ≤ ‖z‖ + ε / 2 := by
      have hwz : ‖w - z‖ < ε / 2 := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.mp hw
      calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
        _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
        _ ≤ ‖z‖ + ε / 2 := by linarith
    have hdl := hlow n w hw
    have hdpos : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
      have := hδ n
      linarith
    rw [hident, norm_div, norm_mul, hnormn1 n, hu]
    simp only
    gcongr
  have husum : Summable u := by
    refine Summable.of_norm_bounded_eventually
      (g := fun n : ℕ => 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹)) ?_ ?_
    · have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
        have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
          have h3 := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
          have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
            funext n
            rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
          rwa [heq] at h3
        have h4 := (summable_nat_add_iff 1).mpr h2
        simpa [add_comm] using h4
      exact h1.mul_left _
    · rw [Nat.cofinite_eq_atTop]
      filter_upwards [Filter.eventually_ge_atTop ⌈2 * (‖z‖ + ε / 2 + 1)⌉₊] with n hn
      have hn2 : 2 * (‖z‖ + ε / 2 + 1) ≤ (n : ℝ) := by
        calc 2 * (‖z‖ + ε / 2 + 1) ≤ (⌈2 * (‖z‖ + ε / 2 + 1)⌉₊ : ℝ) := Nat.le_ceil _
          _ ≤ (n : ℝ) := by exact_mod_cast hn
      have hzn : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h1 : ‖((n : ℂ) + 1)‖ - ‖z‖ ≤ ‖z + ((n : ℂ) + 1)‖ := by
          have h2 := norm_sub_le (z + ((n : ℂ) + 1)) z
          have h3 : (z + ((n : ℂ) + 1)) - z = ((n : ℂ) + 1) := by ring
          rw [h3] at h2
          linarith
        rw [hnormn1 n] at h1
        have hz0 := norm_nonneg z
        linarith
      have hdpos : (0 : ℝ) < ‖z + ((n : ℂ) + 1)‖ - ε / 2 := by
        have h0 : (0 : ℝ) < ((n : ℝ) + 1) / 2 := by positivity
        linarith
      rw [hu, Real.norm_eq_abs]
      simp only
      rw [abs_of_nonneg (by positivity)]
      calc (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (‖z + ((n : ℂ) + 1)‖ - ε / 2))
          ≤ (‖z‖ + ε / 2) / (((n : ℝ) + 1) * (((n : ℝ) + 1) / 2)) := by
            gcongr
        _ = 2 * (‖z‖ + ε / 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
            field_simp
  have hFdiff : ∀ n : ℕ, DifferentiableOn ℂ (F n) U := by
    intro n
    rw [hF]
    simp only
    intro w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    refine DifferentiableAt.sub (differentiableAt_const _) ?_
    have hne : w + (n : ℂ) + 1 ≠ 0 := by
      rw [add_assoc]
      exact hterm_ne n w hw
    have h1 : DifferentiableAt ℂ (fun v : ℂ => v + (n : ℂ) + 1) w := by
      fun_prop
    exact (differentiableAt_const (1 : ℂ)).div h1 hne
  have hkey := hasSum_deriv_of_summable_norm husum hFdiff hUopen hFle hzU
  have hFalt : ∀ n : ℕ, F n = fun w => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
    intro n
    funext w
    rw [hF]
    simp only
    rw [add_assoc]
  have hderiv_term : ∀ n : ℕ, deriv (F n) z = 1 / (z + ((n : ℂ) + 1)) ^ 2 := by
    intro n
    rw [hFalt n]
    have hne : z + ((n : ℂ) + 1) ≠ 0 := hterm_ne n z hzU
    have h1 : HasDerivAt (fun w : ℂ => w + ((n : ℂ) + 1)) 1 z := (hasDerivAt_id z).add_const _
    have h2 := h1.inv hne
    have h3 : HasDerivAt (fun w : ℂ => (w + ((n : ℂ) + 1))⁻¹)
        (-1 / (z + ((n : ℂ) + 1)) ^ 2) z := h2
    have h5 := h3.const_sub (1 / ((n : ℂ) + 1))
    have h6 : (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        = fun w : ℂ => 1 / ((n : ℂ) + 1) - 1 / (w + ((n : ℂ) + 1)) := by
      funext w
      simp [one_div]
    rw [← h6]
    have h7 : HasDerivAt (fun w : ℂ => 1 / ((n : ℂ) + 1) - (w + ((n : ℂ) + 1))⁻¹)
        (1 / (z + ((n : ℂ) + 1)) ^ 2) z := by
      have heq : 1 / (z + ((n : ℂ) + 1)) ^ 2 = -(-1 / (z + ((n : ℂ) + 1)) ^ 2) := by
        ring
      rw [heq]
      exact h5
    exact h7.deriv
  have hγc : ∀ w : ℂ, w ∈ U → (∑' n : ℕ, F n w)
      = Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    intro w hw
    exact (Zeta23.DigammaSeries.hasSum_digamma_series (hUsub hw)).tsum_eq
  have hsum_eq : (fun w : ℂ => ∑' n : ℕ, F n w)
      =ᶠ[nhds z] fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    exact hγc w hw
  have hz0 : z ≠ 0 := Complex.integerComplement.ne_zero hz
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓan : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact (hUsub hw) ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  have hψd : DifferentiableAt ℂ Complex.digamma z := hψan.differentiableAt
  have hinvd : HasDerivAt (fun w : ℂ => 1 / w) (-1 / z ^ 2) z := by
    have h1 := (hasDerivAt_id z).inv hz0
    have h2 : HasDerivAt (fun w : ℂ => w⁻¹) (-1 / z ^ 2) z := h1
    have h3 : (fun w : ℂ => 1 / w) = fun w : ℂ => w⁻¹ := by
      funext w
      rw [one_div]
    rw [h3]
    exact h2
  have hRHSd : HasDerivAt
      (fun w => Complex.digamma w + (Real.eulerMascheroniConstant : ℂ) + 1 / w)
      (deriv Complex.digamma z + (-1 / z ^ 2)) z := by
    exact (hψd.hasDerivAt.add_const ((Real.eulerMascheroniConstant : ℝ) : ℂ)).add hinvd
  have hderiv_sum : deriv (fun w : ℂ => ∑' n : ℕ, F n w) z
      = deriv Complex.digamma z + (-1 / z ^ 2) := by
    rw [hsum_eq.deriv_eq]
    exact hRHSd.deriv
  rw [hderiv_sum] at hkey
  have hfun : (fun n : ℕ => deriv (F n) z)
      = fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2 := funext hderiv_term
  rw [hfun] at hkey
  -- reindex: HasSum (f ∘ (+1)) s ↔ HasSum f (s + Σ_{i<1} f i), f n := 1/(z+n)²
  have hshift : (fun n : ℕ => 1 / (z + ((n : ℂ) + 1)) ^ 2)
      = fun n : ℕ => (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) (n + 1) := by
    funext n
    simp only
    push_cast
    ring_nf
  rw [hshift] at hkey
  have h0 : (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 0 = 1 / z ^ 2 := by
    simp
  have hfin := (hasSum_nat_add_iff (f := fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) 1).mp hkey
  have hval : deriv Complex.digamma z + -1 / z ^ 2
      + ∑ i ∈ Finset.range 1, (fun m : ℕ => 1 / (z + (m : ℂ)) ^ 2) i
      = deriv Complex.digamma z := by
    rw [Finset.sum_range_one]
    have h00 : (1 : ℂ) / (z + ((0 : ℕ) : ℂ)) ^ 2 = 1 / z ^ 2 := by
      norm_num
    rw [h00]
    ring
  rwa [hval] at hfin

/- `digamma_growth_strip` (coarse digamma growth on the EF strip) is proved as
   Zeta23.WeilEF.digamma_growth_strip in Zeta23/WeilEF/VerticalLine.lean, which is what
   the consumers (Horizontal.lean, FullLine.lean) use. -/

end Stirling
end Zeta23
