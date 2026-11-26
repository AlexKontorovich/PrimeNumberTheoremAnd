module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts.lean — the even and smooth clauses of H-Γ [eq:mufacts].

Paper [eq:mufacts] asserts: "μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1,
μ(τ) = (1/2π)log(|τ|/2π) + O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus [eq:muints].

This file proves the EVEN and SMOOTH clauses against Mathlib's
Complex.digamma (= logDeriv Gamma):
  • digamma_conj : Γ'/Γ commutes with conjugation (from Complex.Gamma_conj +
    deriv_conj_conj);
  • mu_even : μ(−τ) = μ(τ);
  • mu_smooth : ContDiff ℝ ∞ μ (Γ is holomorphic hence analytic on Re > 0,
    so digamma is analytic there; compose with the affine line τ ↦ 1/4 + iτ/2).

The remaining clauses (monotonicity in |τ|, μ(0) > −1, the Stirling asymptotic
with O(τ⁻²), the derivative bound, and [eq:muints]) are the fields of
Zeta23.GammaFacts in Hypotheses.lean; they are proved in the files under
Zeta23/GammaFacts/ and assembled in Zeta23/GammaFacts/Complete.lean (`gammaFacts`).
The route: the digamma partial-fraction series
  digamma z = −γ_E + Σ_{n≥0} (1/(n+1) − 1/(n+z))  on ℂ ∖ (−ℕ)
(Zeta23/GammaFacts/Series.lean), from which monotonicity and μ ≥ μ(0) are termwise
monotonicity of (n+σ)/((n+σ)²+t²) in t², μ(0) > −1 is a finite partial-sum bound,
and the derivative bound is termwise differentiation; the Stirling clause uses a
vertical-line Stirling estimate (Zeta23/GammaFacts/StirlingVert.lean,
Zeta23/Analytic/Stirling.lean), and the integrals [eq:muints] follow by integrating
the asymptotic (Zeta23/GammaFacts/IntMu.lean).
-/
public import Zeta23.Defs
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace Zeta23

open Complex

open scoped ContDiff

/-- Γ'/Γ commutes with complex conjugation (from Γ(z̄) = Γ(z)̄). -/
theorem digamma_conj (z : ℂ) :
    Complex.digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Complex.digamma z) := by
  have hG : (starRingEnd ℂ) ∘ Complex.Gamma ∘ (starRingEnd ℂ) = Complex.Gamma := by
    funext w
    simp only [Function.comp_apply]
    rw [Complex.Gamma_conj]
    exact Complex.conj_conj _
  have hd : deriv Complex.Gamma ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (deriv Complex.Gamma z) := by
    conv_lhs => rw [← hG, deriv_conj_conj]
    simp only [Function.comp_apply, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply]
  rw [hd, Complex.Gamma_conj, ← map_div₀]

/-- [eq:mufacts], "μ is even": μ(−τ) = μ(τ). -/
theorem mu_even (τ : ℝ) : mu (-τ) = mu τ := by
  unfold mu
  have harg : (1 / 4 + Complex.I * ((-τ : ℝ) : ℂ) / 2 : ℂ)
      = (starRingEnd ℂ) (1 / 4 + Complex.I * (τ : ℂ) / 2) := by
    apply Complex.ext <;> simp [map_ofNat]
  rw [show ((-τ : ℝ) : ℂ) = -(τ : ℂ) by push_cast; ring] at harg ⊢
  rw [harg, digamma_conj]
  simp

/-- The open right half-plane where Γ is holomorphic and nonvanishing. -/
private lemma gamma_ne_neg_nat {z : ℂ} (hz : 0 < z.re) : ∀ m : ℕ, z ≠ -m := by
  intro m h
  rw [h] at hz
  simp only [Complex.neg_re, Complex.natCast_re] at hz
  exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz

private lemma analyticAt_digamma {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ Complex.digamma z := by
  have hU : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hGamD : DifferentiableOn ℂ Complex.Gamma {w : ℂ | 0 < w.re} := fun w hw =>
    (Complex.differentiableAt_Gamma w (gamma_ne_neg_nat hw)).differentiableWithinAt
  have hGamA := hGamD.analyticOnNhd hU
  have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := (hGamA z hz).deriv
  have h2 : AnalyticAt ℂ Complex.Gamma z := hGamA z hz
  have h3 : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero (gamma_ne_neg_nat hz)
  have h4 := h1.div h2 h3
  exact h4.congr (by
    filter_upwards with w
    rw [Complex.digamma_def, logDeriv_apply]
    rfl)

-- The set_option below is Mathlib's own workaround for instance-path defeq on
-- IsScalarTower ℝ ℂ ℂ (cf. Analysis/CStarAlgebra/ContinuousFunctionalCalculus/
-- RealImaginaryPart.lean, "fails to find IsScalarTower ℝ ℂ A").
set_option backward.isDefEq.respectTransparency false in
/-- [eq:mufacts], "μ is smooth": μ ∈ C^∞(ℝ). -/
theorem mu_smooth : ContDiff ℝ ∞ mu := by
  have hc : ContDiff ℝ ∞ (fun τ : ℝ => (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ)) := by
    have h1 : ContDiff ℝ ∞ (fun τ : ℝ => (τ : ℂ)) := Complex.ofRealCLM.contDiff
    have h2 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ)) := contDiff_const.mul h1
    have h3 : ContDiff ℝ ∞ (fun τ : ℝ => Complex.I * (τ : ℂ) / 2) := by
      simpa [div_eq_mul_inv] using h2.mul contDiff_const
    exact contDiff_const.add h3
  refine contDiff_iff_contDiffAt.mpr fun τ => ?_
  have hz : (0 : ℝ) < (1 / 4 + Complex.I * (τ : ℂ) / 2 : ℂ).re := by
    simp
  have h4' : AnalyticAt ℝ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    AnalyticAt.restrictScalars (analyticAt_digamma hz)
  have h4 : ContDiffAt ℝ ∞ Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2) :=
    h4'.contDiffAt
  have h5 : ContDiffAt ℝ ∞
      (fun τ : ℝ => Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)) τ :=
    h4.comp τ hc.contDiffAt
  have h6 : ContDiffAt ℝ ∞
      (fun τ : ℝ => (Complex.digamma (1 / 4 + Complex.I * (τ : ℂ) / 2)).re) τ :=
    (Complex.reCLM.contDiff.contDiffAt).comp τ h5
  have h7 : ContDiffAt ℝ ∞ mu τ := by
    have := (contDiffAt_const (c := (1 / (2 * Real.pi) : ℝ))).mul h6
    exact (this.sub contDiffAt_const)
  exact h7

end Zeta23
