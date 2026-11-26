module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/GammaSide.lean — the Γ-factor side of the folded contour is
EXACTLY the paper's ∫μ:  (1/π)·Im ∫_L Γℝ'/Γℝ ds = ∫_{T₁}^{T₂} μ(t) dt  for 0 < T₁,
because Γℝ'/Γℝ is holomorphic on Re s > 0 (Cauchy–Goursat on [½,2]×[T₁,T₂] moves L to the critical-line
segment) and Re Γℝ'/Γℝ(½+it) = ½ Re ψ(¼+it/2) − ½ log π = π·μ(t)  (Γℝ(s) = π^{−s/2}Γ(s/2), μ = Zeta23.mu).
-/
public import Zeta23.RvM.Defs
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace Zeta23.RvM

/-- the open right half-plane -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

lemma Gamma_half_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
  apply Complex.differentiableAt_Gamma
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith

lemma Gammaℝ_differentiableOn : DifferentiableOn ℂ Complex.Gammaℝ rightHalfPlane := by
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s := by
    apply DifferentiableAt.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  have : Complex.Gammaℝ = fun s => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  rw [this]
  exact h1.mul h2

lemma Gammaℝ_analyticOnNhd : AnalyticOnNhd ℂ Complex.Gammaℝ rightHalfPlane :=
  Gammaℝ_differentiableOn.analyticOnNhd isOpen_rightHalfPlane

/-- logDeriv Γℝ is holomorphic on Re s > 0. -/
lemma logDeriv_Gammaℝ_differentiableOn : DifferentiableOn ℂ (logDeriv Complex.Gammaℝ) rightHalfPlane := by
  have hA := Gammaℝ_analyticOnNhd
  have hd : DifferentiableOn ℂ (deriv Complex.Gammaℝ) rightHalfPlane := hA.deriv.differentiableOn
  have : logDeriv Complex.Gammaℝ = fun s => deriv Complex.Gammaℝ s / Complex.Gammaℝ s := by
    funext s; rfl
  rw [this]
  exact hd.div hA.differentiableOn fun s hs => Complex.Gammaℝ_ne_zero_of_re_pos hs

/-- logDeriv Γℝ(s) = −(log π)/2 + ½ ψ(s/2) on Re s > 0 (ψ = Complex.digamma = Γ'/Γ). -/
theorem logDeriv_Gammaℝ {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hf : (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, hπ, false_and, not_false_eq_true]
  have hg : (fun s : ℂ => Complex.Gamma (s / 2)) s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  rw [e, logDeriv_fun_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := fun s : ℂ => Complex.Gamma (s / 2)) s hf hg hdf hdg]
  -- first factor
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
      have : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).neg.div_const (2:ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply, hder.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  -- second factor
  have h2 : logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) s = (1/2 : ℂ) * Complex.digamma (s / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s)
      (Gamma_half_differentiableAt hs) (by fun_prop)
    rw [show (Complex.Gamma ∘ fun s : ℂ => s / 2) = fun s => Complex.Gamma (s / 2) from rfl] at this
    rw [this, Complex.digamma_def]
    have : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]

/-- on the critical line: Re(logDeriv Γℝ(½+it)) = π·μ(t). -/
theorem re_logDeriv_Gammaℝ_half (t : ℝ) :
    (logDeriv Complex.Gammaℝ (1/2 + t * I)).re = Real.pi * mu t := by
  rw [logDeriv_Gammaℝ (by simp)]
  have : ((1:ℂ)/2 + t * I) / 2 = 1 / 4 + Complex.I * t / 2 := by ring
  rw [this, mu]
  simp only [Complex.add_re, Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re, Complex.mul_re,
    Complex.one_re]
  have hπ := Real.pi_ne_zero
  field_simp
  simp
  ring

/-- (M4) the Γ-side identity: for 0 < T₁ and any T₂,
(1/π)·Im(halfContour (logDeriv Γℝ) T₁ T₂) = ∫_{T₁}^{T₂} μ. -/
theorem gamma_side {T₁ T₂ : ℝ} (_h0 : 0 < T₁) (_h0' : 0 < T₂) :
    (1 / Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im = ∫ t in T₁..T₂, mu t := by
  set F := logDeriv Complex.Gammaℝ with hF
  -- Cauchy–Goursat on the rectangle [1/2, 2] × [T₁, T₂]
  have hrect : (Set.uIcc (1/2:ℝ) 2 ×ℂ Set.uIcc T₁ T₂) ⊆ rightHalfPlane := by
    rintro s ⟨hre, -⟩
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hre
    show 0 < s.re
    have := hre.1
    linarith [this]
  have hCG := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F (1/2 + T₁ * I) (2 + T₂ * I)
    (logDeriv_Gammaℝ_differentiableOn.mono (by simpa using hrect))
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, one_im, mul_im, zero_add, div_ofNat_re, div_ofNat_im, zero_div,
    re_ofNat, im_ofNat] at hCG
  have hhc : halfContour F T₁ T₂ = I * ∫ y : ℝ in T₁..T₂, F (1/2 + y * I) := by
    unfold halfContour
    have hthis := hCG
    simp only [smul_eq_mul] at hthis
    have hc : ((1/2 : ℝ) : ℂ) = (1/2 : ℂ) := by norm_num
    simp only [hc] at hthis
    -- bottom - top + I*right - I*left = 0
    linear_combination hthis
  rw [hhc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  -- Re ∫ = ∫ Re
  have hcont : Continuous fun y : ℝ => F (1/2 + y * I) := by
    have hd := logDeriv_Gammaℝ_differentiableOn
    have : Continuous fun y : ℝ => ((1:ℂ)/2 + y * I) := by fun_prop
    refine (hd.continuousOn.comp_continuous this fun y => ?_)
    show 0 < ((1:ℂ)/2 + y * I).re
    simp
  rw [show ((∫ y : ℝ in T₁..T₂, F (1/2 + y * I)).re) = ∫ y : ℝ in T₁..T₂, (F (1/2 + y * I)).re from
    (Complex.reCLM.intervalIntegral_comp_comm (hcont.intervalIntegrable _ _)).symm]
  simp_rw [hF, re_logDeriv_Gammaℝ_half]
  rw [intervalIntegral.integral_const_mul]
  field_simp

/-! ### helpers for the assembly -/

/-- μ is continuous (given H-Γ's smoothness field). -/
theorem mu_continuous (hΓ : Zeta23.GammaFacts) : Continuous mu :=
  hΓ.smooth.continuous

/-- |μ(τ)| ≪ log(τ+3) for τ ≥ 1, from H-Γ's Stirling field. -/
theorem mu_le_log (hΓ : Zeta23.GammaFacts) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
    |mu τ| ≤ C * Real.log (τ + 3) := by
  obtain ⟨C₀, hC₀⟩ := hΓ.stirling
  have hlog2π : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  refine ⟨1 + |C₀| + Real.log (2 * Real.pi),
    by linarith [abs_nonneg C₀], fun τ hτ => ?_⟩
  have hτ0 : (0:ℝ) < τ := by linarith
  have h1 := hC₀ τ (by rw [abs_of_pos hτ0]; exact hτ)
  rw [abs_of_pos hτ0] at h1
  obtain ⟨hl, hr⟩ := abs_le.mp h1
  have hlog3 : 1 ≤ Real.log (τ + 3) := by
    rw [← Real.log_exp 1]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_d9; linarith
  have hlogτ0 : 0 ≤ Real.log τ := Real.log_nonneg hτ
  have hlogτ : Real.log τ ≤ Real.log (τ + 3) := Real.log_le_log hτ0 (by linarith)
  have hdiv : Real.log (τ / (2 * Real.pi)) = Real.log τ - Real.log (2 * Real.pi) :=
    Real.log_div (by linarith) (by positivity)
  rw [hdiv] at hl hr
  have hC₀τ : |C₀ / τ ^ 2| ≤ |C₀| := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
    apply div_le_self (abs_nonneg _) (by nlinarith)
  obtain ⟨hCl, hCr⟩ := abs_le.mp hC₀τ
  have h2π : 1 / (2 * Real.pi) ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [Real.pi_gt_three]
  have h2π0 : 0 < 1 / (2 * Real.pi) := by positivity
  rw [abs_le]
  constructor
  · -- lower bound: mu τ ≥ (1/2π)(log τ − log 2π) − C₀/τ² ≥ −(…)·log(τ+3)
    have e1 : -(Real.log (2 * Real.pi)) ≤ 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) := by
      nlinarith
    nlinarith
  · have e2 : 1 / (2 * Real.pi) * (Real.log τ - Real.log (2 * Real.pi)) ≤ Real.log (τ + 3) := by
      nlinarith
    nlinarith

end Zeta23.RvM
