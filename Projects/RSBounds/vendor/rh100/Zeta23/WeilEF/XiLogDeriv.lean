module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Zeta23.Statement

@[expose] public section

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology

/-- Γℝ(s) = π^{−s/2} Γ(s/2) is complex-differentiable at every s with Re s > 0. -/
lemma differentiableAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const _)
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have : Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) := funext Gammaℝ_def
  rw [this]
  exact h1.mul h2

/-- Γℝ is analytic at every point of the right half-plane. -/
lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (differentiableAt_Gammaℝ hu).differentiableWithinAt)
    (hopen.mem_nhds hs)

/-- On the right half-plane, Λ = Γℝ · ζ (as germs). -/
lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp

/-- ζ is analytic at every s ≠ 1. -/
lemma analyticAt_riemannZeta {s : ℂ} (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s :=
  DifferentiableOn.analyticAt (s := ({1}ᶜ : Set ℂ))
    (fun _ hu => (differentiableAt_riemannZeta hu).differentiableWithinAt)
    (isOpen_compl_singleton.mem_nhds hs)

/-- On the right half-plane away from 1 and from the zeros of ζ:  Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ. -/
theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hstrip : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hstrip
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hstrip) hζ (differentiableAt_Gammaℝ hstrip)
    (differentiableAt_riemannZeta hs1)

/-- Functional equation for the log-derivative: Λ'/Λ(1−s) = −Λ'/Λ(s)  (from Λ(1−s) = Λ(s)). -/
theorem logDeriv_completedZeta_one_sub (s : ℂ) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hcomp : completedRiemannZeta = completedRiemannZeta ∘ (fun u : ℂ => 1 - u) := by
    funext u; simp [completedRiemannZeta_one_sub]
  have hd : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta (sub_ne_zero.mpr (Ne.symm hs1)) (by
      intro h; apply hs0; linear_combination -h)
  have hg : DifferentiableAt ℂ (fun u : ℂ => 1 - u) s := (differentiableAt_const _).sub differentiableAt_id
  have key := logDeriv_comp (x := s) hd hg
  rw [← hcomp] at key
  have hderiv : deriv (fun u : ℂ => 1 - u) s = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [key, hderiv]
  ring

/-- In the open critical strip the zeros of Λ are exactly the nontrivial zeros of ζ, with the same
analytic order (Γℝ is analytic and nonvanishing there). -/
theorem completedZeta_zeros_strip {ρ : ℂ} (h : 0 < ρ.re) (h' : ρ.re < 1) :
    (completedRiemannZeta ρ = 0 ↔ IsNontrivialZero ρ) ∧
    analyticOrderAt completedRiemannZeta ρ = analyticOrderAt riemannZeta ρ := by
  have hρ1 : ρ ≠ 1 := fun e => by simp [e] at h'
  have hΓ : Gammaℝ ρ ≠ 0 := Gammaℝ_ne_zero_of_re_pos h
  have hev := completedZeta_eventuallyEq_mul h
  have hval : completedRiemannZeta ρ = Gammaℝ ρ * riemannZeta ρ := hev.eq_of_nhds
  have hΓan := analyticAt_Gammaℝ h
  have hζan := analyticAt_riemannZeta hρ1
  refine ⟨?_, ?_⟩
  · rw [hval, mul_eq_zero, IsNontrivialZero]
    constructor
    · rintro (hΓ0 | hz)
      · exact absurd hΓ0 hΓ
      · exact ⟨hz, h, h'⟩
    · rintro ⟨hz, -, -⟩
      exact Or.inr hz
  · rw [analyticOrderAt_congr hev]
    have hmul := analyticOrderAt_mul hΓan hζan
    rw [show (Gammaℝ * riemannZeta) = (fun u => Gammaℝ u * riemannZeta u) from rfl] at hmul
    rw [hmul, hΓan.analyticOrderAt_eq_zero.mpr hΓ, zero_add]

end WeilEF
end Zeta23
