module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Defs.lean — shared vocabulary for the Riemann–von Mangoldt argument.

Target: Zeta23.RiemannVonMangoldt Zeta23.zetaZeroConfig (Zeta23/Hypotheses.lean), i.e.
  main        : ∃ C T₀, ∀ T ≥ T₀, |N(T,2T) − (T/2π)·ell1 T| ≤ C log T      ([Tit86, Thm 9.4])
  local_count : ∃ A₀ ≥ 1, ∀ t, N(t,t+1] ≤ A₀ log(|t|+3)                      ([Tit86, Thm 9.2]),
                see Zeta23.RvM.zetaZeroConfig_local_count (Zeta23/RvM/LocalCount.lean).
Route for main: argument principle for Λ = completedRiemannZeta
on the rectangle [−1,2]×[T₁,T₂] at zero-free ordinates, folded onto its right half L by
Λ(1−s̄) = conj Λ(s):  N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ;  then Λ'/Λ = ζ'/ζ + Γℝ'/Γℝ (Γℝ = Complex.Gammaℝ,
π^{−s/2}Γ(s/2)), and (1/π)·Im ∫_L Γℝ'/Γℝ = ∫_{T₁}^{T₂} μ exactly (μ = Zeta23.mu), whose asymptotic
∫_T^{2T} μ = T·ell1 T/(2π) + O(1/T) is GammaFacts.int_mu. The ζ'/ζ part is O(log T)
(Backlund on the horizontals, |log ζ| ≤ log 3 on σ = 2). Hence: riemannVonMangoldt (hΓ : GammaFacts).
-/
public import Zeta23.Statement.SeamClosed
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.LogDeriv

@[expose] public section

open Complex

noncomputable section

namespace Zeta23.RvM

/-- T is a zero-free ordinate: no nontrivial zero of ζ has Im ρ = T. -/
def GoodHeight (T : ℝ) : Prop := ∀ ρ : ℂ, IsNontrivialZero ρ → ρ.im ≠ T

/-- The right half-contour L = [½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂] integral of F, as three interval
integrals (bottom rightwards, right side upwards with ds = i dt, top leftwards). -/
def halfContour (F : ℂ → ℂ) (T₁ T₂ : ℝ) : ℂ :=
  (∫ σ in (1/2:ℝ)..2, F (σ + T₁ * I)) + (∫ t in T₁..T₂, F (2 + t * I)) * I
    - ∫ σ in (1/2:ℝ)..2, F (σ + T₂ * I)

lemma halfContour_add (F G : ℂ → ℂ) (T₁ T₂ : ℝ)
    (hb : IntervalIntegrable (fun σ : ℝ => F (σ + T₁ * I)) MeasureTheory.volume (1/2) 2)
    (hb' : IntervalIntegrable (fun σ : ℝ => G (σ + T₁ * I)) MeasureTheory.volume (1/2) 2)
    (hr : IntervalIntegrable (fun t : ℝ => F (2 + t * I)) MeasureTheory.volume T₁ T₂)
    (hr' : IntervalIntegrable (fun t : ℝ => G (2 + t * I)) MeasureTheory.volume T₁ T₂)
    (ht : IntervalIntegrable (fun σ : ℝ => F (σ + T₂ * I)) MeasureTheory.volume (1/2) 2)
    (ht' : IntervalIntegrable (fun σ : ℝ => G (σ + T₂ * I)) MeasureTheory.volume (1/2) 2) :
    halfContour (fun s => F s + G s) T₁ T₂ = halfContour F T₁ T₂ + halfContour G T₁ T₂ := by
  unfold halfContour
  rw [intervalIntegral.integral_add hb hb', intervalIntegral.integral_add hr hr',
    intervalIntegral.integral_add ht ht']
  ring

end Zeta23.RvM
