/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.DivisorIndex
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

/-!
# Local nonvanishing for divisor-indexed Weierstrass factors

This file provides local nonvanishing statements for the factors
`weierstrassFactor m (z / a)` indexed by `divisorZeroIndex₀`, on punctured balls that isolate a
single divisor-support point.
-/

@[expose] public section

open Set

namespace Complex.Hadamard

lemma divisorZeroIndex₀_val_eq_of_mem_ball
    {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ))
    (hp : divisorZeroIndex₀_val p ∈ Metric.ball z₀ ε) :
    divisorZeroIndex₀_val p = z₀ := by
  have hsupp : divisorZeroIndex₀_val p ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
    divisorZeroIndex₀_val_mem_divisor_support' (p := p)
  have : divisorZeroIndex₀_val p ∈
      Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := ⟨hp, hsupp⟩
  simp [hball] at this
  simpa using this

lemma weierstrassFactor_div_ne_zero_on_ball_of_val_ne
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀})
    (p : divisorZeroIndex₀ f (Set.univ : Set ℂ)) (hp : divisorZeroIndex₀_val p ≠ z₀) :
    ∀ z ∈ Metric.ball z₀ ε, weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hzball h0
  have hz_eq : z = divisorZeroIndex₀_val p := by
    have hdiv1 : z / divisorZeroIndex₀_val p = 1 := by
      simpa [weierstrassFactor_eq_zero_iff (m := m)] using h0
    have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
    exact (div_eq_one_iff_eq ha).1 hdiv1
  have hz_support : z ∈ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support := by
    simp [hz_eq]
  have hz0 : z = z₀ := by
    have : z ∈ Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support :=
      ⟨hzball, hz_support⟩
    simp [hball] at this
    simpa using this
  have : divisorZeroIndex₀_val p = z₀ := by
    calc
      divisorZeroIndex₀_val p = z := by simp [hz_eq]
      _ = z₀ := hz0
  exact hp this

lemma weierstrassFactor_div_ne_zero_on_ball_punctured
    (m : ℕ) {f : ℂ → ℂ} {z₀ : ℂ} {ε : ℝ}
    (hball : Metric.ball z₀ ε ∩ (MeromorphicOn.divisor f (Set.univ : Set ℂ)).support = {z₀}) :
    ∀ z ∈ Metric.ball z₀ ε, z ≠ z₀ →
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
        weierstrassFactor m (z / divisorZeroIndex₀_val p) ≠ 0 := by
  intro z hz hz0 p
  by_cases hp : divisorZeroIndex₀_val p = z₀
  · have hz1 : z / divisorZeroIndex₀_val p ≠ (1 : ℂ) := by
      have ha : divisorZeroIndex₀_val p ≠ 0 := divisorZeroIndex₀_val_ne_zero p
      simpa [hp] using (mt (div_eq_one_iff_eq ha).1 (by simpa [hp] using hz0))
    exact _root_.Complex.weierstrassFactor_ne_zero_of_ne_one (m := m) hz1
  · exact weierstrassFactor_div_ne_zero_on_ball_of_val_ne (m := m) (f := f) (z₀ := z₀)
        (ε := ε) hball p (by simpa using hp) z hz

end Complex.Hadamard
