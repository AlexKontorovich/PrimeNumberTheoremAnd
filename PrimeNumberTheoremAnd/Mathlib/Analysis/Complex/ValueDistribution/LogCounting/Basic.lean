/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus, Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Extra logarithmic counting API

This file hosts the WF `LogCounting.Basic` additions needed by the staged Hadamard overlay.
-/

@[expose] public section

open Filter Function MeromorphicOn Metric Real Set

namespace Function.locallyFinsuppWithin

variable {E : Type*} [NormedAddCommGroup E]

/-!
### Support of `toClosedBall`

On the closed ball of radius `|r|`, evaluation agrees with the original function; support points
lie in that ball and correspond bijectively with support points of the original function inside it.
-/

/-- A support point of `toClosedBall r D` lies in the closed ball of radius `|r|`. -/
lemma norm_le_abs_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : ‖z‖ ≤ |r| := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := (toClosedBall r D).supportWithinDomain hz
  simpa [mem_closedBall, dist_zero_right] using hz_ball

/-- If `‖z‖ ≤ |r|`, then `toClosedBall r D` agrees with `D` at `z`. -/
lemma toClosedBall_eval_eq_of_norm_le_abs {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : ‖z‖ ≤ |r|) : toClosedBall r D z = D z := by
  have hz_ball : z ∈ closedBall (0 : E) |r| := by
    simpa [mem_closedBall, dist_zero_right] using hz
  simpa using toClosedBall_eval_within (f := D) hz_ball

/-- Support inside the ball is unchanged by restriction to the closed ball. -/
lemma mem_toClosedBall_support_of_mem_support_of_norm_le_abs
    {D : locallyFinsupp E ℤ} {r : ℝ} {z : E} (hzD : z ∈ D.support) (hzR : ‖z‖ ≤ |r|) :
    z ∈ (toClosedBall r D).support := by
  rw [Function.mem_support]
  rw [toClosedBall_eval_eq_of_norm_le_abs hzR]
  rwa [Function.mem_support] at hzD

/-- Support points of `toClosedBall r D` lie in the support of `D`. -/
lemma mem_support_of_mem_toClosedBall_support {D : locallyFinsupp E ℤ} {r : ℝ} {z : E}
    (hz : z ∈ (toClosedBall r D).support) : z ∈ D.support := by
  have hnorm : ‖z‖ ≤ |r| := norm_le_abs_of_mem_toClosedBall_support hz
  rw [Function.mem_support] at hz ⊢
  rw [toClosedBall_eval_eq_of_norm_le_abs hnorm] at hz
  exact hz

/-- Total multiplicity of nonzero support points inside the closed ball of radius `|R|`. -/
noncomputable def massClosedBall₀ {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    (D : locallyFinsupp E ℤ) (R : ℝ) : ℝ := by
  classical
  exact
    (((finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset).filter
      (fun z => z ≠ (0 : E))).sum fun z => (D z : ℝ)

/-- The nonzero mass in closed balls is monotone in the radius for non-negative functions. -/
lemma massClosedBall₀_mono {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {D : locallyFinsupp E ℤ} (hD : 0 ≤ D) {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    massClosedBall₀ D R₁ ≤ massClosedBall₀ D R₂ := by
  classical
  have hR₂ : 0 ≤ R₂ := le_trans hR₁ hR₁₂
  have habs₁ : |R₁| = R₁ := abs_of_nonneg hR₁
  have habs₂ : |R₂| = R₂ := abs_of_nonneg hR₂
  let SR (R : ℝ) : Finset E :=
    (finiteSupport (toClosedBall R D) (isCompact_closedBall (0 : E) |R|)).toFinset
  let S (R : ℝ) : Finset E := (SR R).filter fun z : E => z ≠ 0
  have hsub : S R₁ ⊆ S R₂ := by
    intro z hz
    have hzSR₁ : z ∈ SR R₁ := (Finset.mem_filter.1 hz).1
    have hz0 : z ≠ 0 := (Finset.mem_filter.1 hz).2
    have hz_sup₁ : z ∈ (toClosedBall R₁ D).support := by
      exact (finiteSupport (toClosedBall R₁ D) (isCompact_closedBall (0 : E) |R₁|)).mem_toFinset.1
        hzSR₁
    have hz_norm₁ : ‖z‖ ≤ R₁ := by
      have h := norm_le_abs_of_mem_toClosedBall_support hz_sup₁
      simpa [habs₁] using h
    have hz_norm₂ : ‖z‖ ≤ R₂ := le_trans hz_norm₁ hR₁₂
    have hz_norm₂_abs : ‖z‖ ≤ |R₂| := by simpa [habs₂] using hz_norm₂
    have hzD : z ∈ D.support := mem_support_of_mem_toClosedBall_support hz_sup₁
    have hz_sup₂ : z ∈ (toClosedBall R₂ D).support :=
      mem_toClosedBall_support_of_mem_support_of_norm_le_abs hzD hz_norm₂_abs
    have hzSR₂ : z ∈ SR R₂ := by
      exact (finiteSupport (toClosedBall R₂ D) (isCompact_closedBall (0 : E) |R₂|)).mem_toFinset.2
        hz_sup₂
    exact Finset.mem_filter.2 ⟨hzSR₂, hz0⟩
  have hterm_nonneg : ∀ z ∈ S R₂, 0 ≤ (D z : ℝ) := by
    intro z _hz
    exact_mod_cast hD z
  simpa [massClosedBall₀, SR, S] using
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun z hz₂ _hznot => hterm_nonneg z hz₂)

end Function.locallyFinsuppWithin

namespace Function.locallyFinsuppWithin

/-- Jensen's formula for the zero-divisor of an entire function on `ℂ`. -/
theorem logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    {R : ℝ} {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hR : R ≠ 0) :
    logCounting (divisor f ⊤) R =
      circleAverage (log ‖f ·‖) 0 R - log ‖meromorphicTrailingCoeffAt f 0‖ := by
  have hmero : Meromorphic f := fun z => (hf.analyticAt z).meromorphicAt
  simpa [top_eq_univ] using
    logCounting_divisor_eq_circleAverage_sub_const (f := f) hmero hR

end Function.locallyFinsuppWithin
