/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFunctionalEquation

/-!
# Local API for Mathlib's completed Riemann zeta and xi functions

This file records basic local facts about Mathlib's `completedRiemannZeta`

`Λ(s) = Γ_ℝ(s) * ζ(s)`.

It also defines the classical entire Riemann xi function
`ξ(s) = s * (s - 1) * Λ(s) / 2` via the pole-removed expression
`(s * (s - 1) * Λ₀(s) + 1) / 2`.  This is the object whose genus-one Hadamard product is used in
Kadiri-style zero-free region arguments.  This file only supplies the elementary bridge facts; the
Hadamard product is specialized in `Mathlib.NumberTheory.LSeries.RiemannZetaHadamard`, while the
xi logarithmic-derivative zero-sum bridge is also recorded there under explicit convergence,
nonvanishing, and point-not-a-zero hypotheses.

## References

* [kadiri2005] for the explicit zero-free-region context motivating the xi/log-derivative bridge
-/

@[expose] public section

noncomputable section

open Complex

namespace Complex

/-! ## The entire Riemann xi function -/

/-- The classical entire Riemann xi function, defined using the pole-removed completed zeta
function `Λ₀`.

Away from `0` and `1`, this agrees with `s * (s - 1) * completedRiemannZeta s / 2`; see
`riemannXi_eq_mul_completedRiemannZeta`. -/
noncomputable def riemannXi (s : ℂ) : ℂ :=
  (s * (s - 1) * completedRiemannZeta₀ s + 1) / 2

/-- The normalization value `ξ(0) = 1 / 2`, immediate from the pole-removed definition. -/
theorem riemannXi_zero : riemannXi 0 = 1 / 2 := by
  simp [riemannXi]

/-- The Riemann xi function is not identically zero. -/
theorem riemannXi_nontrivial : ∃ s : ℂ, riemannXi s ≠ 0 := by
  refine ⟨0, ?_⟩
  simp [riemannXi_zero]

/-- The Riemann xi function is entire. -/
theorem differentiable_riemannXi : Differentiable ℂ riemannXi := by
  exact (((differentiable_id.mul (differentiable_id.sub (differentiable_const (1 : ℂ)))).mul
    differentiable_completedZeta₀).add (differentiable_const (1 : ℂ))).div_const 2

/-- Away from the poles of `completedRiemannZeta`, `riemannXi` is the classical product
`s * (s - 1) * completedRiemannZeta s / 2`. -/
theorem riemannXi_eq_mul_completedRiemannZeta {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = s * (s - 1) * completedRiemannZeta s / 2 := by
  rw [riemannXi, completedRiemannZeta_eq]
  have h1ms : 1 - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hs1)
  field_simp [hs0, h1ms]
  ring

/-- Functional equation for the Riemann xi function. -/
theorem riemannXi_one_sub (s : ℂ) : riemannXi (1 - s) = riemannXi s := by
  rw [riemannXi, riemannXi, completedRiemannZeta₀_one_sub]
  ring

end Complex
