import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HolomorphicLog

/-!
# Holomorphic Logarithm of the Gamma Function

This file constructs the holomorphic logarithm of the Gamma function on the right half-plane.

The Gamma function is non-vanishing on the right half-plane {z | 0 < z.re}.
Since this domain is simply connected (it is convex), a holomorphic logarithm exists.


## Main Results

* `exists_logGamma`: Existence of a holomorphic function L such that exp L = Gamma.
* `logGamma`: A specific choice of logarithm satisfying `logGamma 1 = 0`.

-/

open Complex Set Filter Topology HolomorphicLog
open scoped Topology Real

noncomputable section

namespace GammaLog

/-- Gamma is non-vanishing on the right half-plane. -/
lemma Gamma_ne_zero_on_rightHalfPlane : ∀ z ∈ rightHalfPlane, Gamma z ≠ 0 := by
  intro z hz
  apply Complex.Gamma_ne_zero_of_re_pos
  exact hz

/-- Gamma is differentiable on the right half-plane. -/
lemma differentiableOn_Gamma_rightHalfPlane : DifferentiableOn ℂ Gamma rightHalfPlane := by
  intro z hz
  have hne : ∀ n : ℕ, z ≠ -↑n := fun n heq => by
    simp only [rightHalfPlane, mem_setOf_eq] at hz
    rw [heq] at hz
    simp only [neg_re, natCast_re, neg_pos] at hz
    exact (Nat.cast_nonneg n).not_gt hz
  exact (Complex.differentiableAt_Gamma z hne).differentiableWithinAt

/-- Existence of a holomorphic logarithm of Gamma on the right half-plane. -/
theorem exists_logGamma_aux : ∃ g : ℂ → ℂ, DifferentiableOn ℂ g rightHalfPlane ∧
    ∀ z ∈ rightHalfPlane, exp (g z) = Gamma z :=
  HolomorphicLog.exists_log_of_rightHalfPlane
    differentiableOn_Gamma_rightHalfPlane
    Gamma_ne_zero_on_rightHalfPlane

/-- The holomorphic logarithm of Gamma, normalized so `logGamma 1 = 0`. -/
def logGamma : ℂ → ℂ := fun z =>
  let g := Classical.choose exists_logGamma_aux
  g z - g 1

lemma differentiableOn_logGamma : DifferentiableOn ℂ logGamma rightHalfPlane := by
  let g := Classical.choose exists_logGamma_aux
  have hg : DifferentiableOn ℂ g rightHalfPlane := (Classical.choose_spec exists_logGamma_aux).1
  exact hg.sub_const (g 1)

lemma exp_logGamma {z : ℂ} (hz : z ∈ rightHalfPlane) : exp (logGamma z) = Gamma z := by
  let g := Classical.choose exists_logGamma_aux
  have hexp : ∀ w ∈ rightHalfPlane, exp (g w) = Gamma w := (Classical.choose_spec exists_logGamma_aux).2
  have h1 : 1 ∈ rightHalfPlane := by
    simp only [rightHalfPlane, mem_setOf_eq, one_re]
    exact zero_lt_one
  simp only [logGamma]
  rw [exp_sub, hexp z hz, hexp 1 h1]
  rw [Complex.Gamma_one, div_one]

lemma logGamma_one : logGamma 1 = 0 := by
  simp [logGamma]

end GammaLog
