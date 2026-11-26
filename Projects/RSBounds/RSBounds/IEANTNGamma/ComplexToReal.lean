/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNGamma.RealAsymptotic
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Glue: `Complex.digamma` on the real axis

Stage 1 proves `|ψ(x) - log x| ≤ 1/x` for the *real* function `deriv (fun t ↦ log (Γ t))`, because
Mathlib has no `Real.digamma` and the convexity argument is real-variable throughout. The node's
conclusion is about `Complex.digamma`. This file is the one step between them:

  `Complex.digamma x = ↑(deriv (fun t ↦ Real.log (Real.Gamma t)) x)` for real `x > 0`.

Both sides are `Γ'/Γ`; the content is that `Complex.Gamma` differentiated along the real axis is
the real `Γ'`, which is not automatic — a complex-differentiable function agreeing with a real one
on `ℝ` has a complex derivative that *happens* to be real there, and saying so takes an argument.

**Mathlib has that argument and keeps it `private`.** `HasDerivAt.complex_of_real` in
`NumberTheory/Harmonic/GammaDeriv.lean` is exactly it, marked `private`, so it cannot be imported
and is reproved here verbatim. If any of this goes upstream, that lemma losing its `private` is
the first thing to ask for; `Complex.digamma_ofReal` below is the second.
-/

namespace GammaSolution

open Complex

/-- A complex-differentiable `f` agreeing with a real `g` on `ℝ` has `g`'s derivative there.

Reproved from Mathlib's `private HasDerivAt.complex_of_real`. -/
theorem hasDerivAt_complex_of_real {f : ℂ → ℂ} {g : ℝ → ℝ} {g' s : ℝ}
    (hf : DifferentiableAt ℂ f s) (hg : HasDerivAt g g' s) (hfg : ∀ s : ℝ, f ↑s = ↑(g s)) :
    HasDerivAt f ↑g' s := by
  refine HasDerivAt.congr_deriv hf.hasDerivAt ?_
  rw [← (funext hfg ▸ hf.hasDerivAt.comp_ofReal.deriv :)]
  exact hg.ofReal_comp.deriv

/-- A positive real is not a pole of `Γ`. -/
theorem ofReal_ne_neg_natCast {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) := by
  intro h
  have hx' : x = -(m : ℝ) := by exact_mod_cast h
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

theorem differentiableAt_real_Gamma {x : ℝ} (hx : 0 < x) : DifferentiableAt ℝ Real.Gamma x :=
  Real.differentiableAt_Gamma (fun m ↦ by
    intro hcon
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hcon] at hx
    linarith)

/-- `Γ` differentiated along the real axis is the real `Γ'`. -/
theorem hasDerivAt_Gamma_ofReal {x : ℝ} (hx : 0 < x) :
    HasDerivAt Complex.Gamma ((deriv Real.Gamma x : ℝ) : ℂ) (x : ℂ) :=
  hasDerivAt_complex_of_real
    (Complex.differentiableAt_Gamma _ (ofReal_ne_neg_natCast hx))
    (differentiableAt_real_Gamma hx).hasDerivAt
    Complex.Gamma_ofReal

/-- The real logarithmic derivative of `Γ`, in the form `Γ'/Γ`. -/
theorem deriv_log_Gamma_eq {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x = deriv Real.Gamma x / Real.Gamma x := by
  have hpos := Real.Gamma_pos_of_pos hx
  have h := (Real.hasDerivAt_log hpos.ne').comp x (differentiableAt_real_Gamma hx).hasDerivAt
  simp only [Function.comp_def] at h
  rw [h.deriv]
  ring

/-- **`Complex.digamma` on the positive real axis is Stage 1's real derivative.** -/
theorem digamma_ofReal {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = ((deriv (fun t ↦ Real.log (Real.Gamma t)) x : ℝ) : ℂ) := by
  have hpos := Real.Gamma_pos_of_pos hx
  rw [Complex.digamma_def, logDeriv_apply, (hasDerivAt_Gamma_ofReal hx).deriv,
    Complex.Gamma_ofReal, deriv_log_Gamma_eq hx]
  push_cast
  ring

end GammaSolution
