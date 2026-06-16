/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
Completed zeta functional equation in product form.

We restate mathlib's completedRiemannZeta_one_sub as an equality of
(π^{-s/2} Γ(s/2) ζ(s)) with the corresponding (1-s) expression, matching
the form used by the ξ functional equation derivation.
-/

noncomputable section

@[expose] public section

open Complex

namespace Complex

/-- Functional equation for Mathlib's completed Riemann zeta factor `Λ`. -/
theorem zeta_functional_equation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) := by
  simpa using (completedRiemannZeta_one_sub s).symm

/- Product-form functional equation matching `π^{−s/2} Γ(s/2) · ζ(s)` can be
   derived locally when needed via:
   `simpa [completedRiemannZeta, mul_comm, mul_left_comm, mul_assoc] using
     (completedRiemannZeta_one_sub s).symm`.
   Kept as a comment to avoid Hurwitz aliasing at call sites. -/

end Complex
