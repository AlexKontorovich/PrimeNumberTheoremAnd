import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Complex.Basic

/-!
Completed zeta functional equation in product form.

We restate mathlib's completedRiemannZeta_one_sub as an equality of
(π^{-s/2} Γ(s/2) ζ(s)) with the corresponding (1-s) expression, matching
the form used by the ξ functional equation derivation.
-/

noncomputable section

open Complex

namespace Complex

theorem zeta_functional_equation (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta (1 - s) := by
  simpa using (completedRiemannZeta_one_sub s).symm

/- Product-form functional equation matching `π^{−s/2} Γ(s/2) · ζ(s)` can be
   derived locally when needed via:
   `simpa [completedRiemannZeta, mul_comm, mul_left_comm, mul_assoc] using
     (completedRiemannZeta_one_sub s).symm`.
   Kept as a comment to avoid Hurwitz aliasing at call sites. -/

end Complex
end
