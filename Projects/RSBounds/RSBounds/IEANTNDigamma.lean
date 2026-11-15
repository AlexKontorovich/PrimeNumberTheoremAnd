/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.IEANTNGamma.Analytic

/-!
# Reusing IEANTN's Gauss-series theorem

The proof is vendored from `teorth/IEANTN` at
`466b41b28ecc224398cf53a99c5fe9618131398b`, under Apache 2.0.
The imported files retain their original attribution and proof structure.
This module merely exposes the exact series without its auxiliary definition.
-/

namespace TernaryGoldbach.RSBounds.IEANTNDigamma

/-- The already-proved IEANTN Gauss representation, on the right half-plane. -/
theorem digamma_eq_gauss_series {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s = -(Real.eulerMascheroniConstant : ℂ) +
      ∑' k : ℕ, (((k : ℂ) + 1)⁻¹ - ((k : ℂ) + s)⁻¹) := by
  simpa only [GammaSolution.gaussSum, GammaSolution.gaussTerm] using
    GammaSolution.digamma_eq_gaussSum hs

/-- Absolute convergence is part of the imported proof, not an assumption. -/
theorem summable_gauss_series {s : ℂ} (hs : 0 < s.re) :
    Summable (fun k : ℕ => (((k : ℂ) + 1)⁻¹ - ((k : ℂ) + s)⁻¹)) := by
  change Summable (GammaSolution.gaussTerm s)
  exact GammaSolution.summable_gaussTerm
    (GammaSolution.ne_neg_natCast_of_mem (GammaSolution.mem_rightHalfPlane_iff.mpr hs))

end TernaryGoldbach.RSBounds.IEANTNDigamma
