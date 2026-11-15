import Mathlib

/- Independent Mathlib-only statements of the finite ψ bounds of
`docs/PsiFiniteCheck.md`. The `sorry`s are deliberate: a challenge states, it
does not prove. Neither the solution nor its audit imports this module. -/

namespace PsiFinite

theorem psi_abs_sub_le_four_fifths_sqrt {x : ℝ} (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by sorry

theorem psi_abs_sub_le_sqrt {x : ℝ} (h₁ : 8 < x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x := by sorry

end PsiFinite
