import RSBounds.PsiFinite.Final

/-!
# Audit of the finite ψ bounds

The two statements are restated from scratch, with Mathlib's `Chebyshev.psi`,
and closed by the proved theorems; `#print axioms` must list only `propext`,
`Classical.choice`, `Quot.sound`.

    cd Projects/RSBounds && lake env lean verification/PsiFiniteCheckAudit.lean
-/

theorem audit_psi_abs_sub_le_four_fifths_sqrt {x : ℝ} (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x :=
  PsiFinite.psi_abs_sub_le_four_fifths_sqrt h₁ h₂

theorem audit_psi_abs_sub_le_sqrt {x : ℝ} (h₁ : 8 < x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x :=
  PsiFinite.psi_abs_sub_le_sqrt h₁ h₂

#print axioms audit_psi_abs_sub_le_four_fifths_sqrt
#print axioms audit_psi_abs_sub_le_sqrt
