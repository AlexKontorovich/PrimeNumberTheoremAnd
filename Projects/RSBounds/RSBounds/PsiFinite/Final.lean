import RSBounds.PsiFinite.SmallRange
import RSBounds.PsiFinite.Campaign.T1.Assembly

/-!
# |ψ(x) − x| ≤ (4/5)√x on [1500, 10^10] and |ψ(x) − x| ≤ √x on (8, 10^10]

T1 is Ramaré, Acta Arith. 159 (2013), eq. (3.2), p. 116 (see
`docs/FinitePsiCertification.md`). Below `10^4`: the kernel walk of
`SmallRange`; from `10^4` to `10^10`: the 38,186 kernel-checked segments of
`Campaign/T1`, chained in `Campaign.T1.chain`. See `docs/PsiFiniteCheck.md`.
-/

namespace PsiFinite

theorem psi_abs_sub_le_four_fifths_sqrt {x : ℝ} (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  by_cases h : x < 10000
  · exact small_four_fifths h₁ h
  · have hc := (Campaign.T1.chain encl_tenK).2
    have := hc x (by push_cast; linarith) (by push_cast; linarith)
    simpa using this

theorem psi_abs_sub_le_sqrt {x : ℝ} (h₁ : 8 < x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x := by
  by_cases h : x < 1500
  · exact small_sqrt h₁.le (by linarith)
  · calc |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x :=
          psi_abs_sub_le_four_fifths_sqrt (by linarith) h₂
      _ ≤ Real.sqrt x := by linarith [Real.sqrt_nonneg x]

end PsiFinite
