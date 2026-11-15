import RSBounds.PsiFinite.SmallRange
import RSBounds.PsiFinite.Campaign.E6.Assembly

/-!
# Phase C: the bound on `[1500, 10^6]`, end to end

Uses every component: the certified base primes, the small walk to `10^4`, and
eight kernel-checked segments from `10^4` to `10^6`.
-/

namespace PsiFinite

theorem psi_abs_sub_le_four_fifths_sqrt_le_1e6 {x : ℝ} (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 6) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  by_cases h : x < 10000
  · exact small_four_fifths h₁ h
  · have hc := (Campaign.E6.chain encl_tenK).2
    have := hc x (by push_cast; linarith) (by push_cast; linarith)
    simpa using this

end PsiFinite
