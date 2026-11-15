import RSBounds.BacklundCountEndpoint

/-!
# The public positive-ordinate zeta zero count

This definition uses Mathlib's actual zeta function and analytic multiplicities,
with the inclusive endpoint convention `0 < Im rho <= T`. The finite-sum bridge
uses only the already-proved finiteness of zeta zeros; no finite RH certificate
or numerical zero-count estimate is imported.
-/

open Complex Real MeasureTheory

namespace TernaryGoldbach.RSBounds.Rosser1941
open BacklundCountIdentity

/-- Zeta zeros with positive ordinate at most `T`, counted with multiplicity.
Zero order vanishes at every point where zeta is nonzero. -/
noncomputable def positiveZeroCount (T : ℝ) : ℝ := by
  classical
  exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0

lemma positiveZeroCount_eq {T : ℝ} (hT : 0 < T) :
    positiveZeroCount T = (N_le T : ℝ) := by
  classical
  have hs : ∀ ρ ∉ closedPositiveZeros T,
      (if 0 < ρ.im ∧ ρ.im ≤ T then
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0) = 0 := by
    intro ρ hρ
    by_cases hi : 0 < ρ.im ∧ ρ.im ≤ T
    · have hz : riemannZeta ρ ≠ 0 := by
        intro hz
        exact hρ ((mem_closedPositiveZeros_iff hT).mpr ⟨hz, hi.1, hi.2⟩)
      rw [if_pos hi, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
      simp
    · simp [hi]
  unfold positiveZeroCount
  rw [tsum_eq_sum hs]
  unfold N_le
  push_cast
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := (mem_closedPositiveZeros_iff hT).mp hρ
  simp only [if_pos (show 0 < ρ.im ∧ ρ.im ≤ T from ⟨hi.2.1, hi.2.2⟩)]

end TernaryGoldbach.RSBounds.Rosser1941
