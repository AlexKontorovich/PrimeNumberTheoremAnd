import Mathlib

/- Independent Mathlib-only statement. The deliberate theorem hole is never
imported by the solution; the Comparator rejects sorryAx in the solution. -/
namespace TernaryGoldbach.RSBounds.Rosser1941

noncomputable def positiveZeroCount (T : ℝ) : ℝ := by
  classical
  exact ∑' ρ : ℂ, if 0 < ρ.im ∧ ρ.im ≤ T then
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) else 0

theorem zero_count_bounds (T : ℝ) (hT : 2 ≤ T) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 := by sorry

theorem zero_count_error_lt_one_to_100 (T : ℝ) (hT : 0 ≤ T) (h100 : T ≤ 100) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| < 1 := by sorry

end TernaryGoldbach.RSBounds.Rosser1941
