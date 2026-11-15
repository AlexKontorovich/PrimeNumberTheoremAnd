import Mathlib

/- Independent statements: this file imports no proof module. -/
namespace TernaryGoldbach.RSBounds.Totient

theorem totient_ratio_lt_of_card_le_twenty {q : ℕ} (hq : 1 ≤ q)
    (hcard : q.primeFactors.card ≤ 20) {r : ℝ} (hr : 3 ≤ r) (hqr : (q : ℝ) ≤ r) :
    (q : ℝ) / Nat.totient q < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log r) +
      2.50637 / Real.log (Real.log r) := by sorry

theorem totient_ratio_lt_self_of_le_1e27 {q : ℕ} (hq : 3 ≤ q) (hmax : q ≤ 10 ^ 27) :
    (q : ℝ) / Nat.totient q <
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (q : ℝ)) +
        2.50637 / Real.log (Real.log (q : ℝ)) := by sorry

end TernaryGoldbach.RSBounds.Totient
