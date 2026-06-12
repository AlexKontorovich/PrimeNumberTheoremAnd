import PrimeNumberTheoremAnd.IEANTN.KadiriU6aFarTailClose
import PrimeNumberTheoremAnd.IEANTN.KadiriU6aAvgComparison

/-!
# U6a endpoint closure: the unconditional `(-1, 2)` horizontal bound

`KadiriU6aFarTailClose` discharges the zero-sum remainder hypothesis on the
strip `[-1, 2]` unconditionally, and `KadiriU6aAvgComparison` turns any such
discharge into cofinal horizontal-segment `log² T` bounds via the count-atom
height selector.  This file instantiates the second at the first, exporting
the unsuffixed `(-1, 2)` endpoint with no hypothesis arguments remaining.
-/

namespace Kadiri

/-- Cofinal heights `T` at which `ζ'/ζ` is `O(log² T)` along the horizontal
segments `re ∈ [-1, 2]`, `|im| = T`, with both segments zero- and pole-free.
Unconditional. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_neg_one_two :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Czero, Tzero, hZero⟩ := exists_U6aZeroSumRemainderBoundHypothesis
  exact exists_arbitrarily_large_horizontalSegmentLogDerivBound_of_zeroSumRemainder hZero

end Kadiri
