import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic

open BigOperators

/-- ** Partial summation ** -/
theorem sum_eq_int_deriv (φ : ℝ → ℂ) (a b : ℝ) (φDiff : ContDiffOn ℝ 1 φ (Set.Icc a b)) :
    ∑ n in Finset.Icc (⌊a⌋ + 1) ⌊b⌋, φ n =
    (∫ x in a..b, φ x) + (⌊b⌋ + 1 / 2 - b) * φ b - (⌊a⌋ + 1 / 2 - a) * φ a
      - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by
  sorry
