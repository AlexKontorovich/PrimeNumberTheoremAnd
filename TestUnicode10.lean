import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp
