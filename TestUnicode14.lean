import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (h u : ℝ) : ((innerₗ ℝ) h) u = h * u := by
  -- `innerₗ` is the bilinear map `v ↦ (w ↦ ⟪v,w⟫)`
  simp [inner_mul_left]
