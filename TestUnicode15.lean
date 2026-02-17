import PrimeNumberTheoremAnd.Wiener

open scoped FourierTransform RealInnerProductSpace
open Real MeasureTheory FourierTransform

example (h u : ℝ) : ((innerₗ ℝ) h) u = h * u := by
  -- `innerₗ` is `innerSL`? maybe just simp
  -- This should reduce to `⟪h, u⟫ = h * u`.
  -- `simp` turns `⟪h, u⟫` into `u * h`.
  simp [mul_comm, mul_left_comm, mul_assoc]
