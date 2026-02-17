import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

example (a b : ℝ) : (⟪a, b⟫ : ℝ) = a * b := by
  simp [mul_comm]
