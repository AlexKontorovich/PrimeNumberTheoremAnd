import Mathlib.Analysis.InnerProductSpace.Basic

open scoped RealInnerProductSpace

example (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  simp
