import Mathlib.Analysis.Complex.Schwarz

example (x : ℂ) : HasDerivAt (id : ℂ → ℂ) 1 x := by exact hasDerivAt_id x
