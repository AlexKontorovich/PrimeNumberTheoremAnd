import Mathlib.Analysis.Complex.Schwarz

example : IsOpen {z : ℂ | 0 < z.re} := by
  refine isOpen_lt continuous_const Complex.continuous_re
  · exact continuous_const
  · exact Complex.continuous_re
