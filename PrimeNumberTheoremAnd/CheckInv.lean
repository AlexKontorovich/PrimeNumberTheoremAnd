import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

open Complex

variable {z w : ℂ} {n : ℤ}
variable (path : ℝ → ℂ)
variable (t : ℝ)

example (h_d_path : HasDerivAt path (z-w) t) (h_ne : path t - (n : ℂ) ≠ 0) :
  HasDerivAt (fun x ↦ (path x - (n : ℂ))⁻¹) (-(z-w) / (path t - (n : ℂ))^2) t := by
  have h_d_path_sub : HasDerivAt (fun x ↦ path x - (n : ℂ)) (z - w) t := h_d_path.sub_const (n : ℂ)
  apply HasDerivAt.inv h_d_path_sub h_ne
