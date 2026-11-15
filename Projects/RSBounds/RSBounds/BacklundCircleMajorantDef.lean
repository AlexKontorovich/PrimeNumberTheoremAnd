import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! The actual piecewise majorant used on Rosser's circle of radius 1.32. -/

namespace TernaryGoldbach.RSBounds.BacklundCircleMajorant

noncomputable def radius : ℝ := 33 / 25

/-- The two positive-part terms encode the critical and left strip slopes.
The correction `V` is needed only for `0 ≤ σ < 1`. -/
noncomputable def scalar (H L V σ : ℝ) : ℝ :=
  if 5 / 4 ≤ σ then Real.log ‖riemannZeta (σ : ℂ)‖
  else H + L / 2 * (max (1 - σ) 0 + max (-σ) 0) +
    if 0 ≤ σ ∧ σ < 1 then V else 0

noncomputable def heightLog (T : ℝ) : ℝ := Real.log (Real.log (T + radius))
noncomputable def powerLog (T : ℝ) : ℝ := Real.log ((T + radius) / (2 * Real.pi))
noncomputable def stripLog (T : ℝ) : ℝ :=
  Real.log ((T - radius) ^ 2 / ((T - radius) ^ 2 - 4))

noncomputable def majorant (T : ℝ) (z : ℂ) : ℝ :=
  scalar (heightLog T) (powerLog T) (stripLog T) z.re

end TernaryGoldbach.RSBounds.BacklundCircleMajorant
