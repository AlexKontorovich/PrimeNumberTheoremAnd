import Mathlib.Data.Complex.Abs

open Complex

theorem extracted_1 {z : ℂ} : Continuous fun (y : ℝ) => z.re + y * I := by
  apply Continuous.comp
  apply Continuous.add
  exact continuous_const
  exact { isOpen_preimage := fun s a => a }
  exact continuous_mul_right I

example [TopologicalSpace ℂ] : Continuous fun (x : ℂ) => x := by exact
  { isOpen_preimage := fun s a => a }

example [TopologicalSpace ℂ] : Continuous fun (y : ℝ) => (y : ℂ) * I := by
  exact?
