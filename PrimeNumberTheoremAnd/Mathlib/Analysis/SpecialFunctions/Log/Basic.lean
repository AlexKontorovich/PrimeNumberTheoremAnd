import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  convert squeeze_zero' (f := fun x ↦ log x ^ b / x^a) (g := fun x ↦ (log x ^ ⌈ b/a ⌉₊ / x)^a ) (t₀ := atTop) ?_ ?_ ?_
  . simp
    use 1
    intro x hx
    apply div_nonneg <;> apply Real.rpow_nonneg
    . exact log_nonneg hx
    linarith
  . simp
    use exp 1
    intro x hx
    have h0 : 0 < x := by
      apply lt_of_lt_of_le (exp_pos 1) hx
    have h1 : 1 ≤ log x := by
      rwa [le_log_iff_exp_le h0]
    rw [div_rpow _ (le_of_lt h0)]
    . rw [div_le_div_iff_of_pos_right (rpow_pos_of_pos h0 _), <-rpow_natCast, <-rpow_mul (zero_le_one.trans h1)]
      apply rpow_le_rpow_of_exponent_le h1
      rw [<-div_le_iff₀ ha]
      exact Nat.le_ceil _
    apply pow_nonneg (by linarith)
  rw [(zero_rpow (_root_.ne_of_lt ha).symm).symm]
  apply Tendsto.rpow_const
  . have := tendsto_pow_log_div_mul_add_atTop 1 0 ⌈b/a⌉₊ zero_ne_one.symm
    simp at this
    exact this
  right
  exact le_of_lt ha
