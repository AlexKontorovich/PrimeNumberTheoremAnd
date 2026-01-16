import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GaussianIntegral

/-!
# Sin bound for |sin(π(σ + it))| ≥ e^{π|t|}/4

## Main Results

* `Complex.Gamma.LargeIm.norm_sin_pi_ge_exp`: Sin bound for `|sin(π(σ + it))| ≥ e^{π|t|}/4`


## References

* Titchmarsh, "The Theory of Functions", Chapter 4
* Whittaker & Watson, "Modern Analysis", Chapter XII
-/

noncomputable section

open Complex Real Set Filter Topology
open scoped Real Topology

namespace Complex.Gamma.LargeIm

/-! ## Part 1: The sin bound -/

/-- For `|t| ≥ 1`, `|sin(π(σ + it))| ≥ e^{π|t|}/4`.

This follows from `|sin(z)|² = sin²(Re z) + sinh²(Im z) ≥ sinh²(Im z)`,
and `sinh(x) = (e^x - e^{-x})/2 ≥ (e^|x| - 1)/2 ≥ e^|x|/4` for `|x| ≥ 1`. -/
theorem norm_sin_pi_ge_exp {σ t : ℝ} (ht : 1 ≤ |t|) :
    ‖Complex.sin (Real.pi * (σ + t * I))‖ ≥ Real.exp (Real.pi * |t|) / 4 := by
  -- Rewrite π(σ + it) = (πσ) + (πt)i and expand `sin` in terms of `sin/cos` and `sinh/cosh`.
  have hz : (Real.pi : ℂ) * (σ + t * I) = (Real.pi * σ) + (Real.pi * t) * I := by
    -- `simp` handles coercions from `ℝ` to `ℂ`.
    simp [mul_add, mul_assoc]
  have hnorm_ge :
      ‖Complex.sin ((Real.pi : ℂ) * (σ + t * I))‖ ≥ |Real.sinh (Real.pi * t)| := by
    -- Use the standard identity `sin(x + yi) = sin x cosh y + cos x sinh y · i`.
    have hsin :
        Complex.sin ((Real.pi : ℂ) * (σ + t * I))
            =
          (Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t))
            + (Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t)) * I := by
      -- First put the argument in the form `x + y * I`, then `simp` to turn complex
      -- trigonometric functions of reals into real ones.
      rw [hz]
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (Complex.sin_add_mul_I (x := (Real.pi * σ : ℂ)) (y := (Real.pi * t : ℂ)))
    -- Reduce to a real `sqrt` computation using `‖x + y*I‖ = √(x^2 + y^2)`.
    have hnorm_eq :
        ‖Complex.sin ((Real.pi : ℂ) * (σ + t * I))‖
            =
          Real.sqrt
            ((Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t)) ^ 2 +
              (Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t)) ^ 2) := by
      -- Turn `sin(...)` into `x + y*I` and apply `Complex.norm_add_mul_I`.
      rw [hsin]
      have hmul1 :
          ((Real.sin (Real.pi * σ) : ℂ) * (Real.cosh (Real.pi * t) : ℂ)) =
            ((Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t) : ℝ) : ℂ) := by
        simp
      have hmul2 :
          ((Real.cos (Real.pi * σ) : ℂ) * (Real.sinh (Real.pi * t) : ℂ)) =
            ((Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
        simp
      -- Rewrite to match `Complex.norm_add_mul_I`.
      -- (We keep these rewrites explicit to avoid `simp` turning back into complex `sin/cos/cosh/sinh`.)
      rw [hmul1, hmul2]
      exact
        (Complex.norm_add_mul_I (Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t))
          (Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t)))
    -- Simplify the inside using `cosh^2 = sinh^2 + 1` and `sin^2 + cos^2 = 1`.
    have hinside :
        (Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t)) ^ 2 +
            (Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t)) ^ 2
          =
        (Real.sin (Real.pi * σ)) ^ 2 + (Real.sinh (Real.pi * t)) ^ 2 := by
      -- Expand squares and use the standard identities.
      calc
        (Real.sin (Real.pi * σ) * Real.cosh (Real.pi * t)) ^ 2 +
            (Real.cos (Real.pi * σ) * Real.sinh (Real.pi * t)) ^ 2
            =
          (Real.sin (Real.pi * σ)) ^ 2 * (Real.cosh (Real.pi * t)) ^ 2 +
            (Real.cos (Real.pi * σ)) ^ 2 * (Real.sinh (Real.pi * t)) ^ 2 := by
              simp [pow_two, mul_assoc, mul_left_comm, mul_comm]
        _ =
          (Real.sin (Real.pi * σ)) ^ 2 * ((Real.sinh (Real.pi * t)) ^ 2 + 1) +
            (Real.cos (Real.pi * σ)) ^ 2 * (Real.sinh (Real.pi * t)) ^ 2 := by
              simp [Real.cosh_sq]
        _ =
          (Real.sin (Real.pi * σ)) ^ 2 +
            ((Real.sin (Real.pi * σ)) ^ 2 + (Real.cos (Real.pi * σ)) ^ 2) *
              (Real.sinh (Real.pi * t)) ^ 2 := by
              ring
        _ = (Real.sin (Real.pi * σ)) ^ 2 + (Real.sinh (Real.pi * t)) ^ 2 := by
              simp [Real.sin_sq_add_cos_sq]
    -- Now `√(sin^2 + sinh^2) ≥ √(sinh^2) = |sinh|`.
    rw [hnorm_eq, hinside]
    have hle :
        (Real.sinh (Real.pi * t)) ^ 2 ≤
          (Real.sin (Real.pi * σ)) ^ 2 + (Real.sinh (Real.pi * t)) ^ 2 := by
      exact le_add_of_nonneg_left (sq_nonneg _)
    have := Real.sqrt_le_sqrt hle
    simpa [Real.sqrt_sq_eq_abs] using this
  -- Bound `|sinh(πt)|` below by `exp(π|t|)/4` for `|t| ≥ 1`.
  have hsinh_ge :
      |Real.sinh (Real.pi * t)| ≥ Real.exp (Real.pi * |t|) / 4 := by
    -- Rewrite `|sinh(πt)| = sinh(π|t|)`.
    have habs :
        |Real.sinh (Real.pi * t)| = Real.sinh (Real.pi * |t|) := by
      calc
        |Real.sinh (Real.pi * t)| = Real.sinh |Real.pi * t| := by
          simpa using (Real.abs_sinh (Real.pi * t))
        _ = Real.sinh (Real.pi * |t|) := by
          have hpi0 : 0 ≤ (Real.pi : ℝ) := Real.pi_pos.le
          simp [abs_mul, abs_of_nonneg hpi0]
    -- Show `1 ≤ π|t|`.
    have hpi : (1 : ℝ) ≤ Real.pi := by
      have h2pi : (2 : ℝ) ≤ Real.pi := Real.two_le_pi
      linarith
    have hpiu : (1 : ℝ) ≤ Real.pi * |t| := by
      have : Real.pi ≤ Real.pi * |t| := by
        simpa [mul_one] using (mul_le_mul_of_nonneg_left ht Real.pi_pos.le)
      exact le_trans hpi this
    -- Prove `sinh u ≥ exp u / 4` for `u = π|t|` using the exponential definition.
    have hsinh_u :
        Real.sinh (Real.pi * |t|) ≥ Real.exp (Real.pi * |t|) / 4 := by
      set u : ℝ := Real.pi * |t|
      have hu1 : (1 : ℝ) ≤ u := hpiu
      have hu0 : 0 ≤ u := by
        have : 0 ≤ (Real.pi : ℝ) := Real.pi_pos.le
        exact mul_nonneg this (abs_nonneg t)
      have hexp_neg : Real.exp (-u) ≤ 1 := by
        -- `-u ≤ 0` since `u ≥ 0`.
        exact (Real.exp_le_one_iff.mpr (by linarith))
      have hexp_ge_two : (2 : ℝ) ≤ Real.exp u := by
        have h1 : (2 : ℝ) ≤ u + 1 := by linarith
        exact le_trans h1 (Real.add_one_le_exp u)
      -- Chain the inequalities from the `exp`-definition of `sinh`.
      calc
        Real.sinh u = (Real.exp u - Real.exp (-u)) / 2 := by simp [Real.sinh_eq]
        _ ≥ (Real.exp u - 1) / 2 := by
          have : Real.exp u - Real.exp (-u) ≥ Real.exp u - 1 := by linarith
          exact (div_le_div_of_nonneg_right this (by norm_num : (0 : ℝ) ≤ 2))
        _ ≥ Real.exp u / 4 := by
          -- This is equivalent to `2 ≤ exp u`.
          have : (Real.exp u - 1) / 2 ≥ Real.exp u / 4 := by
            linarith [hexp_ge_two]
          simpa using this
    -- Put the pieces together.
    simpa [habs] using hsinh_u
  -- Combine the two lower bounds.
  have := le_trans (show Real.exp (Real.pi * |t|) / 4 ≤ |Real.sinh (Real.pi * t)| from hsinh_ge) hnorm_ge
  -- `hnorm_ge` is about `sin(π(σ+it))` with an explicit `π` factor.
  simpa using this

end Complex.Gamma.LargeIm
