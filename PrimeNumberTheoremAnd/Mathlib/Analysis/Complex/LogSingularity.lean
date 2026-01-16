import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
## Log-singularity bounds for Hadamard/Cartan arguments

This file packages a small analytic inequality used in the “probabilistic radius / minimum-modulus”
step of Tao’s Hadamard factorization proof:

\[
\max(0, \log(1/|1-t|)) \le \sqrt{2/|1-t|}.
\]

The goal is to keep the Hadamard factorization development in `Riemann/Mathlib` self-contained.
-/

noncomputable section

namespace Complex.Hadamard

open Real

/-!
### A soft pointwise bound for the logarithmic singularity

This is used as an integrable majorant when averaging `max 0 (log(1/|1-t|))` on dyadic intervals.
-/

private lemma neg_log_le_sqrt_two_div {x : ℝ} (hx : 0 < x) (hxle : x ≤ 1) :
    -Real.log x ≤ Real.sqrt (2 / x) := by
  -- Rephrase using `t := -log x ≥ 0` and the inequality `t^2/2 ≤ exp t` for `t ≥ 0`.
  have hx0 : 0 ≤ x := le_of_lt hx
  have ht : 0 ≤ -Real.log x := by
    have : Real.log x ≤ 0 := Real.log_nonpos hx0 hxle
    linarith

  -- A helper: for `t ≥ 0`, we have `t^2/2 ≤ exp t`.
  have hsq_div_two_le_exp : ∀ {t : ℝ}, 0 ≤ t → t ^ 2 / 2 ≤ Real.exp t := by
    intro t ht
    let g : ℝ → ℝ := fun u => Real.exp u - u ^ 2 / 2
    have hg_cont : ContinuousOn g (Set.Ici (0 : ℝ)) := by
      have : Continuous g := by
        -- `exp` and polynomials are continuous.
        fun_prop
      simpa using this.continuousOn
    have hg_diff : DifferentiableOn ℝ g (interior (Set.Ici (0 : ℝ))) := by
      intro u hu
      have : DifferentiableAt ℝ g u := by
        -- `exp` and polynomials are differentiable.
        fun_prop
      exact this.differentiableWithinAt
    have hg'_nonneg : ∀ u ∈ interior (Set.Ici (0 : ℝ)), 0 ≤ deriv g u := by
      intro u hu
      have hu0 : 0 < u := by
        simpa [interior_Ici] using hu
      have hderiv : deriv g u = Real.exp u - u := by
        -- Differentiate `g` using `HasDerivAt`, then take `deriv`.
        have hExp : HasDerivAt Real.exp (Real.exp u) u := Real.hasDerivAt_exp u
        have hpow2 : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
          simpa using ((hasDerivAt_id u).pow 2)
        have hpow2_div : HasDerivAt (fun z : ℝ => z ^ 2 / 2) u u := by
          have := hpow2.div_const (2 : ℝ)
          -- `(2*u)/2 = u`
          simpa using this
        have hG : HasDerivAt g (Real.exp u - u) u := by
          -- `g = exp - (z^2/2)`
          simpa [g] using hExp.sub hpow2_div
        exact hG.deriv
      have hu_le : u ≤ Real.exp u := by
        -- `u ≤ u + 1 ≤ exp u`
        have h1 : u + 1 ≤ Real.exp u := Real.add_one_le_exp u
        have h0 : u ≤ u + 1 := by linarith
        exact h0.trans h1
      have : 0 ≤ Real.exp u - u := sub_nonneg.2 hu_le
      simpa [hderiv] using this
    have hg_mono : MonotoneOn g (Set.Ici (0 : ℝ)) :=
      monotoneOn_of_deriv_nonneg (D := Set.Ici (0 : ℝ)) (hD := convex_Ici 0) hg_cont hg_diff hg'_nonneg
    have hg0 : g 0 = 1 := by simp [g]
    have hle : g 0 ≤ g t := hg_mono (by simp) (by simpa [Set.mem_Ici] using ht) ht
    have : (1 : ℝ) ≤ Real.exp t - t ^ 2 / 2 := by simpa [g, hg0] using hle
    -- rearrange
    linarith

  have hmain : (-Real.log x) ^ 2 / 2 ≤ Real.exp (-Real.log x) :=
    hsq_div_two_le_exp ht
  have hexp : Real.exp (-Real.log x) = x⁻¹ := by
    -- `exp(-log x) = (exp(log x))⁻¹ = 1/x`
    simp [Real.exp_neg, Real.exp_log hx]
  have hsq2 : (-Real.log x) ^ 2 ≤ 2 * Real.exp (-Real.log x) := by
    nlinarith [hmain]
  have hsq' : (-Real.log x) ^ 2 ≤ 2 / x := by
    simpa [hexp, div_eq_mul_inv, mul_assoc] using hsq2
  have hy : 0 ≤ (2 / x) := by
    exact div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hx)
  -- Use `Real.le_sqrt` (with nonneg hypotheses).
  exact (Real.le_sqrt ht hy).2 hsq'

lemma posLog_log_one_div_abs_one_sub_le_sqrt {t : ℝ} :
    max 0 (Real.log (1 / |1 - t|)) ≤ Real.sqrt (2 / |1 - t|) := by
  by_cases ht : |1 - t| ≤ 1
  · by_cases h0 : |1 - t| = 0
    · have : t = 1 := by
        have : 1 - t = 0 := by simpa [abs_eq_zero] using h0
        linarith
      subst this
      simp
    · have hpos : 0 < |1 - t| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm h0)
      have hle : -Real.log |1 - t| ≤ Real.sqrt (2 / |1 - t|) :=
        neg_log_le_sqrt_two_div (x := |1 - t|) hpos ht
      have hlog : Real.log (1 / |1 - t|) = -Real.log |1 - t| := by
        simp [Real.log_inv]
      have hnonneg : 0 ≤ Real.log (1 / |1 - t|) := by
        have : (1 : ℝ) ≤ 1 / |1 - t| := by
          exact (one_le_div hpos).2 ht
        exact Real.log_nonneg this
      have hmax : max 0 (Real.log (1 / |1 - t|)) = Real.log (1 / |1 - t|) :=
        max_eq_right hnonneg
      calc
        max 0 (Real.log (1 / |1 - t|))
            = Real.log (1 / |1 - t|) := hmax
        _ = -Real.log |1 - t| := hlog
        _ ≤ Real.sqrt (2 / |1 - t|) := hle
  · have hlt : 1 < |1 - t| := lt_of_not_ge ht
    have hle0 : Real.log (1 / |1 - t|) ≤ 0 := by
      have hpos : 0 < |1 - t| := lt_trans (by norm_num) hlt
      have : (1 / |1 - t| : ℝ) ≤ 1 := (div_le_one hpos).2 (le_of_lt hlt)
      have h1 : 0 < (1 / |1 - t| : ℝ) := by positivity
      exact le_trans (Real.log_le_log h1 this) (by simp)
    have hmax : max 0 (Real.log (1 / |1 - t|)) = 0 := max_eq_left hle0
    have hrhs : 0 ≤ Real.sqrt (2 / |1 - t|) := by
      have : 0 ≤ 2 / |1 - t| := div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg _)
      exact Real.sqrt_nonneg _
    -- Avoid `simp` rewriting the goal into a conjunction.
    rw [hmax]
    exact hrhs

end Complex.Hadamard
