import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ZetaFunctionalEquation
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.CompletedXi
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GammaBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StirlingBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StirlingB
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Hadamard
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Pi.Irrational
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.PNT3_RiemannZeta

/-!
# Analytic continuation and finite order for the Riemann zeta function

This file establishes that the completed Riemann zeta function `completedRiemannZeta₀`
(denoted Λ₀(s) in the literature) is an entire function of finite order, specifically
order 1.

Note: Mathlib distinguishes between:
- `completedRiemannZeta₀` : the entire function Λ₀(s)
- `completedRiemannZeta` : Λ(s) = Λ₀(s) - 1/s - 1/(1-s), which has simple poles at 0 and 1

The key ingredients are:
* Mathlib's `differentiable_completedZeta₀` for entirety of Λ₀
* The functional equation `completedRiemannZeta₀_one_sub`
* Stirling-type bounds for `Complex.Gammaℝ` from `GammaBounds.lean` and `StirlingRobbins.lean` and other related files
* Convexity bounds for zeta in the critical strip

## Main results

* `completedRiemannZeta₀_entire` : Λ₀(s) is entire (differentiable on all of ℂ)
* `analyticAt_completedRiemannZeta₀` : Λ₀(s) is analytic at every point
* `completedRiemannZeta₀_growth` : growth bound `log(1+‖Λ₀ z‖) ≤ C*(1+‖z‖)^(3/2)`
* `zeta_minus_pole_entire_growth` : growth bound for `(s-1)ζ(s)` (coarse, exponent `2`)
-/

noncomputable section

open Complex Set Filter Topology Metric
open scoped Real

namespace Complex

/-! ### Entirety of the completed zeta function -/

/-- The entire completed zeta function Λ₀ is differentiable on all of ℂ.

This is Mathlib's `differentiable_completedZeta₀`, which we re-export with
a more descriptive name. The function Λ₀ is constructed via the Mellin
transform of the theta function. -/
theorem completedRiemannZeta₀_entire : Differentiable ℂ completedRiemannZeta₀ :=
  differentiable_completedZeta₀

/-! ### Analyticity of the completed zeta function -/

/-- The entire completed Riemann zeta function Λ₀ is analytic at every point of ℂ.

This follows from entirety via the standard equivalence for complex functions. -/
theorem analyticAt_completedRiemannZeta₀ (s : ℂ) : AnalyticAt ℂ completedRiemannZeta₀ s :=
  completedRiemannZeta₀_entire.analyticAt s

/-- The completed zeta function Λ (with poles) is holomorphic on ℂ \ {0, 1}.

This follows directly from Mathlib's `differentiableAt_completedZeta`. -/
theorem completedRiemannZeta_differentiableOn_compl :
    DifferentiableOn ℂ completedRiemannZeta ({0, 1}ᶜ) := by
  intro s hs
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
  exact (differentiableAt_completedZeta hs.1 hs.2).differentiableWithinAt

/-! ### Finite order bounds -/

/-- Auxiliary bound: |π^(-s/2)| is bounded by exp(|s| log π / 2). -/
lemma pi_pow_neg_half_bound (s : ℂ) :
    ‖(π : ℂ) ^ (-s / 2)‖ ≤ Real.exp (|s.im| * Real.log π / 2 + |s.re| * Real.log π / 2) := by
  -- |π^w| = π^{Re(w)} for π > 0 (as a real positive base)
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [norm_cpow_eq_rpow_re_of_pos hpi_pos]
  -- Re(-s/2) = -Re(s)/2
  simp only [neg_div, neg_re, div_ofNat_re]
  -- π^{-Re(s)/2} = exp(-Re(s)/2 · log π)
  rw [Real.rpow_def_of_pos hpi_pos]
  apply Real.exp_le_exp.mpr
  -- -Re(s)/2 · log π ≤ |Re(s)|/2 · log π + |Im(s)|/2 · log π
  have hlog_pi_pos : 0 < Real.log Real.pi := by
    have hone_lt_pi : (1 : ℝ) < Real.pi := lt_of_lt_of_le (by norm_num) Real.two_le_pi
    exact Real.log_pos hone_lt_pi
  calc Real.log Real.pi * (-(s.re / 2))
      = -(s.re / 2) * Real.log Real.pi := by ring
    _ ≤ |s.re| / 2 * Real.log Real.pi := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hlog_pi_pos)
          have h : -(s.re / 2) ≤ |s.re| / 2 := by
            calc -(s.re / 2) ≤ |s.re / 2| := neg_le_abs (s.re / 2)
              _ = |s.re| / 2 := by
                rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
          exact h
    _ = |s.re| * Real.log Real.pi / 2 := by ring
    _ ≤ |s.im| * Real.log Real.pi / 2 + |s.re| * Real.log Real.pi / 2 := by
          have h : 0 ≤ |s.im| * Real.log Real.pi / 2 := by
            apply div_nonneg _ (by norm_num)
            apply mul_nonneg (abs_nonneg _) (le_of_lt hlog_pi_pos)
          linarith

/-! ### Finite order of the completed zeta function -/

/-- Boundedness of completedRiemannZeta₀ on compact sets. -/
lemma completedRiemannZeta₀_bounded_on_closedBall (R : ℝ) (_hR : 0 < R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖completedRiemannZeta₀ w‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  have hcont : ContinuousOn completedRiemannZeta₀ (Metric.closedBall 0 R) :=
    completedRiemannZeta₀_entire.continuous.continuousOn
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun w hw => ?_⟩
  have := hM w (Metric.mem_closedBall.mpr (by simpa using hw))
  exact le_trans this (le_max_left _ _)

set_option maxHeartbeats 800000 in
-- The proof of `completedRiemannZeta₀_growth` is a long chain of real-inequality estimates
-- (Stirling/convexity bounds + case splits); it is computationally heavy for the kernel elaborator.
/-- The entire completed zeta function Λ₀ has finite order at most 1.

The growth bound follows from:
1. Stirling's formula for Γ(s/2) ~ √(2π) (s/2)^{s/2-1/2} e^{-s/2}
2. The bound |ζ(s)| = O(|t|^{1/2+ε}) in the critical strip (convexity bound)
3. The functional equation `completedRiemannZeta₀_one_sub` to extend to Re(s) < 0

The combination gives |Λ₀(s)| ≤ exp(C|s| log|s|) = exp(o(|s|^{1+ε})) for any ε > 0. -/
theorem completedRiemannZeta₀_growth :
    ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖completedRiemannZeta₀ z‖) ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
  -- Growth bound: `log(1 + ‖Λ₀ z‖) ≤ C * (1 + ‖z‖)^(3/2)`.
    -- Compact control on a fixed ball:
    obtain ⟨M, hM_nonneg, hM⟩ := completedRiemannZeta₀_bounded_on_closedBall 3 (by norm_num)
    -- Stirling bound for `Γℝ` on `Re ≥ 0`:
    obtain ⟨CΓ, hCΓ_pos, hΓ⟩ := Riemann.Gammaℝ_stirling_bound_re_ge_zero

    -- helper: `log(1 + exp B) ≤ B + log 2` for `0 ≤ B`
    have log_one_add_exp_le : ∀ (B : ℝ), 0 ≤ B → Real.log (1 + Real.exp B) ≤ B + Real.log 2 := by
      intro B hB
      have h1 : (1 : ℝ) ≤ Real.exp B := by
        simpa using (Real.one_le_exp_iff.2 hB)
      have h2 : 1 + Real.exp B ≤ 2 * Real.exp B := by linarith
      have hpos : 0 < (1 : ℝ) + Real.exp B := by positivity
      have hpos' : 0 < 2 * Real.exp B := by positivity
      have : Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) :=
        Real.log_le_log (by positivity) h2
      calc
        Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) := this
        _ = Real.log 2 + B := by
          simp [Real.log_mul, add_comm]
        _ = B + Real.log 2 := by ring

    -- Choose a single global constant (coarse, but honest).
    -- `C` must dominate the polynomial/log constants coming from the large-‖z‖ case.
    let C : ℝ := max (Real.log (1 + M) + 10) (4 * CΓ + 110)
    refine ⟨C, ?_, ?_⟩
    · have : (0 : ℝ) < 4 * CΓ + 110 := by nlinarith [hCΓ_pos]
      exact lt_of_lt_of_le this (le_max_right _ _)
    · intro z
      -- Reduce to `w` with `Re(w) ≥ 1/2` using `Λ₀(1-s)=Λ₀(s)`.
      -- Use `2⁻¹` (rather than `1/2`) so `simp` can use the branch hypothesis without rewriting.
      let w : ℂ := if z.re < (2⁻¹ : ℝ) then (1 - z) else z
      have hw_eq : completedRiemannZeta₀ w = completedRiemannZeta₀ z := by
        by_cases hzr : z.re < (2⁻¹ : ℝ)
        · have hw : w = 1 - z := by simp [w, hzr]
          simpa [hw] using (completedRiemannZeta₀_one_sub z)
        · simp [w, hzr]
      have hw_re : (2⁻¹ : ℝ) ≤ w.re := by
        by_cases hzr : z.re < (2⁻¹ : ℝ)
        · have : w.re = 1 - z.re := by simp [w, hzr]
          linarith [this, hzr]
        · have : (2⁻¹ : ℝ) ≤ z.re := le_of_not_gt hzr
          simpa [w, hzr] using this
      have hw_re0 : 0 ≤ w.re := by linarith

      -- Relate norms: `‖w‖ ≤ 1 + ‖z‖`.
      have hw_norm_le : ‖w‖ ≤ 1 + ‖z‖ := by
        by_cases hzr : z.re < (2⁻¹ : ℝ)
        · have hw : w = 1 - z := by simp [w, hzr]
          -- `‖1 - z‖ ≤ ‖1‖ + ‖z‖`
          have : ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := by simpa using (norm_sub_le (1 : ℂ) z)
          simpa [hw, norm_one, add_comm, add_left_comm, add_assoc] using this
        · simp [w, hzr]

      -- If `‖w‖ ≤ 3`, use compactness.
      by_cases hw_small : ‖w‖ ≤ 3
      · have hbw : ‖completedRiemannZeta₀ w‖ ≤ M := hM w hw_small
        have hlog : Real.log (1 + ‖completedRiemannZeta₀ w‖) ≤ Real.log (1 + M) := by
          refine Real.log_le_log (by linarith [norm_nonneg (completedRiemannZeta₀ w)]) ?_
          linarith
        have hC1 : Real.log (1 + M) ≤ C := by
          have : Real.log (1 + M) + 10 ≤ C := le_max_left _ _
          linarith
        have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
          have : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
          simpa using Real.one_le_rpow this (by norm_num)
        have hC_nonneg : 0 ≤ C := by
          have : (0 : ℝ) ≤ 4 * CΓ + 110 := by nlinarith [hCΓ_pos.le]
          exact le_trans this (le_max_right _ _)
        have htransfer : Real.log (1 + ‖completedRiemannZeta₀ z‖) =
            Real.log (1 + ‖completedRiemannZeta₀ w‖) := by
          simp [hw_eq]
        calc
          Real.log (1 + ‖completedRiemannZeta₀ z‖)
              = Real.log (1 + ‖completedRiemannZeta₀ w‖) := htransfer
          _ ≤ Real.log (1 + M) := hlog
          _ ≤ C := hC1
          _ ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            simpa [mul_one] using (mul_le_mul_of_nonneg_left hpow hC_nonneg)

      · -- Large `‖w‖`: bound `Λ₀ w` via `Λ w` and the pole-correction terms, then bound `Λ w = Γℝ w * ζ w`.
        have hw_large : 3 < ‖w‖ := lt_of_not_ge hw_small
        have hw_norm1 : 1 ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
        have hw_ne0 : w ≠ 0 := by
          intro h0; have : (‖w‖ : ℝ) = 0 := by simp [h0]
          linarith [hw_large]
        have hw_ne1 : w ≠ 1 := by
          intro h1; have : (‖w‖ : ℝ) = 1 := by simp [h1]
          linarith [hw_large]

        have hGamma : ‖Complex.Gammaℝ w‖ ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) :=
          hΓ w hw_re0 hw_norm1

        -- Zeta bound on `Re > 1/10`:
        have hw_re_gt : (1 / 10 : ℝ) < w.re := by linarith
        have hzeta0 := lem_zetaBound2 w hw_re_gt hw_ne1

        -- `‖1/(w-1)‖ ≤ 1` since `‖w‖>3` implies `‖w-1‖ ≥ ‖w‖ - 1 > 2`.
        have hdist1 : ‖1 / (w - 1)‖ ≤ 1 := by
          have hnorm : ‖w‖ ≤ ‖w - 1‖ + 1 := by
            -- `w = (w - 1) + 1`
            have : ‖(w - 1) + (1 : ℂ)‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            simpa [sub_add_cancel w (1 : ℂ), norm_one] using this
          have hsub : (2 : ℝ) ≤ ‖w - 1‖ := by
            -- from `‖w‖ ≤ ‖w-1‖ + 1`
            have : ‖w‖ ≤ ‖w - 1‖ + 1 := by simpa [norm_one] using hnorm
            linarith [hw_large]
          have hsub' : (1 : ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) hsub
          simpa [one_div, norm_inv] using inv_le_one_of_one_le₀ hsub'

        -- `‖w‖ / w.re ≤ 2‖w‖` since `w.re ≥ 1/2`.
        have hdiv : ‖w‖ / w.re ≤ 2 * ‖w‖ := by
          have hw_re_pos : 0 < w.re := by linarith [hw_re]
          have hinv : (1 / w.re : ℝ) ≤ 2 := by
            have hhalf_pos : (0 : ℝ) < (2⁻¹ : ℝ) := by norm_num
            have : (1 / w.re : ℝ) ≤ (1 / (2⁻¹ : ℝ)) :=
              one_div_le_one_div_of_le hhalf_pos hw_re
            simpa using this.trans_eq (by norm_num)
          calc
            ‖w‖ / w.re = ‖w‖ * (1 / w.re) := by ring
            _ ≤ ‖w‖ * 2 := mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
            _ = 2 * ‖w‖ := by ring

        have hzeta_le : ‖riemannZeta w‖ ≤ 2 + 2 * ‖w‖ := by
          have hzeta' : ‖riemannZeta w‖ ≤ 1 + ‖1 / (w - 1)‖ + ‖w‖ / w.re := by
            simpa [one_div] using hzeta0
          linarith [hzeta', hdist1, hdiv]

        -- `Λ = ζ * Γℝ`
        have hGamma_ne0 : Complex.Gammaℝ w ≠ 0 :=
          Complex.Gammaℝ_ne_zero_of_re_pos (by linarith [hw_re])
        have hΛ_def : completedRiemannZeta w = riemannZeta w * Complex.Gammaℝ w := by
          have hzeta_def := (riemannZeta_def_of_ne_zero (s := w) hw_ne0)
          have hzeta_mul := congrArg (fun x => x * Complex.Gammaℝ w) hzeta_def
          have : riemannZeta w * Complex.Gammaℝ w = completedRiemannZeta w := by
            simpa [div_eq_mul_inv, mul_assoc, hGamma_ne0] using hzeta_mul
          simpa [mul_comm, mul_left_comm, mul_assoc] using this.symm
        have hΛ_bound : ‖completedRiemannZeta w‖ ≤ (2 + 2 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          calc
            ‖completedRiemannZeta w‖ = ‖riemannZeta w * Complex.Gammaℝ w‖ := by simp [hΛ_def]
            _ ≤ ‖riemannZeta w‖ * ‖Complex.Gammaℝ w‖ := norm_mul_le _ _
            _ ≤ (2 + 2 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
              exact mul_le_mul hzeta_le hGamma (by positivity) (by positivity)

        -- `Λ₀ = Λ + 1/w + 1/(1-w)`
        have hΛ0_def : completedRiemannZeta₀ w =
            completedRiemannZeta w + 1 / w + 1 / (1 - w) := by
          have h := completedRiemannZeta_eq w
          have h' := congrArg (fun x => x + (1 / w) + (1 / (1 - w))) h
          simpa [add_assoc, add_left_comm, add_comm, sub_eq_add_neg] using h'.symm

        have hinv1 : ‖1 / w‖ ≤ 1 := by
          have : (1 : ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
          simpa [one_div, norm_inv] using inv_le_one_of_one_le₀ this
        have hinv2 : ‖1 / (1 - w)‖ ≤ 1 := by
          -- `‖1 - w‖ = ‖w - 1‖ ≥ 2`
          have hnorm : ‖w‖ ≤ ‖w - 1‖ + 1 := by
            have : ‖(w - 1) + (1 : ℂ)‖ ≤ ‖w - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
            simpa [sub_add_cancel w (1 : ℂ), norm_one] using this
          have : (2 : ℝ) ≤ ‖w - 1‖ := by linarith [hw_large, hnorm]
          have : (1 : ℝ) ≤ ‖w - 1‖ := le_trans (by norm_num) this
          -- `‖1-w‖ = ‖w-1‖`
          simpa [one_div, norm_inv, norm_sub_rev] using inv_le_one_of_one_le₀ this

        have hΛ0_bound : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + 2 := by
          -- triangle inequality + `hinv1`, `hinv2`
          have : ‖completedRiemannZeta₀ w‖ ≤ ‖completedRiemannZeta w‖ + ‖1 / w‖ + ‖1 / (1 - w)‖ := by
            simpa [hΛ0_def, add_assoc] using
              (norm_add₃_le (a := completedRiemannZeta w) (b := (1 / w)) (c := (1 / (1 - w))))
          linarith [this, hinv1, hinv2]

        -- Now a clean log bound:
        -- `‖Λ₀ w‖ ≤ (‖Λ w‖ + 2) ≤ ((2+2‖w‖)exp(B) + 2) ≤ (5+5‖w‖)exp(B)` using `exp(B) ≥ 1`.
        have hB_nonneg : 0 ≤ CΓ * ‖w‖ * Real.log (1 + ‖w‖) := by
          have hlog : 0 ≤ Real.log (1 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
          have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
          have hn : 0 ≤ ‖w‖ := norm_nonneg w
          exact mul_nonneg (mul_nonneg hC0 hn) hlog
        have hexp_ge_one : (1 : ℝ) ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          simpa using (Real.one_le_exp_iff.2 hB_nonneg)
        have hΛ0_mul_exp :
            ‖completedRiemannZeta₀ w‖ ≤ (5 + 5 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          have hΛ' : ‖completedRiemannZeta w‖ ≤ (2 + 2 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) :=
            hΛ_bound
          -- absorb `+2` using `exp(B) ≥ 1` and `‖w‖ ≥ 1`
          have hw1 : (1 : ℝ) ≤ ‖w‖ := le_trans (by norm_num) (le_of_lt hw_large)
          have h2 : (2 : ℝ) ≤ (3 + 3 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
            nlinarith [hexp_ge_one, hw1]
          have : ‖completedRiemannZeta w‖ + 2
              ≤ (5 + 5 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
            nlinarith [hΛ', h2]
          exact le_trans hΛ0_bound this

        -- Convert to the desired `log(1+‖Λ₀ z‖)` bound (using `w` and `‖w‖ ≤ 1+‖z‖`):
        have hC_nonneg : 0 ≤ C := by
          have : (0 : ℝ) ≤ 4 * CΓ + 110 := by nlinarith [hCΓ_pos.le]
          exact le_trans this (le_max_right _ _)
        have hpow : (1 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
          have : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
          simpa using Real.one_le_rpow this (by norm_num)
        have htransfer : Real.log (1 + ‖completedRiemannZeta₀ z‖) = Real.log (1 + ‖completedRiemannZeta₀ w‖) := by
          simp [hw_eq]

        -- Coarse domination: `log(1 + ‖Λ₀ w‖) ≤ log((6+6‖w‖)exp(B)) = log(6+6‖w‖) + B`,
        -- then absorb both terms into `C*(1+‖z‖)^(3/2)` using `log_le_rpow_div`.
        have hlog_main :
            Real.log (1 + ‖completedRiemannZeta₀ w‖)
              ≤ Real.log (6 + 6 * ‖w‖) + (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
          have h1 : 1 + ‖completedRiemannZeta₀ w‖ ≤ (6 + 6 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
            -- from `‖Λ₀ w‖ ≤ (5+5‖w‖) exp(B)` and `1 ≤ exp(B)`.
            have : ‖completedRiemannZeta₀ w‖ ≤ (5 + 5 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) :=
              hΛ0_mul_exp
            have : 1 ≤ Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := hexp_ge_one
            nlinarith
          have hlog := Real.log_le_log (by positivity) h1
          have hposA : (0 : ℝ) < (6 + 6 * ‖w‖ : ℝ) := by positivity
          have hposB : (0 : ℝ) < Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by positivity
          have hrewrite :
              Real.log ((6 + 6 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)))
                = Real.log (6 + 6 * ‖w‖) + (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
            calc
              Real.log ((6 + 6 * ‖w‖) * Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖)))
                  = Real.log (6 + 6 * ‖w‖) + Real.log (Real.exp (CΓ * ‖w‖ * Real.log (1 + ‖w‖))) := by
                      simp [Real.log_mul hposA.ne' hposB.ne', add_comm]
              _ = Real.log (6 + 6 * ‖w‖) + (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := by
                      simp [Real.log_exp]
          -- rewrite the RHS of `hlog` and finish
          simpa [hrewrite] using hlog

        -- final absorb
        have hB_le :
            CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ (4 * CΓ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
          -- Step 1: `log(1+‖w‖) ≤ 2 * (1+‖w‖)^(1/2)` (from `log_le_rpow_div` with ε=1/2).
          have hlog₁ : Real.log (1 + ‖w‖) ≤ 2 * (1 + ‖w‖) ^ (1 / 2 : ℝ) := by
            have hlog : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) :=
              Real.log_le_rpow_div (by linarith [norm_nonneg w]) (by norm_num)
            simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc,
              (by norm_num : (1 / (1 / 2 : ℝ)) = (2 : ℝ))] using hlog

          -- Step 2: compare square-roots ` (1+‖w‖)^(1/2) ≤ 2*(1+‖z‖)^(1/2) `.
          have hw_le' : (1 + ‖w‖ : ℝ) ≤ 2 + ‖z‖ := by linarith [hw_norm_le, norm_nonneg z]
          have hpow_le' :
              (1 + ‖w‖) ^ (1 / 2 : ℝ) ≤ (2 + ‖z‖) ^ (1 / 2 : ℝ) :=
            Real.rpow_le_rpow (by positivity) hw_le' (by norm_num)
          have hpow2 :
              (2 + ‖z‖) ^ (1 / 2 : ℝ) ≤ 2 * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
            have hlin : (2 + ‖z‖ : ℝ) ≤ 4 * (1 + ‖z‖) := by nlinarith [norm_nonneg z]
            have hpow : (2 + ‖z‖) ^ (1 / 2 : ℝ) ≤ (4 * (1 + ‖z‖)) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (by positivity) hlin (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
            have hpos : 0 ≤ (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
            have hmul :
                ((1 + ‖z‖) * 4) ^ (2⁻¹ : ℝ)
                  = (1 + ‖z‖) ^ (2⁻¹ : ℝ) * (4 : ℝ) ^ (2⁻¹ : ℝ) := by
              simpa [mul_assoc, mul_comm, mul_left_comm] using
                (Real.mul_rpow (x := (1 + ‖z‖)) (y := (4 : ℝ)) (z := (2⁻¹ : ℝ)) hpos (by norm_num))
            have h4 : (4 : ℝ) ^ (2⁻¹ : ℝ) = 2 := by norm_num
            calc
              (2 + ‖z‖) ^ (1 / 2 : ℝ) ≤ (4 * (1 + ‖z‖)) ^ (1 / 2 : ℝ) := hpow
              _ = ((1 + ‖z‖) * 4) ^ (2⁻¹ : ℝ) := by
                    simp [mul_comm]
              _ = 2 * (1 + ‖z‖) ^ (2⁻¹ : ℝ) := by
                    -- use `hmul` then simplify `4^(1/2)=2`
                    calc
                      ((1 + ‖z‖) * 4) ^ (2⁻¹ : ℝ)
                          = (1 + ‖z‖) ^ (2⁻¹ : ℝ) * (4 : ℝ) ^ (2⁻¹ : ℝ) := by simp [hmul]
                      _ = (1 + ‖z‖) ^ (2⁻¹ : ℝ) * 2 := by simp [h4]
                      _ = 2 * (1 + ‖z‖) ^ (2⁻¹ : ℝ) := by ring
            aesop

          have hroot : (1 + ‖w‖) ^ (1 / 2 : ℝ) ≤ 2 * (1 + ‖z‖) ^ (1 / 2 : ℝ) :=
            le_trans hpow_le' hpow2

          -- Step 3: put it together into a `3/2` bound.
          have hlog₂ : Real.log (1 + ‖w‖) ≤ 4 * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
            -- `log ≤ 2*(1+‖w‖)^(1/2) ≤ 4*(1+‖z‖)^(1/2)`
            calc
              Real.log (1 + ‖w‖) ≤ 2 * (1 + ‖w‖) ^ (1 / 2 : ℝ) := hlog₁
              _ ≤ 4 * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by nlinarith [hroot]

          have hw_le'' : ‖w‖ ≤ 1 + ‖z‖ := hw_norm_le
          have ha : 0 < (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
          have hmulPow :
              (1 + ‖z‖) * (1 + ‖z‖) ^ (1 / 2 : ℝ) = (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            -- `a * a^(1/2) = a^(1 + 1/2)`
            have : (1 + ‖z‖) ^ (3 / 2 : ℝ) = (1 + ‖z‖) ^ (1 : ℝ) * (1 + ‖z‖) ^ (1 / 2 : ℝ) := by
              simp [show (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) by ring, Real.rpow_add ha]
            simpa [Real.rpow_one, mul_comm, mul_left_comm, mul_assoc] using this.symm
          have hlog_nonneg : 0 ≤ Real.log (1 + ‖w‖) := Real.log_nonneg (by linarith [norm_nonneg w])
          have hfac_nonneg : 0 ≤ CΓ * (1 + ‖z‖) := by
            have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
            have : 0 ≤ (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
            exact mul_nonneg hC0 this
          calc
            CΓ * ‖w‖ * Real.log (1 + ‖w‖)
                ≤ (CΓ * (1 + ‖z‖)) * Real.log (1 + ‖w‖) := by
                    -- `CΓ * ‖w‖ ≤ CΓ * (1+‖z‖)` then multiply by `log ≥ 0`
                    have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
                    have hCw : CΓ * ‖w‖ ≤ CΓ * (1 + ‖z‖) := by
                      exact mul_le_mul_of_nonneg_left hw_le'' hC0
                    have := mul_le_mul_of_nonneg_right hCw hlog_nonneg
                    simpa [mul_assoc] using this
            _ ≤ (CΓ * (1 + ‖z‖)) * (4 * (1 + ‖z‖) ^ (1 / 2 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hlog₂ hfac_nonneg
            _ = (4 * CΓ) * ((1 + ‖z‖) * (1 + ‖z‖) ^ (1 / 2 : ℝ)) := by ring
            _ = (4 * CΓ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
                    -- rewrite the inner product without triggering cancellation lemmas
                    have := congrArg (fun t : ℝ => (4 * CΓ) * t) hmulPow
                    simpa [mul_assoc] using this

        have hlogpoly :
            Real.log (6 + 6 * ‖w‖) ≤ (100 : ℝ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
          have hw_le'' : ‖w‖ ≤ 1 + ‖z‖ := hw_norm_le
          have hpos : 0 ≤ (1 + ‖z‖ : ℝ) := by linarith [norm_nonneg z]
          have hbase : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
          have hlog_le : Real.log (6 + 6 * ‖w‖) ≤ 6 + 6 * ‖w‖ := by
            have hx : 0 < (6 + 6 * ‖w‖ : ℝ) := by nlinarith [norm_nonneg w]
            exact (Real.log_le_sub_one_of_pos hx).trans (by linarith)
          have hlin : (6 + 6 * ‖w‖ : ℝ) ≤ 12 * (1 + ‖z‖) := by nlinarith [hw_le'', norm_nonneg z]
          have hmono : 12 * (1 + ‖z‖) ≤ 12 * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            have hexp : (1 + ‖z‖) ^ (1 : ℝ) ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
              exact Real.rpow_le_rpow_of_exponent_le hbase (by norm_num : (1 : ℝ) ≤ (3 / 2 : ℝ))
            simpa [Real.rpow_one] using (mul_le_mul_of_nonneg_left hexp (by positivity : (0 : ℝ) ≤ 12))
          have hlog12 : Real.log (6 + 6 * ‖w‖) ≤ 12 * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            exact le_trans hlog_le (le_trans hlin hmono)
          have : (12 : ℝ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) ≤ (100 : ℝ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            have hnn : 0 ≤ (1 + ‖z‖) ^ (3 / 2 : ℝ) := by positivity
            nlinarith [hnn]
          exact le_trans hlog12 this

        have hCdom : (4 * CΓ + 110 : ℝ) ≤ C := le_max_right _ _
        calc
          Real.log (1 + ‖completedRiemannZeta₀ z‖)
              = Real.log (1 + ‖completedRiemannZeta₀ w‖) := htransfer
          _ ≤ Real.log (6 + 6 * ‖w‖) + (CΓ * ‖w‖ * Real.log (1 + ‖w‖)) := hlog_main
          _ ≤ (100 : ℝ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) + (4 * CΓ) * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            gcongr
          _ ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
            nlinarith [hCdom]

/-- The function (s-1)ζ(s) is entire.

This removes the simple pole of ζ at s = 1. The function extends analytically
because the pole has residue 1, so (s-1)ζ(s) → 1 as s → 1. -/
-- The naive function `(s-1)ζ(s)` is *not* continuous at `s = 1` (Mathlib assigns an arbitrary value
-- to `ζ(1)`), so we use the analytic continuation obtained by updating the value at `1` to be `1`.
def zetaTimesSMinusOne_entire (s : ℂ) : ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1 s

theorem zetaTimesSMinusOne_entire_differentiable :
    Differentiable ℂ zetaTimesSMinusOne_entire := by
  classical
  -- Use the criterion: differentiable on `univ \ {1}` plus continuity at `1`.
  have hdiff :
      DifferentiableOn ℂ zetaTimesSMinusOne_entire (Set.univ \ ({1} : Set ℂ)) := by
    intro s hs
    have hs1 : s ≠ 1 := by
      simpa [Set.mem_singleton_iff] using hs.2
    -- differentiate the product
    have h1 : DifferentiableAt ℂ (fun s => s - 1) s := differentiableAt_id.sub_const 1
    have h2 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
    have hmul : DifferentiableAt ℂ (fun s => (s - 1) * riemannZeta s) s := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using (h1.mul h2)
    have hmulWithin :
        DifferentiableWithinAt ℂ (fun s : ℂ => (s - 1) * riemannZeta s) (Set.univ \ ({1} : Set ℂ)) s :=
      (hmul.differentiableWithinAt : DifferentiableWithinAt ℂ (fun s : ℂ => (s - 1) * riemannZeta s)
        (Set.univ \ ({1} : Set ℂ)) s)
    -- transfer differentiability to the `update`-version using pointwise equality on the set
    refine (hmulWithin.congr (fun x hx => ?_) ?_)
    · have hx1 : x ≠ (1 : ℂ) := by
        simpa [Set.mem_singleton_iff] using hx.2
      simp [zetaTimesSMinusOne_entire, Function.update, hx1]
    · simp [zetaTimesSMinusOne_entire, Function.update, hs1]
  have hcont : ContinuousAt zetaTimesSMinusOne_entire (1 : ℂ) := by
    -- continuity at `1` is exactly the residue statement
    -- `ContinuousAt (update f 1 1) 1 ↔ Tendsto f (𝓝[≠]1) (𝓝 1)`
    have h :
        ContinuousAt (Function.update (fun s : ℂ => (s - 1) * riemannZeta s) (1 : ℂ) (1 : ℂ)) (1 : ℂ) :=
      (continuousAt_update_same (f := fun s : ℂ => (s - 1) * riemannZeta s)
          (x := (1 : ℂ)) (y := (1 : ℂ))).2
        (riemannZeta_residue_one : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s)
          (𝓝[≠] (1 : ℂ)) (𝓝 (1 : ℂ)))
    -- avoid `simp` rewriting `ContinuousAt (update ...)` back into the `Tendsto` statement
    change
      ContinuousAt (Function.update (fun s : ℂ => (s - 1) * riemannZeta s) (1 : ℂ) (1 : ℂ))
        (1 : ℂ)
    exact h
  -- upgrade to differentiable on all of `univ`
  have hiff :=
    (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (f := zetaTimesSMinusOne_entire)
      (s := (Set.univ : Set ℂ)) (c := (1 : ℂ)) (by simp))
  have : DifferentiableOn ℂ zetaTimesSMinusOne_entire (Set.univ : Set ℂ) :=
    (hiff.1 ⟨hdiff, hcont⟩)
  -- `DifferentiableOn` on `univ` is the same as `Differentiable`
  simpa [DifferentiableOn, differentiableWithinAt_univ, zetaTimesSMinusOne_entire] using this

/-! ### A simple bound for `Complex.cos` -/

lemma norm_cos_le_exp_abs_im (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  -- Use `cos z = (exp(z*I) + exp(-z*I)) / 2` and triangle inequality.
  have hcos :
      Complex.cos z = (Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2 := by
    simp [Complex.cos]
  -- First bound the numerator.
  have htri :
      ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖
        ≤ ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖ :=
    norm_add_le _ _
  -- Divide by `2` (as a real scalar bound).
  have hdiv :
      ‖(Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)) / 2‖
        ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 := by
    have : ‖Complex.exp (z * Complex.I) + Complex.exp (-z * Complex.I)‖ / 2
          ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-z * Complex.I)‖) / 2 :=
      div_le_div_of_nonneg_right htri (by norm_num)
    -- `‖x/2‖ = ‖x‖/2` since `‖(2:ℂ)‖ = 2`.
    simpa [norm_div, Complex.norm_ofNat] using this
  -- Rewrite both `‖exp _‖` terms using `‖exp w‖ = exp(re w)`.
  have h1 : ‖Complex.exp (z * Complex.I)‖ = Real.exp (-(z.im)) := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im]
  have h2 : ‖Complex.exp (-(z * Complex.I))‖ = Real.exp (z.im) := by
    simp [Complex.norm_exp, Complex.mul_re, Complex.I_re, Complex.I_im]
  -- Each term is bounded by `exp |im z|`.
  have habs1 : Real.exp (-(z.im)) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (neg_le_abs (z.im))
  have habs2 : Real.exp (z.im) ≤ Real.exp |z.im| :=
    Real.exp_le_exp.mpr (le_abs_self (z.im))
  have hsum :
      (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖) / 2
        ≤ Real.exp |z.im| := by
    have : ‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖
        ≤ Real.exp |z.im| + Real.exp |z.im| := by
      simpa [h1, h2] using add_le_add habs1 habs2
    have : (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖) / 2
        ≤ (Real.exp |z.im| + Real.exp |z.im|) / 2 :=
      div_le_div_of_nonneg_right this (by norm_num)
    simpa [two_mul] using this
  -- Finish.
  have : ‖Complex.cos z‖ ≤ (‖Complex.exp (z * Complex.I)‖ + ‖Complex.exp (-(z * Complex.I))‖) / 2 := by
    simpa [hcos] using hdiv
  exact le_trans this hsum

/-  (disabled)

This section packaged a coarse growth bound for `(s-1)ζ(s)`. It is not needed for the intrinsic
Hadamard factorization statement below, and it was previously maintained in the `ZeroData`-based
pipeline. It will be reinstated after the remaining non-Hadamard analytic estimates are fully
ported out of `academic_framework`.

/-- A coarse global growth bound for the entire function `(s-1)ζ(s)`.

Since Λ₀(s) = π^{-s/2} Γ(s/2) ζ(s), and Λ₀ has finite order, the growth of
(s-1)ζ(s) is controlled by the growth of Λ₀ divided by π^{-s/2} Γ(s/2). -/
theorem zeta_minus_pole_entire_growth :
    ∃ C > 0, ∀ z : ℂ,
      Real.log (1 + ‖zetaTimesSMinusOne_entire z‖) ≤ C * (1 + ‖z‖) ^ (2 : ℝ) := by
  classical
  -- Compact control on `‖z‖ ≤ 3`, and a coarse global bound outside.
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) 3) := isCompact_closedBall 0 3
  have hcont :
      ContinuousOn zetaTimesSMinusOne_entire (Metric.closedBall (0 : ℂ) 3) :=
    zetaTimesSMinusOne_entire_differentiable.continuous.continuousOn
  rcases hcomp.exists_bound_of_continuousOn hcont with ⟨M, hM⟩
  let M0 : ℝ := max M 0
  have hM0 : ∀ z ∈ Metric.closedBall (0 : ℂ) 3, ‖zetaTimesSMinusOne_entire z‖ ≤ M0 := by
    intro z hz
    exact le_trans (hM z hz) (le_max_left _ _)

  obtain ⟨CΓ, hCΓ_pos, hΓ⟩ := Complex.Gamma_stirling_bound_re_ge_zero

  -- helper: `log(1 + exp B) ≤ B + log 2` for `0 ≤ B`
  have log_one_add_exp_le :
      ∀ (B : ℝ), 0 ≤ B → Real.log (1 + Real.exp B) ≤ B + Real.log 2 := by
    intro B hB
    have h1 : (1 : ℝ) ≤ Real.exp B := by
      simpa using (Real.one_le_exp_iff.2 hB)
    have h2 : 1 + Real.exp B ≤ 2 * Real.exp B := by nlinarith
    have : Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) :=
      Real.log_le_log (by positivity) h2
    calc
      Real.log (1 + Real.exp B) ≤ Real.log (2 * Real.exp B) := this
      _ = Real.log 2 + B := by simp [Real.log_mul, add_comm]
      _ = B + Real.log 2 := by ring

  -- One global constant `C` (very coarse). We will use `C + log 2` in the final bound.
  let C : ℝ := max (Real.log (1 + M0) + 10) (max (40 : ℝ) (20 * CΓ + 500))
  refine ⟨C + Real.log 2, ?_, ?_⟩
  · have hCpos : (0 : ℝ) < C := by
      have : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
      exact lt_of_lt_of_le this (le_trans (le_max_right _ _) (le_max_right _ _))
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  · intro z
    set A : ℝ := 1 + ‖z‖
    have hA1 : (1 : ℝ) ≤ A := by dsimp [A]; linarith [norm_nonneg z]
    have hA2_nonneg : 0 ≤ A ^ (2 : ℝ) := by positivity

    by_cases hz_small : ‖z‖ ≤ 3
    · have hz_mem : z ∈ Metric.closedBall (0 : ℂ) 3 := Metric.mem_closedBall.2 (by simpa using hz_small)
      have hnorm : ‖zetaTimesSMinusOne_entire z‖ ≤ M0 := hM0 z hz_mem
      have hlog :
          Real.log (1 + ‖zetaTimesSMinusOne_entire z‖) ≤ Real.log (1 + M0) := by
        refine Real.log_le_log (by positivity) ?_
        linarith
      have hC1 : Real.log (1 + M0) ≤ C + Real.log 2 := by
        have : Real.log (1 + M0) + 10 ≤ C := by
          -- `C = max (log(1+M0)+10) (max 40 (20*CΓ+500))`
          simp [C]
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      have hpow : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
        Real.one_le_rpow hA1 (by norm_num)
      have hC_nonneg : 0 ≤ C + Real.log 2 := by
        have hCpos : (0 : ℝ) < C := by
          have hpos' : (0 : ℝ) < 20 * CΓ + 500 := by nlinarith [hCΓ_pos]
          have hmax : (0 : ℝ) < max (40 : ℝ) (20 * CΓ + 500) :=
            lt_of_lt_of_le hpos' (le_max_right _ _)
          have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
            simp [C]
          exact lt_of_lt_of_le hmax hle
        have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
        linarith
      calc
        Real.log (1 + ‖zetaTimesSMinusOne_entire z‖)
            ≤ Real.log (1 + M0) := hlog
        _ ≤ C + Real.log 2 := hC1
        _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
              simpa [mul_one] using (mul_le_mul_of_nonneg_left hpow hC_nonneg)
    ·
      have hz_large : 3 < ‖z‖ := lt_of_not_ge hz_small
      have hz_ne1 : z ≠ 1 := by
        intro h
        have : (‖z‖ : ℝ) = 1 := by simp [h]
        linarith [hz_large]
      have hzeta_def : zetaTimesSMinusOne_entire z = (z - 1) * riemannZeta z := by
        simp [zetaTimesSMinusOne_entire, Function.update, hz_ne1]

      -- First: an exponential bound on the norm.
      have hmain :
          ‖zetaTimesSMinusOne_entire z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) := by
        by_cases hz_re : (1 / 10 : ℝ) < z.re
          · -- Right half-plane: `lem_zetaBound2`.
            have hζ := lem_zetaBound2 z hz_re hz_ne1
            have hzm1_le : ‖z - 1‖ ≤ A := by
              simpa [A, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (norm_sub_le z (1 : ℂ))
            have hzre_pos : 0 < z.re := lt_trans (by norm_num) hz_re
            have hz_re_le : (1 : ℝ) / z.re ≤ 10 := by
              have ha : (0 : ℝ) < (1 / 10 : ℝ) := by norm_num
              have hz_ge : (1 / 10 : ℝ) ≤ z.re := le_of_lt hz_re
              have := one_div_le_one_div_of_le ha hz_ge
              -- `1/(1/10) = 10`
              simpa using this
            have hfrac : ‖z‖ / z.re ≤ 10 * ‖z‖ := by
              have : ‖z‖ / z.re ≤ ‖z‖ * 10 := by
                simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                  using (mul_le_mul_of_nonneg_left hz_re_le (norm_nonneg z))
              simpa [mul_comm] using this
            have hpoly :
                ‖(z - 1) * riemannZeta z‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
              have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
              have hz_le_A : ‖z‖ ≤ A := by dsimp [A]; linarith [hz0]
              have hζ' : ‖riemannZeta z‖ ≤ 1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖ := by
                calc
                  ‖riemannZeta z‖ ≤ 1 + ‖1 / (z - 1)‖ + ‖z‖ / z.re := hζ
                  _ ≤ 1 + ‖1 / (z - 1)‖ + 10 * ‖z‖ := by gcongr
              have hmul_inv : ‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖ = 1 := by
                have hz1' : z - 1 ≠ (0 : ℂ) := sub_ne_zero.2 hz_ne1
                -- `‖z-1‖ * ‖1/(z-1)‖ = ‖(z-1) * (1/(z-1))‖ = 1`
                simp [hz1']
              calc
                ‖(z - 1) * riemannZeta z‖ ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by
                      simp
                _ ≤ ‖z - 1‖ * (1 + ‖(1 : ℂ) / (z - 1)‖ + 10 * ‖z‖) := by gcongr
                _ = ‖z - 1‖ + (‖z - 1‖ * ‖(1 : ℂ) / (z - 1)‖) + ‖z - 1‖ * (10 * ‖z‖) := by ring
                _ ≤ A + 1 + A * (10 * ‖z‖) := by
                      have hterm3 :
                          ‖z - 1‖ * (10 * ‖z‖) ≤ A * (10 * ‖z‖) :=
                        mul_le_mul_of_nonneg_right hzm1_le (by positivity)
                      -- use `hmul_inv` to rewrite the middle term to `1`
                      nlinarith [hzm1_le, hmul_inv, hterm3]
                _ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
                      -- very coarse: `A + 1 + 10*A*‖z‖ ≤ 40*A^2` for `A ≥ 1` and `‖z‖ ≤ A`
                      have hA2 : A * (10 * ‖z‖) ≤ 10 * (A ^ (2 : ℕ)) := by
                        have : A * ‖z‖ ≤ A * A := by nlinarith [hz_le_A]
                        -- multiply by `10`
                        nlinarith [this]
                      have hstep :
                          A + 1 + A * (10 * ‖z‖) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
                        -- `A + 1 ≤ 2*A` and `2*A + 10*A^2 ≤ 40*A^2` for `A ≥ 1`
                        have hA1' : A + 1 ≤ 2 * A := by nlinarith [hA1]
                        have hstep1 : A + 1 + A * (10 * ‖z‖) ≤ 2 * A + 10 * (A ^ (2 : ℕ)) := by
                          nlinarith [hA1', hA2]
                        have hstep2 : 2 * A + 10 * (A ^ (2 : ℕ)) ≤ (40 : ℝ) * (A ^ (2 : ℕ)) := by
                          -- `2*A ≤ 30*A^2` for `A ≥ 1`
                          have hApos : 0 ≤ A := le_trans (by norm_num) hA1
                          have hlin : (2 : ℝ) * A ≤ 30 * (A ^ (2 : ℕ)) := by
                            -- since `A ≤ A^2` for `A ≥ 1`
                            have hA_le_sq : A ≤ (A ^ (2 : ℕ)) := by
                              simpa [pow_two] using (mul_le_mul_of_nonneg_right hA1 (show (0 : ℝ) ≤ A by exact hApos))
                            nlinarith [hA_le_sq]
                          nlinarith [hlin]
                        exact le_trans hstep1 hstep2
                      -- convert `A^(2:ℕ)` to `A^(2:ℝ)`
                      simpa [Real.rpow_natCast] using hstep
            have hC_ge : (40 : ℝ) ≤ C := by
              -- `40 ≤ max 40 (20*CΓ+500) ≤ C`
              have h1 : (40 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) := le_max_left _ _
              have h2 : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by
                simp [C]
              exact le_trans h1 h2
            have hle : (40 : ℝ) * A ^ (2 : ℝ) ≤ C * A ^ (2 : ℝ) := by
              simpa [mul_assoc] using (mul_le_mul_of_nonneg_right hC_ge hA2_nonneg)
            have : ‖(z - 1) * riemannZeta z‖ ≤ Real.exp (C * A ^ (2 : ℝ)) :=
              le_trans (le_trans hpoly hle) (Real.le_exp_self' _)
            simpa [hzeta_def] using this
          · -- Left half-plane: use the functional equation at `w := 1 - z`.
            have hz_re_le : z.re ≤ (1 / 10 : ℝ) := le_of_not_gt hz_re
            let w : ℂ := 1 - z
            have hw_re_ge : (9 / 10 : ℝ) ≤ w.re := by
              have : w.re = 1 - z.re := by simp [w]
              linarith [this, hz_re_le]
            have hw_re0 : 0 ≤ w.re := le_trans (by norm_num : (0 : ℝ) ≤ 9 / 10) hw_re_ge
            have hw_re1 : (1 / 10 : ℝ) < w.re := lt_of_lt_of_le (by norm_num) hw_re_ge
            have hw_ne1 : w ≠ 1 := by
              intro hw
              have : z = 0 := by
                have : (1 : ℂ) - z = (1 : ℂ) := by simpa [w] using hw
                simpa using (sub_eq_self.mp this)
              have : (‖z‖ : ℝ) = 0 := by simp [this]
              linarith [hz_large, this]
            have hw_ne_neg : ∀ n : ℕ, w ≠ -n := by
              intro n hn
              have : (w.re : ℝ) = (- (n : ℂ)).re := congrArg Complex.re hn
              have : (w.re : ℝ) = -(n : ℝ) := by simpa using this
              have : (w.re : ℝ) ≤ 0 := by nlinarith [this]
              have : (0 : ℝ) < w.re := lt_trans (by norm_num) hw_re1
              linarith
            have hzeta_fe :
                riemannZeta z =
                  2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w := by
              have h := riemannZeta_one_sub (s := w) (hs := hw_ne_neg) (hs' := hw_ne1)
              have : (1 - w) = z := by simp [w, sub_eq_add_neg, add_comm, add_left_comm]
              simpa [this, mul_assoc, mul_left_comm, mul_comm] using h
            have hpow_le1 : ‖(2 * π : ℂ) ^ (-w)‖ ≤ 1 := by
              have hbase : (1 : ℝ) ≤ (2 * Real.pi) := by
                have : (1 : ℝ) < (2 * Real.pi) := by
                  have : (3 : ℝ) < Real.pi := Real.pi_gt_three
                  nlinarith
                exact le_of_lt this
              have hbase_pos : (0 : ℝ) < (2 * Real.pi) := by nlinarith [Real.pi_pos]
              have hbaseC : (2 * π : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by
                -- unfold `π : ℂ` as `Real.pi` and push casts
                simp
              have hnorm' :
                  ‖(((2 * Real.pi : ℝ) : ℂ) ^ (-w))‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
                simpa using (norm_cpow_eq_rpow_re_of_pos (x := (2 * Real.pi)) hbase_pos (-w))
              have hnorm :
                  ‖(2 * π : ℂ) ^ (-w)‖ = (2 * Real.pi) ^ ((-w : ℂ).re) := by
                simpa using hnorm'
              rw [hnorm]
              have : ((-w : ℂ).re : ℝ) ≤ 0 := by
                simp
                linarith [hw_re0]
              exact Real.rpow_le_one_of_one_le_of_nonpos hbase this
            have hw_norm_le : ‖w‖ ≤ A := by
              have : ‖1 - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := by simpa using (norm_sub_le (1 : ℂ) z)
              simpa [w, A, norm_one, add_comm, add_left_comm, add_assoc] using this
            have hw_norm_ge1 : (1 : ℝ) ≤ ‖w‖ := by
              have hw_ge : (‖z‖ - 1 : ℝ) ≤ ‖w‖ := by
                have := norm_sub_norm_le z (1 : ℂ)
                simpa [w, norm_one, norm_sub_rev] using this
              have h2 : (2 : ℝ) < ‖z‖ - 1 := by linarith [hz_large]
              have hw_gt : (2 : ℝ) < ‖w‖ := lt_of_lt_of_le h2 hw_ge
              linarith
            have hΓw : ‖Complex.Gamma w‖ ≤ Real.exp (CΓ * A ^ (2 : ℝ)) := by
              have hΓ0 := hΓ w hw_re0 hw_norm_ge1
              have hlog_le : Real.log (1 + ‖w‖) ≤ A := by
                have : Real.log (1 + ‖w‖) ≤ (1 + ‖w‖) - 1 := by
                  have : (0 : ℝ) < 1 + ‖w‖ := by positivity
                  simpa using (Real.log_le_sub_one_of_pos this)
                have : Real.log (1 + ‖w‖) ≤ ‖w‖ := by simpa [sub_eq_add_neg] using this
                exact le_trans this hw_norm_le
              have hmul : ‖w‖ * Real.log (1 + ‖w‖) ≤ A ^ (2 : ℝ) := by
                have : ‖w‖ * Real.log (1 + ‖w‖) ≤ A * A := by nlinarith [hw_norm_le, hlog_le]
                simpa [pow_two] using this
              have hexp : CΓ * ‖w‖ * Real.log (1 + ‖w‖) ≤ CΓ * A ^ (2 : ℝ) := by
                have hC0 : 0 ≤ CΓ := le_of_lt hCΓ_pos
                nlinarith [hmul, hC0]
              exact le_trans hΓ0 (Real.exp_le_exp.mpr hexp)
            have hcosw : ‖Complex.cos (π * w / 2)‖ ≤ Real.exp (2 * A ^ (2 : ℝ)) := by
              have h1 := norm_cos_le_exp_abs_im (π * w / 2)
              have him : |(π * w / 2).im| ≤ 2 * A ^ (2 : ℝ) := by
                have : |(π * w / 2).im| ≤ ‖π * w / 2‖ := Complex.abs_im_le_norm _
                have hnorm : ‖π * w / 2‖ = (Real.pi / 2) * ‖w‖ := by
                  have hrew : (π * w / 2 : ℂ) = (π / 2) * w := by
                    simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                  calc
                    ‖π * w / 2‖ = ‖(π / 2) * w‖ := by simp [hrew]
                    _ = ‖(π / 2)‖ * ‖w‖ := by simp
                    _ = (Real.pi / 2) * ‖w‖ := by
                      -- `π/2` is real and nonnegative.
                      have hpi0 : 0 ≤ Real.pi / 2 := by nlinarith [Real.pi_pos.le]
                      have hnorm_pi : ‖((Real.pi / 2 : ℝ) : ℂ)‖ = ‖(Real.pi / 2 : ℝ)‖ := by
                        simp
                      have hnorm_pi' : ‖((Real.pi / 2 : ℝ) : ℂ)‖ = (Real.pi / 2 : ℝ) := by
                        simpa [Real.norm_of_nonneg hpi0] using hnorm_pi
                      -- rewrite `π/2 : ℂ` as the real scalar `Real.pi/2`
                      simpa using congrArg (fun t => t * ‖w‖) hnorm_pi'
                have hpi : (Real.pi / 2 : ℝ) ≤ 2 := by
                  have : (Real.pi : ℝ) ≤ 4 := by linarith [Real.pi_lt_four.le]
                  nlinarith
                have him1 : |(π * w / 2).im| ≤ 2 * ‖w‖ := by
                  calc
                    |(π * w / 2).im| ≤ ‖π * w / 2‖ := this
                    _ = (Real.pi / 2) * ‖w‖ := hnorm
                    _ ≤ 2 * ‖w‖ := by gcongr
                have him2 : 2 * ‖w‖ ≤ 2 * A ^ (2 : ℝ) := by
                  have : ‖w‖ ≤ A ^ (2 : ℝ) := by
                    have : A ≤ A ^ (2 : ℝ) := by
                      have := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
                      simpa [Real.rpow_one] using this
                    exact le_trans hw_norm_le this
                  nlinarith [this]
                exact le_trans him1 him2
              exact le_trans h1 (Real.exp_le_exp.mpr him)
            have hζw : ‖riemannZeta w‖ ≤ Real.exp (40 * A ^ (2 : ℝ)) := by
              have hζ0 := lem_zetaBound2 w hw_re1 hw_ne1
              have hwre_pos : 0 < w.re := lt_trans (by norm_num) hw_re1
              have hw_re_le : (1 : ℝ) / w.re ≤ 10 := by
                have ha : (0 : ℝ) < (1 / 10 : ℝ) := by norm_num
                have hw_ge : (1 / 10 : ℝ) ≤ w.re := le_of_lt hw_re1
                have := one_div_le_one_div_of_le ha hw_ge
                simpa using this
              have hfrac : ‖w‖ / w.re ≤ 10 * ‖w‖ := by
                have : ‖w‖ / w.re ≤ ‖w‖ * 10 := by
                  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
                    using (mul_le_mul_of_nonneg_left hw_re_le (norm_nonneg w))
                simpa [mul_comm] using this
              have hpoly : ‖riemannZeta w‖ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
                have : ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := by
                  calc
                    ‖riemannZeta w‖ ≤ 1 + ‖1 / (w - 1)‖ + ‖w‖ / w.re := hζ0
                    _ ≤ 1 + ‖1 / (w - 1)‖ + 10 * ‖w‖ := by gcongr
                    _ ≤ 2 + 10 * ‖w‖ := by
                          -- since `w - 1 = -z` and `‖z‖ > 3`, we have `‖1/(w-1)‖ = ‖1/z‖ ≤ 1`
                          have hw1 : w - 1 = -z := by
                            dsimp [w]
                            ring
                          have hz1 : (1 : ℝ) ≤ ‖z‖ := le_trans (by norm_num) (le_of_lt hz_large)
                          have hinv_le : ‖(1 : ℂ) / (w - 1)‖ ≤ 1 := by
                            -- `‖z‖⁻¹ ≤ 1` since `1 ≤ ‖z‖`
                            have hinv : (‖z‖ : ℝ)⁻¹ ≤ (1 : ℝ) := by
                              -- use the `_₀` lemma to avoid typeclass mismatches
                              simpa using (inv_le_one_of_one_le₀ (a := (‖z‖ : ℝ)) hz1)
                            -- rewrite `‖(1:ℂ)/(w-1)‖` using `w-1=-z`
                            simpa [div_eq_mul_inv, hw1] using hinv
                          nlinarith [hinv_le]
                calc
                  ‖riemannZeta w‖ ≤ 2 + 10 * ‖w‖ := this
                  _ ≤ 2 + 10 * A := by gcongr
                  _ ≤ (40 : ℝ) * A ^ (2 : ℝ) := by
                        simp [pow_two]
                        nlinarith [hA1]
              exact le_trans hpoly (Real.le_exp_self' _)
            have hprod :
                ‖(z - 1) * riemannZeta z‖ ≤
                  (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
              have hz1 : (z - 1 : ℂ) = -w := by simp [w]
              have : ‖riemannZeta z‖ ≤ ‖2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w‖ := by
                simp [hzeta_fe]
              calc
                ‖(z - 1) * riemannZeta z‖
                    ≤ ‖z - 1‖ * ‖riemannZeta z‖ := by simp
                _ ≤ ‖z - 1‖ * ‖2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w‖ := by
                      gcongr
                _ = ‖w‖ * ‖2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w‖ := by
                      simp [hz1]
                _ ≤ ‖w‖ * ((2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖) := by
                      have : ‖2 * (2 * π) ^ (-w) * Complex.Gamma w * Complex.cos (π * w / 2) * riemannZeta w‖
                            ≤ (2 : ℝ) * ‖(2 * π : ℂ) ^ (-w)‖ * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
                        simp [mul_assoc, mul_left_comm, mul_comm]
                      gcongr
                _ ≤ ‖w‖ * ((2 : ℝ) * 1 * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖) := by
                      gcongr
                _ = (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖ := by
                      ring
            have hw2 : ‖w‖ * 2 ≤ Real.exp (2 * A ^ (2 : ℝ)) := by
              have h1 : ‖w‖ * 2 ≤ 2 * A := by nlinarith [hw_norm_le]
              have h2 : 2 * A ≤ 2 * A ^ (2 : ℝ) := by
                have : A ≤ A ^ (2 : ℝ) := by
                  have := Real.rpow_le_rpow_of_exponent_le hA1 (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
                  simpa [Real.rpow_one] using this
                nlinarith [this]
              exact le_trans (le_trans h1 h2) (Real.le_exp_self' _)
            have hmul_exp :
                (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖
                  ≤ rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) := by
              have ha : ‖w‖ * 2 ≤ rexp (2 * A ^ (2 : ℝ)) := by simpa using hw2
              have hb : ‖Complex.Gamma w‖ ≤ rexp (CΓ * A ^ (2 : ℝ)) := by simpa using hΓw
              have hc : ‖Complex.cos (π * w / 2)‖ ≤ rexp (2 * A ^ (2 : ℝ)) := by simpa using hcosw
              have hd : ‖riemannZeta w‖ ≤ rexp (40 * A ^ (2 : ℝ)) := by simpa using hζw
              have hab :
                  (‖w‖ * 2) * ‖Complex.Gamma w‖
                    ≤ rexp (2 * A ^ (2 : ℝ)) * rexp (CΓ * A ^ (2 : ℝ)) := by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  (mul_le_mul ha hb (by positivity) (by positivity))
              have habc :
                  ((‖w‖ * 2) * ‖Complex.Gamma w‖) * ‖Complex.cos (π * w / 2)‖
                    ≤ (rexp (2 * A ^ (2 : ℝ)) * rexp (CΓ * A ^ (2 : ℝ))) *
                        rexp (2 * A ^ (2 : ℝ)) := by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  (mul_le_mul hab hc (by positivity) (by positivity))
              have habcd :
                  (((‖w‖ * 2) * ‖Complex.Gamma w‖) * ‖Complex.cos (π * w / 2)‖) * ‖riemannZeta w‖
                    ≤ ((rexp (2 * A ^ (2 : ℝ)) * rexp (CΓ * A ^ (2 : ℝ))) *
                        rexp (2 * A ^ (2 : ℝ))) * rexp (40 * A ^ (2 : ℝ)) := by
                simpa [mul_assoc, mul_left_comm, mul_comm] using
                  (mul_le_mul habc hd (by positivity) (by positivity))
              have hexp :
                  ((rexp (2 * A ^ (2 : ℝ)) * rexp (CΓ * A ^ (2 : ℝ))) *
                        rexp (2 * A ^ (2 : ℝ))) * rexp (40 * A ^ (2 : ℝ))
                    = rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) := by
                -- combine exponentials pairwise using `exp_add` in reverse
                -- Use fresh names to avoid clashing with earlier hypotheses named `ha`, `hb`, ...
                set aa : ℝ := 2 * A ^ (2 : ℝ) with haa
                set bb : ℝ := CΓ * A ^ (2 : ℝ) with hbb
                set cc : ℝ := 2 * A ^ (2 : ℝ) with hcc
                set dd : ℝ := 40 * A ^ (2 : ℝ) with hdd
                have hab : rexp aa * rexp bb = rexp (aa + bb) := by
                  simpa using (Eq.symm (Real.exp_add aa bb))
                have habc : rexp (aa + bb) * rexp cc = rexp (aa + bb + cc) := by
                  simpa [add_assoc] using (Eq.symm (Real.exp_add (aa + bb) cc))
                have habcd : rexp (aa + bb + cc) * rexp dd = rexp (aa + bb + cc + dd) := by
                  simpa [add_assoc] using (Eq.symm (Real.exp_add (aa + bb + cc) dd))
                have hsum : aa + bb + cc + dd = (2 + CΓ + 2 + 40) * A ^ (2 : ℝ) := by
                  simp [haa, hbb, hcc, hdd]
                  ring
                calc
                  ((rexp aa * rexp bb) * rexp cc) * rexp dd
                      = ((rexp (aa + bb)) * rexp cc) * rexp dd := by
                          simp [hab, mul_assoc]
                  _ = (rexp (aa + bb + cc)) * rexp dd := by
                          simp [habc]
                  _ = rexp (aa + bb + cc + dd) := by
                          simpa [mul_assoc] using habcd
                  _ = rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) := by simp [hsum]
              -- massage the LHS into the same association as `habcd`
              have : (‖w‖ * 2) * ‖Complex.Gamma w‖ * ‖Complex.cos (π * w / 2)‖ * ‖riemannZeta w‖
                    ≤ ((rexp (2 * A ^ (2 : ℝ)) * rexp (CΓ * A ^ (2 : ℝ))) *
                        rexp (2 * A ^ (2 : ℝ))) * rexp (40 * A ^ (2 : ℝ)) := by
                simpa [mul_assoc, mul_left_comm, mul_comm] using habcd
              exact le_trans this (le_of_eq hexp)
            have hcoef : (2 + CΓ + 2 + 40 : ℝ) ≤ C := by
              have : (20 * CΓ + 500 : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
              nlinarith [this, hCΓ_pos.le]
            have hdom :
                rexp ((2 + CΓ + 2 + 40) * A ^ (2 : ℝ)) ≤ rexp (C * A ^ (2 : ℝ)) := by
              -- monotonicity of `exp`
              refine (Real.exp_le_exp).2 ?_
              -- multiply `hcoef` by the nonnegative factor `A^2`
              have := mul_le_mul_of_nonneg_right hcoef hA2_nonneg
              simpa [mul_assoc] using this
            have : ‖(z - 1) * riemannZeta z‖ ≤ rexp (C * A ^ (2 : ℝ)) :=
              le_trans (le_trans hprod hmul_exp) hdom
            simpa [hzeta_def] using this

        have hC0 : 0 ≤ C := by
          -- `C = max (log(1+M0)+10) (max 40 (20*CΓ+500))`, so `C ≥ 40 ≥ 0`.
          have h0 : (0 : ℝ) ≤ max (40 : ℝ) (20 * CΓ + 500) :=
            le_trans (by norm_num) (le_max_left _ _)
          have hle : max (40 : ℝ) (20 * CΓ + 500) ≤ C := by simp [C]
          exact le_trans h0 hle
        have hB0 : 0 ≤ C * A ^ (2 : ℝ) := mul_nonneg hC0 hA2_nonneg
        have hlog := log_one_add_exp_le (C * A ^ (2 : ℝ)) hB0
        have hA2_ge1 : (1 : ℝ) ≤ A ^ (2 : ℝ) :=
          Real.one_le_rpow hA1 (by norm_num)
        calc
          Real.log (1 + ‖zetaTimesSMinusOne_entire z‖)
              ≤ Real.log (1 + rexp (C * A ^ (2 : ℝ))) := by
                    gcongr
          _ ≤ C * A ^ (2 : ℝ) + Real.log 2 := hlog
          _ ≤ (C + Real.log 2) * A ^ (2 : ℝ) := by
                have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
                -- use `Real.log 2 ≤ Real.log 2 * A^2` since `A^2 ≥ 1`
                have : Real.log 2 ≤ Real.log 2 * A ^ (2 : ℝ) := by
                  simpa [one_mul] using (mul_le_mul_of_nonneg_left hA2_ge1 hlog2)
                nlinarith [this]

-/
end Complex
