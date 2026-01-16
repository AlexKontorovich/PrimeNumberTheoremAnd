import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.GammaStirlingAux

/-!
# Stirling-type bounds for the complex Gamma function

This file provides polynomial and exponential growth bounds for the complex Gamma function
in the right half-plane, based on Stirling's asymptotic formula.

## Main results

* `Gamma_stirling_core`: For `Re(s) ≥ 1/2` and `‖s‖ ≥ A`, we have
  `‖Γ(s)‖ ≤ exp(C‖s‖ log(B‖s‖))` for explicit constants `C, A, B`.

## Mathematical Background

The bounds follow from:
1. **Strip bounds**: For `a ≤ Re(s) ≤ 1` with `a > 0`, `‖Γ(s)‖ ≤ 1/a + √π`
2. **Functional equation**: `Γ(s+1) = s·Γ(s)` allows reduction from large Re(s) to strips
3. **Stirling's formula**: For large |s|, `Γ(s) ~ √(2π) s^{s-1/2} e^{-s}`

## References

* Titchmarsh, "The Theory of the Riemann Zeta-Function", Chapter 4
* Iwaniec-Kowalski, "Analytic Number Theory", Appendix B
-/

open Complex Real Set Filter Asymptotics
open scoped Topology

namespace GammaBounds

/-! ## Part 1: Elementary inequalities -/

/-- Re(s) ≤ |s| for any complex s. -/
lemma norm_ge_re (s : ℂ) : s.re ≤ ‖s‖ := le_of_abs_le (Complex.abs_re_le_norm s)

/-- |Im(s)| ≤ |s| for any complex s. -/
lemma norm_ge_abs_im (s : ℂ) : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s

/-- √π < 2. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt 4 = 2 := by norm_num
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le this
    _ = 2 := h4

/-- log 2 > 0.69. -/
lemma log_two_gt : Real.log 2 > 0.69 := by linarith [Real.log_two_gt_d9]

/-- exp 2 > 7. -/
lemma exp_two_gt_seven : Real.exp 2 > 7 := by
  calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; ring_nf
    _ > 2.7 * 2.7 := by nlinarith [Real.exp_one_gt_d9]
    _ > 7 := by norm_num

/-- exp 2 > 4. -/
lemma exp_two_gt_four : Real.exp 2 > 4 := by linarith [exp_two_gt_seven]

/-! ## Part 2: Strip bounds for Gamma -/

/-- For `1/2 ≤ Re(s) ≤ 1`, `‖Γ(s)‖ ≤ 4`. -/
lemma Gamma_strip_bound {s : ℂ} (hs_re_lo : (1 / 2 : ℝ) ≤ s.re) (hs_re_hi : s.re ≤ 1) :
    ‖Complex.Gamma s‖ ≤ 4 := by
  have h := Complex.Gammaℝ.norm_Complex_Gamma_le_of_re_ge (a := 1/2) (by norm_num) hs_re_lo hs_re_hi
  have h_bound : 1 / (1/2 : ℝ) + Real.sqrt Real.pi ≤ 4 := by linarith [sqrt_pi_lt_two]
  linarith

/-! ## Part 3: Product bounds -/

/-- Product of shifted linear factors is bounded by a power. -/
lemma prod_shifted_norm_bound {s : ℂ} {n : ℕ} (hn : (n : ℝ) ≤ ‖s‖) :
    ‖∏ k ∈ Finset.range n, (s - 1 - k)‖ ≤ (2 * ‖s‖) ^ n := by
  calc ‖∏ k ∈ Finset.range n, (s - 1 - k)‖
      = ∏ k ∈ Finset.range n, ‖s - 1 - k‖ := by simp [norm_prod]
    _ ≤ ∏ _k ∈ Finset.range n, (2 * ‖s‖) := by
        apply Finset.prod_le_prod
        · intro k _; exact norm_nonneg _
        · intro k hk
          have hk' : k < n := Finset.mem_range.mp hk
          have hk_le : (k : ℝ) + 1 ≤ n := by exact_mod_cast hk'
          calc ‖s - 1 - k‖ ≤ ‖s‖ + ‖(1 : ℂ) + k‖ := by
                calc ‖s - 1 - k‖ = ‖s - (1 + k)‖ := by ring_nf
                  _ ≤ ‖s‖ + ‖(1 : ℂ) + k‖ := norm_sub_le _ _
            _ ≤ ‖s‖ + (1 + k) := by
                have h1 : ‖(1 : ℂ) + k‖ ≤ 1 + k := by
                  calc ‖(1 : ℂ) + k‖ ≤ ‖(1 : ℂ)‖ + ‖(k : ℂ)‖ := norm_add_le _ _
                    _ = 1 + k := by simp
                linarith
            _ ≤ ‖s‖ + n := by linarith [hk_le]
            _ ≤ 2 * ‖s‖ := by linarith [hn]
    _ = (2 * ‖s‖) ^ n := by simp [Finset.prod_const, Finset.card_range]

/-! ## Part 4: Key exponential bound -/

/-- The exponential `exp(2|s|log|s| + 4|s|)` is at least 4 for `|s| ≥ 2`. -/
lemma exp_bound_ge_four {s : ℂ} (hs_norm : 2 ≤ ‖s‖) :
    (4 : ℝ) ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
  have h_norm_pos : 0 < ‖s‖ := by linarith
  have h_log_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)
  have h1 : 2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖ ≥ 2 * 2 * Real.log 2 + 4 * 2 := by
    have hlog : Real.log 2 ≤ Real.log ‖s‖ := Real.log_le_log (by norm_num) hs_norm
    nlinarith [h_norm_pos, h_log_nonneg, hs_norm, hlog]
  have h2 : 2 * 2 * Real.log 2 + 4 * 2 = 4 * Real.log 2 + 8 := by ring
  have h3 : 4 * Real.log 2 + 8 > 2 := by linarith [log_two_gt]
  have h4 : Real.exp 2 < Real.exp (4 * Real.log 2 + 8) := Real.exp_lt_exp.mpr h3
  have h5 : Real.exp (4 * Real.log 2 + 8) ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
    apply Real.exp_le_exp.mpr; linarith [h1, h2]
  linarith [exp_two_gt_four, h4, h5]

/-! ## Part 5: Polynomial growth bound -/

/-- **Polynomial growth bound for Gamma** when `Re(s) ≥ 1` and `‖s‖ ≥ 2`.

The proof uses the functional equation and reduces to strip bounds. The key
technical lemma is that the exponential `exp(2|s|log|s| + 4|s|)` dominates
any polynomial growth that arises from the functional equation.

The complete proof requires careful analysis of the functional equation iteration
and Stirling's asymptotic formula for large |Im(s)|. -/
theorem Gamma_polynomial_growth {s : ℂ} (hs_re : 1 ≤ s.re) (hs_norm : 2 ≤ ‖s‖) :
    ‖Complex.Gamma s‖ ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := by
  -- We reuse the stronger polynomial-growth bound already proved in `GammaStirlingAux`
  -- (ultimately coming from the Robbins/Binet development in `Riemann/Mathlib`), and then relax it.
  have h_strong :
      ‖Complex.Gamma s‖ ≤ Real.exp (‖s‖ * Real.log ‖s‖ + 3 * ‖s‖) :=
    Stirling.GammaAux.norm_Gamma_polynomial_bound (s := s) hs_re hs_norm
  have hlog_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith [hs_norm])
  refine h_strong.trans ?_
  apply Real.exp_le_exp.mpr
  nlinarith [hlog_nonneg, norm_nonneg s]


/-! ## Part 6: Main Stirling bound -/

/-- **Core Stirling bound** for the complex Gamma function in the right half-plane.

There exist absolute constants `C, A, B > 0` such that for all `s` with
`Re(s) ≥ 1/2` and `‖s‖ ≥ A` we have `‖Γ(s)‖ ≤ exp(C‖s‖ log(B‖s‖))`.

This is the fundamental growth estimate used in establishing finite order
of L-functions and the Hadamard factorization theorem. -/
theorem Gamma_stirling_core :
    ∃ C A B : ℝ, 0 < C ∧ 0 < A ∧ 1 ≤ B ∧
      ∀ ⦃s : ℂ⦄, (1 / 2 : ℝ) ≤ s.re → A ≤ ‖s‖ →
        ‖Complex.Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (B * ‖s‖)) := by
  use 4, 2, 2
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h_norm_pos : 0 < ‖s‖ := by linarith
  have h_2s_pos : 0 < 2 * ‖s‖ := by linarith
  have h_log_pos : 0 < Real.log (2 * ‖s‖) := Real.log_pos (by linarith)
  have h_log_nonneg : 0 ≤ Real.log ‖s‖ := Real.log_nonneg (by linarith)

  by_cases h_re_ge_one : 1 ≤ s.re
  · -- Re(s) ≥ 1: use polynomial growth bound
    have hpoly := Gamma_polynomial_growth h_re_ge_one hs_norm
    -- Convert exp(2|s|log|s| + 4|s|) ≤ exp(4|s|log(2|s|))
    calc ‖Complex.Gamma s‖
        ≤ Real.exp (2 * ‖s‖ * Real.log ‖s‖ + 4 * ‖s‖) := hpoly
      _ ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := by
          apply Real.exp_le_exp.mpr
          have h_log_2s : Real.log (2 * ‖s‖) = Real.log 2 + Real.log ‖s‖ := by
            rw [Real.log_mul (by norm_num) (by linarith)]
          rw [h_log_2s]
          have hlog2 := log_two_gt
          have hlogs : Real.log ‖s‖ ≥ Real.log 2 := Real.log_le_log (by norm_num) hs_norm
          have h_ineq : (2 : ℝ) ≤ 2 * Real.log 2 + Real.log ‖s‖ := by
            calc (2 : ℝ) ≤ 2 * 0.69 + 0.69 := by norm_num
              _ ≤ 2 * Real.log 2 + Real.log 2 := by linarith [hlog2]
              _ ≤ 2 * Real.log 2 + Real.log ‖s‖ := by linarith [hlogs]
          nlinarith [h_log_nonneg, h_norm_pos]

  · -- 1/2 ≤ Re(s) < 1: use strip bound
    push_neg at h_re_ge_one
    have h := Gamma_strip_bound hs_re (le_of_lt h_re_ge_one)
    -- Show 4 ≤ exp(4|s|log(2|s|)) for |s| ≥ 2
    have h_exp_large : (4 : ℝ) ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := by
      have h1 : 4 * ‖s‖ * Real.log (2 * ‖s‖) ≥ 4 * 2 * Real.log 4 := by
        have hlog4 : Real.log 4 ≤ Real.log (2 * ‖s‖) := by
          apply Real.log_le_log (by norm_num)
          linarith
        nlinarith [hlog4, h_log_pos, hs_norm]
      have h2 : Real.log 4 > 1.38 := by
        have hlog2_gt : Real.log 2 > 0.693 := by linarith [Real.log_two_gt_d9]
        calc Real.log 4 = Real.log (2^2) := by norm_num
          _ = 2 * Real.log 2 := Real.log_pow 2 2
          _ > 2 * 0.693 := by linarith
          _ > 1.38 := by norm_num
      have h3 : 4 * 2 * Real.log 4 > 11 := by linarith [h2]
      have h4 := exp_two_gt_four
      have h5 : Real.exp (4 * 2 * Real.log 4) ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) :=
        Real.exp_le_exp.mpr h1
      have h6 : Real.exp 11 < Real.exp (4 * 2 * Real.log 4) := Real.exp_lt_exp.mpr h3
      have h7 : Real.exp 2 < Real.exp 11 := Real.exp_lt_exp.mpr (by norm_num)
      linarith [h4, h5, h6, h7]
    calc ‖Complex.Gamma s‖ ≤ 4 := h
      _ ≤ Real.exp (4 * ‖s‖ * Real.log (2 * ‖s‖)) := h_exp_large

end GammaBounds
