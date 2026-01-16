import Mathlib.Tactic.NormNum.RealSqrt
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StripBounds

/-!
# Stirling-type bounds for the complex Gamma function

This file provides bounds on `Complex.Gamma` (and the archimedean factor `Gammaℝ`)
in regions of the complex plane that arise naturally in the analytic theory of
the completed zeta function, Hadamard factorization, and the Selberg class.

## Main results

* `Complex.Gamma_norm_le_strip` :
  In the strip `0 < a ≤ re s ≤ 1`, `‖Γ(s)‖ ≤ 1/a + √π`.

* `Complex.Gamma_stirling_bound_re_ge_one` :
  Stirling-type polynomial bound for `Γ(s)` when `re s ≥ 1`.

* `Complex.Gamma_stirling_bound_re_ge_zero` :
  Stirling-type exponential bound for `Γ(s)` when `re s ≥ 0`.

* `Riemann.Gammaℝ_stirling_bound_re_ge_zero` :
  Stirling bound for the archimedean factor `Γ_ℝ(s) = π^{-s/2} Γ(s/2)`.

These bounds are essential for establishing finite order of L-functions in the
Selberg class and for the Hadamard factorization theorem.
-/

noncomputable section

open Complex Real Set Filter Topology Metric MeasureTheory
open scoped Real Topology BigOperators

/-! ## Part 1: Basic real lemmas -/

namespace Real

/-- For `x ≥ 1`, `log (1 + x) ≥ log 2`. -/
lemma log_one_add_ge_log_two {x : ℝ} (hx : 1 ≤ x) :
    Real.log 2 ≤ Real.log (1 + x) := by
  have h₂ : (0 : ℝ) < 2 := by norm_num
  have hle : (2 : ℝ) ≤ 1 + x := by linarith
  exact Real.log_le_log h₂ hle

/-- For `x ≥ 1`, `log (1 + x) > 0`. -/
lemma log_one_add_pos {x : ℝ} (hx : 1 ≤ x) :
    0 < Real.log (1 + x) := Real.log_pos (by linarith)

/-- The simple inequality `x ≤ exp x` for all real `x`. -/
lemma le_exp_self' (x : ℝ) : x ≤ Real.exp x :=
  le_trans (by linarith : x ≤ x + 1) (Real.add_one_le_exp x)

/-- A convenient bound `1 ≤ π`. -/
lemma one_le_pi : (1 : ℝ) ≤ Real.pi := le_trans (by norm_num : (1:ℝ) ≤ 2) Real.two_le_pi

/-- `√π < 2`. -/
lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  have hπ4 : Real.pi < 4 := Real.pi_lt_four
  have h4 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by norm_num
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le hπ4
    _ = 2 := h4

end Real

/-! ## Part 2: Boundedness of `Γ` on compact sets -/

namespace Complex

/-- `Gamma` is bounded on any compact set that does not contain non-positive integers. -/
lemma Gamma_norm_bounded_on_compact_of_no_poles {K : Set ℂ}
    (hK : IsCompact K)
    (h_poles : ∀ s ∈ K, ∀ n : ℕ, s ≠ -n) :
    ∃ M : ℝ, ∀ s ∈ K, ‖Gamma s‖ ≤ M := by
  have h_cont : ContinuousOn Gamma K := by
    refine continuousOn_of_forall_continuousAt ?_
    intro s hs
    exact (differentiableAt_Gamma s (h_poles s hs)).continuousAt
  rcases hK.exists_bound_of_continuousOn h_cont with ⟨M, hM⟩
  exact ⟨M, fun s hs => hM s hs⟩

/-! ## Part 3: Bounds in the strip `0 < re w ≤ 1` -/

/-- When `0 < a ≤ re w ≤ 1`, we have `‖Γ(w)‖ ≤ 1 / a + √π`. -/
theorem Gamma_norm_le_strip {w : ℂ} {a : ℝ}
    (ha : 0 < a) (hw_lo : a ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Gammaℝ.norm_Complex_Gamma_le_of_re_ge ha hw_lo hw_hi

/-- For `1/2 ≤ re w ≤ 1`, `‖Γ(w)‖ ≤ 4`. -/
lemma Gamma_norm_le_four_of_re_half_to_one {w : ℂ}
    (hw_lo : (1 / 2 : ℝ) ≤ w.re) (hw_hi : w.re ≤ 1) :
    ‖Gamma w‖ ≤ 4 := by
  have h := Gamma_norm_le_strip (w := w) (a := (1 / 2 : ℝ)) (by norm_num) hw_lo hw_hi
  calc ‖Gamma w‖ ≤ 1 / (1 / 2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 2 + 2 := by linarith [Real.sqrt_pi_lt_two]
    _ = 4 := by norm_num

/-! ## Part 4: Product of shifted linear factors -/

/-- For `s : ℂ` and `n : ℕ`, the product
`∏ k ∈ Finset.range n, (s - (k + 1))` has norm at most `(‖s‖ + n)^n`. -/
lemma prod_sub_norm_le {s : ℂ} {n : ℕ} :
    ‖∏ k ∈ Finset.range n, (s - (k + 1))‖ ≤ (‖s‖ + n) ^ n := by
  calc ‖∏ k ∈ Finset.range n, (s - (k + 1))‖
      = ∏ k ∈ Finset.range n, ‖s - (k + 1)‖ := by simp
    _ ≤ ∏ _k ∈ Finset.range n, (‖s‖ + n) := by
      refine Finset.prod_le_prod ?_ ?_
      · intro k _; exact norm_nonneg _
      · intro k hk
        have h1 : ‖s - (k + 1 : ℂ)‖ ≤ ‖s‖ + ‖(k + 1 : ℂ)‖ := norm_sub_le _ _
        have h2 : ‖(k + 1 : ℂ)‖ = (k + 1 : ℝ) := by norm_cast
        have h3 : (k + 1 : ℝ) ≤ n := by
          have := Finset.mem_range.mp hk
          exact_mod_cast Nat.succ_le_of_lt this
        calc ‖s - (k + 1 : ℂ)‖ ≤ ‖s‖ + ‖(k + 1 : ℂ)‖ := h1
          _ = ‖s‖ + (k + 1 : ℝ) := by simp [h2]
          _ ≤ ‖s‖ + n := by
            -- `add_le_add_left` with the left summand `‖s‖`
            simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left h3 ‖s‖)
    _ = (‖s‖ + n) ^ n := by simp [Finset.prod_const, Finset.card_range]

/-! ## Part 5: Floor-shift into the standard strip `[0,1)` -/

/-- For any `s : ℂ`, the real part of `s' := s - ⌊Re(s)⌋` lies in `[0, 1)`. -/
lemma floor_shift_re_in_strip {s : ℂ} :
    let s' := s - (⌊s.re⌋ : ℂ)
    0 ≤ s'.re ∧ s'.re < 1 := by
  intro s'
  have h₁ : 0 ≤ s.re - (⌊s.re⌋ : ℝ) := sub_nonneg.mpr (Int.floor_le _)
  have h₂ : s.re - (⌊s.re⌋ : ℝ) < 1 := by
    have h := Int.lt_floor_add_one (s.re)
    exact (sub_lt_iff_lt_add).mpr (by simp [add_comm])
  constructor
  · simp [s']
  · simpa [s'] using h₂

/-! ## Part 6: Polynomial bound for `re s ≥ 1` -/

/-- For `re s ≥ 1`, `‖Γ(s)‖` is bounded by a polynomial in `‖s‖`. -/
theorem Gamma_norm_bound_re_ge_one :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖Gamma s‖ ≤ C * (1 + ‖s‖) ^ (‖s‖ + 1) := by
  -- Use the already-established polynomial-growth bound in `Stirling.GammaAux`.
  -- (This is the main API we want downstream; this file is a high-level wrapper.)
  obtain ⟨C, hC_pos, hC⟩ := Complex.Gamma.norm_bound_re_ge_one
  refine ⟨C, hC_pos, ?_⟩
  intro s hs_re
  exact hC s hs_re

/-! ## Part 7: Main Stirling-type exponential bound for `re s ≥ 0` -/

/-- **Main Stirling bound** for `Re(s) ≥ 0`.

There exists a constant `C` such that for any `s` with `re s ≥ 0` and
`‖s‖ ≥ 1` we have `‖Γ(s)‖ ≤ exp (C · ‖s‖ · log (1 + ‖s‖))`. -/
theorem Gamma_stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  -- This file is a high-level wrapper; the actual proof lives in the centralized
  -- `Riemann/Mathlib/.../Gamma/StripBounds.lean`.
  simpa using Complex.Gamma.stirling_bound_re_ge_zero

/-! ## Part 8: Stirling bound for `Γ(s/2)` -/

/-- Stirling bound specialized to `Γ(s/2)` for `re s ≥ 0`. -/
theorem Gamma_half_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Gamma (s / 2)‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  -- This file is a high-level wrapper; the actual proof lives in the centralized
  -- `Riemann/Mathlib/.../Gamma/StripBounds.lean`.
  simpa using Complex.Gamma.half_bound_re_ge_zero

end Complex

/-! ## Part 9: Stirling bound for the archimedean factor `Γ_ℝ` -/

namespace Riemann

open Complex Real

/-- The norm of `π^{-s/2}` is at most `1` when `Re(s) ≥ 0`. -/
lemma norm_cpow_pi_neg_half_le_one {s : ℂ} (hs : 0 ≤ s.re) :
    ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [norm_cpow_eq_rpow_re_of_pos hpi_pos]
  simp only [neg_div, neg_re, div_ofNat_re]
  have h_exp : -(s.re / 2 : ℝ) ≤ 0 := by linarith
  have hpi_gt_1 : (1 : ℝ) < Real.pi := by
    calc (1 : ℝ) < 3 := by norm_num
      _ < Real.pi := Real.pi_gt_three
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_gt_1) h_exp

/-- **Stirling bound for the archimedean factor** `Γ_ℝ = π^{-s/2} · Γ(s/2)`. -/
theorem Gammaℝ_stirling_bound_re_ge_zero :
    ∃ C : ℝ, 0 < C ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (C * ‖s‖ * Real.log (1 + ‖s‖)) := by
  obtain ⟨C₁, hC₁_pos, hC₁⟩ := Complex.Gamma_half_bound_re_ge_zero
  refine ⟨C₁ + 2, by linarith, ?_⟩
  intro s hs_re hs_norm
  have hdef : Complex.Gammaℝ s = (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    simp [Complex.Gammaℝ_def]
  have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) :=
    hC₁ s hs_re hs_norm
  have hpi : ‖(Real.pi : ℂ) ^ (-s / 2)‖ ≤ 1 := norm_cpow_pi_neg_half_le_one hs_re
  have h1 : ‖Complex.Gammaℝ s‖ ≤ ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖ := by
    rw [hdef]; exact norm_mul_le _ _
  have h2 : ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := by
    calc ‖(Real.pi : ℂ) ^ (-s / 2)‖ * ‖Complex.Gamma (s / 2)‖
        ≤ 1 * ‖Complex.Gamma (s / 2)‖ := mul_le_mul_of_nonneg_right hpi (norm_nonneg _)
      _ = ‖Complex.Gamma (s / 2)‖ := by ring
      _ ≤ Real.exp (C₁ * ‖s‖ * Real.log (1 + ‖s‖)) := hΓ
  have hlog_nonneg : 0 ≤ Real.log (1 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hnorm_nonneg : 0 ≤ ‖s‖ := norm_nonneg _
  have hC_le : C₁ * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C₁ + 2) * ‖s‖ * Real.log (1 + ‖s‖) := by
    apply mul_le_mul_of_nonneg_right _ hlog_nonneg
    apply mul_le_mul_of_nonneg_right _ hnorm_nonneg
    linarith
  exact le_trans (le_trans h1 h2) (Real.exp_le_exp.mpr hC_le)

/-- Finite order bound for Γ_ℝ. -/
theorem Gammaℝ_finite_order :
    ∃ (A B : ℝ), 0 < A ∧ 0 < B ∧
      ∀ s : ℂ, 0 ≤ s.re → 1 ≤ ‖s‖ →
        ‖Complex.Gammaℝ s‖ ≤ Real.exp (A * ‖s‖ ^ B) := by
  obtain ⟨C, hC_pos, hC⟩ := Gammaℝ_stirling_bound_re_ge_zero
  use C + 1, (2 : ℝ)
  refine ⟨by linarith, by norm_num, ?_⟩
  intro s hs_re hs_norm
  have h := hC s hs_re hs_norm
  -- Show log(1 + |s|) ≤ |s| for |s| ≥ 1
  have h_log : Real.log (1 + ‖s‖) ≤ ‖s‖ := by
    have h1 : 0 < 1 + ‖s‖ := by linarith [norm_nonneg s]
    have h2 : 1 + ‖s‖ ≤ Real.exp ‖s‖ := by
      have := Real.add_one_le_exp ‖s‖
      linarith
    calc Real.log (1 + ‖s‖)
        ≤ Real.log (Real.exp ‖s‖) := Real.log_le_log h1 h2
      _ = ‖s‖ := Real.log_exp ‖s‖
  have step1 : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ C * ‖s‖ * ‖s‖ := by
    apply mul_le_mul_of_nonneg_left h_log
    apply mul_nonneg (by linarith) (norm_nonneg s)
  have step2 : C * ‖s‖ * ‖s‖ = C * ‖s‖ ^ (2 : ℕ) := by
    simp [pow_two, mul_left_comm, mul_comm]
  have step3 : C * ‖s‖ ^ (2 : ℕ) ≤ (C + 1) * ‖s‖ ^ (2 : ℕ) := by
    apply mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h_final' : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ (2 : ℕ) := by
    linarith [step1, step3]
  have h_final : C * ‖s‖ * Real.log (1 + ‖s‖) ≤ (C + 1) * ‖s‖ ^ (2 : ℝ) := by
    simpa [Real.rpow_natCast] using h_final'
  exact h.trans (Real.exp_le_exp.mpr h_final)

end Riemann
