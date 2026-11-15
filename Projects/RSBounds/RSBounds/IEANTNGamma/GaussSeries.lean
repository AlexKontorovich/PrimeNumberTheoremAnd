/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.PSeries

/-!
# Stage 2a: the Gauss series converges

`ψ(s) = -γ + ∑ₖ (1/(k+1) - 1/(k+s))`. This file does the convergence and nothing else: the
summand is

  `1/(k+1) - 1/(k+s) = (s-1) / ((k+1)(k+s))`,

which is `O(1/k²)` once `k` is past `2‖s‖`, so the series converges absolutely.

Mathlib defines `Complex.digamma` and lists this representation as a `TODO` in the same file; the
series here is the left-hand side of that missing theorem, defined so the rest of the solution can
talk about it before it has been identified with `ψ`.
-/

namespace GammaSolution

open Complex

/-- The summand of the Gauss series. -/
noncomputable def gaussTerm (s : ℂ) (k : ℕ) : ℂ := ((k : ℂ) + 1)⁻¹ - ((k : ℂ) + s)⁻¹

/-- The summand in the form that exhibits its size: `(s-1)/((k+1)(k+s))`. -/
theorem gaussTerm_eq {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (k : ℕ) :
    gaussTerm s k = (s - 1) / (((k : ℂ) + 1) * ((k : ℂ) + s)) := by
  have h1 : ((k : ℂ) + 1) ≠ 0 := by
    intro h
    have : ((k : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re h
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have h2 : ((k : ℂ) + s) ≠ 0 := fun h ↦ hs k (by linear_combination h)
  simp only [gaussTerm]
  field_simp
  ring

/-- **The Gauss series converges absolutely.** -/
theorem summable_gaussTerm {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) : Summable (gaussTerm s) := by
  -- Compare with `2‖s-1‖ / k²` past `k ≥ 2‖s‖`.
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖s‖)
  have hcomp : Summable (fun k : ℕ ↦ 2 * ‖s - 1‖ / (k : ℝ) ^ 2) := by
    simpa [div_eq_mul_inv] using
      (Real.summable_one_div_nat_pow.mpr one_lt_two).mul_left (2 * ‖s - 1‖)
  refine Summable.of_norm_bounded_eventually_nat hcomp ?_
  filter_upwards [Filter.eventually_ge_atTop (max N 1)] with k hk
  have hkN : (N : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans (le_max_right N 1) hk
  have hks : 2 * ‖s‖ < (k : ℝ) := lt_of_lt_of_le hN hkN
  -- `‖k + s‖ ≥ k - ‖s‖ ≥ k/2`.
  have hlow : (k : ℝ) / 2 ≤ ‖(k : ℂ) + s‖ := by
    have h := norm_sub_norm_le ((k : ℂ)) (-s)
    simp only [norm_neg, sub_neg_eq_add] at h
    have hkabs : ‖((k : ℕ) : ℂ)‖ = (k : ℝ) := by
      simp
    rw [hkabs] at h
    linarith
  have hpos : (0 : ℝ) < (k : ℝ) := by linarith
  rw [gaussTerm_eq hs k, norm_div, norm_mul]
  have hk1n : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have hcast : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hk1n]
  have hs1 : (0 : ℝ) ≤ ‖s - 1‖ := norm_nonneg _
  have hnormpos : (0 : ℝ) < ‖(k : ℂ) + s‖ := by linarith
  have hden1 : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
    mul_pos (by linarith) hnormpos
  have hden2 : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ hden1 hden2]
  -- `2‖s-1‖ (k+1)‖k+s‖ ≥ 2‖s-1‖ (k+1)(k/2) = ‖s-1‖ (k+1) k ≥ ‖s-1‖ k²`.
  have hmul : ((k : ℝ) + 1) * ((k : ℝ) / 2) ≤ ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ :=
    mul_le_mul_of_nonneg_left hlow (by linarith)
  nlinarith [hmul, hs1, hk1, hpos]

end GammaSolution
