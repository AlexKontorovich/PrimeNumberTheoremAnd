/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Auxiliary lemmas for Gamma strip bounds

This file contains the shared algebraic and geometric lemmas used to shift `Γ(s)` into a
vertical strip by the functional equation.

## References

* [DLMF], §5.11 for Stirling expansions around the Gamma function
* [whittakerWatson1927], Chapter XII for the classical Gamma-function background
* The functional equation Γ(z+1) = z·Γ(z) (Mathlib: `Complex.Gamma_add_one`)

## Main results

* `norm_sub_real_le`: subtracting a positive real smaller than `re s` does not increase `‖s‖`
* `prod_norm_le_pow`: the shifted Gamma product has norm at most `‖s‖ ^ m`
* `Gamma_iterate`: the iterated Gamma functional equation
-/

@[expose] public section

open Complex
open scoped Topology BigOperators

namespace Stirling.GammaAux

/-! ## Geometry of the shifted product -/

/-- If `0 < a < re s`, then subtracting `a` from `s` does not increase the norm. -/
lemma norm_sub_real_le {s : ℂ} {a : ℝ} (ha_pos : 0 < a) (ha_lt : a < s.re) : ‖s - a‖ ≤ ‖s‖ := by
  have h_sq : (s.re - a) ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h1 : Complex.normSq (s - a) ≤ Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
               Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith [sq_nonneg s.im]
  calc
    ‖s - a‖ = Real.sqrt (Complex.normSq (s - a)) := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    _ ≤ Real.sqrt (Complex.normSq s) := Real.sqrt_le_sqrt h1
    _ = ‖s‖ := by
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- For s : ℂ and k : ℕ with k + 1 < Re(s), we have |s - 1 - k| ≤ |s|. -/
lemma norm_shift_le {s : ℂ} {k : ℕ} (hk : (k : ℝ) + 1 < s.re) : ‖s - 1 - k‖ ≤ ‖s‖ := by
  have ha_pos : (0 : ℝ) < 1 + k := by linarith
  have ha_lt : (1 : ℝ) + k < s.re := by linarith
  simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
    norm_sub_real_le (s := s) (a := (1 + k : ℝ)) ha_pos ha_lt

/-- Product bound: |∏_{k < m} (s-1-k)| ≤ |s|^m -/
lemma prod_norm_le_pow {s : ℂ} {m : ℕ} (h : ∀ k < m, (k : ℝ) + 1 < s.re) :
    ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ ≤ ‖s‖ ^ m := by
  calc ‖∏ k ∈ Finset.range m, (s - 1 - k)‖
      = ∏ k ∈ Finset.range m, ‖s - 1 - k‖ := norm_prod _ _
    _ ≤ ∏ _k ∈ Finset.range m, ‖s‖ := by
        apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
        intro k hk; exact norm_shift_le (h k (Finset.mem_range.mp hk))
    _ = ‖s‖ ^ m := by rw [Finset.prod_const, Finset.card_range]

/-! ## Iterated functional equation -/

lemma Gamma_iterate {s : ℂ} {n : ℕ} (hs : ∀ k < n, s - 1 - k ≠ 0) :
    Complex.Gamma s = Complex.Gamma (s - n) * ∏ k ∈ Finset.range n, (s - 1 - k) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have h_prev : ∀ k < m, s - 1 - k ≠ 0 := fun k hk => hs k (Nat.lt_succ_of_lt hk)
    have h_curr : s - 1 - m ≠ 0 := hs m (Nat.lt_succ_self m)
    have h_func : Complex.Gamma (s - m) = (s - m - 1) * Complex.Gamma (s - m - 1) := by
      have h_ne : s - ↑m - 1 ≠ 0 := by convert h_curr using 1; ring
      have := Complex.Gamma_add_one (s - m - 1) h_ne
      simp only [sub_add_cancel] at this
      exact this
    have h_cast : s - ↑(m + 1) = s - m - 1 := by simp only [Nat.cast_add, Nat.cast_one]; ring
    have h_prod_eq : (s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k) =
        ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
      rw [Finset.prod_range_succ]; ring
    calc
      Complex.Gamma s
          = Complex.Gamma (s - m) * ∏ k ∈ Finset.range m, (s - 1 - k) := ih h_prev
      _ = (s - m - 1) * Complex.Gamma (s - m - 1)
            * ∏ k ∈ Finset.range m, (s - 1 - k) := by
          rw [h_func]
      _ = Complex.Gamma (s - m - 1) *
            ((s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k)) := by
          ring
      _ = Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [h_prod_eq]
      _ = Complex.Gamma (s - ↑(m + 1)) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by
          rw [← h_cast]

end Stirling.GammaAux
