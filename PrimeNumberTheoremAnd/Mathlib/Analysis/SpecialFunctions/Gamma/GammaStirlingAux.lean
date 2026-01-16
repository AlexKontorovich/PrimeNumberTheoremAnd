import Mathlib.Tactic.NormNum.RealSqrt
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.StirlingRobbins
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.GaussianIntegral

/-!
# Auxiliary Stirling lemmas for Gamma bounds

This file provides technical lemmas connecting Mathlib's Stirling theory
to explicit bounds on the complex Gamma function.

## References

* NIST DLMF 5.11: Asymptotic Expansions for Γ(z)
* NIST DLMF 5.6.7: |Γ(x+iy)| ≤ Γ(x) for x ≥ 1/2
* Whittaker & Watson: A Course of Modern Analysis, Chapter 12
* The functional equation Γ(z+1) = z·Γ(z) (Mathlib: `Complex.Gamma_add_one`)

## Main results

* `Gamma_strip_bound`: For Re(s) ∈ [1/2, 1], |Γ(s)| ≤ 4
* `Gamma_bound_one_two`: For Re(s) ∈ [1, 2], |Γ(s)| ≤ 1 (from DLMF 5.6.7)
* `norm_Gamma_polynomial_bound`: For Re(s) ≥ 1, |s| ≥ 2: |Γ(s)| ≤ exp(|s|log|s| + 3|s|)
-/

open Real Complex Set Filter Asymptotics
open scoped Topology BigOperators

namespace Stirling.GammaAux

/-! ## Section 1: Basic arithmetic lemmas -/

lemma sqrt_pi_lt_two : Real.sqrt Real.pi < 2 := by
  calc Real.sqrt Real.pi < Real.sqrt 4 := Real.sqrt_lt_sqrt Real.pi_pos.le Real.pi_lt_four
    _ = 2 := by norm_num

lemma four_lt_exp_three_mul {x : ℝ} (hx : 2 ≤ x) : (4 : ℝ) < Real.exp (3 * x) := by
  have h_exp6 : Real.exp 6 > 4 := by
    have := Real.add_one_lt_exp (by norm_num : (6:ℝ) ≠ 0)
    linarith
  calc (4 : ℝ) < Real.exp 6 := h_exp6
    _ ≤ Real.exp (3 * x) := Real.exp_le_exp.mpr (by linarith)

lemma pow_le_exp_mul_log {x : ℝ} {m : ℕ} (hx : 1 ≤ x) (hm : (m : ℝ) ≤ x) :
    x ^ m ≤ Real.exp (x * Real.log x) := by
  have hx_pos : 0 < x := by linarith
  rw [mul_comm, ← Real.rpow_def_of_pos hx_pos, ← Real.rpow_natCast x m]
  exact Real.rpow_le_rpow_of_exponent_le hx hm

lemma re_le_norm {s : ℂ} (hs : 0 ≤ s.re) : s.re ≤ ‖s‖ := by
  have := Complex.abs_re_le_norm s
  rwa [abs_of_nonneg hs] at this

/-! ## Section 2: Key geometric lemma -/

/-- For s : ℂ and real a with 0 < a < Re(s), we have |s - a| ≤ |s|.

Proof: |s - a|² = (Re(s) - a)² + Im(s)² ≤ Re(s)² + Im(s)² = |s|²
since 0 < Re(s) - a < Re(s) implies (Re(s) - a)² ≤ Re(s)². -/
lemma norm_sub_real_le {s : ℂ} {a : ℝ} (ha_pos : 0 < a) (ha_lt : a < s.re) : ‖s - a‖ ≤ ‖s‖ := by
  -- Key insight: 0 < Re(s) - a < Re(s), so (Re(s) - a)² < Re(s)²
  -- Thus |s - a|² = (Re(s) - a)² + Im(s)² < Re(s)² + Im(s)² = |s|²
  have h_sq : (s.re - a) ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h1 : Complex.normSq (s - a) ≤ Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
               Complex.sub_im, Complex.ofReal_im, sub_zero]
    linarith [sq_nonneg s.im]
  calc ‖s - a‖ = Real.sqrt (Complex.normSq (s - a)) := rfl
    _ ≤ Real.sqrt (Complex.normSq s) := Real.sqrt_le_sqrt h1
    _ = ‖s‖ := rfl

/-- For s : ℂ and k : ℕ with k + 1 < Re(s), we have |s - 1 - k| ≤ |s|. -/
lemma norm_shift_le {s : ℂ} {k : ℕ} (hk : (k : ℝ) + 1 < s.re) : ‖s - 1 - k‖ ≤ ‖s‖ := by
  -- Direct proof: |s - 1 - k|² ≤ |s|² using normSq
  have ha_pos : (0 : ℝ) < 1 + k := by linarith
  have ha_lt : (1 : ℝ) + k < s.re := by linarith
  have h_sq : (s.re - (1 + k)) ^ 2 ≤ s.re ^ 2 := by nlinarith
  have h1 : Complex.normSq (s - 1 - k) ≤ Complex.normSq s := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.natCast_re,
               Complex.sub_im, Complex.one_im, Complex.natCast_im, sub_zero]
    linarith [sq_nonneg s.im]
  calc ‖s - 1 - k‖ = Real.sqrt (Complex.normSq (s - 1 - k)) := rfl
    _ ≤ Real.sqrt (Complex.normSq s) := Real.sqrt_le_sqrt h1
    _ = ‖s‖ := rfl

/-- Product bound: |∏_{k < m} (s-1-k)| ≤ |s|^m -/
lemma prod_norm_le_pow {s : ℂ} {m : ℕ} (h : ∀ k < m, (k : ℝ) + 1 < s.re) :
    ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ ≤ ‖s‖ ^ m := by
  calc ‖∏ k ∈ Finset.range m, (s - 1 - k)‖
      = ∏ k ∈ Finset.range m, ‖s - 1 - k‖ := norm_prod _ _
    _ ≤ ∏ _k ∈ Finset.range m, ‖s‖ := by
        apply Finset.prod_le_prod (fun k _ => norm_nonneg _)
        intro k hk; exact norm_shift_le (h k (Finset.mem_range.mp hk))
    _ = ‖s‖ ^ m := by rw [Finset.prod_const, Finset.card_range]

/-! ## Section 3: Stirling's approximation for factorial -/

/-- Stirling's approximation (Robbins upper bound): n! ≤ √(2πn) (n/e)^n e^{1/(12n)}

Reference: Robbins, H. "A Remark on Stirling's Formula."
The American Mathematical Monthly 62.1 (1955): 26-29.

Note: Mathlib's `Stirling.le_factorial_stirling` provides only the LOWER bound:
  √(2πn)(n/e)^n ≤ n!
The upper bound requires the Robbins error analysis which is not yet in Mathlib. -/
lemma factorial_asymptotic (n : ℕ) (hn : 0 < n) :
    (n.factorial : ℝ) ≤ Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n *
      Real.exp (1 / (12 * n)) := by
  -- This is Robbins' sharp upper bound, proved in `Riemann/Mathlib`.
  simpa using Stirling.factorial_upper_robbins n hn

/-! ## Section 4: Strip bounds for Gamma -/

lemma Gamma_strip_bound_general {s : ℂ} {a : ℝ} (ha : 0 < a) (hs_lo : a ≤ s.re) (hs_hi : s.re ≤ 1) :
    ‖Complex.Gamma s‖ ≤ 1 / a + Real.sqrt Real.pi :=
  Complex.Gammaℝ.norm_Complex_Gamma_le_of_re_ge ha hs_lo hs_hi

lemma Gamma_strip_bound {s : ℂ} (hs_lo : (1/2 : ℝ) ≤ s.re) (hs_hi : s.re ≤ 1) :
    ‖Complex.Gamma s‖ ≤ 4 := by
  have h := Gamma_strip_bound_general (by norm_num : (0:ℝ) < 1/2) hs_lo hs_hi
  calc ‖Complex.Gamma s‖ ≤ 1 / (1/2 : ℝ) + Real.sqrt Real.pi := h
    _ = 2 + Real.sqrt Real.pi := by norm_num
    _ ≤ 4 := by linarith [sqrt_pi_lt_two]

/-- DLMF 5.6.7: For Re(z) ∈ [1, 2], |Γ(z)| ≤ Γ(Re(z)) ≤ 1.

The proof requires two facts:
1. |Γ(x+iy)| ≤ Γ(x) for x ≥ 1/2 (DLMF 5.6.7)
2. Γ(x) ≤ 1 for x ∈ [1, 2] since Γ(1) = Γ(2) = 1 and Γ achieves its minimum ≈ 0.886 at x ≈ 1.46

Neither fact is currently in Mathlib. -/
lemma Gamma_bound_one_two {s : ℂ} (hs_lo : 1 ≤ s.re) (hs_hi : s.re ≤ 2) :
    ‖Complex.Gamma s‖ ≤ 1 := by
  -- This is available in `Riemann/Mathlib` as `Binet.norm_Gamma_le_one`.
  exact Binet.norm_Gamma_le_one hs_lo hs_hi

/-! ## Section 4: Iterated functional equation -/

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
    calc Complex.Gamma s
        = Complex.Gamma (s - m) * ∏ k ∈ Finset.range m, (s - 1 - k) := ih h_prev
      _ = (s - m - 1) * Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k) := by rw [h_func]
      _ = Complex.Gamma (s - m - 1) * ((s - m - 1) * ∏ k ∈ Finset.range m, (s - 1 - k)) := by ring
      _ = Complex.Gamma (s - m - 1) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by rw [h_prod_eq]
      _ = Complex.Gamma (s - ↑(m + 1)) * ∏ k ∈ Finset.range (m + 1), (s - 1 - k) := by rw [← h_cast]

/-! ## Section 5: Main polynomial growth theorem -/

/-- Main theorem: For Re(s) ≥ 1 and |s| ≥ 2, |Γ(s)| ≤ exp(|s| log|s| + 3|s|) -/
theorem norm_Gamma_polynomial_bound {s : ℂ} (hs_re : 1 ≤ s.re) (hs_norm : 2 ≤ ‖s‖) :
    ‖Complex.Gamma s‖ ≤ Real.exp (‖s‖ * Real.log ‖s‖ + 3 * ‖s‖) := by
  have h_norm_pos : 0 < ‖s‖ := by linarith

  -- Case 1: Re(s) < 2
  by_cases h_base : s.re < 2
  · have h_gamma := Gamma_bound_one_two hs_re (le_of_lt h_base)
    have h_nonneg : 0 ≤ ‖s‖ * Real.log ‖s‖ := mul_nonneg (by linarith) (Real.log_nonneg (by linarith))
    calc ‖Complex.Gamma s‖ ≤ 1 := h_gamma
      _ ≤ Real.exp 0 := by simp
      _ ≤ Real.exp (‖s‖ * Real.log ‖s‖ + 3 * ‖s‖) := by
          apply Real.exp_le_exp.mpr; linarith [mul_pos (by linarith : (0:ℝ) < 3) h_norm_pos]

  -- Case 2: Re(s) ≥ 2
  push_neg at h_base
  let m := ⌊s.re⌋₊ - 1

  have h_floor_ge2 : 2 ≤ ⌊s.re⌋₊ := Nat.le_floor h_base
  have hm_pos : 0 < m := by simp only [m]; omega
  have h_floor_le : (⌊s.re⌋₊ : ℝ) ≤ s.re := Nat.floor_le (by linarith : 0 ≤ s.re)
  have h_floor_gt : s.re < ⌊s.re⌋₊ + 1 := Nat.lt_floor_add_one s.re
  have hm_eq : (m : ℝ) = ⌊s.re⌋₊ - 1 := by
    simp only [m, Nat.cast_sub (by omega : 1 ≤ ⌊s.re⌋₊), Nat.cast_one]

  have h_re_lo : 1 ≤ (s - m).re := by simp only [sub_re, natCast_re]; linarith [hm_eq, h_floor_le]
  have h_re_hi : (s - m).re < 2 := by simp only [sub_re, natCast_re]; linarith [hm_eq, h_floor_gt]
  have hm_le : (m : ℝ) ≤ ‖s‖ := by
    have h1 : (m : ℝ) ≤ s.re - 1 := by rw [hm_eq]; linarith
    have h2 : s.re ≤ ‖s‖ := re_le_norm (by linarith)
    linarith

  have h_k_bound : ∀ k < m, (k : ℝ) + 1 < s.re := by
    intro k hk
    have h1 : (1 : ℝ) ≤ ⌊s.re⌋₊ := by exact_mod_cast (by omega : 1 ≤ ⌊s.re⌋₊)
    calc (k : ℝ) + 1 ≤ m := by exact_mod_cast Nat.lt_iff_add_one_le.mp hk
      _ = ⌊s.re⌋₊ - 1 := hm_eq
      _ < ⌊s.re⌋₊ := by linarith
      _ ≤ s.re := h_floor_le

  have h_nonzero : ∀ k < m, s - 1 - k ≠ 0 := by
    intro k hk heq
    have : (s - 1 - k).re = 0 := by rw [heq]; simp
    simp at this; linarith [h_k_bound k hk]

  have h_iter := Gamma_iterate h_nonzero
  rw [h_iter]

  have h_prod : ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ ≤ ‖s‖ ^ m := prod_norm_le_pow h_k_bound
  have h_gamma_base : ‖Complex.Gamma (s - m)‖ ≤ 1 := Gamma_bound_one_two h_re_lo (le_of_lt h_re_hi)

  calc ‖Complex.Gamma (s - m) * ∏ k ∈ Finset.range m, (s - 1 - k)‖
      = ‖Complex.Gamma (s - m)‖ * ‖∏ k ∈ Finset.range m, (s - 1 - k)‖ := norm_mul _ _
    _ ≤ 1 * ‖s‖ ^ m := mul_le_mul h_gamma_base h_prod (norm_nonneg _) (by norm_num)
    _ = ‖s‖ ^ m := one_mul _
    _ ≤ Real.exp (‖s‖ * Real.log ‖s‖) := pow_le_exp_mul_log (by linarith) hm_le
    _ ≤ Real.exp (‖s‖ * Real.log ‖s‖ + 3 * ‖s‖) := by
        apply Real.exp_le_exp.mpr; linarith [mul_pos (by linarith : (0:ℝ) < 3) h_norm_pos]

end Stirling.GammaAux
