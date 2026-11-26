/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import RSBounds.PolynomialSmoothing
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

/-!
# Quartic smoothing of the Chebyshev function

This file supplies the finite arithmetic part of polynomial smoothing: an
upper/lower sandwich for psi and the exact fourth-difference identity for its
truncated-power primitive. It contains no zeta explicit formula, zero-count
estimate, or RH hypothesis.

One common finite range `0 <= n <= N` is used throughout. The hypothesis
`x + 4*h <= N` makes it adequate for all five arguments in the forward
difference; terms beyond that range have zero weight.
-/

open Finset
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.PolynomialPsi

open PolynomialSmoothing

/-- The fourth truncated-power primitive of a point mass. -/
noncomputable def quarticPrimitive (t : ℝ) : ℝ := (max t 0) ^ 4 / 24

/-- A common finite truncation of the fourth primitive of psi. -/
noncomputable def psi4Trunc (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * quarticPrimitive (t - n)

/-- The canonical finite truncated-power primitive. -/
noncomputable def Psi4 (t : ℝ) : ℝ := psi4Trunc ⌊t⌋₊ t

/-- Forward fourth difference, before normalization by the step size. -/
def fourthDifference (f : ℝ → ℝ) (x h : ℝ) : ℝ :=
  f (x + 4 * h) - 4 * f (x + 3 * h) + 6 * f (x + 2 * h) -
    4 * f (x + h) + f x

/-- Polynomial upper smoothing of psi. -/
noncomputable def psiUpper (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x + 4 * h - n) / h)

/-- Polynomial lower smoothing of psi. -/
noncomputable def psiLower (N : ℕ) (x h : ℝ) : ℝ :=
  ∑ n ∈ Icc 0 N, (Λ n : ℝ) * W ((x - n) / h)

/-- Psi represented on any sufficiently large common finite range. -/
theorem psi_eq_indicator_sum {x : ℝ} (hx : 0 ≤ x) {N : ℕ} (hN : x ≤ N) :
    Chebyshev.psi x =
      ∑ n ∈ Icc 0 N, if (n : ℝ) ≤ x then (Λ n : ℝ) else 0 := by
  have hfloor : ⌊x⌋₊ ≤ N := by
    exact_mod_cast (Nat.floor_le hx).trans hN
  have hs : (Icc 0 N).filter (fun n : ℕ => (n : ℝ) ≤ x) = Icc 0 ⌊x⌋₊ := by
    ext n
    simp only [mem_filter, mem_Icc]
    constructor
    · rintro ⟨⟨h0, _⟩, hn⟩
      exact ⟨h0, (Nat.le_floor_iff hx).2 hn⟩
    · rintro ⟨h0, hn⟩
      exact ⟨⟨h0, hn.trans hfloor⟩, (Nat.le_floor_iff hx).1 hn⟩
  rw [Chebyshev.psi_eq_sum_Icc, ← hs, sum_filter]

/-- The lower smoothing never exceeds psi. -/
theorem psiLower_le_psi {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : psiLower N x h ≤ Chebyshev.psi x := by
  rw [psi_eq_indicator_sum hx hN]
  unfold psiLower
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · rw [if_pos hn]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (W_le_one ((x - n) / h))
        (ArithmeticFunction.vonMangoldt_nonneg (n := n))
  · rw [if_neg hn, W_eq_zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg
      (by linarith [lt_of_not_ge hn]) hh.le), mul_zero]

/-- The upper smoothing majorizes psi, including at prime-power jumps. -/
theorem psi_le_psiUpper {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x ≤ N) : Chebyshev.psi x ≤ psiUpper N x h := by
  rw [psi_eq_indicator_sum hx hN]
  unfold psiUpper
  apply sum_le_sum
  intro n _
  by_cases hn : (n : ℝ) ≤ x
  · have hw : 4 ≤ (x + 4 * h - n) / h := (le_div_iff₀ hh).2 (by linarith)
    rw [if_pos hn, W_eq_one_of_four_le hw, mul_one]
  · rw [if_neg hn]
    exact mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (W_nonneg _)

/-- The two polynomial smoothings sandwich psi on one common truncation. -/
theorem psi_sandwich {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N) :
    psiLower N x h ≤ Chebyshev.psi x ∧ Chebyshev.psi x ≤ psiUpper N x h :=
  ⟨psiLower_le_psi hx hh (by linarith), psi_le_psiUpper hx hh (by linarith)⟩

/-- Terms beyond the common truncation have zero upper weight. -/
theorem upper_weight_eq_zero {x h : ℝ} (hh : 0 < h) {N n : ℕ}
    (hN : x + 4 * h ≤ N) (hn : N < n) : W ((x + 4 * h - n) / h) = 0 := by
  apply W_eq_zero_of_nonpos
  apply div_nonpos_of_nonpos_of_nonneg _ hh.le
  have hn' : (N : ℝ) < n := by exact_mod_cast hn
  linarith

/-- A sufficiently large finite truncation equals the canonical primitive. -/
theorem psi4Trunc_eq_Psi4 {t : ℝ} (ht : 0 ≤ t) {N : ℕ} (hN : t ≤ N) :
    psi4Trunc N t = Psi4 t := by
  have hfloor : ⌊t⌋₊ ≤ N := by exact_mod_cast (Nat.floor_le ht).trans hN
  unfold Psi4 psi4Trunc
  symm
  apply sum_subset (Icc_subset_Icc le_rfl hfloor)
  intro n hn hn'
  have hnf : ⌊t⌋₊ < n := by
    have hn0 : 0 ≤ n := Nat.zero_le n
    simp only [mem_Icc, hn0, true_and] at hn'
    omega
  have hnt : t < n := (Nat.floor_lt ht).1 hnf
  simp [quarticPrimitive, max_eq_right (show t - n ≤ 0 by linarith)]

/-- Fourth differences commute with finite sums. -/
theorem fourthDifference_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x h : ℝ) :
    fourthDifference (fun t => ∑ i ∈ s, f i t) x h =
      ∑ i ∈ s, fourthDifference (f i) x h := by
  simp only [fourthDifference, sum_add_distrib, sum_sub_distrib, mul_sum]

/-- Fourth differences commute with scalar multiplication. -/
theorem fourthDifference_mul (c : ℝ) (f : ℝ → ℝ) (x h : ℝ) :
    fourthDifference (fun t => c * f t) x h = c * fourthDifference f x h := by
  unfold fourthDifference
  ring

/-- The normalized fourth difference of one truncated power is the quartic
CDF weight. This is a purely algebraic identity. -/
theorem fourthDifference_quarticPrimitive {h : ℝ} (hh : 0 < h) (x a : ℝ) :
    fourthDifference (fun t => quarticPrimitive (t - a)) x h / h ^ 4 =
      W ((x + 4 * h - a) / h) := by
  have hd (t : ℝ) : max (t / h) 0 = max t 0 / h := by
    simpa only [zero_div] using max_div_div_right hh.le t 0
  have e1 : (x + 4 * h - a) / h - 1 = (x + 3 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e2 : (x + 4 * h - a) / h - 2 = (x + 2 * h - a) / h := by
    field_simp [hh.ne']; ring
  have e3 : (x + 4 * h - a) / h - 3 = (x + h - a) / h := by
    field_simp [hh.ne']; ring
  have e4 : (x + 4 * h - a) / h - 4 = (x - a) / h := by
    field_simp [hh.ne']; ring
  unfold fourthDifference quarticPrimitive W
  rw [e1, e2, e3, e4]
  simp only [hd, div_pow]
  ring

/-- The normalized forward difference of the finite fourth primitive is
exactly the upper polynomial smoothing. -/
theorem fourthDifference_psi4Trunc {h : ℝ} (hh : 0 < h) (N : ℕ) (x : ℝ) :
    fourthDifference (psi4Trunc N) x h / h ^ 4 = psiUpper N x h := by
  unfold psi4Trunc psiUpper
  rw [fourthDifference_sum, sum_div]
  apply sum_congr rfl
  intro n _
  rw [fourthDifference_mul, mul_div_assoc,
    fourthDifference_quarticPrimitive hh]

/-- The canonical fourth primitive has the same difference identity whenever
the finite upper sum contains its complete support. -/
theorem fourthDifference_Psi4 {x h : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N) :
    fourthDifference Psi4 x h / h ^ 4 = psiUpper N x h := by
  have h0 := psi4Trunc_eq_Psi4 hx (show x ≤ N by linarith)
  have h1 := psi4Trunc_eq_Psi4 (show 0 ≤ x + h by linarith)
    (show x + h ≤ N by linarith)
  have h2 := psi4Trunc_eq_Psi4 (show 0 ≤ x + 2 * h by linarith)
    (show x + 2 * h ≤ N by linarith)
  have h3 := psi4Trunc_eq_Psi4 (show 0 ≤ x + 3 * h by linarith)
    (show x + 3 * h ≤ N by linarith)
  have h4 := psi4Trunc_eq_Psi4 (show 0 ≤ x + 4 * h by linarith) hN
  have hd : fourthDifference Psi4 x h = fourthDifference (psi4Trunc N) x h := by
    unfold fourthDifference
    rw [h0, h1, h2, h3, h4]
  rw [hd]
  exact fourthDifference_psi4Trunc hh N x

/-- The backward-shifted forward difference is exactly the lower smoothing. -/
theorem fourthDifference_Psi4_lower {x h : ℝ} (hh : 0 < h) (hx : 4 * h ≤ x)
    {N : ℕ} (hN : x ≤ N) :
    fourthDifference Psi4 (x - 4 * h) h / h ^ 4 = psiLower N x h := by
  have ht := fourthDifference_Psi4 (x := x - 4 * h) (by linarith) hh
    (show x - 4 * h + 4 * h ≤ N by linarith)
  simpa only [psiUpper, psiLower, sub_add_cancel] using ht

/-- Once the two polynomial smoothings have controlled errors, the cost of
unsmoothing is precisely `2*h`. The analytic error bound remains explicit. -/
theorem psi_error_of_polynomial_errors {x h E : ℝ} (hx : 0 ≤ x) (hh : 0 < h)
    {N : ℕ} (hN : x + 4 * h ≤ N)
    (hupper : |psiUpper N x h - (x + 2 * h)| ≤ E)
    (hlower : |psiLower N x h - (x - 2 * h)| ≤ E) :
    |Chebyshev.psi x - x| ≤ E + 2 * h := by
  obtain ⟨hlo, hup⟩ := psi_sandwich hx hh hN
  obtain ⟨hu1, hu2⟩ := abs_le.mp hupper
  obtain ⟨hl1, hl2⟩ := abs_le.mp hlower
  rw [abs_le]
  constructor <;> linarith

end TernaryGoldbach.RSBounds.PolynomialPsi
