import RSBounds.Mertens

/-!
# The finite-interval inverse-linear von Mangoldt weight

This is an exact finite-sum identity, without RH or an asymptotic hypothesis.
It supplies the arithmetic side of the degree-two integrated explicit formula:
the difference of two inverse-linear ramps sums to `∫ ψ(t) / t²`.
-/

open Finset Real MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensIntervalSum

/-- The inverse-linear ramp, cut off at `x`. Its value at zero is immaterial
in the von Mangoldt sum because `Λ 0 = 0`. -/
noncomputable def ramp (x t : ℝ) : ℝ := max (1 / t - 1 / x) 0

theorem ramp_eq {x t : ℝ} (ht : 0 < t) (htx : t ≤ x) :
    ramp x t = 1 / t - 1 / x := by
  apply max_eq_left
  exact sub_nonneg.mpr (one_div_le_one_div_of_le ht htx)

theorem ramp_eq_zero {x t : ℝ} (hx : 0 < x) (hxt : x ≤ t) :
    ramp x t = 0 := by
  apply max_eq_right
  exact sub_nonpos.mpr (one_div_le_one_div_of_le hx hxt)

theorem mangoldt_mul_ramp_eq_zero {x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : n ∉ Icc 0 ⌊x⌋₊) : (Λ n : ℝ) * ramp x n = 0 := by
  have hnx : x < n := by
    have hfloor : ⌊x⌋₊ < n := by simpa using hn
    exact (Nat.floor_lt (le_of_lt hx)).mp hfloor
  rw [ramp_eq_zero hx hnx.le, mul_zero]

theorem summable_mangoldt_mul_ramp {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => (Λ n : ℝ) * ramp x n) := by
  apply summable_of_ne_finset_zero (s := Icc 0 ⌊x⌋₊)
  exact fun n hn => mangoldt_mul_ramp_eq_zero hx hn

theorem tsum_mangoldt_mul_ramp {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, (Λ n : ℝ) * ramp x n) =
      mangoldtWeightedSum x - Chebyshev.psi x / x := by
  rw [tsum_eq_sum (s := Icc 0 ⌊x⌋₊)
    (fun n hn => mangoldt_mul_ramp_eq_zero (by linarith) hn)]
  rw [mangoldtWeightedSum, Chebyshev.psi_eq_sum_Icc, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp
  · have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
      |>.trans' (by exact_mod_cast (mem_Icc.mp hn).2)
    rw [ramp_eq (by exact_mod_cast hn0) hnx]
    ring

/-- The real weighted sum equals the finite integral of `ψ(t)/t²`. -/
theorem tsum_mangoldt_mul_intervalWeight {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑' n : ℕ, (Λ n : ℝ) * (ramp b n - ramp a n)) =
      ∫ t in a..b, Chebyshev.psi t / t ^ 2 := by
  simp_rw [mul_sub]
  rw [(summable_mangoldt_mul_ramp (by linarith : 0 < b)).tsum_sub
    (summable_mangoldt_mul_ramp (by linarith : 0 < a)),
    tsum_mangoldt_mul_ramp (ha.trans hab), tsum_mangoldt_mul_ramp ha]
  have h := mangoldtWeightedSum_sub_log_eq_anchor ha hab
  rw [integral_psi_error_div_sq ha hab] at h
  have ha0 : a ≠ 0 := by linarith
  have hb0 : b ≠ 0 := by linarith
  rw [sub_div, sub_div, div_self ha0, div_self hb0] at h
  linarith

/-- Centering the finite weighted sum introduces exactly `log b - log a`. -/
theorem tsum_mangoldt_mul_intervalWeight_sub_log {a b : ℝ}
    (ha : 1 ≤ a) (hab : a ≤ b) :
    (∑' n : ℕ, (Λ n : ℝ) * (ramp b n - ramp a n)) -
      (Real.log b - Real.log a) =
      ∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 := by
  rw [tsum_mangoldt_mul_intervalWeight ha hab, integral_psi_error_div_sq ha hab]

end TernaryGoldbach.RSBounds.MertensIntervalSum
