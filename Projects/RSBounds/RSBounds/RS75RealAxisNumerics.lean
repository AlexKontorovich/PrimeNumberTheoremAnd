import RSBounds.ZetaZeroTableHead

/-!
# Two rational numerical inputs for the RS75 real-axis argument

The odd-square series uses 24 exact terms followed by the telescoping tail
`1 / (2 * (2 * 24 + 1)) = 1/98`. The second constant uses only the already
certified rational upper brackets for the first 29 zeros. No zero evaluation
is performed in this module.
-/

namespace TernaryGoldbach.RSBounds.RS75RealAxisNumerics
open BacklundLowCount

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Zero-based indexing of `sum (n >= 1), 1/(2*n+1)^2`. -/
noncomputable def oddSquareTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) + 3) ^ 2

private noncomputable def tailMajorant (n : ℕ) : ℝ := 1 / (2 * (2 * (n : ℝ) + 1))

theorem oddSquareTerm_nonneg (n : ℕ) : 0 ≤ oddSquareTerm n := by
  unfold oddSquareTerm
  positivity

private theorem tailMajorant_nonneg (n : ℕ) : 0 ≤ tailMajorant n := by
  unfold tailMajorant
  positivity

private theorem oddSquareTerm_le_tail_difference (n : ℕ) :
    oddSquareTerm n ≤ tailMajorant n - tailMajorant (n + 1) := by
  have h1 : 0 < 2 * (n : ℝ) + 1 := by positivity
  have h3 : 0 < 2 * (n : ℝ) + 3 := by positivity
  unfold oddSquareTerm tailMajorant
  push_cast
  calc
    1 / (2 * (n : ℝ) + 3) ^ 2 ≤
        1 / ((2 * (n : ℝ) + 1) * (2 * (n : ℝ) + 3)) :=
      div_le_div_of_nonneg_left (by norm_num) (mul_pos h1 h3) (by nlinarith)
    _ = _ := by
      rw [show 2 * ((n : ℝ) + 1) + 1 = 2 * (n : ℝ) + 3 by ring]
      field_simp
      ring

private theorem sum_range_tail_le (m n : ℕ) :
    (∑ k ∈ Finset.range n, oddSquareTerm (k + m)) ≤
      tailMajorant m - tailMajorant (n + m) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have ht := oddSquareTerm_le_tail_difference (n + m)
      have he : n + 1 + m = n + m + 1 := by omega
      rw [he]
      linarith

private theorem sum_range_tail_le_bound (m n : ℕ) :
    (∑ k ∈ Finset.range n, oddSquareTerm (k + m)) ≤ tailMajorant m :=
  (sum_range_tail_le m n).trans (sub_le_self _ (tailMajorant_nonneg _))

theorem summable_oddSquareTerm : Summable oddSquareTerm := by
  apply summable_of_sum_range_le oddSquareTerm_nonneg
  intro n
  simpa only [Nat.add_zero] using sum_range_tail_le_bound 0 n

/-- General elementary tail bound, including the `1/98` tail after 24 terms. -/
theorem tsum_oddSquareTerm_tail_le (m : ℕ) :
    (∑' n : ℕ, oddSquareTerm (n + m)) ≤ 1 / (2 * (2 * (m : ℝ) + 1)) := by
  apply Real.tsum_le_of_sum_range_le (fun n => oddSquareTerm_nonneg (n + m))
  exact sum_range_tail_le_bound m

def oddFiniteUpper : ℚ :=
  (∑ n ∈ Finset.range 24, (1 : ℚ) / (2 * (n : ℚ) + 3) ^ 2) + 1 / 98

theorem oddFiniteUpper_le : oddFiniteUpper ≤ 0.23391 := by decide +kernel

private theorem odd_finite_bound_real :
    (∑ n ∈ Finset.range 24, oddSquareTerm n) + 1 / 98 ≤ (0.23391 : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr oddFiniteUpper_le
  simpa only [oddFiniteUpper, oddSquareTerm, Rat.cast_add, Rat.cast_sum,
    Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat,
    Rat.cast_one, Rat.cast_ofScientific] using h

theorem tsum_oddSquareTerm_le : (∑' n : ℕ, oddSquareTerm n) ≤ 0.23391 := by
  rw [← Summable.sum_add_tsum_nat_add 24 summable_oddSquareTerm]
  have ht := tsum_oddSquareTerm_tail_le 24
  norm_num at ht
  linarith [odd_finite_bound_real]

/-- Twice the explicit 29-zero lower bound for the xi logarithmic-derivative increment. -/
def headCoefficient : ℚ :=
  2 * ∑ i : Fin 29,
    (bracketUpper i ^ 2 - (0.53 : ℚ) ^ 2) /
      (bracketUpper i ^ 2 + (0.53 : ℚ) ^ 2) ^ 2

theorem headCoefficient_lower : (0.03414 : ℚ) ≤ headCoefficient := by decide +kernel

theorem headCoefficient_cast : (headCoefficient : ℝ) =
    2 * ∑ i : Fin 29,
      ((bracketUpper i : ℝ) ^ 2 - (0.53 : ℝ) ^ 2) /
        ((bracketUpper i : ℝ) ^ 2 + (0.53 : ℝ) ^ 2) ^ 2 := by
  simp only [headCoefficient, Rat.cast_mul, Rat.cast_sum, Rat.cast_div,
    Rat.cast_sub, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific]

theorem headCoefficient_lower_real : (0.03414 : ℝ) ≤ (headCoefficient : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr headCoefficient_lower
  simpa only [Rat.cast_ofScientific] using h

theorem odd_sum_sub_headCoefficient_le :
    (∑' n : ℕ, oddSquareTerm n) - (headCoefficient : ℝ) ≤ 0.19977 := by
  linarith [tsum_oddSquareTerm_le, headCoefficient_lower_real]

theorem odd_sum_sub_headCoefficient_lt :
    (∑' n : ℕ, oddSquareTerm n) - (headCoefficient : ℝ) < 0.2 := by
  linarith [odd_sum_sub_headCoefficient_le]

end TernaryGoldbach.RSBounds.RS75RealAxisNumerics
