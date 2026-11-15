import Mathlib

/-!
# The exact quartic kernel for fourfold additive smoothing

`W` is the distribution function of a sum of four variables uniformly
distributed on `[0,1]`, expressed as a finite difference of the truncated
quartic. The proofs below are polynomial identities and inequalities; no
probabilistic premise or analytic prime estimate is used.

This is the compact smoothing relevant to Rosser--Schoenfeld (1975),
Lemma 8, with `m = 4`.
-/

namespace TernaryGoldbach.RSBounds.PolynomialSmoothing

/-- The normalized fourth difference of the truncated fourth power. -/
noncomputable def W (t : ℝ) : ℝ :=
  ((max t 0) ^ 4 - 4 * (max (t - 1) 0) ^ 4 +
    6 * (max (t - 2) 0) ^ 4 - 4 * (max (t - 3) 0) ^ 4 +
    (max (t - 4) 0) ^ 4) / 24

theorem W_eq_sum (t : ℝ) :
    W t = (∑ j ∈ Finset.range 5,
      (-1 : ℝ) ^ j * (Nat.choose 4 j : ℝ) * (max (t - j) 0) ^ 4) / 24 := by
  norm_num [W, Finset.sum_range_succ, Nat.choose]
  ring

private theorem posPart_pow_four_add (t : ℝ) :
    (max t 0) ^ 4 + (max (-t) 0) ^ 4 = t ^ 4 := by
  rcases le_or_gt 0 t with ht | ht
  · rw [max_eq_left ht, max_eq_right (by linarith : -t ≤ 0)]
    ring
  · rw [max_eq_right ht.le, max_eq_left (by linarith : 0 ≤ -t)]
    ring

/-- Reflection about the midpoint of the fourfold averaging interval. -/
theorem W_add_reflect (t : ℝ) : W t + W (4 - t) = 1 := by
  have h0 := posPart_pow_four_add t
  have h1 := posPart_pow_four_add (t - 1)
  have h2 := posPart_pow_four_add (t - 2)
  have h3 := posPart_pow_four_add (t - 3)
  have h4 := posPart_pow_four_add (t - 4)
  unfold W
  rw [show 4 - t - 1 = -(t - 3) by ring,
    show 4 - t - 2 = -(t - 2) by ring,
    show 4 - t - 3 = -(t - 1) by ring,
    show 4 - t - 4 = -t by ring,
    show 4 - t = -(t - 4) by ring]
  linear_combination (h0 - 4 * h1 + 6 * h2 - 4 * h3 + h4) / 24

theorem W_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) : W t = 0 := by
  unfold W
  rw [max_eq_right ht,
    max_eq_right (by linarith : t - 1 ≤ 0),
    max_eq_right (by linarith : t - 2 ≤ 0),
    max_eq_right (by linarith : t - 3 ≤ 0),
    max_eq_right (by linarith : t - 4 ≤ 0)]
  norm_num

theorem W_eq_one_of_four_le {t : ℝ} (ht : 4 ≤ t) : W t = 1 := by
  have h := W_add_reflect t
  rw [W_eq_zero_of_nonpos (by linarith : 4 - t ≤ 0), add_zero] at h
  exact h

private theorem W_bounds_of_le_two {t : ℝ} (ht : t ≤ 2) :
    0 ≤ W t ∧ W t ≤ 1 := by
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [W_eq_zero_of_nonpos ht0]
    norm_num
  rcases le_or_gt t 1 with ht1 | ht1
  · have he : W t = t ^ 4 / 24 := by
      unfold W
      rw [max_eq_left ht0.le,
        max_eq_right (by linarith : t - 1 ≤ 0),
        max_eq_right (by linarith : t - 2 ≤ 0),
        max_eq_right (by linarith : t - 3 ≤ 0),
        max_eq_right (by linarith : t - 4 ≤ 0)]
      ring
    have hp := pow_le_pow_left₀ ht0.le ht1 4
    rw [he]
    constructor
    · positivity
    · norm_num at hp
      linarith
  · have he : W t = (t ^ 4 - 4 * (t - 1) ^ 4) / 24 := by
      unfold W
      rw [max_eq_left ht0.le,
        max_eq_left (by linarith : 0 ≤ t - 1),
        max_eq_right (by linarith : t - 2 ≤ 0),
        max_eq_right (by linarith : t - 3 ≤ 0),
        max_eq_right (by linarith : t - 4 ≤ 0)]
      ring
    have hp : (2 * (t - 1)) ^ 4 ≤ t ^ 4 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 4
    have ht4 : t ^ 4 ≤ 16 := by
      have := pow_le_pow_left₀ ht0.le ht 4
      norm_num at this
      exact this
    have hu4 : 0 ≤ (t - 1) ^ 4 := by positivity
    rw [he]
    constructor <;> nlinarith

theorem W_bounds (t : ℝ) : 0 ≤ W t ∧ W t ≤ 1 := by
  rcases le_or_gt t 2 with ht | ht
  · exact W_bounds_of_le_two ht
  · have h := W_bounds_of_le_two (show 4 - t ≤ 2 by linarith)
    have he := W_add_reflect t
    constructor <;> linarith

theorem W_nonneg (t : ℝ) : 0 ≤ W t := (W_bounds t).1

theorem W_le_one (t : ℝ) : W t ≤ 1 := (W_bounds t).2

theorem continuous_W : Continuous W := by
  unfold W
  fun_prop

/-- Fourfold finite differences of the integrated main term `x^5/120`.
After dividing by `h^4`, the upper average differs from `x` by exactly `2h`. -/
theorem fourth_difference_main_term {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    ((x + 4 * h) ^ 5 - 4 * (x + 3 * h) ^ 5 + 6 * (x + 2 * h) ^ 5 -
      4 * (x + h) ^ 5 + x ^ 5) / (120 * h ^ 4) = x + 2 * h := by
  field_simp
  ring

/-- The corresponding lower average has main term `x - 2h`. -/
theorem fourth_difference_main_term_lower {h : ℝ} (hh : h ≠ 0) (x : ℝ) :
    (x ^ 5 - 4 * (x - h) ^ 5 + 6 * (x - 2 * h) ^ 5 -
      4 * (x - 3 * h) ^ 5 + (x - 4 * h) ^ 5) / (120 * h ^ 4) = x - 2 * h := by
  field_simp
  ring

end TernaryGoldbach.RSBounds.PolynomialSmoothing
