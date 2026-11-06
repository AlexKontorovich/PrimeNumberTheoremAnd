import RSBounds.RosserWeightedBounds

/-!
# Joining actual zero-sum bounds and subdividing finite bands

The split estimate retains the count correction at the splitting height until
the reciprocal and fifth-power contributions are combined. All bounds concern
actual zeta zeros with analytic multiplicity; no RH or count premise is used.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.RosserWeightedSplit
open Rosser1941 WeightedZetaZeros RosserWeightedBounds RosserTailIntegrals
open BacklundCountIdentity

/-- Combined reciprocal/fifth-power estimate, keeping the signed split correction
until it can be bounded by twice Rosser's error. -/
theorem reciprocal_fifth_split_le {D Y T k C : ℝ}
    (hD : 7 ≤ D) (hDY : D ≤ Y) (hYT : Y ≤ T)
    (hk : 0 ≤ k) (hC : 0 ≤ C) (hcoeff : k / Y ≤ C / Y ^ 5) :
    k * weightedSum D Y (fun t => 1 / t) +
      C * weightedSum Y T (fun t => 1 / t ^ 5) ≤
    k * (I D Y + (G D - positiveZeroCount D) / D) + C * J Y +
      2 * rosserR 1.588 Y * (C / Y ^ 5 - k / Y) := by
  have hlo := mul_le_mul_of_nonneg_left (reciprocal_sum_le_endpoints hD hDY) hk
  have hhi := mul_le_mul_of_nonneg_left (fifth_sum_le_head (hD.trans hDY) hYT) hC
  have hcorr := mul_le_mul_of_nonneg_right
    (head_correction_le (by linarith : 2 ≤ Y)) (sub_nonneg.mpr hcoeff)
  calc
    _ ≤ k * (I D Y + (positiveZeroCount Y - G Y) / Y +
        (G D - positiveZeroCount D) / D) +
        C * (J Y + (G Y - positiveZeroCount Y) / Y ^ 5) := add_le_add hlo hhi
    _ = k * (I D Y + (G D - positiveZeroCount D) / D) + C * J Y +
        (G Y - positiveZeroCount Y) * (C / Y ^ 5 - k / Y) := by ring
    _ ≤ _ := add_le_add le_rfl hcorr

/-- A window with identical endpoints contains no zeros. -/
theorem weightedSum_self {a : ℝ} (ha : 0 < a) (φ : ℝ → ℝ) :
    weightedSum a a φ = 0 := by
  classical
  unfold weightedSum
  apply Finset.sum_eq_zero
  intro ρ hρ
  exact if_neg (not_lt.mpr (((mem_closedPositiveZeros_iff ha).mp hρ).2.2))

/-- Exact adjacent-window decomposition; no regularity of the weight is needed. -/
theorem weightedSum_adjacent {a Y b : ℝ} (hY : 0 < Y) (haY : a ≤ Y) (hYb : Y ≤ b)
    (φ : ℝ → ℝ) :
    weightedSum a b φ = weightedSum a Y φ + weightedSum Y b φ := by
  classical
  unfold weightedSum
  rw [← filter_closedPositiveZeros hY hYb, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ρ _
  by_cases hi : ρ.im ≤ Y
  · simp [hi, not_lt.mpr hi]
  · have hYi : Y < ρ.im := lt_of_not_ge hi
    have hai : a < ρ.im := haY.trans_lt hYi
    simp [hi, hYi, hai]

/-- A finite monotone partition telescopes for every actual zero weight. -/
theorem weightedSum_telescope (n : ℕ) (x : ℕ → ℝ) (hx : Monotone x)
    (hx0 : 0 < x 0) (φ : ℝ → ℝ) :
    weightedSum (x 0) (x n) φ =
      ∑ j ∈ Finset.range n, weightedSum (x j) (x (j + 1)) φ := by
  induction n with
  | zero => simp [weightedSum_self hx0]
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact weightedSum_adjacent (hx0.trans_le (hx (Nat.zero_le n)))
      (hx (Nat.zero_le n)) (hx (Nat.le_succ n)) φ

/-- Sum any finite collection of nonnegatively weighted reciprocal-band lower
bounds. Instantiating `n=8` supplies the eight-band cancellation allowance. -/
theorem weighted_reciprocal_bands_lower (n : ℕ) (x c : ℕ → ℝ)
    (hx : Monotone x) (hx0 : 2 ≤ x 0) (hc : ∀ j < n, 0 ≤ c j) :
    (∑ j ∈ Finset.range n, c j *
      ((rosserF (x (j + 1)) - rosserR 1.588 (x (j + 1)) -
        rosserF (x j) - rosserR 1.588 (x j)) / x (j + 1))) ≤
      ∑ j ∈ Finset.range n, c j * weightedSum (x j) (x (j + 1)) (fun t => 1 / t) := by
  apply Finset.sum_le_sum
  intro j hj
  exact mul_le_mul_of_nonneg_left
    (reciprocal_sum_ge_rosser (hx0.trans (hx (Nat.zero_le j))) (hx (Nat.le_succ j)))
    (hc j (Finset.mem_range.mp hj))

/-- The unweighted finite band bounds telescope to a single actual reciprocal sum. -/
theorem reciprocal_bands_lower (n : ℕ) (x : ℕ → ℝ) (hx : Monotone x)
    (hx0 : 2 ≤ x 0) :
    (∑ j ∈ Finset.range n,
      (rosserF (x (j + 1)) - rosserR 1.588 (x (j + 1)) -
        rosserF (x j) - rosserR 1.588 (x j)) / x (j + 1)) ≤
      weightedSum (x 0) (x n) (fun t => 1 / t) := by
  have he := weighted_reciprocal_bands_lower n x (fun _ => 1) hx hx0
    (fun _ _ => by norm_num)
  simp only [one_mul] at he
  rw [← weightedSum_telescope n x hx (by linarith : 0 < x 0)] at he
  exact he

end TernaryGoldbach.RSBounds.RosserWeightedSplit
