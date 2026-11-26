import RSBounds.RS75MomentCalculus
import RSBounds.RS75GoldenSeries
import RSBounds.RS75GoldenNumerics

/-!
# Binding the finite golden-ratio certificates to the actual zeta moments

The infinite-tail inequalities use proved calculus and actual L-series
summability. The finite centers and allowances are exactly the expressions
certified by `RS75GoldenNumerics`.
-/

open Finset

namespace TernaryGoldbach.RSBounds.RS75GoldenTails

open RS75MomentCalculus

theorem sum_range_eq_momentSum {s : ℝ} (hs : 1 < s) (j m : ℕ) :
    (∑ n ∈ Finset.range (m + 1), momentFn s j n) = RS75GoldenNumerics.momentSum s j m := by
  induction m with
  | zero => simp [momentFn, RS75GoldenNumerics.momentSum,
      Real.zero_rpow (show -s ≠ 0 by linarith)]
  | succ m ih =>
      rw [Finset.sum_range_succ, ih, RS75GoldenNumerics.momentSum]
      simp only [momentFn, Nat.cast_add, Nat.cast_one]

theorem tailPrimitive_eq_tailIntegral (s : ℝ) (j : ℕ) :
    tailPrimitive s j 64 = RS75GoldenNumerics.tailIntegral s j := by
  have hp : (64 : ℝ) ^ (-(s - 1)) = 64 * (64 : ℝ) ^ (-s) := by
    rw [show -(s - 1) = -s + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
    ring
  rcases j with _ | _ | _ | j
  all_goals simp only [tailPrimitive, RS75GoldenNumerics.tailIntegral, momentFn,
    hp, pow_zero, pow_one, one_mul]
  all_goals ring

theorem center_le_moment_le_upper {s : ℝ} (hs : 1.6 ≤ s) (hs' : s ≤ 1.7)
    (j : ℕ) (hj : j ≤ 2) :
    RS75GoldenNumerics.center s j ≤ RS75GoldenSeries.moment s j ∧
      RS75GoldenSeries.moment s j ≤ RS75GoldenNumerics.upper s j := by
  have hs1 : 1 < s := by linarith
  have hsum : Summable (fun n : ℕ => momentFn s j n) := by
    simpa only [momentFn] using RS75GoldenSeries.summable_moment hs1 j
  have h := moment_bounds hs hs' j hj hsum
  have hsum := sum_range_eq_momentSum hs1 j 63
  norm_num only [Nat.reduceAdd] at hsum
  rw [hsum, tailPrimitive_eq_tailIntegral] at h
  constructor
  · simpa only [RS75GoldenNumerics.center, RS75GoldenSeries.moment, momentFn] using h.1
  · calc
      RS75GoldenSeries.moment s j ≤
          RS75GoldenNumerics.momentSum s j 63 + momentFn s j 64 / 2 +
            RS75GoldenNumerics.tailIntegral s j - momentDeriv s j 64 / 8 := h.2
      _ = RS75GoldenNumerics.upper s j := by
        unfold RS75GoldenNumerics.upper RS75GoldenNumerics.center momentFn momentDeriv
        ring

theorem center_le_moment {s : ℝ} (hs : 1.6 ≤ s) (hs' : s ≤ 1.7)
    (j : ℕ) (hj : j ≤ 2) :
    RS75GoldenNumerics.center s j ≤ RS75GoldenSeries.moment s j :=
  (center_le_moment_le_upper hs hs' j hj).1

theorem moment_le_upper {s : ℝ} (hs : 1.6 ≤ s) (hs' : s ≤ 1.7)
    (j : ℕ) (hj : j ≤ 2) :
    RS75GoldenSeries.moment s j ≤ RS75GoldenNumerics.upper s j :=
  (center_le_moment_le_upper hs hs' j hj).2

end TernaryGoldbach.RSBounds.RS75GoldenTails
