module

public import HardyFirstZero.EulerMaclaurin
public import ZetaLean.IntervalCExp

@[expose] public section

/-!
# Support for the two term-box tables (hunt `hardy_first_zero`)

Generic pieces between `EulerMaclaurin.lean` (the remainder) and the generated
`Boxes.lean` (the term boxes at the two endpoints):

* `lit`, `sumBoxes`, `contains_sumBoxes`: literal rectangles and their running sum;
* `ptBox`, `ptBox_contains`: the exact rectangle of `1/2 + it`;
* `main_eq`: the order-4 main term as `Σ_{i<N} i^{-s} + N^{-s} · c_N(s)` with
  `c_N(s) = N/(s-1) + 1/2 + s/(12N)`, so that it needs `N` term boxes and one
  exact product;
* `em30_bound`: the remainder at `N = 30` on the critical line, bounded by an
  explicit rational function of the height.
-/

open Complex Finset ZetaLean ZetaLean.ComplexInterval
open scoped ComplexConjugate

namespace HardyFirstZero

/-- A literal rectangle. -/
def lit (a b c d : ℚ) (h1 : a ≤ b) (h2 : c ≤ d) : ComplexInterval := ⟨⟨a, b, h1⟩, ⟨c, d, h2⟩⟩

/-- The running sum `B 0 + ⋯ + B (n-1)` of rectangles. -/
def sumBoxes (B : ℕ → ComplexInterval) : ℕ → ComplexInterval
  | 0 => ComplexInterval.exact 0 0
  | n + 1 => (sumBoxes B n).add (B n)

theorem contains_sumBoxes {B : ℕ → ComplexInterval} {f : ℕ → ℂ} :
    ∀ {N : ℕ}, (∀ m < N, (B m).contains (f m)) →
      (sumBoxes B N).contains (∑ m ∈ range N, f m)
  | 0, _ => by simpa [sumBoxes] using contains_zero
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    exact contains_add (contains_sumBoxes fun m hm => h m (by omega)) (h n (by omega))

/-- The exact rectangle of `1/2 + it`. -/
def ptBox (t : ℚ) : ComplexInterval := ComplexInterval.exact (1 / 2) t

theorem ptBox_contains (t : ℚ) : (ptBox t).contains (sOf (t : ℝ)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    simp [ptBox, ComplexInterval.exact, Interval.exact, sOf]

/-- The order-4 main term, regrouped around the single power `N^{-s}`. -/
theorem main_eq (s : ℂ) {N : ℕ} (hN : N ≠ 0) :
    ∑ i ∈ range N, (i : ℂ) ^ (-s) + (N : ℂ) ^ (1 - s) / (s - 1)
        + (N : ℂ) ^ (-s) / 2 + s / 12 * (N : ℂ) ^ (-s - 1)
      = ∑ i ∈ range N, (i : ℂ) ^ (-s)
        + (N : ℂ) ^ (-s) * ((N : ℂ) / (s - 1) + 1 / 2 + s / (12 * N)) := by
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have h1 : (N : ℂ) ^ (1 - s) = N * (N : ℂ) ^ (-s) := by
    rw [show (1 - s) = 1 + (-s) by ring, cpow_add _ _ hN', cpow_one]
  have h2 : (N : ℂ) ^ (-s - 1) = (N : ℂ) ^ (-s) * (N : ℂ)⁻¹ := by
    rw [show (-s - 1) = -s + (-1) by ring, cpow_add _ _ hN', cpow_neg_one]
  rw [h1, h2]
  ring

/-- `‖z + j‖ ≤ (1/2 + j) + t` on the critical line. -/
private lemma norm_add_le_of_sOf {t : ℝ} (ht : 0 ≤ t) (j : ℝ) (hj : 0 ≤ j) :
    ‖sOf t + j‖ ≤ 1 / 2 + j + t := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans (le_of_eq ?_)
  have hre : (sOf t + j).re = 1 / 2 + j := by simp [sOf]
  have him : (sOf t + j).im = t := by simp [sOf]
  rw [hre, him, abs_of_nonneg (by linarith), abs_of_nonneg ht]

/-- **The remainder at `N = 30` on the critical line**, for `0 < t ≤ T`:
`‖ζ(1/2+it) - M_30‖ ≤ (1/2+T)(3/2+T)(5/2+T)(7/2+T) / (24389 · 5 · (7/2) · 720)`,
from `zeta_em4_error`, `‖z‖ ≤ |Re z| + |Im z|` and `29^{-7/2} ≤ 1/(29³ · 5)`. -/
theorem em30_bound {t T : ℝ} (ht : 0 < t) (hT : t ≤ T) :
    ‖riemannZeta (sOf t) - (∑ i ∈ range 30, (i : ℂ) ^ (-sOf t) + ((30 : ℕ) : ℂ) ^ (1 - sOf t)
        / (sOf t - 1) + ((30 : ℕ) : ℂ) ^ (-sOf t) / 2
        + sOf t / 12 * ((30 : ℕ) : ℂ) ^ (-sOf t - 1))‖
      ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) / (24389 * 5 * (7 / 2) * 720) := by
  have hQP : sOf t ∈ QP := ⟨by simp [sOf], by simp [sOf, ht]⟩
  have h := zeta_em4_error hQP (N := 30) (by norm_num)
  refine h.trans ?_
  have hre : (sOf t).re = 1 / 2 := sOf_re t
  rw [hre]
  -- the four norms
  have e0 : ‖sOf t‖ ≤ 1 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 0 le_rfl; simp at this; linarith
  have e1 : ‖sOf t + 1‖ ≤ 3 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 1 zero_le_one; push_cast at this; linarith
  have e2 : ‖sOf t + 2‖ ≤ 5 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 2 zero_le_two; push_cast at this; linarith
  have e3 : ‖sOf t + 3‖ ≤ 7 / 2 + T := by
    have := norm_add_le_of_sOf ht.le 3 (by norm_num); push_cast at this; linarith
  have hT0 : 0 ≤ T := by linarith
  have hP : ‖P4 (sOf t)‖ ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) := by
    unfold P4
    rw [norm_mul, norm_mul, norm_mul]
    have a1 := mul_le_mul e0 e1 (norm_nonneg _) (by linarith)
    have a2 := mul_le_mul a1 e2 (norm_nonneg _) (mul_nonneg (by linarith) (by linarith))
    exact mul_le_mul a2 e3 (norm_nonneg _)
      (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  -- the power of 29
  have h29 : ((30 : ℕ) : ℝ) - 1 = 29 := by norm_num
  rw [h29]
  have hpow : (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) ≤ 1 / (24389 * 5) := by
    rw [show (-(1 / 2 : ℝ) - 3) = -(1 / 2) + (-3 : ℝ) by ring,
      Real.rpow_add (by norm_num), Real.rpow_neg (by norm_num), Real.rpow_neg (by norm_num),
      ← Real.sqrt_eq_rpow, show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hs : (5 : ℝ) ≤ Real.sqrt 29 := Real.le_sqrt_of_sq_le (by norm_num)
    have hs0 : 0 < Real.sqrt 29 := by positivity
    rw [show (1 : ℝ) / (24389 * 5) = (5 : ℝ)⁻¹ * ((29 : ℝ) ^ 3)⁻¹ by norm_num]
    gcongr
  have hnn : 0 ≤ (29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) := Real.rpow_nonneg (by norm_num) _
  have hQ0 : 0 ≤ (1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)) (by linarith)
  calc ‖P4 (sOf t)‖ * ((29 : ℝ) ^ (-(1 / 2 : ℝ) - 3) / (1 / 2 + 3)) / 720
      ≤ ((1 / 2 + T) * (3 / 2 + T) * (5 / 2 + T) * (7 / 2 + T))
          * ((1 / (24389 * 5)) / (1 / 2 + 3)) / 720 :=
        div_le_div_of_nonneg_right (mul_le_mul hP
          (div_le_div_of_nonneg_right hpow (by norm_num)) (by positivity) hQ0) (by norm_num)
    _ = _ := by ring

end HardyFirstZero
