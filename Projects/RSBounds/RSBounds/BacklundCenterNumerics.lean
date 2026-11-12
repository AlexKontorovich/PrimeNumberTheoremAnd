import RSBounds.BacklundCenterNumericsData

/-!
# Numerical certification of Backlund's center bound

Both sides of `3.425 < ζ(5/4)/ζ(5/2) < 3.426` are proved in Lean.
The finite sums contain 625 terms. Every root enclosure is checked by
the kernel using integer arithmetic; the infinite tails use the proved
integral test. No external numerical result is used.
-/

namespace TernaryGoldbach.RSBounds

open CenterNumerics

private theorem zeta54_upper :
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ ≤ (459527487 : ℝ) / 100000000 := by
  have ht := zeta_tail_upper (σ := 5 / 4) (by norm_num) (N := 625) (by norm_num)
  have hr := root_upper (n := 625) (p := 1) (k := 4) (D := 5) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
    show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
  linarith [partial54_bounds.2]

private theorem zeta54_lower :
    (459486862 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
  have ht := zeta_tail_lower (σ := 5 / 4) (by norm_num) 625
  have hr := root_lower (n := 626) (p := 1) (k := 4) (D := 10000) (b := 1999)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 4 = -(1 : ℝ) / 4 by norm_num,
    show (5 / 4 : ℝ) - 1 = 1 / 4 by norm_num] at ht
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at ht
  linarith [partial54_bounds.1]

private theorem zeta52_lower :
    (134144158 : ℝ) / 100000000 ≤ ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ :=
  partial52_bounds.1.trans (zeta_partial_lower (by norm_num) 625)

private theorem zeta52_upper :
    ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ≤
      (134144783 : ℝ) / 100000000 + 2 / 46875 := by
  have ht := zeta_tail_upper (σ := 5 / 2) (by norm_num) (N := 625) (by norm_num)
  have hr := root_upper (n := 625) (p := 3) (k := 2) (D := 15625) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num only [Nat.cast_ofNat] at hr
  rw [show (1 : ℝ) - 5 / 2 = -(3 : ℝ) / 2 by norm_num,
    show (5 / 2 : ℝ) - 1 = 3 / 2 by norm_num] at ht
  linarith [partial52_bounds.2]

/-- A coarse upper bound useful for fixing the continuous logarithm branch
on the vertical line through Backlund's center. -/
theorem zeta_five_fourths_upper :
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ < (23 / 5 : ℝ) := by
  linarith [zeta54_upper]

/-- A kernel-checked enclosure for the exact center ratio. In particular,
the printed `3.425` cannot be obtained by rounding this ratio upwards. -/
theorem zeta_five_fourths_ratio_bounds :
    (3.425 : ℝ) <
      ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ ∧
    ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ < 3.426 := by
  have hpos : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [zeta52_lower]
  constructor
  · rw [lt_div_iff₀ hpos]
    linarith [zeta54_lower, zeta52_upper]
  · rw [div_lt_iff₀ hpos]
    linarith [zeta54_upper, zeta52_lower]

/-- The fully certified numerical lower bound at Backlund's center.
It holds for every real height, without any RH or zero-count assumption. -/
theorem zeta_norm_lower_five_fourths_3426 (T : ℝ) :
    (1 : ℝ) / 3.426 ≤ ‖riemannZeta (((5 / 4 : ℝ) : ℂ) + T * Complex.I)‖ := by
  have h1 : 0 < ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by linarith [zeta54_lower]
  have h2 : 0 < ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ := by linarith [zeta52_lower]
  have hratio := (div_lt_iff₀ h2).mp zeta_five_fourths_ratio_bounds.2
  have hc : (1 : ℝ) / 3.426 ≤
      ‖riemannZeta ((5 / 2 : ℝ) : ℂ)‖ / ‖riemannZeta ((5 / 4 : ℝ) : ℂ)‖ := by
    rw [le_div_iff₀ h1]
    linarith
  exact hc.trans (zeta_norm_lower_five_fourths_ratio T)

end TernaryGoldbach.RSBounds
