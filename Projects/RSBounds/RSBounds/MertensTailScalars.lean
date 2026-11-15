import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Elementary scalar certificate for the reciprocal-square tail at 1894439.
This module imports no zeta-zero or finite-RH theorem. -/

namespace TernaryGoldbach.RSBounds.MertensTailScalars

private theorem rational_pow_le_exp_nat (n : ℕ) : (2.7 : ℝ) ^ n ≤ Real.exp n := by
  calc
    (2.7 : ℝ) ^ n ≤ (Real.exp 1) ^ n := by
      gcongr
      linarith [Real.exp_one_gt_d9]
    _ = Real.exp n := by rw [← Real.exp_nat_mul]; simp

theorem log_A_bounds : 1 ≤ Real.log 1894439 ∧ Real.log 1894439 ≤ 15 := by
  constructor
  · apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 1894439)).mpr
    exact Real.exp_one_lt_three.le.trans (by norm_num)
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 1894439)).mpr
    exact (by norm_num : (1894439 : ℝ) ≤ 2.7 ^ 15).trans (rational_pow_le_exp_nat 15)

theorem log_A_div_two_pi_le : Real.log (1894439 / (2 * Real.pi)) ≤ 13 := by
  apply (Real.log_le_iff_le_exp (by positivity : (0 : ℝ) < 1894439 / (2 * Real.pi))).mpr
  calc
    (1894439 : ℝ) / (2 * Real.pi) ≤ 1894439 / 6 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      linarith [Real.pi_gt_three]
    _ ≤ (2.7 : ℝ) ^ 13 := by norm_num
    _ ≤ Real.exp 13 := rational_pow_le_exp_nat 13

theorem coefficient_A_le : (0.137 : ℝ) + 0.443 / Real.log 1894439 ≤ 0.58 := by
  have h : (0.443 : ℝ) / Real.log 1894439 ≤ 0.443 := by
    rw [div_le_iff₀ (by linarith [log_A_bounds.1])]
    nlinarith [log_A_bounds.1]
  linarith

theorem error_A_le :
    (0.137 : ℝ) * Real.log 1894439 + 0.443 * Real.log (Real.log 1894439) + 1.588 ≤ 6 := by
  have hloglog : Real.log (Real.log 1894439) ≤ 3 := by
    apply (Real.log_le_iff_le_exp (by linarith [log_A_bounds.1])).mpr
    exact log_A_bounds.2.trans
      ((by norm_num : (15 : ℝ) ≤ 2.7 ^ 3).trans (rational_pow_le_exp_nat 3))
  linarith [log_A_bounds.2]

/-- A closed rational/elementary bound for the exact Rosser square-tail allowance. -/
theorem square_tail_A_lt :
    (Real.log (1894439 / (2 * Real.pi)) + 1) / (2 * Real.pi * 1894439) +
      (0.137 + 0.443 / Real.log 1894439) / (2 * (1894439 : ℝ) ^ 2) +
      2 * (0.137 * Real.log 1894439 + 0.443 * Real.log (Real.log 1894439) + 1.588) /
        (1894439 : ℝ) ^ 2 < 1.2e-6 := by
  have h1 : (Real.log (1894439 / (2 * Real.pi)) + 1) /
      (2 * Real.pi * 1894439) ≤ (14 : ℝ) / (6.28 * 1894439) := by
    calc
      _ ≤ (14 : ℝ) / (2 * Real.pi * 1894439) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith [log_A_div_two_pi_le]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        nlinarith [Real.pi_gt_d2]
  have h2 : (0.137 + 0.443 / Real.log 1894439) / (2 * (1894439 : ℝ) ^ 2) ≤
      (0.58 : ℝ) / (2 * (1894439 : ℝ) ^ 2) :=
    div_le_div_of_nonneg_right coefficient_A_le (by positivity)
  have h3 : 2 * (0.137 * Real.log 1894439 + 0.443 * Real.log (Real.log 1894439) + 1.588) /
      (1894439 : ℝ) ^ 2 ≤ (12 : ℝ) / (1894439 : ℝ) ^ 2 := by
    apply div_le_div_of_nonneg_right _ (by norm_num)
    linarith [error_A_le]
  have hrat : (14 : ℝ) / (6.28 * 1894439) +
      0.58 / (2 * (1894439 : ℝ) ^ 2) + 12 / (1894439 : ℝ) ^ 2 < 1.2e-6 := by norm_num
  linarith

end TernaryGoldbach.RSBounds.MertensTailScalars
