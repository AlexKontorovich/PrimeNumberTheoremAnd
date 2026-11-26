import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The elementary budget that preserves the exact logarithmic zeta bound. -/

namespace TernaryGoldbach.RSBounds.BacklundGammaModulus

theorem log_le_half {t : ℝ} (ht : 0 < t) : Real.log t ≤ t / 2 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < t / 2 by positivity)
  rw [Real.log_div ht.ne' (by norm_num)] at h
  have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  linarith

/-- The right-half-plane saving `0.048` absorbs the full Gamma multiplier
allowance `exp(5/(2t²))` already at height fifty. -/
theorem exp_mul_log_saving_lt {t : ℝ} (ht : 50 ≤ t) :
    Real.exp (5 / (2 * t ^ 2)) * (Real.log t - 6 / 125) < Real.log t := by
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hl0 : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have hq : 5 / (2 * t ^ 2) * Real.log t < 6 / 125 := by
    have h := mul_le_mul_of_nonneg_left (log_le_half ht0)
      (by positivity : 0 ≤ 5 / (2 * t ^ 2))
    have he : 5 / (2 * t ^ 2) * (t / 2) = 5 / (4 * t) := by
      field_simp
      ring
    rw [he] at h
    have hb : 5 / (4 * t) < 6 / 125 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    exact h.trans_lt hb
  have hexp := Real.add_one_le_exp (-(5 / (2 * t ^ 2)))
  have hprod := mul_le_mul_of_nonneg_right hexp hl0
  have hs : Real.log t - 6 / 125 <
      Real.exp (-(5 / (2 * t ^ 2))) * Real.log t := by
    nlinarith
  have hm := mul_lt_mul_of_pos_left hs (Real.exp_pos (5 / (2 * t ^ 2)))
  have he : Real.exp (5 / (2 * t ^ 2)) *
      (Real.exp (-(5 / (2 * t ^ 2))) * Real.log t) = Real.log t := by
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rwa [he] at hm

end TernaryGoldbach.RSBounds.BacklundGammaModulus
