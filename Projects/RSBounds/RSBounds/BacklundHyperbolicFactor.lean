import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Real

namespace TernaryGoldbach.RSBounds.BacklundHyperbolicFactor

theorem exp_neg_pi_mul_le {t : ℝ} (ht : 50 ≤ t) :
    Real.exp (-Real.pi * t) ≤ 1 / (8 * t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hp := Real.pow_div_factorial_le_exp (Real.pi * t) (by positivity : 0 ≤ Real.pi * t) 3
  norm_num at hp
  have hcub : (3 * t) ^ 3 ≤ (Real.pi * t) ^ 3 := by
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.pi_gt_three).le ht0.le
  have hbig : 8 * t ^ 2 ≤ (Real.pi * t) ^ 3 / 6 := by
    have hh := mul_nonneg (by linarith : 0 ≤ t - 2) (sq_nonneg t)
    nlinarith
  have hexp : 8 * t ^ 2 ≤ Real.exp (Real.pi * t) := hbig.trans hp
  have he : -Real.pi * t = -(Real.pi * t) := by ring
  rw [he, Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hexp

theorem sqrt_ratio_le_exp {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 2) :
    Real.sqrt ((1 + q) / (1 - q)) ≤ Real.exp (2 * q) := by
  have hd : 0 < 1 - q := by linarith
  have hr : (1 + q) / (1 - q) ≤ 1 + 4 * q := by
    rw [div_le_iff₀ hd]
    nlinarith [mul_nonneg hq0 (by linarith : 0 ≤ 1 / 2 - q)]
  have he : 1 + 4 * q ≤ Real.exp (4 * q) := by
    linarith [Real.add_one_le_exp (4 * q)]
  have heq : Real.exp (4 * q) = Real.exp (2 * q) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hs : Real.sqrt ((1 + q) / (1 - q)) ^ 2 = (1 + q) / (1 - q) :=
    Real.sq_sqrt (by positivity)
  rw [heq] at he
  nlinarith [Real.sqrt_nonneg ((1 + q) / (1 - q)), Real.exp_pos (2 * q)]

theorem sqrt_exp_ratio_le {t : ℝ} (ht : 50 ≤ t) :
    Real.sqrt ((1 + Real.exp (-Real.pi * t)) / (1 - Real.exp (-Real.pi * t))) ≤
      Real.exp (1 / (4 * t ^ 2)) := by
  have ht0 : 0 < t := by linarith
  have hq := exp_neg_pi_mul_le ht
  have hu : 1 / (8 * t ^ 2) ≤ (1 / 2 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb := sqrt_ratio_le_exp (Real.exp_pos _).le (hq.trans hu)
  refine hb.trans (Real.exp_le_exp.mpr ?_)
  calc
    2 * Real.exp (-Real.pi * t) ≤ 2 * (1 / (8 * t ^ 2)) := by gcongr
    _ = 1 / (4 * t ^ 2) := by ring

end TernaryGoldbach.RSBounds.BacklundHyperbolicFactor
