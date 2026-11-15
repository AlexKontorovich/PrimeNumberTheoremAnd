import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Elementary scalar budget for the finite-to-analytic weighted-Mertens handoff.
There is no prime, zero, finite-RH, or PNT premise in this module. -/

namespace TernaryGoldbach.RSBounds.MertensModerateBudget

private theorem half_power_eq {x : ℝ} (hx : 0 < x) :
    x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
  rw [neg_div, Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, one_div]

private theorem three_half_power_eq {x : ℝ} (hx : 0 < x) :
    x ^ (-3 / 2 : ℝ) = 1 / (x * Real.sqrt x) := by
  rw [show (-3 / 2 : ℝ) = -1 + (-1 / 2) by norm_num,
    Real.rpow_add hx, Real.rpow_neg_one, half_power_eq hx]
  simp only [one_div, mul_inv_rev]
  ring

/-- Rewriting the actual moderate psi error as a relative error. -/
theorem error_mul_eq {x : ℝ} (hx : 0 < x) :
    (0.0023 + 6 / Real.sqrt x) * x = 0.0023 * x + 6 * Real.sqrt x := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsq := Real.sq_sqrt hx.le
  field_simp [hs]
  nlinarith

/-- A strict scalar margin over the entire real interval up to exp(23). -/
theorem budget_lt {x : ℝ} (hx : 100000 ≤ x) (hlog : Real.log x ≤ 23) :
    (0.0023 + 6 / Real.sqrt x) +
      (0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x) < 1 / (2 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hs : (316 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hhalf : x ^ (-1 / 2 : ℝ) ≤ (1 : ℝ) / 316 := by
    rw [half_power_eq hx0]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hthree : x ^ (-3 / 2 : ℝ) ≤ (1 : ℝ) / (100000 * 316) := by
    rw [three_half_power_eq hx0]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact mul_le_mul hx hs (by norm_num) hx0.le
  have he : (6 : ℝ) / Real.sqrt x ≤ 6 / 316 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hl : Real.log (2 * Real.pi) ≤ 6 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith [Real.pi_lt_d4]
  have hi : Real.log (2 * Real.pi) / x ≤ (6 : ℝ) / 100000 := by
    calc
      _ ≤ 6 / x := div_le_div_of_nonneg_right hl hx0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hrat : (0.0023 : ℝ) + 6 / 316 +
      (0.0463 / 316 + 2.4e-6 + 6000 / (100000 * 316) + 6 / 100000) < 1 / 46 := by
    norm_num
  have hbudget : (0.0023 + 6 / Real.sqrt x) +
      (0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x) < 1 / 46 := by
    nlinarith only [hhalf, hthree, he, hi, hrat]
  have hL : 0 < Real.log x := Real.log_pos hx1
  have hlast : (1 : ℝ) / 46 ≤ 1 / (2 * Real.log x) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  exact hbudget.trans_le hlast

/-- The b23 relative error fits the Mertens budget through log x=2400. -/
theorem b23_budget_lt {x : ℝ} (hx : 1000000000 ≤ x) (hlog : Real.log x ≤ 2400) :
    0.00020211 +
      (0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x) < 1 / (2 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hs : (30000 : ℝ) ≤ Real.sqrt x :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hx])
  have hhalf : x ^ (-1 / 2 : ℝ) ≤ (1 : ℝ) / 30000 := by
    rw [half_power_eq hx0]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hthree : x ^ (-3 / 2 : ℝ) ≤ (1 : ℝ) / (1000000000 * 30000) := by
    rw [three_half_power_eq hx0]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    exact mul_le_mul hx hs (by norm_num) hx0.le
  have hl : Real.log (2 * Real.pi) ≤ 6 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith [Real.pi_lt_d4]
  have hi : Real.log (2 * Real.pi) / x ≤ (6 : ℝ) / 1000000000 := by
    calc
      _ ≤ 6 / x := div_le_div_of_nonneg_right hl hx0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hrat : (0.00020211 : ℝ) +
      (0.0463 / 30000 + 2.4e-6 + 6000 / (1000000000 * 30000) + 6 / 1000000000) <
        1 / 4800 := by norm_num
  have hb : 0.00020211 +
      (0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
        Real.log (2 * Real.pi) / x) < 1 / 4800 := by
    nlinarith only [hhalf, hthree, hi, hrat]
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hlast : (1 : ℝ) / 4800 ≤ 1 / (2 * Real.log x) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith
  exact hb.trans_le hlast

end TernaryGoldbach.RSBounds.MertensModerateBudget
