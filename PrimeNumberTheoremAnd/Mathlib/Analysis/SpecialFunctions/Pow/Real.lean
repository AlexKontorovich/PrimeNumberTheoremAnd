/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Real-power estimates

Elementary logarithmic and real-power inequalities used in decay and growth estimates.
-/
@[expose] public section

namespace Real

/-- For `1 < u` and `ε > 0`, `log u * u^(-1-ε) ≤ (2/ε) * u^(-1-ε/2)`. -/
theorem log_mul_rpow_neg_le_two_div_mul_rpow_neg {ε : ℝ} (hε : 0 < ε) {u : ℝ} (hu : 1 < u) :
    Real.log u * u ^ (-1 - ε) ≤ (2 / ε) * u ^ (-1 - ε / 2) := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hpos_coeff : 0 < 2 / ε := by
    simpa [one_div, div_eq_mul_inv] using mul_pos (by norm_num : (0 : ℝ) < 2) (inv_pos.mpr hε)
  have hle_exp : (ε / 2) * Real.log u ≤ Real.exp ((ε / 2) * Real.log u) :=
    le_trans (by linarith) (Real.add_one_le_exp ((ε / 2) * Real.log u))
  have hlog_bound : Real.log u ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) := by
    calc
      Real.log u = (2 / ε) * ((ε / 2) * Real.log u) := by field_simp [hεne]
      _ ≤ (2 / ε) * Real.exp ((ε / 2) * Real.log u) :=
        mul_le_mul_of_nonneg_left hle_exp (le_of_lt hpos_coeff)
  have hexp_rpow : Real.exp ((ε / 2) * Real.log u) = u ^ (ε / 2) := by
    simp [Real.rpow_def_of_pos hu0, mul_comm]
  have hmul : Real.log u * u ^ (-1 - ε) ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) :=
    mul_le_mul_of_nonneg_right (by simpa [hexp_rpow] using hlog_bound)
      (le_of_lt (Real.rpow_pos_of_pos hu0 _))
  have hpow_mul : u ^ (ε / 2) * u ^ (-1 - ε) = u ^ (-1 - ε / 2) := by
    rw [← Real.rpow_add hu0, show ε / 2 + (-1 - ε) = -1 - ε / 2 by ring]
  calc
    Real.log u * u ^ (-1 - ε)
        ≤ ((2 / ε) * u ^ (ε / 2)) * u ^ (-1 - ε) := hmul
    _ = (2 / ε) * u ^ (-1 - ε / 2) := by rw [mul_assoc, hpow_mul]

end Real

namespace Complex

/-- For `0 ≤ p`, one has `1 ≤ (1 + ‖z‖)^p`. -/
theorem one_le_one_add_norm_rpow (z : ℂ) {p : ℝ} (hp : 0 ≤ p) : (1 : ℝ) ≤ (1 + ‖z‖) ^ p :=
  Real.one_le_rpow (by linarith [norm_nonneg z]) hp

end Complex
