import RSBounds.RS75ZeroFreeNumerics

/-!
# The scalar assembly for the RS75 zero-free constant

The zeta estimates are separate analytic obligations. This module proves the
actual radical/logarithm constants, chosen parameter range, and the residual
inequality needed when the near-pole slope is .2, the shifted real-axis bound
is -1.1398+3.3606*x, and the frequency remainder is 15/t^2.
-/
namespace TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
noncomputable section

/-- Existing proved Euler-constant enclosure, reused without a new computation. -/
theorem gamma_lower : (0.5772156646 : ℝ) ≤ Real.eulerMascheroniConstant :=
  SmallTotientProduct.gamma_bounds.1

theorem H_nonneg : 0 ≤ H := by
  norm_num [H, RS75Polynomial.coeff, Finset.sum_Icc_succ_top]

theorem H_upper : H < 22.584 := by
  norm_num [H, RS75Polynomial.coeff, Finset.sum_Icc_succ_top]

theorem a0_pos : 0 < a0 := by norm_num [a0]
theorem A0_pos : 0 < A0 := by norm_num [A0]
theorem v_pos : 0 < v := by linarith [v_lower]

theorem chosen_x_bounds {t : ℝ} (ht : 1894439 ≤ t) :
    0 < v / Real.log (t / 17) ∧ v / Real.log (t / 17) < 0.029172 := by
  have htdiv : (1894439 : ℝ) / 17 ≤ t / 17 := by linarith
  have hlA : 0 < Real.log ((1894439 : ℝ) / 17) := Real.log_pos (by norm_num)
  have hl : Real.log ((1894439 : ℝ) / 17) ≤ Real.log (t / 17) :=
    Real.log_le_log (by norm_num) htdiv
  constructor
  · exact div_pos v_pos (hlA.trans_le hl)
  · have hh : v / Real.log (t / 17) ≤ heightRatio := by
      exact div_le_div_of_nonneg_left v_pos.le hlA hl
    exact hh.trans_lt (by convert heightRatio_upper using 1 <;> norm_num)

theorem frequency_tail_lt {t : ℝ} (ht : 1894439 ≤ t) :
    15 * H / t ^ 2 < 0.0000000001 := by
  have ht0 : 0 ≤ t := by linarith
  have hs : (1894439 : ℝ) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ (by norm_num) ht 2
  calc
    15 * H / t ^ 2 ≤ 15 * 22.584 / t ^ 2 :=
      div_le_div_of_nonneg_right (by linarith [H_upper]) (sq_nonneg t)
    _ ≤ 15 * 22.584 / (1894439 : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    _ < 0.0000000001 := by norm_num

/-- Polynomial obtained after using the proved cubic kappa lower bound. -/
def residual (x : ℝ) : ℝ :=
  -a0 * 0.5772156646 - 52.38865 / 2 + h * Real.log 17 + 0.2 * a0 * x +
  k0 * (RS75Parameters.cubic x * (a0 * (-1.1398 + 3.3606 * x) + 52.38865 / 2) -
    A0 / 2 * (4 / 5 - 26 / 25 * x + 6 / 5 * x ^ 2) * (v + x * Real.log 17))

theorem residual_eq (x : ℝ) :
    residual x = c0 + c1 * x + c2 * x ^ 2 + c3 * x ^ 3 + c4 * x ^ 4 := by
  unfold residual c0 c1 c2 c3 c4 RS75Parameters.cubic
  ring

theorem residual_add_frequency_lt {x t : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 0.029172)
    (ht : 1894439 ≤ t) : residual x + 15 * H / t ^ 2 < -0.0009 := by
  have hc0 := c0_upper.le
  have hc1 := mul_le_mul_of_nonneg_right c1_upper.le hx
  have hc2 := mul_le_mul_of_nonneg_right c2_upper.le (pow_nonneg hx 2)
  have hc3 := mul_le_mul_of_nonneg_right c3_upper.le (pow_nonneg hx 3)
  have hc4 := mul_le_mul_of_nonneg_right c4_upper.le (pow_nonneg hx 4)
  have hx2 := pow_le_pow_left₀ hx hx' 2
  have hx4 := pow_le_pow_left₀ hx hx' 4
  have hfreq := frequency_tail_lt ht
  rw [residual_eq]
  norm_num at hc0 hc1 hc2 hc3 hc4 hx2 hx4
  nlinarith

private def logHeight (x : ℝ) : ℝ := v / x + Real.log 17
private def shiftCoefficient (x : ℝ) : ℝ :=
  a0 * (-1.1398 + 3.3606 * x) + 52.38865 / 2 - A0 / 2 * logHeight x
private def basePart (x γ : ℝ) : ℝ :=
  -a0 * γ - 52.38865 / 2 + h * Real.log 17 + k0 * A0 / 2 * logHeight x + 0.2 * a0 * x

/-- Actual kappa/Euler-constant residual before the cubic replacement. -/
def rawResidual (x : ℝ) : ℝ :=
  (k0 - RS75Parameters.kappa (1 + x)) * A0 / 2 * (v / x + Real.log 17) +
    a0 * (RS75Parameters.kappa (1 + x) * (-1.1398 + 3.3606 * x) -
      Real.eulerMascheroniConstant + 0.2 * x) -
    (1 - RS75Parameters.kappa (1 + x)) * 52.38865 / 2 + h * Real.log 17

private theorem rawResidual_eq (x : ℝ) :
    rawResidual x = basePart x Real.eulerMascheroniConstant +
      RS75Parameters.kappa (1 + x) * shiftCoefficient x := by
  unfold rawResidual basePart shiftCoefficient logHeight
  ring

private theorem residual_eq_shift {x : ℝ} (hx : x ≠ 0) :
    residual x = basePart x 0.5772156646 +
      (RS75Parameters.cubic x * k0) * shiftCoefficient x := by
  unfold residual basePart shiftCoefficient logHeight RS75Parameters.cubic
  field_simp [hx]
  <;> ring

private theorem shiftCoefficient_neg {x : ℝ} (hx : 0 < x) (hx' : x ≤ 0.03) :
    shiftCoefficient x < 0 := by
  have hx2 := pow_le_pow_left₀ hx.le hx' 2
  have hl : 0 ≤ x * Real.log 17 :=
    mul_nonneg hx.le (Real.log_pos (by norm_num : (1 : ℝ) < 17)).le
  have he : x * shiftCoefficient x =
      a0 * 3.3606 * x ^ 2 + (52.38865 / 2) * x - A0 / 2 * v -
        a0 * 1.1398 * x - A0 / 2 * (x * Real.log 17) := by
    unfold shiftCoefficient logHeight
    field_simp [hx.ne']
    <;> ring
  have hn : x * shiftCoefficient x < -5.36 := by
    rw [he]
    unfold a0 A0
    norm_num at hx2
    nlinarith [v_lower]
  by_contra hb
  have hp := mul_nonneg hx.le (not_lt.1 hb)
  linarith

/-- The arithmetic substitution has the correct sign for the actual kappa. -/
theorem rawResidual_le {x : ℝ} (hx : 0 < x) (hx' : x ≤ 0.03) :
    rawResidual x ≤ residual x := by
  have hk : RS75Parameters.cubic x * k0 ≤ RS75Parameters.kappa (1 + x) := by
    simpa only [k0, div_eq_mul_inv, one_mul] using RS75Parameters.cubic_kappa_lower hx.le hx'
  have hm := mul_le_mul_of_nonpos_right hk (shiftCoefficient_neg hx hx').le
  have hg : -a0 * Real.eulerMascheroniConstant ≤ -a0 * 0.5772156646 := by
    unfold a0
    nlinarith [gamma_lower]
  rw [rawResidual_eq, residual_eq_shift hx.ne']
  exact add_le_add (by unfold basePart; linarith) hm

theorem rawResidual_add_frequency_lt {x t : ℝ} (hx : 0 < x) (hx' : x ≤ 0.029172)
    (ht : 1894439 ≤ t) : rawResidual x + 15 * H / t ^ 2 < -0.0009 := by
  have hr := rawResidual_le hx (by linarith : x ≤ 0.03)
  have hp := residual_add_frequency_lt hx.le hx' ht
  linarith

/-- Final scalar residual at the actual height-dependent choice of sigma. -/
theorem chosen_residual_lt {t : ℝ} (ht : 1894439 ≤ t) :
    rawResidual (v / Real.log (t / 17)) + 15 * H / t ^ 2 < -0.0009 :=
  rawResidual_add_frequency_lt (chosen_x_bounds ht).1 (chosen_x_bounds ht).2.le ht

end
end TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
