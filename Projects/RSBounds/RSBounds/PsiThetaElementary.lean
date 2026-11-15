import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic

/-!
# An elementary psi-to-theta transfer above 100000

This module uses only Mathlib's three-prime-power decomposition and its
elementary Chebyshev bound. No finite RH certificate or analytic number
theory result from the surrounding project is imported.
-/

namespace TernaryGoldbach.RSBounds.PsiThetaElementary

open Real

theorem log_four_add_four_lt : Real.log 4 + 4 < (5.4 : ℝ) := by
  have hlog : Real.log 4 = 2 * Real.log 2 := by
    have h := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)
    norm_num at h
    linarith
  rw [hlog]
  linarith [Real.log_two_lt_d9]

theorem cube_root_le {x : ℝ} (hx : 100000 ≤ x) :
    x ^ ((3 : ℝ)⁻¹) ≤ 0.15 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have h6 : (20 / 3 : ℝ) ≤ x ^ ((6 : ℝ)⁻¹) := by
    apply (Real.le_rpow_inv_iff_of_pos (by norm_num : (0 : ℝ) ≤ 20 / 3) hx0.le
      (by norm_num : (0 : ℝ) < 6)).2
    calc
      (20 / 3 : ℝ) ^ (6 : ℝ) ≤ 100000 := by norm_num [Real.rpow_natCast]
      _ ≤ x := hx
  have h := mul_le_mul_of_nonneg_right h6
    (Real.rpow_nonneg hx0.le ((3 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (6 : ℝ)⁻¹ + (3 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow] at h
  nlinarith

theorem fifth_root_le {x : ℝ} (hx : 100000 ≤ x) :
    x ^ ((5 : ℝ)⁻¹) ≤ 0.04 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hbase : (25 : ℝ) ^ (10 : ℕ) ≤ x ^ (3 : ℕ) := by
    calc
      (25 : ℝ) ^ (10 : ℕ) ≤ (100000 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ x ^ (3 : ℕ) := by gcongr
  have h10 : (25 : ℝ) ≤ x ^ (3 / 10 : ℝ) := by
    apply (Real.rpow_le_rpow_iff (by norm_num)
      (Real.rpow_nonneg hx0.le (3 / 10 : ℝ))
      (by norm_num : (0 : ℝ) < 10)).mp
    rw [← Real.rpow_mul hx0.le]
    rw [show (3 / 10 : ℝ) * 10 = 3 by norm_num]
    simpa only [Real.rpow_ofNat] using hbase
  have h := mul_le_mul_of_nonneg_right h10
    (Real.rpow_nonneg hx0.le ((5 : ℝ)⁻¹))
  rw [← Real.rpow_add hx0] at h
  rw [show (3 / 10 : ℝ) + (5 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num,
    ← Real.sqrt_eq_rpow] at h
  nlinarith

/-- A coarse unconditional transfer sufficient for the moderate RS62 range. -/
theorem psi_sub_theta_le {x : ℝ} (hx : 100000 ≤ x) :
    Chebyshev.psi x - Chebyshev.theta x ≤ 6.5 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have h2 := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx0 ((2 : ℝ)⁻¹))
  have h3 := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx0 ((3 : ℝ)⁻¹))
  have h5 := Chebyshev.psi_le_const_mul_self
    (Real.rpow_nonneg hx0 ((5 : ℝ)⁻¹))
  have h2' : Chebyshev.psi (x ^ ((2 : ℝ)⁻¹)) ≤ 5.4 * Real.sqrt x := by
    calc
      _ ≤ (Real.log 4 + 4) * x ^ ((2 : ℝ)⁻¹) := h2
      _ ≤ 5.4 * x ^ ((2 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right log_four_add_four_lt.le (by positivity)
      _ = 5.4 * Real.sqrt x := by rw [Real.sqrt_eq_rpow]; norm_num
  have h3' : Chebyshev.psi (x ^ ((3 : ℝ)⁻¹)) ≤ 5.4 * (0.15 * Real.sqrt x) := by
    calc
      _ ≤ (Real.log 4 + 4) * x ^ ((3 : ℝ)⁻¹) := h3
      _ ≤ 5.4 * x ^ ((3 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right log_four_add_four_lt.le (by positivity)
      _ ≤ 5.4 * (0.15 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (cube_root_le hx) (by norm_num)
  have h5' : Chebyshev.psi (x ^ ((5 : ℝ)⁻¹)) ≤ 5.4 * (0.04 * Real.sqrt x) := by
    calc
      _ ≤ (Real.log 4 + 4) * x ^ ((5 : ℝ)⁻¹) := h5
      _ ≤ 5.4 * x ^ ((5 : ℝ)⁻¹) :=
        mul_le_mul_of_nonneg_right log_four_add_four_lt.le (by positivity)
      _ ≤ 5.4 * (0.04 * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left (fifth_root_le hx) (by norm_num)
  have h := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  nlinarith [Real.sqrt_nonneg x]

theorem log_hundred_thousand_bounds :
    2 ≤ Real.log (100000 : ℝ) ∧ Real.log (100000 : ℝ) ≤ 11.52 := by
  have h10 : Real.log (10 : ℝ) = Real.log 2 + Real.log 5 := by
    have h := Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (by norm_num : (5 : ℝ) ≠ 0)
    norm_num at h
    exact h
  have h100000 : Real.log (100000 : ℝ) = 5 * Real.log 10 := by
    have h := Real.log_pow (10 : ℝ) 5
    norm_num at h
    exact h
  rw [h100000, h10]
  constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9,
    Real.log_five_gt_d9, Real.log_five_lt_d9]

theorem sqrt_exp_eq (L : ℝ) : Real.sqrt (Real.exp L) = Real.exp (L / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.exp_mul]
  congr 1
  ring

theorem exp_six_ge : (400 : ℝ) ≤ Real.exp 6 := by
  calc
    (400 : ℝ) ≤ (2.718 : ℝ) ^ (6 : ℕ) := by norm_num
    _ ≤ (Real.exp 1) ^ (6 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 6
    _ = Real.exp 6 := by simpa using (Real.exp_nat_mul 1 6).symm

theorem exp_ten_ge : (20000 : ℝ) ≤ Real.exp 10 := by
  calc
    (20000 : ℝ) ≤ (2.7 : ℝ) ^ (10 : ℕ) := by norm_num
    _ ≤ (Real.exp 1) ^ (10 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 10
    _ = Real.exp 10 := by simpa using (Real.exp_nat_mul 1 10).symm

theorem log_div_sqrt_le_at_exp {x L B : ℝ} (hx : 0 < x) (hL : 2 ≤ L)
    (hB : 0 < B) (hBL : B ≤ Real.exp (L / 2)) (hLx : L ≤ Real.log x) :
    Real.log x / Real.sqrt x ≤ L / B := by
  have hex : Real.exp L ≤ x := (Real.le_log_iff_exp_le hx).mp hLx
  have he2 : Real.exp 2 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have h := Real.log_div_sqrt_antitoneOn he2 (he2.trans hex) hex
  change Real.log x / Real.sqrt x ≤ Real.log (Real.exp L) / Real.sqrt (Real.exp L) at h
  rw [Real.log_exp, sqrt_exp_eq] at h
  exact h.trans (div_le_div_of_nonneg_left (by linarith) hB hBL)

theorem log_div_sqrt_le_at_hundred_thousand {x : ℝ} (hx : 100000 ≤ x) :
    Real.log x / Real.sqrt x ≤ 11.52 / 316 := by
  have hbase : Real.exp 2 ≤ (100000 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).mp log_hundred_thousand_bounds.1
  have h := Real.log_div_sqrt_antitoneOn hbase (hbase.trans hx) hx
  have hs : (316 : ℝ) ≤ Real.sqrt (100000 : ℝ) := by
    have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 100000)
    nlinarith [Real.sqrt_nonneg (100000 : ℝ)]
  calc
    Real.log x / Real.sqrt x ≤ Real.log (100000 : ℝ) / Real.sqrt (100000 : ℝ) := h
    _ ≤ 11.52 / Real.sqrt (100000 : ℝ) :=
      div_le_div_of_nonneg_right log_hundred_thousand_bounds.2 (by positivity)
    _ ≤ 11.52 / 316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs

/-- Numerical budget for the moderate psi bound and the elementary transfer. -/
theorem moderate_theta_budget {x : ℝ} (hx : 100000 ≤ x) (hL : Real.log x ≤ 23) :
    0.0023 + 12.5 / Real.sqrt x ≤ 1 / (2 * Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hprod : (0.0023 + 12.5 / Real.sqrt x) * Real.log x ≤ 0.5 := by
    by_cases h12 : Real.log x ≤ 12
    · calc
        _ = 0.0023 * Real.log x + 12.5 * (Real.log x / Real.sqrt x) := by ring
        _ ≤ 0.0023 * 12 + 12.5 * (11.52 / 316) := by
          exact add_le_add (mul_le_mul_of_nonneg_left h12 (by norm_num))
            (mul_le_mul_of_nonneg_left (log_div_sqrt_le_at_hundred_thousand hx) (by norm_num))
        _ ≤ 0.5 := by norm_num
    · have hr := log_div_sqrt_le_at_exp hx0 (by norm_num : (2 : ℝ) ≤ 12)
        (by norm_num : (0 : ℝ) < 400)
        (by simpa only [show (12 : ℝ) / 2 = 6 by norm_num] using exp_six_ge) (le_of_not_ge h12)
      calc
        _ = 0.0023 * Real.log x + 12.5 * (Real.log x / Real.sqrt x) := by ring
        _ ≤ 0.0023 * 23 + 12.5 * (12 / 400) := by
          exact add_le_add (mul_le_mul_of_nonneg_left hL (by norm_num))
            (mul_le_mul_of_nonneg_left hr (by norm_num))
        _ ≤ 0.5 := by norm_num
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hL0)).mpr
  nlinarith only [hprod]

/-- Numerical budget from b=23 up to the auxiliary weak-tail threshold. -/
theorem b23_theta_budget {x : ℝ} (hx : Real.exp 23 ≤ x)
    (hL1 : Real.log x ≤ 2400) :
    0.00020211 + 6.5 / Real.sqrt x ≤ 1 / (2 * Real.log x) := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hL0 : 23 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 23) hx
    simpa using h
  have hLp : 0 < Real.log x := by linarith
  have hr := log_div_sqrt_le_at_exp hx0 (by norm_num : (2 : ℝ) ≤ 20)
    (by norm_num : (0 : ℝ) < 20000)
    (by simpa only [show (20 : ℝ) / 2 = 10 by norm_num] using exp_ten_ge) (by linarith : 20 ≤ Real.log x)
  have hprod : (0.00020211 + 6.5 / Real.sqrt x) * Real.log x ≤ 0.5 := by
    calc
      _ = 0.00020211 * Real.log x + 6.5 * (Real.log x / Real.sqrt x) := by ring
      _ ≤ 0.00020211 * 2400 + 6.5 * (20 / 20000) := by
        exact add_le_add (mul_le_mul_of_nonneg_left hL1 (by norm_num))
          (mul_le_mul_of_nonneg_left hr (by norm_num))
      _ ≤ 0.5 := by norm_num
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hLp)).mpr
  nlinarith only [hprod]

/-- Numerical budget for any psi error at most 0.1*x/log x on this range. -/
theorem large_theta_budget_of_log {x : ℝ} (hx0 : 0 < x) (hL : 20 ≤ Real.log x) :
    0.1 / Real.log x + 6.5 / Real.sqrt x ≤ 1 / (2 * Real.log x) := by
  have hLp : 0 < Real.log x := by linarith
  have hr := log_div_sqrt_le_at_exp hx0 (by norm_num : (2 : ℝ) ≤ 20)
    (by norm_num : (0 : ℝ) < 20000) (by simpa only [show (20 : ℝ) / 2 = 10 by norm_num] using exp_ten_ge) hL
  have hprod : (0.1 / Real.log x + 6.5 / Real.sqrt x) * Real.log x ≤ 0.5 := by
    calc
      _ = 0.1 + 6.5 * (Real.log x / Real.sqrt x) := by
        rw [add_mul, div_mul_cancel₀ _ hLp.ne']
        ring
      _ ≤ 0.1 + 6.5 * (20 / 20000) := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by norm_num))
      _ ≤ 0.5 := by norm_num
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hLp)).mpr
  nlinarith only [hprod]

theorem large_theta_budget {x : ℝ} (hx : Real.exp 2400 ≤ x) :
    0.1 / Real.log x + 6.5 / Real.sqrt x ≤ 1 / (2 * Real.log x) := by
  apply large_theta_budget_of_log ((Real.exp_pos 2400).trans_le hx)
  have h := Real.log_le_log (Real.exp_pos 2400) hx
  rw [Real.log_exp] at h
  linarith

end TernaryGoldbach.RSBounds.PsiThetaElementary
