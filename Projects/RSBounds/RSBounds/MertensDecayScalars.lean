import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Elementary variable-cutoff budget for the signed Mertens integral.
This module has no zeta, prime-counting, or finite-RH premise. -/

namespace TernaryGoldbach.RSBounds.MertensDecayScalars

noncomputable def squareExpr (T : ℝ) : ℝ :=
  (Real.log (T / (2 * Real.pi)) + 1) / (2 * Real.pi * T) +
    (0.137 + 0.443 / Real.log T) / (2 * T ^ 2) +
    2 * (0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588) / T ^ 2

noncomputable def scalarEnvelope (X : ℝ) : ℝ :=
  0.0463 * Real.exp (-5 * X ^ 2) + 0.0463 * Real.exp (-X) +
    2 * squareExpr (17 * Real.exp X) + 6000 * Real.exp (-15 * X ^ 2) +
    Real.log (2 * Real.pi) / Real.exp (10 * X ^ 2)

theorem exp_fifteen_lower : (3200000 : ℝ) ≤ Real.exp 15 := by
  have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718)
    (show (2.718 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 15
  rw [← Real.exp_nat_mul] at h
  norm_num only [Nat.cast_ofNat, mul_one] at h
  linarith

theorem log_seventeen_bounds : 0 ≤ Real.log 17 ∧ Real.log 17 ≤ 3 := by
  constructor
  · exact Real.log_nonneg (by norm_num)
  · apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 17)).mpr
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7)
      (show (2.7 : ℝ) ≤ Real.exp 1 by linarith [Real.exp_one_gt_d9]) 3
    rw [← Real.exp_nat_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h
    linarith

theorem cutoff_height {X : ℝ} (hX : 15 ≤ X) : 1894439 ≤ 17 * Real.exp X := by
  have h := exp_fifteen_lower.trans (Real.exp_le_exp.mpr hX)
  linarith

theorem twice_squareExpr_le {X : ℝ} (hX : 15 ≤ X) :
    2 * squareExpr (17 * Real.exp X) ≤
      ((X + 4) / 51 + 0.01) * Real.exp (-X) := by
  have hX0 : 0 ≤ X := by linarith
  have hE := Real.exp_pos X
  have hT : 0 < 17 * Real.exp X := by positivity
  have hlog : Real.log (17 * Real.exp X) = Real.log 17 + X := by
    rw [Real.log_mul (by norm_num) hE.ne', Real.log_exp]
  have hl1 : 1 ≤ Real.log (17 * Real.exp X) := by
    rw [hlog]
    linarith [log_seventeen_bounds.1]
  have hl0 : 0 < Real.log (17 * Real.exp X) := by linarith
  have hlu : Real.log (17 * Real.exp X) ≤ X + 3 := by
    rw [hlog]
    linarith [log_seventeen_bounds.2]
  have hquot : Real.log ((17 * Real.exp X) / (2 * Real.pi)) ≤ X + 3 := by
    apply (Real.log_le_log (by positivity) ?_).trans hlu
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).mpr
    have hh := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hT.le
    nlinarith only [hh, hT]
  have hcoef : (0.137 : ℝ) + 0.443 / Real.log (17 * Real.exp X) ≤ 0.58 := by
    have hd : (0.443 : ℝ) / Real.log (17 * Real.exp X) ≤ 0.443 := by
      apply (div_le_iff₀ hl0).mpr
      nlinarith
    linarith
  have hll : Real.log (Real.log (17 * Real.exp X)) ≤ Real.log (17 * Real.exp X) := by
    have hh := Real.log_le_sub_one_of_pos hl0
    linarith
  have hr : 0.137 * Real.log (17 * Real.exp X) +
      0.443 * Real.log (Real.log (17 * Real.exp X)) + 1.588 ≤ 0.58 * X + 3.328 := by
    linarith
  have h1 : (Real.log ((17 * Real.exp X) / (2 * Real.pi)) + 1) /
      (2 * Real.pi * (17 * Real.exp X)) ≤ (X + 4) / (102 * Real.exp X) := by
    calc
      _ ≤ (X + 4) / (2 * Real.pi * (17 * Real.exp X)) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      _ ≤ _ := by
        apply div_le_div_of_nonneg_left (by linarith) (by positivity)
        have hh := mul_le_mul_of_nonneg_right Real.pi_gt_three.le hE.le
        nlinarith only [hh]
  have h2 := div_le_div_of_nonneg_right hcoef
    (by positivity : (0 : ℝ) ≤ 2 * (17 * Real.exp X) ^ 2)
  have h3 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr
    (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg (17 * Real.exp X))
  have htail : (2.32 * X + 13.892) / (289 * (Real.exp X) ^ 2) ≤
      0.01 / Real.exp X := by
    have ht := Real.pow_div_factorial_le_exp X hX0 2
    norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at ht
    have hn : 2.32 * X + 13.892 ≤ 2.89 * Real.exp X := by
      nlinarith [sq_nonneg (X - 15)]
    apply (div_le_div_iff₀ (by positivity) hE).mpr
    nlinarith [mul_le_mul_of_nonneg_right hn hE.le]
  have heq : 2 * ((X + 4) / (102 * Real.exp X) +
      0.58 / (2 * (17 * Real.exp X) ^ 2) +
      2 * (0.58 * X + 3.328) / (17 * Real.exp X) ^ 2) =
      (X + 4) / (51 * Real.exp X) +
        (2.32 * X + 13.892) / (289 * (Real.exp X) ^ 2) := by ring
  have hh : 2 * squareExpr (17 * Real.exp X) ≤
      (X + 4) / (51 * Real.exp X) + 0.01 / Real.exp X := by
    unfold squareExpr
    linarith only [h1, h2, h3, heq, htail]
  calc
    _ ≤ (X + 4) / (51 * Real.exp X) + 0.01 / Real.exp X := hh
    _ = _ := by rw [Real.exp_neg]; ring

theorem scalarEnvelope_le {X : ℝ} (hX : 15 ≤ X) :
    scalarEnvelope X ≤ (X / 25) * Real.exp (-X) := by
  have hX0 : 0 ≤ X := by linarith
  have he := Real.exp_pos (-X)
  have hlo : Real.exp (-5 * X ^ 2) ≤ Real.exp (-X) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (X - 15)])
  have hleft : 6000 * Real.exp (-15 * X ^ 2) ≤ 0.01 * Real.exp (-X) := by
    have hex : (600000 : ℝ) ≤ Real.exp (15 * X ^ 2 - X) :=
      (by norm_num : (600000 : ℝ) ≤ 3200000).trans
        (exp_fifteen_lower.trans (Real.exp_le_exp.mpr
          (by nlinarith [sq_nonneg (X - 15)])))
    have hh := mul_le_mul_of_nonneg_right hex (Real.exp_pos (-15 * X ^ 2)).le
    rw [← Real.exp_add] at hh
    have heq : 15 * X ^ 2 - X + (-15 * X ^ 2) = -X := by ring
    rw [heq] at hh
    linarith
  have hlog : Real.log (2 * Real.pi) ≤ 6 := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 2 * Real.pi by positivity)
    linarith [Real.pi_lt_d4]
  have hlast : Real.log (2 * Real.pi) / Real.exp (10 * X ^ 2) ≤
      0.01 * Real.exp (-X) := by
    have hex : (600 : ℝ) ≤ Real.exp (10 * X ^ 2 - X) :=
      (by norm_num : (600 : ℝ) ≤ 3200000).trans
        (exp_fifteen_lower.trans (Real.exp_le_exp.mpr
          (by nlinarith [sq_nonneg (X - 15)])))
    have hh := mul_le_mul_of_nonneg_right hex (Real.exp_pos (-10 * X ^ 2)).le
    rw [← Real.exp_add] at hh
    have heq : 10 * X ^ 2 - X + (-10 * X ^ 2) = -X := by ring
    rw [heq] at hh
    have hl := mul_le_mul_of_nonneg_right hlog (Real.exp_pos (-10 * X ^ 2)).le
    rw [show -10 * X ^ 2 = -(10 * X ^ 2) by ring,
      Real.exp_neg, ← div_eq_mul_inv] at hl
    have hh' : 6 / Real.exp (10 * X ^ 2) ≤ 0.01 * Real.exp (-X) := by
      rw [show -10 * X ^ 2 = -(10 * X ^ 2) by ring,
        Real.exp_neg, ← div_eq_mul_inv] at hh
      simp only [div_eq_mul_inv] at hh ⊢
      linarith
    exact hl.trans hh'
  have hs := twice_squareExpr_le hX
  have hp : 0.0463 + 0.0463 + ((X + 4) / 51 + 0.01) + 0.01 + 0.01 ≤ X / 25 := by
    linarith
  have hm := mul_le_mul_of_nonneg_right hp he.le
  unfold scalarEnvelope
  nlinarith only [hlo, hleft, hlast, hs, hm]

theorem fifth_power_exp_le {X : ℝ} (hX : 15 ≤ X) :
    X ^ 5 * Real.exp (-X) ≤ 15 ^ 5 * Real.exp (-15) := by
  have hX0 : 0 < X := by linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < X / (15 : ℝ))
  rw [Real.log_div hX0.ne' (by norm_num)] at hl
  have ha : 5 * Real.log X - X ≤ 5 * Real.log 15 - 15 := by linarith
  have hh := Real.exp_le_exp.mpr ha
  have hxe : Real.exp (5 * Real.log X) = X ^ 5 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hX0] using Real.exp_nat_mul (Real.log X) 5
  have h15e : Real.exp (5 * Real.log 15) = (15 : ℝ) ^ 5 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 15)] using
      Real.exp_nat_mul (Real.log 15) 5
  simpa only [Real.exp_sub, hxe, h15e, Real.exp_neg, div_eq_mul_inv] using hh

theorem scalarEnvelope_lt {X : ℝ} (hX : 15 ≤ X) :
    scalarEnvelope X < 1 / (10 * X ^ 2) ^ 2 := by
  have hX0 : 0 < X := by linarith
  have hb := scalarEnvelope_le hX
  have hp := mul_le_mul_of_nonneg_left (fifth_power_exp_le hX)
    (by norm_num : (0 : ℝ) ≤ 4)
  have he : 4 * (15 : ℝ) ^ 5 * Real.exp (-15) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv]
    apply (div_lt_iff₀ (Real.exp_pos _)).mpr
    linarith [exp_fifteen_lower]
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < (10 * X ^ 2) ^ 2)).mpr
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg (10 * X ^ 2))
  have hid : (X / 25 * Real.exp (-X)) * (10 * X ^ 2) ^ 2 =
      4 * (X ^ 5 * Real.exp (-X)) := by ring
  rw [hid] at hm
  exact hm.trans_lt (hp.trans_lt (by simpa only [mul_assoc] using he))

end TernaryGoldbach.RSBounds.MertensDecayScalars
