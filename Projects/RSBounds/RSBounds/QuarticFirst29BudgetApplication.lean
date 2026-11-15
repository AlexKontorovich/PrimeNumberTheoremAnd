import RSBounds.QuarticFirst29BudgetNumerics
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The certified first-29 scalar budget for every x at least exp23

This module extends the closed scalar calculation using positive coefficients
and denominator monotonicity. It still asserts no inequality for psi or for
an actual zeta zero sum.
-/

namespace TernaryGoldbach.RSBounds.QuarticFirst29BudgetApplication
open QuarticFirst29BudgetNumerics BacklundLowScalar

private def log98715Certificate : LogCert := ⟨16, 65536, 33179⟩

private theorem log98715Certificate_valid : log98715Certificate.Valid := by
  decide +kernel

private theorem log98715Certificate_upper :
    log98715Certificate.upper < (23 / 2 : ℚ) := by
  decide +kernel

theorem log_98715_lt : Real.log (98715 : ℝ) < 23 / 2 := by
  have hb := (LogCert.log_bounds log98715Certificate_valid).2
  have he : (log98715Certificate.ratio : ℝ) = 98715 := by
    norm_num [log98715Certificate, LogCert.ratio]
  rw [he] at hb
  have hu : (log98715Certificate.upper : ℝ) < 23 / 2 := by
    have hh := (Rat.cast_lt (K := ℝ)).mpr log98715Certificate_upper
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at hh
    exact hh
  exact hb.trans_lt hu

theorem square_lower_lt_exp23 : (98715 : ℝ) ^ 2 < Real.exp 23 := by
  apply (Real.log_lt_iff_lt_exp (by positivity : (0 : ℝ) < 98715 ^ 2)).mp
  rw [Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith [log_98715_lt]

theorem x_lower {x : ℝ} (hx : Real.exp 23 ≤ x) : (98715 : ℝ) ^ 2 ≤ x :=
  square_lower_lt_exp23.le.trans hx

theorem sqrt_lower {x : ℝ} (hx : Real.exp 23 ≤ x) : 98715 ≤ Real.sqrt x := by
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  exact (Real.le_sqrt (by norm_num) hx0.le).mpr (x_lower hx)

private theorem C_pos : (0 : ℝ) < (C : ℝ) := by
  have hd : (0 : ℚ) < delta := by norm_num [delta]
  have hc : (0 : ℚ) < C := by unfold C; positivity
  exact_mod_cast hc

private theorem fifthTail_A_nonneg : 0 ≤ fifthTail (A : ℝ) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by norm_num [A]
  have hr : (1 : ℝ) ≤ (A : ℝ) / (2 * Real.pi) := by
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hp := Real.pi_le_four
    norm_num [A]
    linarith
  have hlr : 0 ≤ Real.log ((A : ℝ) / (2 * Real.pi)) := Real.log_nonneg hr
  have hlA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg hA1
  unfold fifthTail
  positivity

private theorem R_A_nonneg : 0 ≤ R (A : ℝ) := by
  have hA0 : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  have hlA : 1 ≤ Real.log (A : ℝ) := by
    apply (Real.le_log_iff_exp_le hA0).mpr
    exact Real.exp_one_lt_three.le.trans (by norm_num [A])
  have hlA0 : 0 ≤ Real.log (A : ℝ) := by linarith
  have hllA : 0 ≤ Real.log (Real.log (A : ℝ)) := Real.log_nonneg hlA
  unfold R
  positivity

theorem highWeight_nonneg : 0 ≤ highWeight := by
  have hC := C_pos.le
  have hJ := fifthTail_A_nonneg
  have hR := R_A_nonneg
  have hA : (0 : ℝ) < (A : ℝ) := by norm_num [A]
  unfold highWeight
  positivity

theorem constant_term_pos : 0 < highWeight + Real.log (2 * Real.pi) + 0.1 := by
  have hlog : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by linarith [Real.pi_gt_three])
  linarith [highWeight_nonneg]

/-- The explicit scalar envelope, not an asserted bound for psi. -/
noncomputable def relativeBudget (x : ℝ) : ℝ :=
  2 * (delta : ℝ) + highWeight + sqrtCoefficient / Real.sqrt x +
    (highWeight + Real.log (2 * Real.pi) + 0.1) / x

theorem relativeBudget_le_scalarBudget {x : ℝ} (hx : Real.exp 23 ≤ x) :
    relativeBudget x ≤ scalarBudget := by
  have hq : sqrtCoefficient / Real.sqrt x ≤ sqrtCoefficient / 98715 :=
    div_le_div_of_nonneg_left sqrtCoefficient_pos.le (by norm_num) (sqrt_lower hx)
  have hk : (highWeight + Real.log (2 * Real.pi) + 0.1) / x ≤
      (highWeight + Real.log (2 * Real.pi) + 0.1) / (98715 : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left constant_term_pos.le (by norm_num) (x_lower hx)
  unfold relativeBudget scalarBudget
  linarith

/-- The full literal scalar expression is below the historical target for
every x at least exp23. The remaining analytic domination is a separate task. -/
theorem relativeBudget_lt {x : ℝ} (hx : Real.exp 23 ≤ x) :
    2 * (delta : ℝ) + highWeight + sqrtCoefficient / Real.sqrt x +
      (highWeight + Real.log (2 * Real.pi) + 0.1) / x < 0.00020211 :=
  (relativeBudget_le_scalarBudget hx).trans_lt scalarBudget_lt

end TernaryGoldbach.RSBounds.QuarticFirst29BudgetApplication
