import RSBounds.BacklundLowScalarData
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Elementary shape of the Riemann--von Mangoldt main term. -/

open Set Real

namespace TernaryGoldbach.RSBounds.BacklundLowScalar

theorem rosserF_monotone : MonotoneOn rosserF (Ici (2 * Real.pi)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t ht
    change 2 * Real.pi ≤ t at ht
    exact (hasDerivAt_rosserF (t := t) (by have := pi_pos; linarith [ht])).continuousAt.continuousWithinAt
  · intro t ht
    have ht' : 2 * Real.pi ≤ t := interior_subset ht
    exact (hasDerivAt_rosserF (t := t) (by
      have := pi_pos
      linarith)).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 2 * Real.pi ≤ t := interior_subset ht
    rw [(hasDerivAt_rosserF (t := t) (by have := pi_pos; linarith)).deriv]
    exact div_nonneg (log_nonneg ((le_div_iff₀ (by positivity)).mpr (by linarith)))
      (by positivity)

/-- The global minimum is attained at `2*Real.pi`, and is exactly `-1/8`. -/
theorem rosserF_lower {t : ℝ} (ht : 0 < t) : -(1 / 8 : ℝ) ≤ rosserF t := by
  have hx : 0 < t / (2 * Real.pi) := by positivity
  have h := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hx) hx.le
  rw [mul_sub, mul_one, mul_inv_cancel₀ hx.ne'] at h
  unfold rosserF
  linarith

theorem rosserF_lt_one_small {t : ℝ} (ht : 0 < t) (hu : t ≤ 1413 / 100) :
    rosserF t < 1 := by
  by_cases hpi : t ≤ 2 * Real.pi
  · have hx : 0 < t / (2 * Real.pi) := by positivity
    have hx1 : t / (2 * Real.pi) ≤ 1 := (div_le_one₀ (by positivity)).mpr hpi
    have hl : log (t / (2 * Real.pi)) ≤ 0 := log_nonpos hx.le hx1
    have hm := mul_nonpos_of_nonneg_of_nonpos hx.le hl
    unfold rosserF
    linarith
  · have hcert := (certificate_bounds ⟨0, by decide⟩).2
    change rosserF ((1413 / 100 : ℚ) : ℝ) < ((1 : ℚ) : ℝ) at hcert
    norm_num at hcert
    exact lt_of_le_of_lt (rosserF_monotone (le_of_not_ge hpi)
      (by change 2 * Real.pi ≤ (1413 / 100 : ℝ); have := pi_lt_four; linarith) hu) hcert

theorem rosserF_hundred_lt : rosserF 100 < 30 := by
  have hcert := (certificate_bounds ⟨58, by decide⟩).2
  change rosserF ((100 : ℚ) : ℝ) < ((30 : ℚ) : ℝ) at hcert
  norm_num at hcert
  exact hcert

theorem one_lt_rosserR {t : ℝ} (ht : 2 ≤ t) : 1 < rosserR 1.588 t := by
  have h2 : (1 / 2 : ℝ) ≤ log 2 := by
    have := one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this
    exact this
  have hlog : (1 / 2 : ℝ) ≤ log t := h2.trans (log_le_log (by norm_num) ht)
  have hlog2 : log (2 : ℝ) ≤ 1 := by
    have h := log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have hhalf : log (1 / 2 : ℝ) ≥ -1 := by
    rw [one_div, log_inv]
    linarith
  have hloglog : -1 ≤ log (log t) :=
    hhalf.trans (log_le_log (by norm_num) hlog)
  unfold rosserR
  linarith

end TernaryGoldbach.RSBounds.BacklundLowScalar
