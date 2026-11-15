import RSBounds.WeightedZeroSums
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# Elementary integrals for the quartic Rosser zero-sum bound

These are unconditional calculus estimates. The logarithmic reciprocal in
the derivative of Rosser's error function is bounded by its value at the
lower endpoint. No zero-count or Riemann-hypothesis premise is used.
-/

open Real Set MeasureTheory

namespace TernaryGoldbach.RSBounds.RosserTailIntegrals

/-- The derivative of `rosserF + rosserR C`, independent of `C`. -/
noncomputable def density (t : ℝ) : ℝ :=
  Real.log (t / (2 * Real.pi)) / (2 * Real.pi) +
    (0.137 + 0.443 / Real.log t) / t

/-- Freeze the reciprocal logarithm at the lower endpoint. -/
noncomputable def coefficient (a : ℝ) : ℝ := 0.137 + 0.443 / Real.log a

noncomputable def upperDensity (a t : ℝ) : ℝ :=
  Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + coefficient a / t

/-- Positive tail primitive, whose negative has derivative `upperDensity / t^5`. -/
noncomputable def tailPrimitive (c t : ℝ) : ℝ :=
  (Real.log (t / (2 * Real.pi)) / 4 + 1 / 16) / (2 * Real.pi * t ^ 4) +
    c / (5 * t ^ 5)

/-- The elementary tail allowance in the degree-four smoothing budget. -/
noncomputable def J (a : ℝ) : ℝ :=
  (Real.log (a / (2 * Real.pi)) / 4 + 1 / 16) / (2 * Real.pi * a ^ 4) +
    0.137 / (5 * a ^ 5) + 0.443 / (5 * a ^ 5 * Real.log a)

noncomputable def lowPrimitive (c t : ℝ) : ℝ :=
  Real.log (t / (2 * Real.pi)) ^ 2 / (4 * Real.pi) - c / t

theorem hasDerivAt_rosserEnvelope (C : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun t => rosserF t + rosserR C t) (density t) t := by
  exact (hasDerivAt_rosserF (by linarith)).add (hasDerivAt_rosserR C ht)

theorem density_le_upperDensity {a t : ℝ} (ha : 1 < a) (hat : a ≤ t) :
    density t ≤ upperDensity a t := by
  have ha0 : 0 < a := by linarith
  have ht0 : 0 < t := ha0.trans_le hat
  have hla : 0 < Real.log a := Real.log_pos ha
  have hlat : Real.log a ≤ Real.log t := Real.log_le_log ha0 hat
  have hquot : (0.443 : ℝ) / Real.log t ≤ 0.443 / Real.log a :=
    div_le_div_of_nonneg_left (by norm_num) hla hlat
  unfold density upperDensity coefficient
  exact add_le_add le_rfl (div_le_div_of_nonneg_right (add_le_add le_rfl hquot) ht0.le)

theorem continuousAt_density {t : ℝ} (ht : 1 < t) : ContinuousAt density t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  unfold density
  fun_prop (disch := positivity)

theorem continuousAt_upperDensity (a : ℝ) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (upperDensity a) t := by
  unfold upperDensity
  fun_prop (disch := positivity)

theorem hasDerivAt_neg_tailPrimitive (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t => -tailPrimitive c t)
      ((Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + c / t) / t ^ 5) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn : t ≠ 0 := ht.ne'
  have hi := hasDerivAt_id t
  have hl := (hi.div_const (2 * Real.pi)).log (div_ne_zero hn hp)
  have h₁ := ((hl.div_const 4).add_const (1 / 16 : ℝ)).div
    ((hi.pow 4).const_mul (2 * Real.pi)) (by
      simpa only [Pi.pow_apply, id_eq] using mul_ne_zero hp (pow_ne_zero 4 hn))
  have h₂ := (hasDerivAt_const t c).div ((hi.pow 5).const_mul 5) (by
    simpa only [Pi.pow_apply, id_eq] using
      mul_ne_zero (by norm_num : (5 : ℝ) ≠ 0) (pow_ne_zero 5 hn))
  convert (h₁.add h₂).neg using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [hp, hn]
    <;> ring

theorem hasDerivAt_lowPrimitive (c : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (lowPrimitive c)
      ((Real.log (t / (2 * Real.pi)) / (2 * Real.pi) + c / t) / t) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hn : t ≠ 0 := ht.ne'
  have hi := hasDerivAt_id t
  have hl := (hi.div_const (2 * Real.pi)).log (div_ne_zero hn hp)
  have hh := ((hl.pow 2).div_const (4 * Real.pi)).sub
    ((hasDerivAt_const t c).div hi hn)
  convert hh using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [hp, hn]
    <;> ring

theorem coefficient_nonneg {a : ℝ} (ha : 1 < a) : 0 ≤ coefficient a := by
  have hl : 0 < Real.log a := Real.log_pos ha
  unfold coefficient
  positivity

theorem tailPrimitive_nonneg {c t : ℝ} (hc : 0 ≤ c) (ht : 7 ≤ t) :
    0 ≤ tailPrimitive c t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have ht0 : 0 < t := by linarith
  have hpt : 2 * Real.pi ≤ t := by linarith [Real.pi_lt_d4]
  have hlog : 0 ≤ Real.log (t / (2 * Real.pi)) :=
    Real.log_nonneg ((le_div_iff₀ hp).mpr (by simpa using hpt))
  unfold tailPrimitive
  positivity

theorem J_eq_tailPrimitive {a : ℝ} (ha : 1 < a) :
    J a = tailPrimitive (coefficient a) a := by
  have ha0 : a ≠ 0 := by linarith
  have hl : Real.log a ≠ 0 := (Real.log_pos ha).ne'
  unfold J tailPrimitive coefficient
  field_simp [ha0, hl]
  <;> ring

/-- Exact integral of the frozen-coefficient majorant in the high range. -/
theorem integral_upperDensity_div_pow_five {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, upperDensity a t / t ^ 5) =
      tailPrimitive (coefficient a) a - tailPrimitive (coefficient a) b := by
  have hc : ContinuousOn (fun t => upperDensity a t / t ^ 5) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div
      (continuousAt_id.pow 5) (by
        simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 5 ht0.ne')).continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_neg_tailPrimitive (coefficient a)
      (ha.trans_le (by rw [uIcc_of_le hab] at ht; exact ht.1))) hc.intervalIntegrable
  simpa only [upperDensity, neg_sub_neg] using h

/-- Elementary finite tail bound; the right side is independent of the upper endpoint. -/
theorem integral_density_div_pow_five_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, density t / t ^ 5) ≤ J a := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t => density t / t ^ 5) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    have ht0 : 0 < t := by linarith
    exact ((continuousAt_density ht1).div (continuousAt_id.pow 5)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 5 ht0.ne')).continuousWithinAt
  have hu : IntervalIntegrable (fun t => upperDensity a t / t ^ 5) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div (continuousAt_id.pow 5)
      (by simpa only [Pi.pow_apply, id_eq] using pow_ne_zero 5 ht0.ne')).continuousWithinAt
  have hle := intervalIntegral.integral_mono_on hab hi hu (fun t ht =>
    div_le_div_of_nonneg_right (density_le_upperDensity ha1 ht.1)
      (by have ht0 : 0 ≤ t := ha0.le.trans ht.1; positivity))
  rw [integral_upperDensity_div_pow_five ha0 hab] at hle
  rw [J_eq_tailPrimitive ha1]
  exact hle.trans (sub_le_self _ (tailPrimitive_nonneg (coefficient_nonneg ha1) (ha.trans hab)))

/-- Exact integral of the frozen-coefficient majorant in the low range. -/
theorem integral_upperDensity_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ t in a..b, upperDensity a t / t) =
      (Real.log (b / (2 * Real.pi)) ^ 2 - Real.log (a / (2 * Real.pi)) ^ 2) /
        (4 * Real.pi) + coefficient a * (1 / a - 1 / b) := by
  have hc : ContinuousOn (fun t => upperDensity a t / t) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div continuousAt_id ht0.ne').continuousWithinAt
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hasDerivAt_lowPrimitive (coefficient a)
      (ha.trans_le (by rw [uIcc_of_le hab] at ht; exact ht.1))) hc.intervalIntegrable
  simp only [upperDensity]
  rw [h]
  unfold lowPrimitive
  ring

/-- Elementary finite integral bound for the low weight `1/t`. -/
theorem integral_density_div_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, density t / t) ≤
      (Real.log (b / (2 * Real.pi)) ^ 2 - Real.log (a / (2 * Real.pi)) ^ 2) /
        (4 * Real.pi) + (0.137 + 0.443 / Real.log a) * (1 / a - 1 / b) := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hi : IntervalIntegrable (fun t => density t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := ha1.trans_le ht.1
    exact ((continuousAt_density ht1).div continuousAt_id
      (by change t ≠ 0; linarith)).continuousWithinAt
  have hu : IntervalIntegrable (fun t => upperDensity a t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ((continuousAt_upperDensity a ht0).div continuousAt_id ht0.ne').continuousWithinAt
  have hle := intervalIntegral.integral_mono_on hab hi hu (fun t ht =>
    div_le_div_of_nonneg_right (density_le_upperDensity ha1 ht.1) (ha0.le.trans ht.1))
  rw [integral_upperDensity_div ha0 hab] at hle
  exact hle

end TernaryGoldbach.RSBounds.RosserTailIntegrals
