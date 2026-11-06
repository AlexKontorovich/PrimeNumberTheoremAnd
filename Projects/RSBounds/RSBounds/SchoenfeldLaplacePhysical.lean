import RSBounds.SchoenfeldLaplaceTails
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The logarithmic change of variable in Schoenfeld's Theorem 11

This binds the elementary Laplace inequalities to the actual physical-height
integrals, preserving the factor `17^m` in equations (7.11) and (7.18).
-/

open Real Set MeasureTheory
open scoped Interval

namespace TernaryGoldbach.RSBounds.SchoenfeldLaplaceTails

noncomputable def heightIntegrand (a d : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  (Real.log (t / 17) + d) * Real.exp (-a / Real.log (t / 17)) / t ^ (m + 1)

theorem integrand_log_mul_inv {a d t : ℝ} (ht : 0 < t) (m : ℕ) :
    integrand a d m (Real.log (t / 17)) * (1 / t) =
      17 ^ m * heightIntegrand a d m t := by
  have hq : 0 < t / 17 := by positivity
  unfold integrand heightIntegrand
  simp only [neg_div]
  rw [Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hq, Real.exp_neg]
  simp only [div_pow, pow_succ]
  field_simp [ht.ne', Real.exp_ne_zero]
  <;> ring

/-- Exact finite-interval substitution `u=log(t/17)`. -/
theorem integral_height_eq {a d l r : ℝ} (hl : 17 < l) (hlr : l ≤ r) (m : ℕ) :
    (∫ t in l..r, heightIntegrand a d m t) =
      (∫ u in Real.log (l / 17)..Real.log (r / 17), integrand a d m u) / 17 ^ m := by
  have hlt : ∀ t ∈ uIcc l r, 17 < t := by
    intro t ht
    rw [uIcc_of_le hlr] at ht
    exact hl.trans_le ht.1
  have hderiv : ∀ t ∈ uIcc l r,
      HasDerivAt (fun t : ℝ => Real.log (t / 17)) (1 / t) t := by
    intro t ht
    have ht0 : 0 < t := by linarith [hlt t ht]
    convert ((hasDerivAt_id t).div_const 17).log (by positivity : t / 17 ≠ 0) using 1 <;> simp only [id_eq] <;> field_simp [ht0.ne']
  have hcont : ContinuousOn (fun t : ℝ => 1 / t) (uIcc l r) := by
    intro t ht
    have ht0 : 0 < t := by linarith [hlt t ht]
    fun_prop (disch := positivity)
  have hg : ContinuousOn (integrand a d m)
      ((fun t : ℝ => Real.log (t / 17)) '' (uIcc l r)) := by
    rintro u ⟨t, ht, rfl⟩
    have ht17 : 1 < t / 17 := by linarith [hlt t ht]
    have hu0 := Real.log_pos ht17
    unfold integrand
    fun_prop (disch := positivity)
  have he := intervalIntegral.integral_comp_mul_deriv' hderiv hcont hg
  have hid : (∫ t in l..r,
      (integrand a d m ∘ fun t : ℝ => Real.log (t / 17)) t * (1 / t)) =
      17 ^ m * (∫ t in l..r, heightIntegrand a d m t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    exact integrand_log_mul_inv (by linarith [hlt t ht]) m
  rw [hid] at he
  apply (eq_div_iff (by positivity : (17 : ℝ) ^ m ≠ 0)).mpr
  simpa only [mul_comm] using he

/-- The physical near-height integral in (7.11). -/
theorem integral_height_near_le {a d l r : ℝ} (ha : 0 < a) (hd : 0 ≤ d)
    (hl : 17 < l) (hlr : l ≤ r) :
    (∫ t in l..r, heightIntegrand a d 0 t) ≤
      nearPrimitive a d (Real.log (r / 17)) := by
  have hl0 : 0 < l := by linarith
  rw [integral_height_eq hl hlr]
  simp only [pow_zero, div_one, Nat.cast_zero]
  apply integral_near_le ha hd
  · apply Real.log_pos
    linarith
  · apply Real.log_le_log (by positivity : 0 < l / 17)
    exact div_le_div_of_nonneg_right hlr (by norm_num)

/-- The physical quadratic far-height integral in (7.18). -/
theorem integral_height_far_le {a d l r : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hl : 17 < l) (hlr : l ≤ r) (hq : a < 2 * Real.log (l / 17) ^ 2) :
    (∫ t in l..r, heightIntegrand a d 2 t) ≤
      farPrimitive a d 2 (Real.log (l / 17)) / 289 := by
  have hl0 : 0 < l := by linarith
  rw [integral_height_eq hl hlr]
  norm_num only [show (17 : ℝ) ^ 2 = 289 by norm_num]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply integral_far_le ha hd (by norm_num)
  · apply Real.log_pos
    linarith
  · apply Real.log_le_log (by positivity : 0 < l / 17)
    exact div_le_div_of_nonneg_right hlr (by norm_num)
  · exact hq

end TernaryGoldbach.RSBounds.SchoenfeldLaplaceTails
