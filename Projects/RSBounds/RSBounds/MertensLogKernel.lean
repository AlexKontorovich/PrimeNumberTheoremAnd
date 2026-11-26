import TernaryGoldbach.Prelim.PNTMertens
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The positive logarithmic kernel in RS62 Lemma 8

The two kernel masses are evaluated exactly. The final integral estimate is
abstract: its bound on the function is an explicit hypothesis. No estimate on
the Chebyshev functions, zero-free region, or RH hypothesis occurs here.
-/

open Real Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace TernaryGoldbach.RSBounds.MertensLogKernel

open TernaryGoldbach.PNTMertens

def logKernel (t : ℝ) : ℝ :=
  1 / (t * Real.log t ^ 2) + 2 / (t * Real.log t ^ 3)

def logMass (x : ℝ) : ℝ := 1 / Real.log x + 1 / Real.log x ^ 2

theorem hasDerivAt_inv_log_sq {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun u : ℝ => 1 / Real.log u ^ 2)
      (-2 / (t * Real.log t ^ 3)) t := by
  have ht0 : t ≠ 0 := by linarith
  have hL : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  convert ((hasDerivAt_log ht0).fun_pow 2).fun_inv (pow_ne_zero 2 hL) using 1
  · simp only [one_div]
  · field_simp
    <;> ring

theorem inv_log_sq_tendsto :
    Tendsto (fun t : ℝ => 1 / Real.log t ^ 2) atTop (𝓝 0) := by
  have h := (tendsto_log_atTop.inv_tendsto_atTop).pow 2
  simpa only [one_div, inv_pow, Pi.inv_apply, zero_pow (by decide : 2 ≠ 0)] using h

theorem integrable_log_cube {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t : ℝ => 2 / (t * Real.log t ^ 3)) (Ioi x) := by
  apply integrableOn_Ioi_deriv_of_nonneg' (g := fun t : ℝ => -(1 / Real.log t ^ 2))
  · intro t ht
    convert (hasDerivAt_inv_log_sq (lt_of_lt_of_le hx ht)).neg using 1 <;> ring
  · intro t ht
    have ht0 : 0 < t := lt_trans (lt_trans zero_lt_one hx) ht
    have hL : 0 < Real.log t := Real.log_pos (lt_trans hx ht)
    positivity
  · simpa using inv_log_sq_tendsto.neg

theorem integral_log_cube {x : ℝ} (hx : 1 < x) :
    (∫ t in Ioi x, 2 / (t * Real.log t ^ 3)) = 1 / Real.log x ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (f := fun t : ℝ => -(1 / Real.log t ^ 2)) (m := 0)
    (fun t (ht : x ≤ t) => show HasDerivAt (fun u : ℝ => -(1 / Real.log u ^ 2))
      (2 / (t * Real.log t ^ 3)) t from by
        convert (hasDerivAt_inv_log_sq (lt_of_lt_of_le hx ht)).neg using 1 <;> ring)
    (integrable_log_cube hx) (by simpa using inv_log_sq_tendsto.neg)
  simpa using h

theorem logKernel_nonneg {t : ℝ} (ht : 1 < t) : 0 ≤ logKernel t := by
  have ht0 : 0 < t := by linarith
  have hL : 0 < Real.log t := Real.log_pos ht
  unfold logKernel
  positivity

theorem integrable_logKernel {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn logKernel (Ioi x) :=
  (integrable_const_div_mul_log_sq 1 hx).add (integrable_log_cube (by linarith))

theorem integral_logKernel {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in Ioi x, logKernel t) = logMass x := by
  unfold logKernel logMass
  rw [integral_add (integrable_const_div_mul_log_sq 1 hx)
    (integrable_log_cube (by linarith)), integ_div_mul_log_sq 1 hx,
    integral_log_cube (by linarith)]

theorem integrable_mul_logKernel {x j : ℝ} {f : ℝ → ℝ}
    (hx : 2 ≤ x) (hj : 0 ≤ j) (hm : Measurable f)
    (hb : ∀ t, x ≤ t → |f t| ≤ j) :
    IntegrableOn (fun t => f t * logKernel t) (Ioi x) := by
  refine ((integrable_logKernel hx).const_mul j).mono ?_ ?_
  · exact (hm.mul (by unfold logKernel; fun_prop)).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hK := logKernel_nonneg (show 1 < t by linarith [show x < t from ht])
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hj, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right (hb t ht.le) hK

theorem abs_integral_mul_logKernel_le {x j : ℝ} {f : ℝ → ℝ}
    (hx : 2 ≤ x) (hb : ∀ t, x ≤ t → |f t| ≤ j) :
    |∫ t in Ioi x, f t * logKernel t| ≤ j * logMass x := by
  have h := norm_integral_le_of_norm_le ((integrable_logKernel hx).const_mul j)
    (f := fun t => f t * logKernel t) ?_
  · simpa only [Real.norm_eq_abs, integral_const_mul, integral_logKernel hx] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hK := logKernel_nonneg (show 1 < t by linarith [show x < t from ht])
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
    exact mul_le_mul_of_nonneg_right (hb t ht.le) hK

theorem logMass_nonneg {x : ℝ} (hx : 1 < x) : 0 ≤ logMass x := by
  have hL := Real.log_pos hx
  unfold logMass
  positivity

/-- The signed endpoint and the positive integral each cost one kernel mass. -/
theorem signed_expression_bound {x j : ℝ} {f : ℝ → ℝ}
    (hx : 2 ≤ x) (hb : ∀ t, x ≤ t → |f t| ≤ j) :
    |-(logMass x * f x) + ∫ t in Ioi x, f t * logKernel t| ≤
      2 * j * logMass x := by
  have hM := logMass_nonneg (show 1 < x by linarith)
  calc
    _ ≤ |-(logMass x * f x)| + |∫ t in Ioi x, f t * logKernel t| := abs_add_le _ _
    _ ≤ logMass x * j + j * logMass x := by
      apply add_le_add
      · rw [abs_neg, abs_mul, abs_of_nonneg hM]
        exact mul_le_mul_of_nonneg_left (hb x le_rfl) hM
      · exact abs_integral_mul_logKernel_le hx hb
    _ = _ := by ring

end TernaryGoldbach.RSBounds.MertensLogKernel
