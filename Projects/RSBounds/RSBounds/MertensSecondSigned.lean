import RSBounds.MertensDFinite
import RSBounds.MertensFiniteParts
import RSBounds.MertensLogKernel

/-!
# The second Mertens error with its signed endpoint cancellation

The centered function J is defined from the first Mertens error. The separate
signed-limit theorem identifies it with the improper integral of (psi-t)/t^2.
Here its finite primitive identity suffices for integration by parts.
-/

open Real Set Filter MeasureTheory
open scoped Topology

noncomputable section

namespace TernaryGoldbach.RSBounds.MertensSecondSigned

open TernaryGoldbach.PNTMertens MertensPsiAbel MertensLogKernel MertensFiniteParts

def J (x : ℝ) : ℝ := -D x - Real.eulerMascheroniConstant - 1

def error (x : ℝ) : ℝ := (Chebyshev.psi x - x) / x

def JBound : ℝ := 2 * (Real.log 4 + 4) + |Real.eulerMascheroniConstant| + 1

theorem measurable_J : Measurable J := by
  exact (measurable_D.neg.sub_const _).sub_const _

theorem J_bound {x : ℝ} (hx : 1 ≤ x) : |J x| ≤ JBound := by
  have h1 := abs_add_le (-D x) (-Real.eulerMascheroniConstant)
  have h2 := abs_add_le (-D x - Real.eulerMascheroniConstant) (-1)
  simp only [← sub_eq_add_neg, abs_neg, abs_one] at h1 h2
  dsimp [J, JBound]
  linarith [D_bound hx]

theorem first_error_eq {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x = error x - Real.eulerMascheroniConstant - J x := by
  have hx0 : x ≠ 0 := by linarith
  unfold error J D
  rw [sub_div, div_self hx0]
  ring

theorem J_sub_eq_integral {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    J a - J b = ∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 := by
  have h := MertensDLimit.D_sub_eq_integral ha hab
  dsimp [J]
  linarith

theorem intervalIntegrable_centered_psi {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Chebyshev.psi t - t) / t ^ 2) volume a b := by
  have hne : ∀ t ∈ uIcc a b, t ≠ 0 := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    linarith [ht.1]
  have hpsi : IntervalIntegrable Chebyshev.psi volume a b :=
    Chebyshev.psi_mono.intervalIntegrable
  have h := hpsi.sub
    (continuous_id.intervalIntegrable a b)
  simpa only [div_eq_mul_inv, Pi.inv_apply, Pi.pow_apply, id_eq] using h.mul_continuousOn
    ((continuousOn_id.pow 2).inv₀ (fun t ht => pow_ne_zero 2 (hne t ht)))

theorem finite_parts {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, ((Chebyshev.psi t - t) / t ^ 2) * (1 / Real.log t ^ 2)) =
      J a * (1 / Real.log a ^ 2) - J b * (1 / Real.log b ^ 2) +
        ∫ t in a..b, J t * (-2 / (t * Real.log t ^ 3)) := by
  apply integral_mul_eq_boundary_add_of_contDiffOn
    (intervalIntegrable_centered_psi (by linarith) hab)
    (Ja := J a)
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact J_sub_eq_integral (by linarith) ht.1
  · have hpos : ∀ t ∈ uIcc a b, 1 < t := by
      intro t ht
      rw [uIcc_of_le hab] at ht
      linarith [ht.1]
    exact contDiffOn_const.div
      ((contDiffOn_id.log (fun t ht => ne_of_gt (lt_trans zero_lt_one (hpos t ht)))).pow 2)
      (fun t ht => pow_ne_zero 2 (Real.log_pos (hpos t ht)).ne')
  · intro t ht
    rw [uIcc_of_le hab] at ht
    exact hasDerivAt_inv_log_sq (by linarith [ht.1])

theorem integrable_J_mul {x : ℝ} {w : ℝ → ℝ} (hx : 1 ≤ x)
    (hw : IntegrableOn w (Ioi x)) :
    IntegrableOn (fun t => J t * w t) (Ioi x) := by
  apply hw.bdd_mul measurable_J.aestronglyMeasurable.restrict (c := JBound)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact J_bound (hx.trans ht.le)

theorem error_bound {t : ℝ} (ht : 1 ≤ t) : |error t| ≤ Real.log 4 + 5 := by
  have ht0 : t ≠ 0 := by linarith
  have h := abs_add_le (Chebyshev.psi t / t) (-1)
  simp only [← sub_eq_add_neg, abs_neg, abs_one] at h
  unfold error
  rw [sub_div, div_self ht0]
  linarith [psi_ratio_bound ht]

theorem integrable_error_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => error t / (t * Real.log t ^ 2)) (Ioi x) := by
  have hm : Measurable error := by
    exact (Chebyshev.psi_mono.measurable.sub measurable_id).div measurable_id
  have h : IntegrableOn (fun t => error t * (1 / (t * Real.log t ^ 2)))
      (Ioi x) := (integrable_const_div_mul_log_sq 1 hx).bdd_mul
    hm.aestronglyMeasurable.restrict (c := Real.log 4 + 5) ?_
  · simpa only [mul_one_div] using h
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact error_bound (by linarith [show x < t from ht])

theorem integrable_centered_log_sq {x : ℝ} (hx : 2 ≤ x) :
    IntegrableOn (fun t => ((Chebyshev.psi t - t) / t ^ 2) *
      (1 / Real.log t ^ 2)) (Ioi x) := by
  apply (integrable_error_log_sq hx).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : t ≠ 0 := by linarith [show x < t from ht]
  have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [show x < t from ht])).ne'
  unfold error
  field_simp
  <;> ring

theorem boundary_tendsto_zero :
    Tendsto (fun t : ℝ => J t * (1 / Real.log t ^ 2)) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (a := fun t : ℝ => JBound * (1 / Real.log t ^ 2))
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hs : 0 ≤ 1 / Real.log t ^ 2 := by positivity
    simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_right (J_bound ht) hs
  · simpa using inv_log_sq_tendsto.const_mul JBound

theorem integral_parts {x : ℝ} (hx : 2 ≤ x) :
    (∫ t in Ioi x, error t / (t * Real.log t ^ 2)) =
      J x / Real.log x ^ 2 - ∫ t in Ioi x, J t * (2 / (t * Real.log t ^ 3)) := by
  have hleft := intervalIntegral_tendsto_integral_Ioi x
    (integrable_centered_log_sq hx) tendsto_id
  have hJneg : IntegrableOn (fun t => J t * (-2 / (t * Real.log t ^ 3)))
      (Ioi x) := by
    simpa only [Pi.neg_apply, neg_div] using
      integrable_J_mul (by linarith : 1 ≤ x) (integrable_log_cube (by linarith)).neg
  have hright := (((tendsto_const_nhds (x := J x * (1 / Real.log x ^ 2))).sub
    boundary_tendsto_zero).add
    (intervalIntegral_tendsto_integral_Ioi x hJneg tendsto_id))
  have hlim := tendsto_nhds_unique_of_eventuallyEq hleft hright ?_
  · have heq : (∫ t in Ioi x, ((Chebyshev.psi t - t) / t ^ 2) *
        (1 / Real.log t ^ 2)) = ∫ t in Ioi x, error t / (t * Real.log t ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      have ht0 : t ≠ 0 := by linarith [show x < t from ht]
      have hL : Real.log t ≠ 0 := (Real.log_pos (by linarith [show x < t from ht])).ne'
      unfold error
      field_simp
      <;> ring
    rw [heq] at hlim
    have hneg : (∫ t in Ioi x, J t * (-2 / (t * Real.log t ^ 3))) =
        -(∫ t in Ioi x, J t * (2 / (t * Real.log t ^ 3))) := by
      simp only [neg_div, mul_neg, integral_neg]
    simp only [sub_zero, mul_one_div, hneg, ← sub_eq_add_neg] at hlim
    exact hlim
  · filter_upwards [eventually_ge_atTop x] with b hb
    exact finite_parts hx hb

/-- RS62's signed second-error identity; the first-error normalization and the
finite primitive retain cancellation at the lower endpoint. -/
theorem second_error_eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = error x / Real.log x - logMass x * J x +
      ∫ t in Ioi x, J t * logKernel t := by
  have hJ2 : IntegrableOn (fun t => J t / (t * Real.log t ^ 2)) (Ioi x) := by
    simpa only [mul_one_div] using integrable_J_mul (by linarith : 1 ≤ x)
      (integrable_const_div_mul_log_sq 1 hx)
  have hJ3 := integrable_J_mul (by linarith : 1 ≤ x)
    (integrable_log_cube (by linarith))
  have hsplit : (∫ t in Ioi x, E₁Λ t / (t * Real.log t ^ 2)) =
      (∫ t in Ioi x, error t / (t * Real.log t ^ 2)) -
        Real.eulerMascheroniConstant / Real.log x -
        ∫ t in Ioi x, J t / (t * Real.log t ^ 2) := by
    calc
      _ = ∫ t in Ioi x, error t / (t * Real.log t ^ 2) -
          Real.eulerMascheroniConstant / (t * Real.log t ^ 2) -
          J t / (t * Real.log t ^ 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        dsimp only
        rw [first_error_eq (by linarith [show x < t from ht]), sub_div, sub_div]
      _ = _ := by
        have h := integral_sub ((integrable_error_log_sq hx).sub
          (integrable_const_div_mul_log_sq Real.eulerMascheroniConstant hx)) hJ2
        simp only [Pi.sub_apply] at h
        rw [integral_sub (integrable_error_log_sq hx)
          (integrable_const_div_mul_log_sq Real.eulerMascheroniConstant hx),
          integ_div_mul_log_sq Real.eulerMascheroniConstant hx] at h
        exact h
  have hkernel : (∫ t in Ioi x, J t * logKernel t) =
      (∫ t in Ioi x, J t / (t * Real.log t ^ 2)) +
        ∫ t in Ioi x, J t * (2 / (t * Real.log t ^ 3)) := by
    simp only [logKernel, mul_add, mul_one_div]
    exact integral_add hJ2 hJ3
  rw [E₂Λ.eq hx, first_error_eq (by linarith), hsplit, integral_parts hx, hkernel]
  unfold logMass
  ring

theorem second_error_sub_endpoint_le {x j : ℝ} (hx : 2 ≤ x)
    (hJ : ∀ t, x ≤ t → |J t| ≤ j) :
    |E₂Λ x - error x / Real.log x| ≤ 2 * j * logMass x := by
  rw [second_error_eq hx]
  convert signed_expression_bound hx hJ using 1 <;> congr 1 <;> ring

/-- A direct quantitative input for the prime-product/totient argument. The
uniform signed-tail budget remains an explicit hypothesis. -/
theorem second_error_abs_le {x e j : ℝ} (hx : 2 ≤ x)
    (hpsi : |Chebyshev.psi x - x| ≤ e * x)
    (hJ : ∀ t, x ≤ t → |J t| ≤ j) :
    |E₂Λ x| ≤ e / Real.log x + 2 * j * logMass x := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have he : |error x| ≤ e := by
    unfold error
    rw [abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
    exact hpsi
  calc
    _ ≤ |error x / Real.log x| + |E₂Λ x - error x / Real.log x| := by
      convert (abs_add_le (error x / Real.log x) (E₂Λ x - error x / Real.log x)) using 1
      congr 1
      ring
    _ ≤ e / Real.log x + 2 * j * logMass x := by
      apply add_le_add
      · rw [abs_div, abs_of_pos hL]
        exact div_le_div_of_nonneg_right he hL.le
      · exact second_error_sub_endpoint_le hx hJ

end TernaryGoldbach.RSBounds.MertensSecondSigned
