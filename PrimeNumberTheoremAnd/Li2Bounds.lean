/-
Bounds on li(2) using LeanCert numerical integration.

This file provides bounds on the logarithmic integral li(2) ≈ 1.0451
using the symmetric form which makes the principal value integral
absolutely convergent.

## Status

- `li2_symmetric_lower` - done (via LeanCert.Examples.Li2Verified)
- `li2_symmetric_upper` - done (via LeanCert.Examples.Li2Verified)
- `li2_symmetric_eq_li2` - sorry, connects symmetric form to principal value (#764)

See: https://github.com/alerad/leancert
-/
import Architect
import LeanCert
import LeanCert.Engine.TaylorModel.Log1p
import LeanCert.Engine.Integrate
import LeanCert.Examples.Li2Verified
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import PrimeNumberTheoremAnd.SecondaryDefinitions

open Real MeasureTheory Set
open scoped Interval

open LeanCert.Core
open LeanCert.Validity.Integration
open LeanCert.Engine.TaylorModel

namespace Li2Bounds

/-! ### Symmetric Form Definition -/

/-- The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t).
    This has a removable singularity at t=0 with limit 1. -/
noncomputable def g (t : ℝ) : ℝ := symmetricLogCombination t

/-- li(2) via the symmetric integral form.
    This equals the principal value integral ∫₀² dt/log(t). -/
noncomputable def li2_symmetric : ℝ := ∫ t in (0:ℝ)..1, g t

/-- Our li2_symmetric equals LeanCert's Li2.li2 (both are ∫₀¹ symmetricLogCombination). -/
theorem li2_symmetric_eq_Li2_li2 : li2_symmetric = Li2.li2 := rfl

/-! ### Key Properties from LeanCert -/

/-- g(t) → 1 as t → 0⁺ (the removable singularity). -/
theorem g_tendsto_one :
    Filter.Tendsto g (nhdsWithin 0 (Ioi 0)) (nhds 1) :=
  symmetricLogCombination_tendsto_one

/-- |g(t)| ≤ 2 for t ∈ (0, 1/2]. -/
theorem g_bounded (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1 / 2) :
    |g t| ≤ 2 :=
  symmetricLogCombination_bounded t ht_pos ht_lt

/-- g(t) = log(1-t²)/(log(1+t)·log(1-t)) for t ∈ (0, 1). -/
theorem g_alt (t : ℝ) (ht_pos : 0 < t) (ht_lt : t < 1) :
    g t = log (1 - t^2) / (log (1 + t) * log (1 - t)) :=
  symmetricLogCombination_alt t ht_pos ht_lt

/-! ### Numerical Integration Setup -/

/-- The expression g_alt_expr represents log(1-t²)/(log(1+t)·log(1-t)).
    This form is better for interval arithmetic as it avoids the apparent
    singularity in the symmetric form. -/
def g_alt_expr : Expr :=
  Expr.mul
    (Expr.log (Expr.add (Expr.const 1)
      (Expr.neg (Expr.mul (Expr.var 0) (Expr.var 0)))))
    (Expr.inv
      (Expr.mul
        (Expr.log (Expr.add (Expr.const 1) (Expr.var 0)))
        (Expr.log (Expr.add (Expr.const 1) (Expr.neg (Expr.var 0))))))

theorem g_alt_expr_supported : ExprSupportedWithInv g_alt_expr := by
  unfold g_alt_expr
  apply ExprSupportedWithInv.mul
  · apply ExprSupportedWithInv.log
    apply ExprSupportedWithInv.add
    · exact ExprSupportedWithInv.const 1
    · apply ExprSupportedWithInv.neg
      apply ExprSupportedWithInv.mul <;> exact ExprSupportedWithInv.var 0
  · apply ExprSupportedWithInv.inv
    apply ExprSupportedWithInv.mul
    · apply ExprSupportedWithInv.log
      apply ExprSupportedWithInv.add
      exact ExprSupportedWithInv.const 1
      exact ExprSupportedWithInv.var 0
    · apply ExprSupportedWithInv.log
      apply ExprSupportedWithInv.add
      exact ExprSupportedWithInv.const 1
      exact ExprSupportedWithInv.neg (ExprSupportedWithInv.var 0)

/-! ### Certified Bound Helpers -/

def checkIntegralLowerBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (c ≤ J.lo)
  | none => false

def checkIntegralUpperBound (e : Expr) (I : IntervalRat) (n : ℕ) (c : ℚ) : Bool :=
  match integratePartitionWithInv e I n with
  | some J => decide (J.hi ≤ c)
  | none => false

/-! ### Integrability Lemmas -/

/-- 1/log(1-u) is integrable on [ε, 1) for ε > 0. -/
theorem log_one_minus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 - u)) volume ε 1 := by
  have hle : ε ≤ 1 := le_of_lt hε1
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
  have hmeas : Measurable (fun u => 1 / log (1 - u)) := by
    exact Real.measurable_log.comp (measurable_const.sub measurable_id) |>.inv |> fun h => by
      simpa [one_div] using h
  have hbdd : ∀ u ∈ Ioc ε 1, ‖1 / log (1 - u)‖ ≤ 1 / ε := by
    intro u ⟨hε_lt_u, hu_le_1⟩
    by_cases hu_eq_1 : u = 1
    · simp [hu_eq_1, log_zero]; positivity
    · have hu_lt_1 : u < 1 := lt_of_le_of_ne hu_le_1 hu_eq_1
      have h1mu_pos : 0 < 1 - u := by linarith
      have h1mu_lt1 : 1 - u < 1 := by linarith
      have hlog_neg : log (1 - u) < 0 := log_neg h1mu_pos h1mu_lt1
      rw [Real.norm_eq_abs, abs_one_div, abs_of_neg hlog_neg]
      have hlog_ub : log (1 - u) ≤ -u := by
        have h := log_le_sub_one_of_pos h1mu_pos; linarith
      have hneglog_lb : u ≤ -log (1 - u) := by linarith
      have hu_pos : 0 < u := by linarith
      calc 1 / -log (1 - u) ≤ 1 / u := one_div_le_one_div_of_le hu_pos hneglog_lb
        _ ≤ 1 / ε := one_div_le_one_div_of_le hε (le_of_lt hε_lt_u)
  exact Measure.integrableOn_of_bounded (M := 1 / ε)
    (measure_Ioc_lt_top.ne) hmeas.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ hbdd))

/-- 1/log(1+u) is integrable on [ε, 1] for ε > 0. -/
theorem log_one_plus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 + u)) volume ε 1 := by
  have hcont : ContinuousOn (fun u => 1 / log (1 + u)) (Icc ε 1) := by
    apply ContinuousOn.div continuousOn_const
    · have hadd_cont : ContinuousOn (fun u => 1 + u) (Icc ε 1) :=
        continuousOn_const.add continuousOn_id
      have hadd_ne : ∀ u ∈ Icc ε 1, (1 : ℝ) + u ≠ 0 := fun u hu => by linarith [hu.1]
      exact continuousOn_log.comp hadd_cont hadd_ne
    · intro u hu
      have h1pu_gt1 : 1 < 1 + u := by linarith [hu.1]
      exact ne_of_gt (log_pos h1pu_gt1)
  exact ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hε1) hcont

/-! ### Integrability of g on [0, 1] -/

/-- g is integrable on [0, 1]. Uses boundedness by 2 from Li2Verified. -/
theorem g_intervalIntegrable_full : IntervalIntegrable g volume 0 1 := by
  have hmeas : Measurable g := by
    have hlog1p : Measurable fun t : ℝ => log (1 + t) :=
      Real.measurable_log.comp (measurable_const.add measurable_id)
    have hlog1m : Measurable fun t : ℝ => log (1 - t) :=
      Real.measurable_log.comp (measurable_const.sub measurable_id)
    have hlog1p_inv : Measurable fun t : ℝ => (log (1 + t))⁻¹ := hlog1p.inv
    have hlog1m_inv : Measurable fun t : ℝ => (log (1 - t))⁻¹ := hlog1m.inv
    unfold g symmetricLogCombination
    simpa [one_div] using hlog1p_inv.add hlog1m_inv
  have hInt_Ioo : IntegrableOn g (Ioo (0:ℝ) 1) volume := by
    apply Measure.integrableOn_of_bounded
    · exact measure_Ioo_lt_top.ne
    · exact hmeas.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
      exact ae_of_all _ (fun t ht => by
        have hpos := Li2.g_pos t ht.1 ht.2
        have hle := Li2.g_le_two t ht.1 ht.2
        have habs : |g t| = g t := abs_of_pos hpos
        simpa [Real.norm_eq_abs, habs] using hle)
  exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0:ℝ) ≤ 1)).2 hInt_Ioo

/-- g is integrable on any subinterval [a, b] ⊆ (0, 1). -/
theorem g_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  have hab' : a ≤ b := hab
  have hIcc : Icc a b ⊆ Icc 0 1 := Icc_subset_Icc (le_of_lt ha) (le_of_lt hb)
  have huIcc_ab : uIcc a b = Icc a b := Set.uIcc_of_le hab'
  have huIcc_01 : uIcc (0:ℝ) 1 = Icc 0 1 := Set.uIcc_of_le (by norm_num)
  exact g_intervalIntegrable_full.mono_set (by rw [huIcc_ab, huIcc_01]; exact hIcc)

/-! ### Certified Bounds on li(2)

Using LeanCert's integratePartitionWithInv with 3000 partitions on the main
interval [1/1000, 999/1000], we obtain certified bounds. -/

@[blueprint
  "li2-lower"
  (title := "Lower bound on li(2)")
  (statement := /-- $\mathrm{li}(2) \geq 1.039$ -/)
  (discussion := 759)]
theorem li2_symmetric_lower : (1039:ℚ)/1000 ≤ li2_symmetric := by
  rw [li2_symmetric_eq_Li2_li2]
  exact Li2.li2_lower

@[blueprint
  "li2-upper"
  (title := "Upper bound on li(2)")
  (statement := /-- $\mathrm{li}(2) \leq 1.06$ -/)
  (discussion := 759)]
theorem li2_symmetric_upper : li2_symmetric ≤ (106:ℚ)/100 := by
  rw [li2_symmetric_eq_Li2_li2]
  exact Li2.li2_upper

@[blueprint
  "li2-bounds"
  (title := "Bounds on li(2)")
  (statement := /-- $1.039 \leq \mathrm{li}(2) \leq 1.06$ -/)
  (discussion := 759)]
theorem li2_symmetric_bounds : (1039:ℚ)/1000 ≤ li2_symmetric ∧ li2_symmetric ≤ (106:ℚ)/100 :=
  ⟨li2_symmetric_lower, li2_symmetric_upper⟩

/-! ### Substitution Lemmas for Principal Value Connection -/

/-- For ε > 0, ∫₀^{1-ε} dt/log(t) = ∫_ε^1 du/log(1-u) via t = 1 - u. -/
theorem integral_sub_left (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (0:ℝ)..(1 - ε), 1 / log t = ∫ u in ε..1, 1 / log (1 - u) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x => 1 / log x) (1:ℝ) (a := ε) (b := 1)
  have h1 : (1:ℝ) - 1 = 0 := by ring
  rw [h1] at h
  exact h.symm

/-- For ε > 0, ∫_{1+ε}^2 dt/log(t) = ∫_ε^1 du/log(1+u) via t = 1 + u. -/
theorem integral_sub_right (ε : ℝ) (_hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in (1 + ε)..(2:ℝ), 1 / log t = ∫ u in ε..1, 1 / log (1 + u) := by
  have h := intervalIntegral.integral_comp_add_right (fun x => 1 / log x) (1:ℝ) (a := ε) (b := 1)
  have h1 : ε + (1:ℝ) = 1 + ε := by ring
  have h2 : (1:ℝ) + 1 = 2 := by ring
  rw [h1, h2] at h
  have heq : ∀ u : ℝ, 1 / log (u + 1) = 1 / log (1 + u) := by intro u; ring_nf
  simp_rw [heq] at h
  exact h.symm

/-- The principal value integral for li(2) equals ∫_ε^1 g(u) du. -/
theorem pv_integral_eq_symmetric (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    (∫ t in (0:ℝ)..(1 - ε), 1 / log t) + (∫ t in (1 + ε)..(2:ℝ), 1 / log t) =
    ∫ u in ε..1, g u := by
  have h1 := integral_sub_left ε hε hε1
  have h2 := integral_sub_right ε hε hε1
  have hInt1 := log_one_minus_integrable ε hε hε1
  have hInt2 := log_one_plus_integrable ε hε hε1
  have hsum := intervalIntegral.integral_add hInt1 hInt2
  have heq_g : ∀ u, (1 / log (1 - u) + 1 / log (1 + u)) = g u := by
    intro u; simp only [g, symmetricLogCombination, add_comm]
  simp_rw [heq_g] at hsum
  have hstep : (∫ u in ε..1, 1 / log (1 - u)) + (∫ u in ε..1, 1 / log (1 + u)) =
      ∫ u in ε..1, g u := hsum.symm
  have hlhs : (∫ t in (0:ℝ)..(1 - ε), 1 / log t) + (∫ t in (1 + ε)..(2:ℝ), 1 / log t) =
      (∫ u in ε..1, 1 / log (1 - u)) + (∫ u in ε..1, 1 / log (1 + u)) :=
    congrArg₂ (· + ·) h1 h2
  exact Trans.trans hlhs hstep

/-- The limit as ε → 0⁺ of ∫_ε^1 g(u) du equals ∫_0^1 g(u) du. -/
theorem limit_integral_g :
    Filter.Tendsto (fun ε => ∫ u in ε..1, g u) (nhdsWithin 0 (Ioi 0)) (nhds (∫ u in (0:ℝ)..1, g u)) := by
  have hInt := g_intervalIntegrable_full
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have huIcc_eq : uIcc (0:ℝ) 1 = Icc 0 1 := Set.uIcc_of_le h01
  have hcont : ContinuousOn (fun x => ∫ u in (1:ℝ)..x, g u) (Icc 0 1) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hInt.symm
      (by rw [Set.uIcc_comm, huIcc_eq]; exact Set.right_mem_Icc.2 h01)
    rwa [Set.uIcc_comm, huIcc_eq] at h
  have heq : ∀ ε, ∫ u in ε..(1:ℝ), g u = -∫ u in (1:ℝ)..ε, g u := fun ε =>
    intervalIntegral.integral_symm 1 ε
  have heq' : (fun ε => ∫ u in ε..(1:ℝ), g u) = (fun ε => -∫ u in (1:ℝ)..ε, g u) := funext heq
  rw [heq']
  have hval : -∫ u in (1:ℝ)..0, g u = ∫ u in (0:ℝ)..1, g u := by
    rw [intervalIntegral.integral_symm 0 1]; ring
  rw [← hval]
  have hcont_neg : ContinuousOn (fun x => -∫ u in (1:ℝ)..x, g u) (Icc 0 1) := hcont.neg
  have h0mem : (0:ℝ) ∈ Icc 0 1 := Set.left_mem_Icc.2 h01
  have hcwa := hcont_neg 0 h0mem
  rw [ContinuousWithinAt] at hcwa
  have hfilter : nhdsWithin (0:ℝ) (Ioo 0 1) = nhdsWithin 0 (Ioi 0) :=
    nhdsWithin_Ioo_eq_nhdsGT (by norm_num : (0:ℝ) < 1)
  exact (hcwa.mono_left (nhdsWithin_mono 0 Ioo_subset_Icc_self)).mono_left (le_of_eq hfilter.symm)

/-! ### Connection to Principal Value li(2)

The symmetric integral li2_symmetric equals the principal value li(2).
This follows from the substitutions u = 1-t and u = t-1 which transform
the principal value integral into the absolutely convergent symmetric form. -/

@[blueprint
  "li2-eq"
  (title := "Symmetric form equals principal value")
  (statement := /-- $\int_0^1 \left(\frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}\right) dt = \mathrm{li}(2)$ -/)
  (discussion := 764)]
theorem li2_symmetric_eq_li2 : li2_symmetric = li 2 := by
  -- The PNT+ li uses lim with set difference; we need to show this equals our form
  -- For now, we show the symmetric form equals the split-integral principal value
  -- The full proof requires showing the set-diff integral equals the split integral
  sorry -- TODO: Connect lim-based definition to limUnder-based proof

/-- The main result: certified bounds on li(2). -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li 2 ∧ li 2 ≤ (106:ℚ)/100 := by
  rw [← li2_symmetric_eq_li2]
  exact li2_symmetric_bounds

end Li2Bounds
