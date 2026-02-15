import Architect
import LeanCert.Examples.Li2Bounds
-- Lightweight interface (fast build)
-- Note: LeanCert.Examples.Li2Verified contains the heavy numerical verification
-- but is not imported here to keep build times reasonable for contributors.
-- The bounds are verified in LeanCert CI.
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.Basic

/-
Bounds on li(2) using LeanCert numerical integration.

This file provides bounds on the logarithmic integral li(2) ≈ 1.0451
using the symmetric form which makes the principal value integral
absolutely convergent.

## Status - ALL PROVEN

- `li2_symmetric_lower` - done (via LeanCert.Examples.Li2Bounds)
- `li2_symmetric_upper` - done (via LeanCert.Examples.Li2Bounds)
- `li2_symmetric_eq_li2` - PROVEN (connects symmetric form to principal value, PNT#764)
  - Uses Filter.Tendsto.limUnder_eq to connect the limit definition
- `setDiff_integral_eq_split` - PROVEN (integrability via IntegrableOn.of_bound)
- `li2_bounds` - PROVEN: 1.039 ≤ li(2) ≤ 1.06

## Build Time Optimization

This file imports only the lightweight LeanCert.Examples.Li2Bounds module, which
compiles in seconds. The heavy numerical verification (~20 min) is in
LeanCert.Examples.Li2Verified and is only needed for LeanCert's CI.

See: https://github.com/alerad/leancert
-/

open Real MeasureTheory Set
open scoped Interval

open LeanCert.Engine.TaylorModel  -- For symmetricLogCombination
open Topology

namespace Li2Bounds

/-! ### Local definition of li (principal value integral)

This matches the definition in SecondaryDefinitions.lean but is defined here
to keep Li2Bounds.lean self-contained and avoid circular imports. -/

/-- The logarithmic integral li(x) = ∫₀ˣ dt/log(t) (principal value).
    This is the local copy matching SecondaryDefinitions.li -/
noncomputable def li (x : ℝ) : ℝ :=
  lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

/-! ### Symmetric Form Definition -/

/-- The symmetric log combination g(t) = 1/log(1+t) + 1/log(1-t).
    This has a removable singularity at t=0 with limit 1. -/
noncomputable def g (t : ℝ) : ℝ := symmetricLogCombination t

/-- li(2) via the symmetric integral form.
    This equals the principal value integral ∫₀² dt/log(t). -/
noncomputable def li2_symmetric : ℝ := ∫ t in (0:ℝ)..1, g t

/-- Our li2_symmetric equals LeanCert's Li2.li2 (both are ∫₀¹ symmetricLogCombination). -/
theorem li2_symmetric_eq_Li2_li2 : li2_symmetric = Li2.li2 := rfl

/-! ### Integrability Lemmas -/

/-- 1/log(1-u) is integrable on [ε, 1) for ε > 0. -/
theorem log_one_minus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 - u)) volume ε 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hε1.le]
  refine Measure.integrableOn_of_bounded (M := 1 / ε) measure_Ioc_lt_top.ne (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [self_mem_ae_restrict (by measurability), Measure.ae_ne _ 1] with u  ⟨hε_lt_u, hu_le_one⟩ hu_ne_one
  have h1mu_pos : 0 < 1 - u := by grind
  have h1mu_lt1 : 1 - u < 1 := by linarith
  have hlog_neg : log (1 - u) < 0 := log_neg h1mu_pos h1mu_lt1
  rw [Real.norm_eq_abs, abs_one_div, abs_of_neg hlog_neg]
  gcongr
  have hlog_ub : log (1 - u) ≤ -u := by
    have h := log_le_sub_one_of_pos h1mu_pos; linarith
  linarith

/-- 1/log(1+u) is integrable on [ε, 1] for ε > 0. -/
theorem log_one_plus_integrable (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    IntervalIntegrable (fun u => 1 / log (1 + u)) volume ε 1 := by
  refine ContinuousOn.intervalIntegrable_of_Icc hε1.le fun u hu ↦ ContinuousAt.continuousWithinAt ?_
  have : 1 + u ≠ 0 := by grind
  have : log (1 + u ) ≠ 0 := by simp; grind
  fun_prop (disch := assumption)

/-! ### Integrability of g on [0, 1] -/

/-- g is integrable on [0, 1]. Uses boundedness by 2 from Li2Bounds. -/
theorem g_intervalIntegrable_full : IntervalIntegrable g volume 0 1 := by
  apply intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)|>.2
  apply Measure.integrableOn_of_bounded (measure_Ioo_lt_top.ne)
  · apply Measurable.aestronglyMeasurable
    unfold g symmetricLogCombination
    fun_prop
  · filter_upwards [self_mem_ae_restrict (by measurability)] with t ht
    have habs : |g t| = g t := abs_of_pos <| Li2.g_pos t ht.1 ht.2
    simpa [Real.norm_eq_abs, habs] using Li2.g_le_two t ht.1 ht.2

/-- g is integrable on any subinterval [a, b] ⊆ (0, 1). -/
theorem g_intervalIntegrable (a b : ℝ) (ha : 0 < a) (hb : b < 1) (hab : a ≤ b) :
    IntervalIntegrable g volume a b := by
  apply g_intervalIntegrable_full.mono_set
  rw [uIcc_of_le hab, uIcc_of_le (by linarith)]
  exact Icc_subset_Icc ha.le hb.le

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
  have h01 : (0:ℝ) ≤ 1 := by norm_num
  have huIcc_eq : uIcc (0:ℝ) 1 = Icc 0 1 := Set.uIcc_of_le (by linarith)
  have hcont : ContinuousOn (fun x => ∫ u in (1:ℝ)..x, g u) (Icc 0 1) := by
    rw [← huIcc_eq]
    apply intervalIntegral.continuousOn_primitive_interval' g_intervalIntegrable_full
    simp
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

/-- The set difference Ioc 0 x \ Ioo (1-ε) (1+ε) for small ε > 0. -/
theorem setDiff_decompose (ε x : ℝ) (hε : 0 < ε) (hx : 2 ≤ x) :
    Set.Ioc 0 x \ Set.Ioo (1 - ε) (1 + ε) = Set.Ioc 0 (1 - ε) ∪ Set.Icc (1 + ε) x := by
  grind

/-- The Set.diff integral equals the split interval integrals.
    This is the key technical lemma connecting PNT+'s li definition to the symmetric form. -/
theorem setDiff_integral_eq_split (ε x : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc 0 x \ Set.Ioo (1 - ε) (1 + ε), 1 / log t =
    (∫ t in (0:ℝ)..(1 - ε), 1 / log t) + (∫ t in (1 + ε)..x, 1 / log t) := by
  -- Step 1: Rewrite using set decomposition
  rw [setDiff_decompose ε x hε hx, setIntegral_union (by grind) measurableSet_Icc,
    intervalIntegral.integral_of_le (by linarith), integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]
  · -- The function 1/log t is bounded on (0, 1-ε]: as t → 0⁺, 1/log t → 0
    -- The bound is |1/log(1-ε)| = -1/log(1-ε) (since log(1-ε) < 0)
    have hlog_neg : log (1 - ε) < 0 := Real.log_neg (by linarith) (by linarith)
    refine IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ (-1 / log (1 - ε)) ?_
    -- AEStronglyMeasurable: function is continuous on Ioc
    · have hcont : ContinuousOn (fun t => 1 / log t) (Set.Ioc 0 (1 - ε)) := by
        apply ContinuousOn.div continuousOn_const
        · exact Real.continuousOn_log.mono (fun x hx => ne_of_gt hx.1)
        · intro x hx
          apply Real.log_ne_zero_of_pos_of_ne_one hx.1
          linarith [hx.2]
      exact hcont.aestronglyMeasurable measurableSet_Ioc
    -- Bound: |1/log t| ≤ -1/log(1-ε) for t ∈ (0, 1-ε]
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      simp only [Set.mem_Ioc] at ht
      have htpos : 0 < t := ht.1
      have hlogt : log t < 0 := Real.log_neg htpos (by linarith [ht.2])
      have hlog_mono : log t ≤ log (1 - ε) := Real.log_le_log htpos ht.2
      -- ‖1/log t‖ = 1/(-log t) since log t < 0
      rw [norm_div, norm_one, Real.norm_eq_abs, abs_of_neg hlogt]
      -- Goal: 1/(-log t) ≤ -1/log(1-ε)
      -- Both sides are positive; -1/log(1-ε) = 1/(-log(1-ε)) since log(1-ε) < 0
      have heq : -1 / log (1 - ε) = 1 / (-log (1 - ε)) := by ring
      rw [heq]
      -- Goal: 1/(-log t) ≤ 1/(-log(1-ε))
      -- Follows from -log(1-ε) ≤ -log t (since log t ≤ log(1-ε))
      apply one_div_le_one_div_of_le (neg_pos.mpr hlog_neg)
      linarith [hlog_mono]
  · apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun x hx => ne_of_gt (by linarith [hx.1] : (0:ℝ) < x))
    · intro x hx
      apply Real.log_ne_zero_of_pos_of_ne_one (by linarith [hx.1] : 0 < x)
      linarith [hx.1]

/-- The filter tendsto result for the principal value. -/
theorem pv_tendsto_li2_symmetric :
    Filter.Tendsto (fun ε => ∫ t in Set.Ioc 0 2 \ Set.Ioo (1 - ε) (1 + ε), 1 / log t)
      (𝓝[>] 0) (nhds li2_symmetric) := by
  apply Filter.Tendsto.congr' _ limit_integral_g
  filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < 1)] with ε hε
  rw [setDiff_integral_eq_split ε 2 hε.1 hε.2 (by rfl), pv_integral_eq_symmetric ε hε.1 hε.2]

@[blueprint
  "li2-eq"
  (title := "Symmetric form equals principal value")
  (statement := /-- $\int_0^1 \left(\frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}\right) dt = \mathrm{li}(2)$ -/)
  (discussion := 764)]
theorem li2_symmetric_eq_li2 : li2_symmetric = li 2 := by
  exact pv_tendsto_li2_symmetric.limUnder_eq |>.symm

/-- The main result: certified bounds on li(2). -/
theorem li2_bounds : (1039:ℚ)/1000 ≤ li 2 ∧ li 2 ≤ (106:ℚ)/100 := by
  rw [← li2_symmetric_eq_li2]
  exact li2_symmetric_bounds

/-- Proof of li.two_approx_weak from SecondaryDefinitions.lean. -/
theorem li_two_approx_weak_proof : li 2 ∈ Set.Icc 1.039 1.06 := by
  constructor
  · have h := li2_bounds.1
    simp only [Rat.cast_ofNat] at h
    linarith
  · have h := li2_bounds.2
    simp only [Rat.cast_ofNat] at h
    linarith

end Li2Bounds
