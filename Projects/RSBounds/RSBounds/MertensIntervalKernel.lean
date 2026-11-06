import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-!
# The finite-interval kernel for the integrated explicit formula

The difference of two truncated inverse-linear weights has Mellin transform
`(b^(s-1)-a^(s-1))/(s*(s-1))`.  Its numerator vanishes at `s=1`, so the
divided-difference continuation has only the pole at zero.  All statements
here are elementary Mellin/complex-analysis identities; no zero-location or
prime-number estimate is assumed.
-/

open Complex Set MeasureTheory
open scoped Topology

namespace TernaryGoldbach.RSBounds.MertensIntervalKernel

noncomputable def intervalWeight (a b u : ℝ) : ℝ :=
  max (1 / u - 1 / b) 0 - max (1 / u - 1 / a) 0

noncomputable def weight (a b u : ℝ) : ℂ := (intervalWeight a b u : ℂ)

noncomputable def numerator (a b : ℝ) (s : ℂ) : ℂ :=
  (b : ℂ) ^ (s - 1) - (a : ℂ) ^ (s - 1)

noncomputable def H (a b : ℝ) : ℂ → ℂ := dslope (numerator a b) 1

noncomputable def kernel (a b : ℝ) (s : ℂ) : ℂ := H a b s / s

theorem numerator_one (a b : ℝ) : numerator a b 1 = 0 := by
  simp [numerator]

theorem differentiable_numerator {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Differentiable ℂ (numerator a b) := by
  exact ((differentiable_id.sub_const 1).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))).sub
      ((differentiable_id.sub_const 1).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne')))

theorem differentiable_H {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Differentiable ℂ (H a b) := by
  have hh : DifferentiableOn ℂ (H a b) Set.univ :=
    (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 (1 : ℂ))).mpr
      (differentiable_numerator ha hb).differentiableOn
  exact differentiableOn_univ.mp hh

theorem H_eq {a b : ℝ} {s : ℂ} (hs : s ≠ 1) :
    H a b s = numerator a b s / (s - 1) := by
  rw [H, dslope_of_ne _ hs, slope_def_field, numerator_one, sub_zero]

theorem kernel_eq {a b : ℝ} {s : ℂ} (hs : s ≠ 1) :
    kernel a b s = numerator a b s / (s * (s - 1)) := by
  rw [kernel, H_eq hs, div_div]
  congr 1
  ring

theorem H_zero (a b : ℝ) : H a b 0 = (1 / a - 1 / b : ℝ) := by
  rw [H_eq (by norm_num : (0 : ℂ) ≠ 1)]
  simp [numerator, Complex.cpow_neg_one]
  ring

theorem H_one {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    H a b 1 = (Real.log b - Real.log a : ℝ) := by
  have hd := (((hasDerivAt_id (1 : ℂ)).sub_const 1).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))).sub
      (((hasDerivAt_id (1 : ℂ)).sub_const 1).const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne')))
  rw [H, dslope_same]
  change deriv ((fun s : ℂ => (b : ℂ) ^ (s - 1)) -
    fun s : ℂ => (a : ℂ) ^ (s - 1)) 1 = _
  simpa [← Complex.ofReal_log ha.le, ← Complex.ofReal_log hb.le] using hd.deriv

theorem continuousAt_weight (a b : ℝ) {u : ℝ} (hu : 0 < u) :
    ContinuousAt (weight a b) u := by
  unfold weight intervalWeight
  fun_prop (disch := exact hu.ne')

private theorem hasMellin_congr_pos {f g : ℝ → ℂ} {s z : ℂ}
    (hfg : ∀ u : ℝ, 0 < u → f u = g u) (hf : HasMellin f s z) :
    HasMellin g s z := by
  constructor
  · exact (integrableOn_congr_fun
      (fun (u : ℝ) hu => congrArg (fun v : ℂ => (u : ℂ) ^ (s - 1) • v) (hfg u hu))
      measurableSet_Ioi).mp hf.1
  · calc
      mellin g s = mellin f s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change (u : ℂ) ^ (s - 1) • g u = (u : ℂ) ^ (s - 1) • f u
        rw [hfg u hu]
      _ = z := hf.2

private noncomputable def baseWeight (u : ℝ) : ℂ :=
  ((max (1 / u - 1) 0 : ℝ) : ℂ)

private theorem hasMellin_baseWeight {s : ℂ} (hs : 1 < s.re) :
    HasMellin baseWeight s (1 / (s * (s - 1))) := by
  have hm := hasMellin_cpow_Ioc (-1 : ℂ) (s := s) (by simpa using sub_pos.mpr hs)
  have hz := hasMellin_cpow_Ioc (0 : ℂ) (s := s) (by simp; linarith)
  have hd := hasMellin_sub hm.1 hz.1
  rw [hm.2, hz.2] at hd
  have hb : HasMellin baseWeight s (1 / (s + -1) - 1 / (s + 0)) := by
    refine hasMellin_congr_pos (fun u hu => ?_) hd
    by_cases hu1 : u ≤ 1
    · have hmem : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
      have hnonneg : 0 ≤ 1 / u - 1 := by
        rw [sub_nonneg, le_div_iff₀ hu]
        simpa using hu1
      simp only [indicator_of_mem hmem, Complex.cpow_neg_one, Complex.cpow_zero,
        baseWeight, max_eq_left hnonneg]
      push_cast
      simp
    · have hnmem : u ∉ Ioc (0 : ℝ) 1 := fun h => hu1 h.2
      have hnonpos : 1 / u - 1 ≤ 0 := by
        rw [sub_nonpos, div_le_iff₀ hu]
        simpa using (le_of_not_ge hu1)
      simp only [indicator_of_notMem hnmem, sub_zero, baseWeight,
        max_eq_right hnonpos, Complex.ofReal_zero]
  have h0 : s ≠ 0 := by intro h; norm_num [h] at hs
  have h1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [sub_re, one_re, zero_re] at this
    linarith
  convert hb using 1
  simp only [← sub_eq_add_neg, add_zero]
  field_simp [h0, h1]
  ring

private theorem scaled_baseWeight {c u : ℝ} (hc : 0 < c) (hu : 0 < u) :
    baseWeight ((1 / c) * u) / (c : ℂ) = ((max (1 / u - 1 / c) 0 : ℝ) : ℂ) := by
  unfold baseWeight
  rw [← Complex.ofReal_div]
  congr 1
  rw [← max_div_div_right hc.le, zero_div]
  congr 1
  field_simp

private theorem hasMellin_cutoff {c : ℝ} (hc : 0 < c) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (fun u : ℝ => ((max (1 / u - 1 / c) 0 : ℝ) : ℂ)) s
      ((c : ℂ) ^ (s - 1) / (s * (s - 1))) := by
  have hb := hasMellin_baseWeight hs
  have hconv : MellinConvergent (fun u => baseWeight ((1 / c) * u)) s :=
    (MellinConvergent.comp_mul_left (one_div_pos.mpr hc)).mpr hb.1
  have hv : HasMellin (fun u => baseWeight ((1 / c) * u) / (c : ℂ)) s
      (((1 / c : ℝ) : ℂ) ^ (-s) * (1 / (s * (s - 1))) / (c : ℂ)) := by
    refine ⟨hconv.div_const _, ?_⟩
    rw [mellin_div_const, mellin_comp_mul_left _ _ (one_div_pos.mpr hc), hb.2,
      smul_eq_mul]
  have hpow : ((1 / c : ℝ) : ℂ) ^ (-s) / (c : ℂ) = (c : ℂ) ^ (s - 1) := by
    rw [one_div, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hc.le,
      Complex.cpow_neg, inv_inv, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hc.ne'),
      Complex.cpow_one]
  have hv' := hasMellin_congr_pos (fun u hu => scaled_baseWeight hc hu) hv
  convert hv' using 1
  rw [show ((1 / c : ℝ) : ℂ) ^ (-s) * (1 / (s * (s - 1))) / (c : ℂ) =
      (((1 / c : ℝ) : ℂ) ^ (-s) / (c : ℂ)) / (s * (s - 1)) by ring]
  rw [hpow]

/-- The convergent Mellin integral on the right of the cancelled singularity. -/
theorem hasMellin_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) : HasMellin (weight a b) s (kernel a b s) := by
  have haM := hasMellin_cutoff ha hs
  have hbM := hasMellin_cutoff hb hs
  have hd := hasMellin_sub hbM.1 haM.1
  rw [hbM.2, haM.2] at hd
  have hs1 : s ≠ 1 := by intro h; simp [h] at hs
  have heq : weight a b = fun u : ℝ =>
      ((max (1 / u - 1 / b) 0 : ℝ) : ℂ) - ((max (1 / u - 1 / a) 0 : ℝ) : ℂ) := by
    funext u
    simp only [weight, intervalWeight, Complex.ofReal_sub]
  rw [heq, kernel_eq hs1, numerator, sub_div]
  exact hd

theorem mellinConvergent_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) : MellinConvergent (weight a b) s :=
  (hasMellin_weight ha hb hs).1

theorem mellin_weight {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hs : 1 < s.re) : mellin (weight a b) s = kernel a b s :=
  (hasMellin_weight ha hb hs).2

end TernaryGoldbach.RSBounds.MertensIntervalKernel
