import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

import PrimeNumberTheoremAnd.Mathlib.Analysis.Fourier.FourierTransformDeriv

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap VectorFourier

@[simp]
theorem nnnorm_eq_of_mem_circle (z : circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 (-v * u)
  map_bounded' := ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 (-v * u) := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) : Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable ⟨_, e.norm_coe_le_norm⟩

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourierIntegral_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x :=
  congr_fun (fourierIntegral_add continuous_fourierChar (by exact continuous_mul) hf hg).symm x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simp_rw [sub_eq_add_neg] ; rw [F_add] ; simp ; exact hf ; exact hg.neg

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} : 𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourierIntegral_real_eq, ← integral_mul_left] ; congr ; ext
  simp [Real.fourierChar, expMapCircle] ; ring

structure W21 (f : ℝ → ℂ) : Prop where
  hh : ContDiff ℝ 2 f
  hf : Integrable f
  hf' : Integrable (deriv f)
  hf'' : Integrable (deriv (deriv f))
  h3 : Tendsto f (cocompact ℝ) (𝓝 0)
  h4 : Tendsto (deriv f) (cocompact ℝ) (𝓝 0)

lemma W21.sub {f g : ℝ → ℂ} (hf : W21 f) (hg : W21 g) : W21 (f - g) := by
  have l1 : deriv (f - g) = deriv f - deriv g := by
    ext x ; apply deriv_sub
    · exact (hf.hh.differentiable one_le_two).differentiableAt
    · exact (hg.hh.differentiable one_le_two).differentiableAt
  have l2 : deriv (deriv (f - g)) = deriv (deriv f) - deriv (deriv g) := by
    rw [l1] ; ext x ; apply deriv_sub
    · exact (hf.hh.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt
    · exact (hg.hh.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt
  refine ⟨hf.hh.sub hg.hh, hf.hf.sub hg.hf, ?_, ?_, ?_, ?_⟩
  · simpa [l1] using hf.hf'.sub hg.hf'
  · simpa [l2] using hf.hf''.sub hg.hf''
  · simpa using hf.h3.sub hg.h3
  · simpa [l1] using hf.h4.sub hg.h4

noncomputable def W21.norm (f : ℝ → ℂ) : ℝ := (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

lemma W21.norm_nonneg {f : ℝ → ℂ} : 0 ≤ W21.norm f :=
  add_nonneg (integral_nonneg (fun t => by simp)) (mul_nonneg (by positivity) (integral_nonneg (fun t => by simp)))

noncomputable def W21_of_schwartz (f : 𝓢(ℝ, ℂ)) : W21 f where
  hh := f.smooth 2
  hf := f.integrable
  hf' := (SchwartzMap.derivCLM ℝ f).integrable
  hf'' := (SchwartzMap.derivCLM ℝ (SchwartzMap.derivCLM ℝ f)).integrable
  h3 := f.toZeroAtInfty.zero_at_infty'
  h4 := (SchwartzMap.derivCLM ℝ f).toZeroAtInfty.zero_at_infty'

noncomputable def W21_of_compactSupport {f : ℝ → ℂ} (h1 : ContDiff ℝ 2 f) (h2 : HasCompactSupport f) : W21 f where
  hh := h1
  hf := h1.continuous.integrable_of_hasCompactSupport h2
  hf' := (h1.continuous_deriv one_le_two).integrable_of_hasCompactSupport h2.deriv
  hf'' := (h1.iterate_deriv' 0 2).continuous.integrable_of_hasCompactSupport h2.deriv.deriv
  h3 := h2.is_zero_at_infty
  h4 := h2.deriv.is_zero_at_infty

theorem fourierIntegral_self_add_deriv_deriv {f : ℝ → ℂ} (hf : W21 f) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 f u = 𝓕 (fun u => f u - (1 / (4 * π ^ 2)) * deriv^[2] f u) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := (hf.hf''.const_mul _)
  have l4 : Differentiable ℝ f := hf.hh.differentiable one_le_two
  have l5 : Differentiable ℝ (deriv f) := (hf.hh.iterate_deriv' 1 1).differentiable le_rfl
  simp [hf.hf, l1, add_mul, Real.fourierIntegral_deriv hf.hf' l5 hf.hf'', Real.fourierIntegral_deriv hf.hf l4 hf.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

structure trunc (g : ℝ → ℝ) : Prop :=
  h1 : ContDiff ℝ ⊤ g
  h2 : HasCompactSupport g
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ g
  h4 : g ≤ Set.indicator (Set.Ioo (-2) (2)) 1

lemma W21.mul_compact_support {f g : ℝ → ℂ} (hf : W21 f) (hg1 : ContDiff ℝ 2 g) (hg2 : HasCompactSupport g) :
    W21 (fun x => g x * f x) := by

  let f' := deriv f
  let f'' := deriv (deriv f)
  have f_d x : HasDerivAt f (f' x) x := hf.hh.differentiable one_le_two |>.differentiableAt.hasDerivAt
  have f_i : Integrable f := hf.hf
  have f'_d x : HasDerivAt f' (f'' x) x := (hf.hh.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt.hasDerivAt
  have f'_i : Integrable f' := hf.hf'
  have f''_i : Integrable f'' := hf.hf''

  let g' := deriv g
  let g'' := deriv (deriv g)
  have g_0 : g =ᶠ[cocompact ℝ] 0 := by simpa using hasCompactSupport_iff_eventuallyEq.mp hg2
  have g_c : Continuous g := hg1.continuous
  have g_b : ∃ C, ∀ x, ‖g x‖ ≤ C := g_c.bounded_above_of_compact_support hg2
  have g_d x : HasDerivAt g (g' x) x := hg1.differentiable one_le_two |>.differentiableAt.hasDerivAt
  have g_a : AEStronglyMeasurable g volume := g_c.aestronglyMeasurable
  have g'_0 : g' =ᶠ[cocompact ℝ] 0 := by simpa using hasCompactSupport_iff_eventuallyEq.mp hg2.deriv
  have g'_c : Continuous g' := hg1.continuous_deriv one_le_two
  have g'_d x : HasDerivAt g' (g'' x) x := (hg1.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt.hasDerivAt
  have g'_a : AEStronglyMeasurable g' volume := g'_c.aestronglyMeasurable
  have g'_b : ∃ C, ∀ x, ‖g' x‖ ≤ C := g'_c.bounded_above_of_compact_support hg2.deriv
  have g''_c : Continuous g'' := hg1.iterate_deriv' 0 2 |>.continuous
  have g''_a : AEStronglyMeasurable g'' volume := g''_c.aestronglyMeasurable
  have g''_b : ∃ C, ∀ x, ‖g'' x‖ ≤ C := g''_c.bounded_above_of_compact_support hg2.deriv.deriv

  let h := fun x => g x * f x
  let h' := fun x => g' x * f x + g x * f' x
  let h'' := fun x => g'' x * f x + 2 * g' x * f' x + g x * f'' x
  have h_d x : HasDerivAt h (h' x) x := (g_d x).mul (f_d x)
  have h_d' : deriv h = h' := funext (fun x => (h_d x).deriv)
  have h'_d x : HasDerivAt h' (h'' x) x := by
    convert ((g'_d x).mul (f_d x)).add ((g_d x).mul (f'_d x)) using 1 ; simp [h', h''] ; ring
  have h'_d' : deriv h' = h'' := funext (fun x => (h'_d x).deriv)

  refine ⟨hg1.mul hf.hh, ?_, ?_, ?_, ?_, ?_⟩
  · exact hf.hf.bdd_mul g_c.aestronglyMeasurable g_b
  · rw [h_d'] ; exact (f_i.bdd_mul g'_a g'_b).add (f'_i.bdd_mul g_a g_b)
  · rw [h_d', h'_d'] ; refine Integrable.add ?_ (f''_i.bdd_mul g_a g_b)
    apply (f_i.bdd_mul g''_a g''_b).add
    simp_rw [mul_assoc] ; apply (f'_i.bdd_mul g'_a g'_b).const_mul
  · apply tendsto_nhds_of_eventually_eq ; filter_upwards [g_0] with x hgx ; simp [hgx]
  · simp only [h_d', h'] ; apply tendsto_nhds_of_eventually_eq
    filter_upwards [g_0, g'_0] with x hgx hg'x; simp [hgx, hg'x]

theorem W21_approximation {f : ℝ → ℂ} (hf : W21 f) {g : ℝ → ℝ} (hg : trunc g) :
    Tendsto (fun R => W21.norm (fun v => (1 - g (v * R⁻¹)) * f v)) atTop (𝓝 0) := by

  -- Preliminaries
  have cR {R : ℝ} : Continuous (fun v => v * R⁻¹) := continuous_id.mul continuous_const
  have vR v : Tendsto (fun R : ℝ => v * R⁻¹) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.const_mul v

  -- About f
  let f' v := deriv f v
  let f'' v := deriv (deriv f) v
  have cf : Continuous f := hf.hh.continuous
  have cf' : Continuous f' := (hf.hh.iterate_deriv' 1 1).continuous
  have cf'' : Continuous f'' := (hf.hh.iterate_deriv' 0 2).continuous
  have df v : HasDerivAt f (f' v) v := hf.hh.differentiable one_le_two |>.differentiableAt.hasDerivAt
  have df' v : HasDerivAt f' (f'' v) v := (hf.hh.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt.hasDerivAt

  -- About g
  let g' := deriv g
  let g'' v := deriv (deriv g) v
  have cg : Continuous g := hg.h1.continuous
  have cg' : Continuous g' := (hg.h1.iterate_deriv 1).continuous
  have cg'' : Continuous g'' := (hg.h1.iterate_deriv 2).continuous
  have dg v : HasDerivAt g (g' v) v := hg.h1.hasStrictDerivAt le_top |>.hasDerivAt
  have dg' v : HasDerivAt g' (g'' v) v := (hg.h1.iterate_deriv 1).hasStrictDerivAt le_top |>.hasDerivAt
  have mg' : ∃ c1, ∀ v, |g' v| ≤ c1 := by
    obtain ⟨x, hx⟩ := cg'.abs.exists_forall_ge_of_hasCompactSupport hg.h2.deriv.norm ; exact ⟨_, hx⟩
  have mg'' : ∃ c2, ∀ v, |g'' v| ≤ c2 := by
    obtain ⟨x, hx⟩ := cg''.abs.exists_forall_ge_of_hasCompactSupport hg.h2.deriv.deriv.norm ; exact ⟨_, hx⟩
  obtain ⟨c1, mg'⟩ := mg' ; obtain ⟨c2, mg''⟩ := mg''

  have g0 v : 0 ≤ g v := by have := hg.h3 v ; by_cases h : v ∈ Set.Icc (-1) 1 <;> simp [h] at this <;> linarith
  have g1 v : g v ≤ 1 := by have := hg.h4 v ; by_cases h : v ∈ Set.Ioo (-2) 2 <;> simp [h] at this <;> linarith
  have evg : g =ᶠ[𝓝 0] 1 := by
    have : Set.Icc (-1) 1 ∈ 𝓝 (0 : ℝ) := by apply Icc_mem_nhds <;> linarith
    exact eventually_of_mem this (fun x hx => le_antisymm (g1 x) (by simpa [hx] using hg.h3 x))
  have evg' : g' =ᶠ[𝓝 0] 0 := by convert ← evg.deriv ; exact deriv_const' _
  have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert ← evg'.deriv ; exact deriv_const' _

  -- About h
  let h R v := 1 - g (v * R⁻¹)
  let h' R v := - g' (v * R⁻¹) * R⁻¹
  let h'' R v := - g'' (v * R⁻¹) * R⁻¹ * R⁻¹
  have ch {R} : Continuous (fun v => (h R v : ℂ)) := continuous_ofReal.comp <| continuous_const.sub <| cg.comp cR
  have ch' {R} : Continuous (fun v => (h' R v : ℂ)) := continuous_ofReal.comp <| (cg'.comp cR).neg.mul continuous_const
  have ch'' {R} : Continuous (fun v => (h'' R v : ℂ)) :=
    continuous_ofReal.comp <| ((cg''.comp cR).neg.mul continuous_const).mul continuous_const
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h'] using ((dg _).comp _ <| hasDerivAt_mul_const _).const_sub _
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := by
    simpa [h', h''] using HasDerivAt.mul_const ((dg' _).comp _ <| hasDerivAt_mul_const _).neg (R⁻¹)
  have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
    filter_upwards [eventually_ge_atTop 1] with R hR v
    have : 0 ≤ R := by linarith
    simp [h', abs_mul, abs_inv, abs_eq_self.mpr this]
    convert_to _ ≤ c1 * 1 ; simp
    apply mul_le_mul (mg' _) (inv_le_of_inv_le (by linarith) (by simpa using hR)) (by positivity)
    exact (abs_nonneg _).trans (mg' 0)
  have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
    filter_upwards [eventually_ge_atTop 1] with R hR v
    have e1 : 0 ≤ R := by linarith
    have e2 : R⁻¹ ≤ 1 := inv_le_of_inv_le (by linarith) (by simpa using hR)
    simp [h'', abs_mul, abs_inv, abs_eq_self.mpr e1, mul_assoc]
    convert_to _ ≤ c2 * (1 * 1) ; simp
    apply mul_le_mul (mg'' _) ?_ (by positivity) ((abs_nonneg _).trans (mg'' 0))
    exact mul_le_mul e2 e2 (by positivity) zero_le_one

  have h0 R v : 0 ≤ h R v := by simpa [h] using g1 _
  have h1 R v : h R v ≤ 1 := by simpa [h] using g0 _
  have hh1 R v : |h R v| ≤ 1 := by rw [abs_le] ; constructor <;> linarith [h0 R v, h1 R v]
  have eh v : ∀ᶠ R in atTop, h R v = 0 := by filter_upwards [(vR v).eventually evg] with R hR ; simp [h, hR]
  have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by filter_upwards [(vR v).eventually evg'] with R hR ; simp [h', hR]
  have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by filter_upwards [(vR v).eventually evg''] with R hR ; simp [h'', hR]

  -- Computations
  have l16 R v : deriv (deriv (fun v => h R v * f v)) v = h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
    have l3 v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v := (dh R v).ofReal_comp.mul (df v)
    have l5 : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v := (dh' R v).ofReal_comp.mul (df v)
    have l7 : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v := (dh R v).ofReal_comp.mul (df' v)
    have d1 : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v := funext (fun v => (l3 v).deriv)
    rw [d1] ; convert (l5.add l7).deriv using 1 ; ring

  -- Proof
  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0) ; simp [h]
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖h R v * f v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply eventually_of_forall ; intro R
      exact (ch.mul hf.hh.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply eventually_of_forall ; intro R
      apply eventually_of_forall ; intro v
      simpa [F] using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply eventually_of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 hf.hf.norm e4
  · simp_rw [l16]
    let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply eventually_of_forall ; intro R
      exact (((ch''.mul cf).add ((continuous_const.mul ch').mul cf')).add (ch.mul cf'')).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ bound a := by
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply eventually_of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp <;> gcongr
      · simpa using mul_le_mul (hh1 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume := (((hf.hf.norm).const_mul _).add ((hf.hf'.norm).const_mul _)).add hf.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply eventually_of_forall ; intro v
      refine tendsto_norm_zero.comp <| (ZeroAtFilter.add ?_ ?_).add ?_
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh'' v] with R hR ; simp [hR]
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh' v] with R hR ; simp [hR]
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4

-- Things we should use, most of them from Sébastien Gouëzel:
-- Real.iteratedDeriv_fourierIntegral
-- Real.fourierIntegral_iteratedDeriv
-- contDiff_fourierIntegral

noncomputable def FS (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun := 𝓕 f
  smooth' := sorry
  decay' := sorry
