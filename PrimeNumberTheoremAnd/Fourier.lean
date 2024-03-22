import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap VectorFourier

@[simp]
theorem nnnorm_eq_of_mem_circle (z : circle) : ‖z.val‖₊ = 1 := NNReal.coe_eq_one.mp (by simp)

@[simp]
theorem nnnorm_circle_smul (z : circle) (s : ℂ) : ‖z • s‖₊ = ‖s‖₊ := by
  simp [show z • s = z.val * s from rfl]

noncomputable def e (u : ℝ) : ℝ →ᵇ ℂ where
  toFun v := 𝐞 [-v * u]
  continuous_toFun := by simp only [Multiplicative.ofAdd] ; have := continuous_fourierChar ; continuity
  map_bounded' := ⟨2, fun x y => (dist_le_norm_add_norm _ _).trans (by simp [one_add_one_eq_two])⟩

@[simp] lemma e_apply (u : ℝ) (v : ℝ) : e u v = 𝐞 [-v * u] := rfl

theorem hasDerivAt_e {u x : ℝ} : HasDerivAt (e u) (-2 * π * u * I * e u x) x := by
  have l2 : HasDerivAt (fun v => -v * u) (-u) x := by simpa only [neg_mul_comm] using hasDerivAt_mul_const (-u)
  convert (hasDerivAt_fourierChar (-x * u)).scomp x l2 using 1
  simp ; ring

lemma fourierIntegral_deriv_aux2 (e : ℝ →ᵇ ℂ) {f : ℝ → ℂ} (hf : Integrable f) : Integrable (⇑e * f) :=
  hf.bdd_mul e.continuous.aestronglyMeasurable ⟨_, e.norm_coe_le_norm⟩

lemma fourierIntegral_deriv_aux1 (e : ℝ →ᵇ ℂ) (ψ : 𝓢(ℝ, ℂ)) : Integrable (⇑e * ⇑ψ) :=
  fourierIntegral_deriv_aux2 e ψ.integrable

theorem fourierIntegral_deriv {f f' : ℝ → ℂ} (h1 : ∀ x, HasDerivAt f (f' x) x) (h2 : Integrable f)
    (h3 : Integrable f') (h4 : Tendsto f (cocompact ℝ) (𝓝 0)) (u : ℝ) :
    𝓕 f' u = 2 * π * I * u * 𝓕 f u := by
  convert_to ∫ v, e u v * f' v = 2 * ↑π * I * ↑u * ∫ v, e u v * f v
    <;> try { simp [fourierIntegral_real_eq] }
  have l1 (x) : HasDerivAt (e u) (-2 * π * u * I * e u x) x := hasDerivAt_e
  have l3 : Integrable (⇑(e u) * f') := fourierIntegral_deriv_aux2 (e u) h3
  have l4 : Integrable (fun x ↦ -2 * π * u * I * e u x * f x) := by
    simpa [mul_assoc] using (fourierIntegral_deriv_aux2 (e u) h2).const_mul (-2 * π * u * I)
  have l7 : Tendsto (⇑(e u) * f) (cocompact ℝ) (𝓝 0) := by
    simpa [tendsto_zero_iff_norm_tendsto_zero] using h4
  have l5 : Tendsto (⇑(e u) * f) atBot (𝓝 0) := l7.mono_left _root_.atBot_le_cocompact
  have l6 : Tendsto (⇑(e u) * f) atTop (𝓝 0) := l7.mono_left _root_.atTop_le_cocompact
  rw [integral_mul_deriv_eq_deriv_mul l1 h1 l3 l4 l5 l6]
  simp [integral_neg, ← integral_mul_left] ; congr ; ext ; ring

theorem fourierIntegral_deriv_schwartz (ψ : 𝓢(ℝ, ℂ)) (u : ℝ) : 𝓕 (deriv ψ) u = 2 * π * I * u * 𝓕 ψ u :=
  fourierIntegral_deriv (fun _ => ψ.differentiableAt.hasDerivAt) ψ.integrable
    (SchwartzMap.derivCLM ℝ ψ).integrable ψ.toZeroAtInfty.zero_at_infty' u

theorem fourierIntegral_deriv_compactSupport {f : ℝ → ℂ} (h1 : ContDiff ℝ 1 f) (h2 : HasCompactSupport f) (u : ℝ) :
    𝓕 (deriv f) u = 2 * π * I * u * 𝓕 f u := by
  have l1 (x) : HasDerivAt f (deriv f x) x := (h1.differentiable le_rfl).differentiableAt.hasDerivAt
  have l2 : Integrable f := h1.continuous.integrable_of_hasCompactSupport h2
  have l3 : Integrable (deriv f) := (h1.continuous_deriv le_rfl).integrable_of_hasCompactSupport h2.deriv
  exact fourierIntegral_deriv l1 l2 l3 h2.is_zero_at_infty u

@[simp] lemma F_neg {f : ℝ → ℂ} {u : ℝ} : 𝓕 (fun x => -f x) u = - 𝓕 f u := by
  simp [fourierIntegral_eq, integral_neg]

@[simp] lemma F_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x + g x) x = 𝓕 f x + 𝓕 g x :=
  congr_fun (fourierIntegral_add continuous_fourierChar (by exact continuous_mul) hf hg).symm x

@[simp] lemma F_sub {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (x : ℝ) :
    𝓕 (fun x => f x - g x) x = 𝓕 f x - 𝓕 g x := by
  simp_rw [sub_eq_add_neg] ; rw [F_add] ; simp ; exact hf ; exact hg.neg

@[simp] lemma F_mul {f : ℝ → ℂ} {c : ℂ} {u : ℝ} : 𝓕 (fun x => c * f x) u = c * 𝓕 f u := by
  simp [fourierIntegral_eq, ← integral_mul_left] ; congr ; ext ; ring

structure W21 (f : ℝ → ℂ) : Prop where
  hh : ContDiff ℝ 2 f
  hf : Integrable f
  hf' : Integrable (deriv f)
  hf'' : Integrable (deriv (deriv f))
  h3 : Tendsto f (cocompact ℝ) (𝓝 0)
  h4 : Tendsto (deriv f) (cocompact ℝ) (𝓝 0)

noncomputable def W21.norm (f : ℝ → ℂ) : ℝ := (∫ v, ‖f v‖) + (4 * π ^ 2)⁻¹ * (∫ v, ‖deriv (deriv f) v‖)

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
  have l2 x : HasDerivAt f (deriv f x) x := hf.hh.differentiable one_le_two |>.differentiableAt.hasDerivAt
  have l3 x : HasDerivAt (deriv f) (deriv (deriv f) x) x := by
    exact (hf.hh.iterate_deriv' 1 1).differentiable le_rfl |>.differentiableAt.hasDerivAt
  simp [hf.hf, l1, add_mul, fourierIntegral_deriv l2 hf.hf hf.hf' hf.h3, fourierIntegral_deriv l3 hf.hf' hf.hf'' hf.h4]
  field_simp [pi_ne_zero] ; ring_nf ; simp

structure trunc (g : ℝ → ℝ) : Prop :=
  h1 : ContDiff ℝ ⊤ g
  h2 : HasCompactSupport g
  h3 : (Set.Icc (-1) (1)).indicator 1 ≤ g
  h4 : g ≤ Set.indicator (Set.Ioo (-2) (2)) 1

theorem W21_approximation {f : ℝ → ℂ} (hf : W21 f) {g : ℝ → ℝ} (hg : trunc g) :
    Tendsto (fun R => W21.norm (fun v => (1 - g (v * R⁻¹)) * f v)) atTop (𝓝 0) := by

  -- Preliminaries
  have cR {R : ℝ} : Continuous (fun v => v * R⁻¹) := continuous_id.mul continuous_const

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
    refine eventually_of_mem this (fun x hx => ?_)
    have e2 : 1 ≤ g x := by simpa [hx] using hg.h3 x
    apply le_antisymm (g1 x) e2
  have evg' : g' =ᶠ[𝓝 0] 0 := by convert ← evg.deriv ; exact deriv_const' _
  have evg'' : g'' =ᶠ[𝓝 0] 0 := by convert ← evg'.deriv ; exact deriv_const' _

  -- About h
  let h R v := 1 - g (v * R⁻¹)
  let h' R v := - g' (v * R⁻¹) * R⁻¹
  let h'' R v := - g'' (v * R⁻¹) * R⁻¹ * R⁻¹
  have ch {R} : Continuous (h R) := continuous_const.sub <| cg.comp cR
  have ch' {R} : Continuous (h' R) := (cg'.comp cR).neg.mul continuous_const
  have ch'' {R} : Continuous (h'' R) := ((cg''.comp cR).neg.mul continuous_const).mul continuous_const
  have dh R v : HasDerivAt (h R) (h' R v) v := by
    simpa [h, h'] using ((dg _).comp _ <| hasDerivAt_mul_const _).const_sub _
  have dh' R v : HasDerivAt (h' R) (h'' R v) v := by
    simpa [h', h''] using HasDerivAt.mul_const ((dg' _).comp _ <| hasDerivAt_mul_const _).neg (R⁻¹)

  have hc1 : ∀ᶠ R in atTop, ∀ v, |h' R v| ≤ c1 := by
    filter_upwards [eventually_ge_atTop 1] with R hR v
    have : 0 ≤ R := by linarith
    simp [h', abs_mul, abs_inv, abs_eq_self.mpr this]
    rw [mul_inv_le_iff (by linarith)]
    have := mg' (v * R⁻¹)
    refine this.trans ?_
    convert_to (1 * c1 ≤ R * c1) ; simp
    gcongr
    exact (abs_nonneg _).trans this
  have hc2 : ∀ᶠ R in atTop, ∀ v, |h'' R v| ≤ c2 := by
    filter_upwards [eventually_ge_atTop 1] with R hR v
    have : 0 ≤ R := by linarith
    simp [h'', abs_mul, abs_inv, abs_eq_self.mpr this, mul_assoc]
    convert_to _ ≤ c2 * (1 * 1) ; simp
    apply mul_le_mul (mg'' _) ?_ (by positivity) ?_
    · apply mul_le_mul
      · apply inv_le_of_inv_le (by linarith) (by simpa using hR)
      · apply inv_le_of_inv_le (by linarith) (by simpa using hR)
      · positivity
      · exact zero_le_one
    · exact (abs_nonneg _).trans (mg'' 0)

  have l9 R v : 0 ≤ h R v := by simpa [h] using g1 _
  have l10 R v : h R v ≤ 1 := by simpa [h] using g0 _
  have l11 R v : |h R v| ≤ 1 := by
    rw [abs_le] ; constructor <;> linarith [l9 R v, l10 R v]
  have eh v : ∀ᶠ R in atTop, h R v = 0 := by
    have e1 : Tendsto (fun R => v * R⁻¹) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.const_mul v
    filter_upwards [e1.eventually evg] with R hR ; simp [h, hR]
  have eh' v : ∀ᶠ R in atTop, h' R v = 0 := by
    have e1 : Tendsto (fun R => v * R⁻¹) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.const_mul v
    filter_upwards [e1.eventually evg'] with R hR ; simp [h', hR]
  have eh'' v : ∀ᶠ R in atTop, h'' R v = 0 := by
    have e1 : Tendsto (fun R => v * R⁻¹) atTop (𝓝 0) := by simpa using tendsto_inv_atTop_zero.const_mul v
    filter_upwards [e1.eventually evg''] with R hR ; simp [h'', hR]

  have l3 R v : HasDerivAt (fun v => h R v * f v) (h' R v * f v + h R v * f' v) v := (dh R v).ofReal_comp.mul (df v)
  have l5 R v : HasDerivAt (fun v => h' R v * f v) (h'' R v * f v + h' R v * f' v) v := (dh' R v).ofReal_comp.mul (df v)
  have l7 R v : HasDerivAt (fun v => h R v * f' v) (h' R v * f' v + h R v * f'' v) v := (dh R v).ofReal_comp.mul (df' v)

  have d1 R : deriv (fun v => h R v * f v) = fun v => h' R v * f v + h R v * f' v := funext (fun v => (l3 R v).deriv)

  have l16 R v : deriv (deriv (fun v => h R v * f v)) v = h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v := by
    rw [d1] ; convert ((l5 R v).add (l7 R v)).deriv using 1 ; ring

  convert_to Tendsto (fun R => W21.norm (fun v => h R v * f v)) atTop (𝓝 0) ; simp [h]
  rw [show (0 : ℝ) = 0 + ((4 * π ^ 2)⁻¹ : ℝ) * 0 by simp]
  refine Tendsto.add ?_ (Tendsto.const_mul _ ?_)
  · let F R v := ‖h R v * f v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply eventually_of_forall ; intro R
      exact ((continuous_ofReal.comp ch).mul hf.hh.continuous).norm.aestronglyMeasurable
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ ‖f a‖ := by
      apply eventually_of_forall ; intro R
      apply eventually_of_forall ; intro v
      simpa [F] using mul_le_mul (l11 R v) le_rfl (by simp) zero_le_one
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply eventually_of_forall ; intro v
      apply tendsto_nhds_of_eventually_eq
      filter_upwards [eh v] with R hR ; simp [F, hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence _ e1 e2 hf.hf.norm e4
  · simp_rw [l16]
    let F R v := ‖h'' R v * f v + 2 * h' R v * f' v + h R v * f'' v‖
    let bound v := c2 * ‖f v‖ + 2 * c1 * ‖f' v‖ + ‖f'' v‖
    have e1 : ∀ᶠ (n : ℝ) in atTop, AEStronglyMeasurable (F n) volume := by
      apply eventually_of_forall ; intro R ; refine ((Continuous.add ?_ ?_).add ?_).norm.aestronglyMeasurable
      · exact (continuous_ofReal.comp ch'').mul cf
      · exact (continuous_const.mul (continuous_ofReal.comp ch')).mul cf'
      · exact (continuous_ofReal.comp ch).mul cf''
    have e2 : ∀ᶠ (n : ℝ) in atTop, ∀ᵐ (a : ℝ), ‖F n a‖ ≤ bound a := by
      filter_upwards [hc1, hc2] with R hc1 hc2
      apply eventually_of_forall ; intro v ; specialize hc1 v ; specialize hc2 v
      simp only [F, bound, norm_norm]
      refine (norm_add_le _ _).trans ?_ ; apply add_le_add
      · refine (norm_add_le _ _).trans ?_ ; apply add_le_add <;> simp <;> gcongr
      · simpa using mul_le_mul (l11 R v) le_rfl (by simp) zero_le_one
    have e3 : Integrable bound volume := (((hf.hf.norm).const_mul _).add ((hf.hf'.norm).const_mul _)).add hf.hf''.norm
    have e4 : ∀ᵐ (a : ℝ), Tendsto (fun n ↦ F n a) atTop (𝓝 0) := by
      apply eventually_of_forall ; intro v
      apply tendsto_norm_zero.comp
      change ZeroAtFilter _ _
      refine (ZeroAtFilter.add ?_ ?_).add ?_
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh'' v] with R hR ; simp [hR]
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh' v] with R hR ; simp [hR]
      · apply tendsto_nhds_of_eventually_eq ; filter_upwards [eh v] with R hR ; simp [hR]
    simpa [F] using tendsto_integral_filter_of_dominated_convergence bound e1 e2 e3 e4
