import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousFunction.Bounded

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
