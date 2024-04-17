import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousFunction.Bounded
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.Inversion

import PrimeNumberTheoremAnd.Mathlib.Analysis.Fourier.FourierTransformDeriv
import PrimeNumberTheoremAnd.Sobolev

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas

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

end lemmas

theorem fourierIntegral_self_add_deriv_deriv (f : W21) (u : ℝ) :
    (1 + u ^ 2) * 𝓕 f u = 𝓕 (fun u => f u - (1 / (4 * π ^ 2)) * deriv^[2] f u) u := by
  have l1 : Integrable (fun x => (((π : ℂ) ^ 2)⁻¹ * 4⁻¹) * deriv (deriv f) x) := by
    apply Integrable.const_mul ; simpa [iteratedDeriv_succ] using f.integrable le_rfl
  have l4 : Differentiable ℝ f := f.differentiable
  have l5 : Differentiable ℝ (deriv f) := f.deriv.differentiable
  simp [f.hf, l1, add_mul, Real.fourierIntegral_deriv f.hf' l5 f.hf'', Real.fourierIntegral_deriv f.hf l4 f.hf']
  field_simp [pi_ne_zero] ; ring_nf ; simp

@[simp] lemma deriv_ofReal : deriv ofReal' = fun _ => 1 := by
  ext x ; exact ((hasDerivAt_id x).ofReal_comp).deriv

theorem bla (a : ℂ) (f : ℝ → ℂ) (n : ℕ) (hf : ContDiff ℝ n f) :
    iteratedDeriv n (fun x ↦ a * x * f x) = fun x =>
      a * x * iteratedDeriv n f x + n * a * iteratedDeriv (n - 1) f x := by

  induction n with
  | zero => simp
  | succ n ih =>
    have l0 : ContDiff ℝ n f := hf.of_succ
    rw [iteratedDeriv_succ, ih l0] ; ext x
    have l5 : ContDiff ℝ (↑(1 + n)) f := by convert hf using 1 ; simp ; ring
    have l4 : DifferentiableAt ℝ (fun x ↦ iteratedDeriv n f x) x := by
      have := ((l5.iterate_deriv' 1 n).differentiable le_rfl).differentiableAt (x := x)
      simpa [iteratedDeriv_eq_iterate] using this
    have l3 : DifferentiableAt ℝ (fun x ↦ a * ↑x) x := by
      apply DifferentiableAt.const_mul
      exact (contDiff_ofReal.differentiable le_top).differentiableAt
    have l1 : DifferentiableAt ℝ (fun x ↦ a * ↑x * iteratedDeriv n f x) x := l3.mul l4
    have l2 : DifferentiableAt ℝ (fun x ↦ ↑n * a * iteratedDeriv (n - 1) f x) x := by
      apply DifferentiableAt.const_mul
      apply l5.differentiable_iteratedDeriv
      norm_cast ; exact Nat.sub_le _ _ |>.trans_lt (by simp)
    simp [deriv_add l1 l2, deriv_mul l3 l4, ← iteratedDeriv_succ]
    cases n <;> simp <;> ring

noncomputable def MS (a : ℂ) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun x := a * x * f x
  smooth' := contDiff_const.mul contDiff_ofReal |>.mul f.smooth'
  decay' k n := by
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    simp_rw [bla a f n <| f.smooth'.of_le le_top]
    obtain ⟨C₁, hC₁⟩ := f.decay' (k + 1) n
    obtain ⟨C₂, hC₂⟩ := f.decay' k (n - 1)
    use ‖a‖ * C₁ + ‖a‖ * n * C₂ ; intro x
    have l2 := norm_add_le (a * x * iteratedDeriv n f x) (n * a * iteratedDeriv (n - 1) f x)
    have l3 : 0 ≤ ‖x‖ ^ k := by positivity
    apply (mul_le_mul_of_nonneg_left l2 l3).trans ; rw [mul_add] ; apply add_le_add
    · have : 0 ≤ ‖a‖ := by positivity
      convert mul_le_mul_of_nonneg_left (hC₁ x) this using 1
      simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv, abs_eq_self.mpr pi_nonneg] ; ring_nf ; rfl
    · have : 0 ≤ ‖a‖ * n := by positivity
      convert mul_le_mul_of_nonneg_left (hC₂ x) this using 1
      simp [norm_iteratedFDeriv_eq_norm_iteratedDeriv, abs_eq_self.mpr pi_nonneg] ; ring_nf ; rfl

@[simp] lemma MS_apply (a : ℂ) (f : 𝓢(ℝ, ℂ)) (x : ℝ) : MS a f x = (a * x) • f x := rfl

lemma MS_iterate (a : ℂ) (f : 𝓢(ℝ, ℂ)) (n : ℕ) : (MS a)^[n] f = fun x : ℝ => (a * x) ^ n • f x := by
  induction n generalizing f with
  | zero => simp
  | succ n ih => ext x ; simp [ih, pow_succ] ; ring

lemma fourierIntegral_decay_aux (f : ℝ → ℂ) (k : ℕ) (h1 : ContDiff ℝ k f)
    (h2 : ∀ n ≤ k, Integrable (iteratedDeriv n f)) (x : ℝ) :
    ‖(2 * π * I * x) ^ k • 𝓕 f x‖ ≤ (∫ y : ℝ, ‖iteratedDeriv k f y‖) := by
  have l2 (x : ℝ) : (2 * π * I * x) ^ k • 𝓕 f x = 𝓕 (iteratedDeriv k f) x := by
    simp [Real.fourierIntegral_iteratedDeriv h1 (fun n hn => h2 n <| Nat.cast_le.mp hn) le_rfl]
  simpa only [l2] using Fourier.norm_fourierIntegral_le_integral_norm ..

lemma iteratedDeriv_schwartz (f : 𝓢(ℝ, ℂ)) (n : ℕ) : iteratedDeriv n f = (SchwartzMap.derivCLM ℝ)^[n] f := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ, ih, Function.iterate_succ'] ; rfl

theorem fourierIntegral_decay (f : 𝓢(ℝ, ℂ)) (k : ℕ) : ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖𝓕 f x‖ ≤ C := by
  convert_to ∃ C, ∀ x : ℝ, ‖x ^ k * 𝓕 f x‖ ≤ C ; · simp
  convert_to ∃ C, ∀ x : ℝ, ‖(2 * π * I * x) ^ k * 𝓕 f x‖ / (2 * π) ^ k ≤ C using 4
  · field_simp [mul_pow, abs_eq_self.mpr pi_nonneg] ; ring
  convert_to ∃ C, ∀ x : ℝ, ‖(2 * π * I * x) ^ k • 𝓕 f x‖ / (2 * π) ^ k ≤ C
  use (∫ (y : ℝ), ‖iteratedDeriv k (⇑f) y‖) / (2 * π) ^ k ; intro x
  have l1 : ∀ n ≤ k, Integrable (iteratedDeriv n f) volume := by
    simp_rw [iteratedDeriv_schwartz] ; simp [SchwartzMap.integrable]
  have := fourierIntegral_decay_aux f k (f.smooth'.of_le le_top) l1 x
  apply div_le_div_of_nonneg_right this (by positivity)

noncomputable def FS (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) where
  toFun := 𝓕 f
  smooth' := by
    rw [contDiff_top] ; intro n
    apply Real.contDiff_fourierIntegral ; intro k _
    apply SchwartzMap.integrable_pow_mul
  decay' := by
    simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    intro k n
    have l1 (k : ℕ) (_ : k ≤ (n : ℕ∞)) : Integrable (fun x ↦ x ^ k • f x) volume := by
      convert_to Integrable ((MS 1)^[k] f) ; · simp [MS_iterate]
      apply SchwartzMap.integrable
    simp_rw [@Real.iteratedDeriv_fourierIntegral ℂ _ _ f n n l1 le_rfl]
    convert_to ∃ C, ∀ (x : ℝ), ‖x‖ ^ k * ‖𝓕 ((MS (-2 * π * I))^[n] f) x‖ ≤ C ; · simp [MS_iterate]
    apply fourierIntegral_decay

@[simp] lemma FS_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : FS f x = 𝓕 f x := rfl

@[simp] lemma FS_toFun (f : 𝓢(ℝ, ℂ)) : ⇑(FS f) = 𝓕 f := rfl

@[simp] lemma schwarz_reduce (f : ℝ → ℂ) h1 h2 x : SchwartzMap.mk f h1 h2 x = f x := rfl

theorem fourierfourier {f : ℝ → ℂ} (hfi : Integrable f) (hfi' : Integrable (𝓕 f))
    (hfc : Continuous f) (x : ℝ) :
    𝓕 (𝓕 f) x = f (-x) := by
  rw [← MeasureTheory.Integrable.fourier_inversion (v := -x) hfi hfi' hfc.continuousAt]
  simp [fourierIntegralInv, Real.fourierIntegral, VectorFourier.fourierIntegral]

lemma FS4 (f : 𝓢(ℝ, ℂ)) : FS^[4] f = f := by
  have li0 : Integrable (⇑f) volume := f.integrable
  have li1 : Integrable (𝓕 ⇑f) := (FS f).integrable
  have li2 : Integrable (𝓕 (𝓕 ⇑f)) := (FS (FS f)).integrable
  have li3 : Integrable (𝓕 (𝓕 (𝓕 ⇑f))) volume := (FS (FS (FS f))).integrable
  have lc2 : Continuous (𝓕 (𝓕 ⇑f)) := (FS (FS f)).continuous
  ext x ; change 𝓕 (𝓕 (𝓕 (𝓕 f))) x = f x
  rw [fourierfourier li2 li3 lc2, fourierfourier li0 li1 f.continuous]
  simp
