/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Function.L1Space

import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Derivatives of the Fourier transform

In this file we compute the Fréchet derivative of the Fourier transform of `f`, where `f` is a
function such that both `f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here the Fourier transform is
understood as an operator `(V → E) → (W → E)`, where `V` and `W` are normed `ℝ`-vector spaces
and the Fourier transform is taken with respect to a continuous `ℝ`-bilinear
pairing `L : V × W → ℝ` and a given reference measure `μ`.

We also investigate higher derivatives: Assuming that `‖v‖^n * ‖f v‖` is integrable, we show
that the Fourier transform of `f` is `C^n`.

We also study in a parallel way the Fourier transform of the derivative, which is obtained by
tensoring the Fourier transform of the original function with the bilinear form.

We give specialized versions of these results on inner product spaces (where `L` is the scalar
product) and on the real line, where we express the one-dimensional derivative in more concrete
terms, as the Fourier transform of `-2πI x * f x` (or `(-2πI x)^n * f x` for higher derivatives).

## Main definitions and results

We introduce two convenience definitions:

* `VectorFourier.fourierSMulRight L f`: given `f : V → E` and `L` a bilinear pairing
  between `V` and `W`, then this is the function `fun v ↦ -(2 * π * I) (L v ⬝) • f v`,
  from `V` to `Hom (W, E)`.
  This is essentially `ContinousLinearMap.smulRight`, up to the factor `- 2πI` designed to make sure
  that the Fourier integral of `fourierSMulRight L f` is the derivative of the Fourier
  integral of `f`.
* `VectorFourier.fourierPowSMulRight` is the higher order analogue for higher derivatives:
  `fourierPowSMulRight L f v n` is informally `(-(2 * π * I))^n (L v ⬝)^n • f v`, in
  the space of continuous multilinear maps `W [×n]→L[ℝ] E`.

With these definitions, the statements read as follows, first in a general context
(arbitrary `L` and `μ`):

* `VectorFourier.hasFDerivAt_fourierIntegral`: the Fourier integral of `f` is differentiable, with
    derivative the Fourier integral of `fourierSMulRight L f`.
* `VectorFourier.differentiable_fourierIntegral`: the Fourier integral of `f` is differentiable.
* `VectorFourier.fderiv_fourierIntegral`: formula for the derivative of the Fourier integral of `f`.
* `VectorFourier.fourierIntegral_fderiv`: formula for the Fourier integral of the derivative of `f`.
* `VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` has an explicit Taylor series up to order `N`, given by the Fourier
  integrals of `fun v ↦ fourierPowSMulRight L f v n`.
* `VectorFourier.contDiff_fourierIntegral`: under suitable integrability conditions,
  the Fourier integral of `f` is `C^n`.
* `VectorFourier.iteratedFDeriv_fourierIntegral`: under suitable integrability conditions,
  explicit formula for the `n`-th derivative of the Fourier integral of `f`, as the Fourier
  integral of `fun v ↦ fourierPowSMulRight L f v n`.

These statements are then specialized to the case of the usual Fourier transform on
finite-dimensional inner product spaces with their canonical Lebesgue measure (covering in
particular the case of the real line), replacing the namespace `VectorFourier` by
the namespace `Real` in the above statements.

We also give specialized versions of the one-dimensional real derivative (and iterated derivative)
in `Real.deriv_fourierIntegral` and `Real.iteratedDeriv_fourierIntegral`.
-/

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology BigOperators

-- without this local instance, Lean tries first the instance
-- `secondCountableTopologyEither_of_right` (whose priority is 100) and takes a very long time to
-- fail. Since we only use the left instance in this file, we make sure it is tried first.
attribute [local instance 101] secondCountableTopologyEither_of_left

namespace Real

lemma differentiable_fourierChar : Differentiable ℝ (𝐞 · : ℝ → ℂ) :=
  fun x ↦ (Real.hasDerivAt_fourierChar x).differentiableAt

lemma deriv_fourierChar (x : ℝ) : deriv (𝐞 · : ℝ → ℂ) x = 2 * π * I * 𝐞 x :=
  (Real.hasDerivAt_fourierChar x).deriv

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ)

lemma hasFDerivAt_fourierChar_neg_bilinear_right (v : V) (w : W) :
    HasFDerivAt (fun w ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L v))) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert (hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg
  ext y
  simp only [neg_mul, ContinuousLinearMap.coe_smul', ContinuousLinearMap.coe_comp', Pi.smul_apply,
    Function.comp_apply, ofRealCLM_apply, smul_eq_mul, ContinuousLinearMap.comp_neg,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, real_smul, neg_inj]
  ring

lemma fderiv_fourierChar_neg_bilinear_right_apply (v : V) (w y : W) :
    fderiv ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) w y = -2 * π * I * L v y * 𝐞 (-L v w) := by
  simp [(hasFDerivAt_fourierChar_neg_bilinear_right L v w).fderiv]
  ring

lemma differentiable_fourierChar_neg_bilinear_right (v : V) :
    Differentiable ℝ (fun w ↦ (𝐞 (-L v w) : ℂ)) :=
  fun w ↦ (hasFDerivAt_fourierChar_neg_bilinear_right L v w).differentiableAt

lemma hasFDerivAt_fourierChar_neg_bilinear_left (v : V) (w : W) :
    HasFDerivAt (fun v ↦ (𝐞 (-L v w) : ℂ))
      ((-2 * π * I * 𝐞 (-L v w)) • (ofRealCLM ∘L (L.flip w))) v :=
  hasFDerivAt_fourierChar_neg_bilinear_right L.flip w v

lemma fderiv_fourierChar_neg_bilinear_left_apply (v y : V) (w : W) :
    fderiv ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) v y = -2 * π * I * L y w * 𝐞 (-L v w) := by
  simp [(hasFDerivAt_fourierChar_neg_bilinear_left L v w).fderiv]
  ring

lemma differentiable_fourierChar_neg_bilinear_left (w : W) :
    Differentiable ℝ (fun v ↦ (𝐞 (-L v w) : ℂ)) :=
  fun v ↦ (hasFDerivAt_fourierChar_neg_bilinear_left L v w).differentiableAt

end Real

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

variable {f}

/-- The Fourier integral of the derivative of a function is obtained by multiplying the Fourier
integral of the original function by `-L w v`. -/
theorem fourierIntegral_fderiv [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ]
    (hf : Integrable f μ) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f) μ) :
    fourierIntegral 𝐞 μ L.toLinearMap₂ (fderiv ℝ f)
      = fourierSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₂ f) := by
  ext w y
  let g : V → ℂ := fun v ↦ 𝐞 (-L v w)
  have J : Integrable (fun v ↦ 𝐞 (-(L v) w) • fderiv ℝ f v) μ :=
    (fourierIntegral_convergent_iff' _ _).2 hf'
  /- First rewrite things in a simplified form, without any real change. -/
  suffices ∫ x, g x • fderiv ℝ f x y ∂μ = ∫ x, (2 * ↑π * I * L y w * g x) • f x ∂μ by
    simpa only [fourierIntegral, ContinuousLinearMap.toLinearMap₂_apply,
      ContinuousLinearMap.integral_apply J, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      fourierSMulRight_apply, ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply, ←
      integral_smul, neg_smul, smul_neg, ← smul_smul, Complex.coe_smul, neg_neg]
  have A x : fderiv ℝ g x y = - 2 * ↑π * I * L y w * g x :=
    fderiv_fourierChar_neg_bilinear_left_apply _ _ _ _
  /- Key step: integrate by parts with respect to `y` to switch the derivative from `f` to `g`. -/
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable, ← integral_neg]
  · congr with x
    simp only [A, neg_mul, neg_smul, neg_neg]
  · have : Integrable (fun x ↦ (-(2 * ↑π * I * ↑((L y) w)) • ((g x : ℂ) • f x))) μ :=
      ((fourierIntegral_convergent_iff' _ _).2 hf).smul _
    convert this using 2 with x
    simp [A, smul_smul]
  · exact (fourierIntegral_convergent_iff' _ _).2 (hf'.apply_continuousLinearMap _)
  · exact (fourierIntegral_convergent_iff' _ _).2 hf
  · exact differentiable_fourierChar_neg_bilinear_left _ _
  · exact h'f

open ContinuousMultilinearMap

variable [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}

/-- The Fourier integral of the `n`-th derivative of a function is obtained by multiplying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`. -/
theorem fourierIntegral_iteratedFDeriv [FiniteDimensional ℝ V]
    {μ : Measure V} [Measure.IsAddHaarMeasure μ] {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) μ) {n : ℕ} (hn : n ≤ N) :
    fourierIntegral 𝐞 μ L.toLinearMap₂ (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-L.flip) (fourierIntegral 𝐞 μ L.toLinearMap₂ f) w n) := by
  induction n with
  | zero =>
    ext w m
    have I : Integrable (fun v ↦ 𝐞 (- L v w) • iteratedFDeriv ℝ 0 f v) μ :=
      (fourierIntegral_convergent_iff' _ _).2 (h'f 0 bot_le)
    simp only [Nat.zero_eq, fourierIntegral, ContinuousLinearMap.toLinearMap₂_apply,
      integral_apply I, smul_apply, iteratedFDeriv_zero_apply, fourierPowSMulRight_apply, pow_zero,
      Finset.univ_eq_empty, ContinuousLinearMap.neg_apply, ContinuousLinearMap.flip_apply,
      Finset.prod_empty, one_smul]
  | succ n ih =>
    ext w m
    -- instance on next line should not be necessary, but proof breaks down without it.
    let NS : NormedSpace ℝ (V [×n]→L[ℝ] E) := by infer_instance
    have J : Integrable (fderiv ℝ (iteratedFDeriv ℝ n f)) μ := by
      specialize h'f (n + 1) hn
      simp_rw [iteratedFDeriv_succ_eq_comp_left] at h'f
      exact (LinearIsometryEquiv.integrable_comp_iff _).1 h'f
    suffices H : (fourierIntegral 𝐞 μ L.toLinearMap₂ (fderiv ℝ (iteratedFDeriv ℝ n f)) w)
          (m 0) (Fin.tail m) =
        (-(2 * π * I)) ^ (n + 1) • (∏ x : Fin (n + 1), -L (m x) w) • ∫ v, 𝐞 (-L v w) • f v ∂μ by
      have A : ∫ v, 𝐞 (-L v w) • (fderiv ℝ (iteratedFDeriv ℝ n f) v (m 0)) (Fin.tail m) ∂μ
          = (∫ v, 𝐞 (-L v w) • (fderiv ℝ (iteratedFDeriv ℝ n f) v (m 0)) ∂μ) (Fin.tail m) := by
        rw [integral_apply]
        · simp only [smul_apply]
        · exact (fourierIntegral_convergent_iff' L w).2 (J.apply_continuousLinearMap _)
      have B : ∫ v, 𝐞 (-L v w) • (fderiv ℝ (iteratedFDeriv ℝ n f) v (m 0)) ∂μ =
          (∫ v, 𝐞 (-L v w) • (fderiv ℝ (iteratedFDeriv ℝ n f) v) ∂μ) (m 0) := by
        rw [ContinuousLinearMap.integral_apply]
        · simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply]
        · exact (fourierIntegral_convergent_iff' L w).2 J
      simp only [fourierIntegral, ContinuousLinearMap.toLinearMap₂_apply,
        integral_apply ((fourierIntegral_convergent_iff' L w).2 (h'f _ hn)), smul_apply,
        iteratedFDeriv_succ_apply_left, fourierPowSMulRight_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.flip_apply, A, B]
      exact H
    have h'n : n < N := lt_of_lt_of_le (by simp [-Nat.cast_succ]) hn
    rw [fourierIntegral_fderiv]
    · have A : ∀ (x : ℝ) (v : E), x • v = (x : ℂ) • v := fun x v ↦ rfl
      simp only [ih h'n.le, fourierSMulRight_apply, ContinuousLinearMap.neg_apply,
        ContinuousLinearMap.flip_apply, neg_smul, smul_neg, neg_neg, smul_apply,
        fourierPowSMulRight_apply, A, smul_smul]
      congr 1
      have B : ∀ (i : Fin n), Fin.tail m i = m (Fin.succ i) := fun i ↦ rfl
      simp only [ofReal_prod, ofReal_neg, pow_succ, mul_neg, Fin.prod_univ_succ, neg_mul,
        ofReal_mul, neg_neg, B]
      ring
    · exact h'f n h'n.le
    · exact hf.differentiable_iteratedFDeriv h'n
    · exact J

end VectorFourier

namespace Real
open VectorFourier

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {f : V → E}

/-- The Fourier integral of the Fréchet derivative of a function is obtained by multiplying the
Fourier integral of the original function by `2πI ⟪v, w⟫`. -/
theorem fourierIntegral_fderiv
    (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (fderiv ℝ f)) :
    𝓕 (fderiv ℝ f) = fourierSMulRight (-innerSL ℝ) (𝓕 f) := by
  rw [← innerSL_real_flip V]
  exact VectorFourier.fourierIntegral_fderiv (innerSL ℝ) hf h'f hf'

/-- The Fourier integral of the `n`-th derivative of a function is obtained by multiplying the
Fourier integral of the original function by `(2πI L w ⬝ )^n`. -/
theorem fourierIntegral_iteratedFDeriv {N : ℕ∞} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f)) {n : ℕ} (hn : n ≤ N) :
    𝓕 (iteratedFDeriv ℝ n f)
      = (fun w ↦ fourierPowSMulRight (-innerSL ℝ) (𝓕 f) w n) := by
  rw [← innerSL_real_flip V]
  exact VectorFourier.fourierIntegral_iteratedFDeriv (innerSL ℝ) hf h'f hn

/-- The Fourier integral of the Fréchet derivative of a function is obtained by multiplying the
Fourier integral of the original function by `2πI x`. -/
theorem fourierIntegral_deriv
    {f : ℝ → E} (hf : Integrable f) (h'f : Differentiable ℝ f) (hf' : Integrable (deriv f)) :
    𝓕 (deriv f) = fun (x : ℝ) ↦ (2 * π * I * x) • (𝓕 f x) := by
  ext x
  have I : Integrable (fun x ↦ fderiv ℝ f x) := by
    simp_rw [← deriv_fderiv]
    change Integrable (fun x ↦ ContinuousLinearMap.smulRightL _ _ _ 1 (deriv f x)) volume
    apply ContinuousLinearMap.integrable_comp _ hf'
  have : 𝓕 (deriv f) x = 𝓕 (fderiv ℝ f) x 1 := by
    simp_rw [fourierIntegral_eq, deriv,
      ContinuousLinearMap.integral_apply ((fourierIntegral_convergent_iff _).2 I)]
    rfl
  rw [this, fourierIntegral_fderiv hf h'f I]
  have : x • 𝓕 f x = (x : ℂ) • 𝓕 f x := rfl
  simp only [fourierSMulRight_apply, ContinuousLinearMap.neg_apply, innerSL_apply, smul_smul,
    RCLike.inner_apply, conj_trivial, mul_one, neg_smul, smul_neg, neg_neg, neg_mul, this]

theorem fourierIntegral_iteratedDeriv {f : ℝ → E} {N : ℕ∞} {n : ℕ} (hf : ContDiff ℝ N f)
    (h'f : ∀ (n : ℕ), n ≤ N → Integrable (iteratedDeriv n f)) (hn : n ≤ N) :
    𝓕 (iteratedDeriv n f) = fun (x : ℝ) ↦ (2 * π * I * x) ^ n • (𝓕 f x) := by
  ext x : 1
  have A : ∀ (n : ℕ), n ≤ N → Integrable (iteratedFDeriv ℝ n f) := by
    intro n hn
    rw [iteratedFDeriv_eq_equiv_comp]
    exact (LinearIsometryEquiv.integrable_comp_iff _).2 (h'f n hn)
  have B : 𝓕 (fun x ↦ (iteratedFDeriv ℝ n f x) (fun i ↦ 1)) x =
      𝓕 (iteratedFDeriv ℝ n f) x (fun i ↦ 1) := by
    rw [fourierIntegral_eq, fourierIntegral_eq, ContinuousMultilinearMap.integral_apply]
    · rfl
    · exact (fourierIntegral_convergent_iff _).2 (A n hn)
  have C : ∀ (c : ℝ) (v : E), c • v = (c : ℂ) • v := fun c v ↦ rfl
  change 𝓕 (fun x ↦ iteratedDeriv n f x) x = _
  simp_rw [iteratedDeriv, B, fourierIntegral_iteratedFDeriv hf A hn]
  simp [C, smul_smul, ← mul_pow]

end Real
