import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import PrimeNumberTheoremAnd.Mathlib.Topology.MetricSpace.Cauchy

/-!
# Bilateral Laplace inversion

This file collects bilateral Laplace transform infrastructure used by the
explicit-formula contour arguments.
-/

open Real Complex Set MeasureTheory Filter FourierTransform
open scoped FourierTransform Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The bilateral Laplace transform on a vertical complex line. -/
def laplaceTransformBilateral (f : ℝ → E) (s : ℂ) : E :=
  ∫ x : ℝ, Complex.exp (-s * (x : ℂ)) • f x

/-- Complex-valued bilateral Laplace integral, written in multiplication form. -/
def laplaceIntegral (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ y : ℝ, f y * Complex.exp (-s * (y : ℂ))

/-- Continuity of the bilateral Laplace integral along a vertical line, under
integrability of the exponentially weighted source on that line. -/
theorem continuous_laplaceIntegral_verticalLine_of_integrable
    {f : ℝ → ℂ} {sigma : ℝ} (hf_cont : Continuous f)
    (hf_int : Integrable (fun y : ℝ => exp (-((sigma : ℂ) * (y : ℂ))) * f y)) :
    Continuous (fun t : ℝ => laplaceIntegral f ((sigma : ℂ) - (t : ℂ) * I)) := by
  rw [continuous_iff_continuousAt]
  intro t0
  let bound : ℝ → ℝ := fun y => ‖exp (-((sigma : ℂ) * (y : ℂ))) * f y‖
  let F : ℝ → ℝ → ℂ := fun t y =>
    f y * exp ((((t : ℂ) * I - (sigma : ℂ)) * (y : ℂ)))
  have hbound_int : Integrable bound := by
    simpa [bound, mul_comm] using hf_int.norm
  have hF_meas : ∀ᶠ t in 𝓝 t0, AEStronglyMeasurable (F t) volume := by
    refine Eventually.of_forall ?_
    intro t
    dsimp [F]
    exact (hf_cont.mul (continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  have h_bound : ∀ᶠ t in 𝓝 t0, ∀ᵐ y ∂volume, ‖F t y‖ ≤ bound y := by
    refine Eventually.of_forall ?_
    intro t
    filter_upwards with y
    dsimp [F, bound]
    rw [norm_mul, norm_mul, norm_exp, norm_exp]
    have hsig : (-(↑sigma * ↑y) : ℂ).re = -sigma * y := by
      norm_num [Complex.mul_re]
    have ht : (((↑t * I - ↑sigma) * ↑y) : ℂ).re = -sigma * y := by
      norm_num [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [hsig, ht]
    rw [mul_comm]
  have h_lim : ∀ᵐ y ∂volume, Tendsto (fun t => F t y) (𝓝 t0) (𝓝 (F t0 y)) := by
    filter_upwards with y
    dsimp [F]
    have hcont : Continuous
        (fun t : ℝ => f y * exp ((((t : ℂ) * I - (sigma : ℂ)) * (y : ℂ)))) := by
      fun_prop
    exact hcont.continuousAt
  have h_tendsto :=
    tendsto_integral_filter_of_dominated_convergence
      (μ := volume) bound hF_meas h_bound hbound_int h_lim
  unfold ContinuousAt laplaceIntegral
  simpa [F, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_tendsto

/-- The truncated inverse bilateral Laplace integral in the multiplication
`x^s` form used by Perron and explicit-formula arguments. -/
def laplaceIntegralCpowTrunc (f : ℝ → ℂ) (sigma x T : ℝ) : ℂ :=
  (1 / (2 * (π : ℂ))) *
    ∫ t in (-T)..T, laplaceIntegral f ((sigma : ℂ) + (t : ℂ) * I) *
      (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I)

/-- The multiplication-form complex Laplace integral agrees with the vector-valued definition. -/
theorem laplaceIntegral_eq_laplaceTransformBilateral (f : ℝ → ℂ) (s : ℂ) :
    laplaceIntegral f s = laplaceTransformBilateral f s := by
  unfold laplaceIntegral laplaceTransformBilateral
  congr with y
  rw [smul_eq_mul]
  ring

def fourierInvTrunc (F : ℝ → E) (x T : ℝ) : E :=
  (1 / (2 * π) : ℝ) •
    ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) • F (t / (2 * π))

def laplaceInvLineTrunc (sigma : ℝ) (F : ℂ → E) (x T : ℝ) : E :=
  (1 / (2 * π) : ℝ) •
    ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
      F ((sigma : ℂ) + (t : ℂ) * I)

/-- On a vertical line, the bilateral Laplace transform is the Fourier transform
of the exponentially weighted function. -/
theorem laplaceTransformBilateral_eq_fourier (f : ℝ → E) (s : ℂ) :
    laplaceTransformBilateral f s =
      𝓕 (fun x : ℝ => Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) (s.im / (2 * π)) := by
  calc
    laplaceTransformBilateral f s
      = ∫ x : ℝ, Complex.exp (-(s.im : ℂ) * (x : ℂ) * I) •
          (Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) := by
        unfold laplaceTransformBilateral
        congr
        ext x
        conv => lhs; rw [← re_add_im s]
        rw [neg_add, add_mul, Complex.exp_add, mul_comm, ← smul_eq_mul, smul_assoc]
        norm_cast
        push_cast
        ring_nf
    _ = 𝓕 (fun x : ℝ => Complex.exp (-(s.re : ℂ) * (x : ℂ)) • f x) (s.im / (2 * π)) := by
      rw [Real.fourier_eq']
      congr
      ext x
      congr 1
      have h2pi : (2 * (π : ℝ) : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
      rw [Real.inner_apply]
      push_cast
      field_simp [h2pi]

theorem fourierInvTrunc_fourier_eq_integral_integral
    (f : ℝ → E) (x T : ℝ) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ t in (-T)..T,
          ∫ y : ℝ, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y := by
  unfold fourierInvTrunc
  congr 1
  refine intervalIntegral.integral_congr ?_
  intro t _ht
  change Complex.exp (((t * x : ℝ) : ℂ) * I) • 𝓕 f (t / (2 * π)) =
    ∫ y : ℝ, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y
  rw [Real.fourier_real_eq_integral_exp_smul]
  rw [← MeasureTheory.integral_smul]
  congr with y
  rw [← smul_assoc]
  congr 1
  rw [smul_eq_mul]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]
  ring

/-- The truncated oscillatory Fourier kernel is product-integrable when the
source is integrable. This is the finite-height Fubini input for principal-value
inversion. -/
theorem integrable_truncated_fourier_kernel_prod
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun z : ℝ × ℝ => Complex.exp (((z.1 * (x - z.2) : ℝ) : ℂ) * I) • f z.2)
      ((volume.restrict (Set.Ioc (-T) T)).prod volume) := by
  have hconst : Integrable (fun _ : ℝ => (1 : ℂ))
      (volume.restrict (Set.Ioc (-T) T)) := by
    exact MeasureTheory.integrable_const (1 : ℂ)
  have hprod := hconst.smul_prod hf
  refine hprod.mono ?_ ?_
  · exact (by fun_prop : Continuous
        (fun z : ℝ × ℝ => Complex.exp (((z.1 * (x - z.2) : ℝ) : ℂ) * I)))
        |>.aestronglyMeasurable.smul hf.aestronglyMeasurable.comp_snd
  · filter_upwards with z
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]
    simp

/-- Fubini swaps the finite-height inverse Fourier integral into the standard
Dirichlet-kernel form. The hypothesis `0 ≤ T` is the only orientation condition
needed for the interval integral. -/
theorem fourierInvTrunc_fourier_eq_integral_kernel
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) (hT : 0 ≤ T) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ y : ℝ,
          ∫ t in (-T)..T, Complex.exp (((t * (x - y) : ℝ) : ℂ) * I) • f y := by
  rw [fourierInvTrunc_fourier_eq_integral_integral]
  congr 1
  have hle : -T ≤ T := by linarith
  rw [intervalIntegral.integral_of_le hle]
  rw [MeasureTheory.integral_integral_swap
    (integrable_truncated_fourier_kernel_prod (E := E) hf x T)]
  congr with y
  rw [← intervalIntegral.integral_of_le hle]

/-- Scaled finite-height exponential integral, away from zero frequency. -/
theorem integral_exp_mul_I_scaled_of_ne {a T : ℝ} (ha : a ≠ 0) :
    ∫ t in (-T)..T, Complex.exp (((t * a : ℝ) : ℂ) * I) =
      (2 * Real.sin (T * a) : ℂ) / (a : ℂ) := by
  have hc : ((a : ℂ) * I) ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ha) Complex.I_ne_zero
  calc
    ∫ t in (-T)..T, Complex.exp (((t * a : ℝ) : ℂ) * I)
        = ∫ t in (-T)..T, Complex.exp (((a : ℂ) * I) * t) := by
          apply intervalIntegral.integral_congr
          intro t _ht
          push_cast
          ring_nf
    _ = (2 * Real.sin (T * a) : ℂ) / (a : ℂ) := by
          rw [integral_exp_mul_complex (c := ((a : ℂ) * I)) hc]
          have harg : ((a : ℂ) * I) * (T : ℂ) = ((T * a : ℝ) : ℂ) * I := by
            push_cast
            ring_nf
          have hneg :
              ((a : ℂ) * I) * ((-T : ℝ) : ℂ) = (((-(T * a) : ℝ) : ℂ) * I) := by
            push_cast
            ring_nf
          rw [harg, hneg]
          simp only [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, ofReal_neg,
            Complex.ofReal_sin]
          field_simp [Complex.ofReal_ne_zero.mpr ha, Complex.I_ne_zero]
          ring_nf

/-- Scaled finite-height exponential integral, including the zero-frequency case. -/
theorem integral_exp_mul_I_scaled (a T : ℝ) :
    ∫ t in (-T)..T, Complex.exp (((t * a : ℝ) : ℂ) * I) =
      if a = 0 then (2 * T : ℂ) else (2 * Real.sin (T * a) : ℂ) / (a : ℂ) := by
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl]
    simp [intervalIntegral.integral_const]
    ring
  · rw [if_neg ha]
    exact integral_exp_mul_I_scaled_of_ne ha

/-- Scaled finite-height exponential integral, written with the normalized
`sinc` kernel and no removable-singularity case split. -/
theorem integral_exp_mul_I_scaled_sinc (a T : ℝ) :
    ∫ t in (-T)..T, Complex.exp (((t * a : ℝ) : ℂ) * I) =
      (2 * T * Real.sinc (T * a) : ℂ) := by
  rw [integral_exp_mul_I_scaled]
  by_cases hT : T = 0
  · subst T
    simp
  by_cases ha : a = 0
  · subst a
    rw [if_pos rfl]
    simp [Real.sinc_zero]
  · rw [if_neg ha]
    have hTa : T * a ≠ 0 := mul_ne_zero hT ha
    rw [Real.sinc_of_ne_zero hTa]
    push_cast
    field_simp [ha, hT]

theorem fourierInvTrunc_fourier_eq_sinc_kernel
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) (x T : ℝ) (hT : 0 ≤ T) :
    fourierInvTrunc (𝓕 f) x T =
      (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y := by
  rw [fourierInvTrunc_fourier_eq_integral_kernel hf x T hT]
  congr 1
  congr with y
  rw [intervalIntegral.integral_smul_const]
  rw [integral_exp_mul_I_scaled_sinc]

theorem fourierInvTrunc_tendsto_of_sinc_kernel
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x : ℝ}
    (hdir : Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x))) :
    Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 f) x T)
      Filter.atTop (nhds (f x)) := by
  refine hdir.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (fourierInvTrunc_fourier_eq_sinc_kernel hf x T hT).symm

/-- Whole-line change of variables for the reflection-translation `y ↦ x - y`. -/
theorem integral_comp_sub_left_eq_self (g : ℝ → E) (x : ℝ) :
    (∫ y : ℝ, g (x - y)) = ∫ u : ℝ, g u := by
  calc
    (∫ y : ℝ, g (x - y)) = ∫ y : ℝ, g (x + y) := by
      simpa [sub_eq_add_neg] using
        integral_neg_eq_self (f := fun y : ℝ => g (x + y)) (μ := volume)
    _ = ∫ u : ℝ, g u := by
      simpa using integral_add_left_eq_self (μ := volume) g x

/-- The sinc kernel can be written in translated coordinates `u = x - y`. -/
theorem sinc_kernel_integral_comp_sub_left
    (f : ℝ → E) (x T : ℝ) :
    (∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y) =
      ∫ u : ℝ, (2 * T * Real.sinc (T * u) : ℂ) • f (x - u) := by
  let g : ℝ → E := fun u => (2 * T * Real.sinc (T * u) : ℂ) • f (x - u)
  have h := integral_comp_sub_left_eq_self (E := E) g x
  simpa [g] using h

/-- The normalized sinc kernel is the usual `sin (T * u) / (π * u)` kernel,
with the removable value at `u = 0` made explicit. -/
theorem normalized_sinc_smul_eq_sin_div (T u : ℝ) (z : E) :
    (1 / (2 * π) : ℝ) • ((2 * T * Real.sinc (T * u) : ℂ) • z) =
      (if u = 0 then (T / π : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • z := by
  by_cases hu : u = 0
  · subst u
    rw [if_pos rfl]
    simp only [one_div, mul_inv_rev, mul_zero, Real.sinc_zero, ofReal_one, mul_one]
    rw [← smul_assoc]
    congr 1
    rw [RCLike.real_smul_eq_coe_mul]
    push_cast
    field_simp [Real.pi_ne_zero]
    ring_nf
    rfl
  · rw [if_neg hu]
    by_cases hT : T = 0
    · subst T
      simp
    · rw [Real.sinc_of_ne_zero (mul_ne_zero hT hu)]
      rw [← smul_assoc]
      congr 1
      rw [RCLike.real_smul_eq_coe_mul]
      push_cast
      field_simp [Real.pi_ne_zero, hT, hu]
      ring_nf
      rfl

/-- The normalized sinc kernel integral in translated coordinates, with the
removable singularity of `sin (T * u) / (π * u)` exposed. -/
theorem normalized_sinc_kernel_integral_comp_sub_left_sin_div
    (f : ℝ → E) (x T : ℝ) :
    (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y =
      ∫ u : ℝ,
        (if u = 0 then (T / π : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u) := by
  rw [sinc_kernel_integral_comp_sub_left]
  rw [← integral_smul]
  congr with u
  exact normalized_sinc_smul_eq_sin_div (E := E) T u (f (x - u))

/-- The value assigned at the removable singularity of `sin (T * u) / (π * u)`
does not affect the whole-line kernel integral. -/
theorem normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae
    (f : ℝ → E) (x T : ℝ) :
    (1 / (2 * π) : ℝ) •
        ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y =
      ∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u) := by
  rw [normalized_sinc_kernel_integral_comp_sub_left_sin_div]
  refine integral_congr_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by simp [ae_iff, measure_singleton]] with u hu
  rw [if_neg hu, if_neg hu]

/-- The scaled positive-frequency ray `T / (2π)` tends to the cocompact filter. -/
lemma tendsto_div_two_pi_atTop_cocompact :
    Filter.Tendsto (fun T : ℝ => T / (2 * π)) Filter.atTop (Filter.cocompact ℝ) := by
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ) ?_
  have h : Filter.Tendsto (fun T : ℝ => (1 / (2 * π)) * T) Filter.atTop
      Filter.atTop := by
    exact (Filter.tendsto_const_mul_atTop_of_pos
      (by positivity : 0 < (1 / (2 * π) : ℝ))).2 Filter.tendsto_id
  have h' : Filter.Tendsto (fun T : ℝ => T / (2 * π)) Filter.atTop Filter.atTop := by
    simpa [one_div, div_eq_mul_inv, mul_comm] using h
  simpa [dist_eq_norm, Function.comp_def, norm_div,
    abs_of_pos (by positivity : 0 < (2 * π : ℝ))]
    using tendsto_norm_atTop_atTop.comp h'

/-- The scaled negative-frequency ray `-T / (2π)` tends to the cocompact filter. -/
lemma tendsto_neg_div_two_pi_atTop_cocompact :
    Filter.Tendsto (fun T : ℝ => -T / (2 * π)) Filter.atTop (Filter.cocompact ℝ) := by
  refine tendsto_cocompact_of_tendsto_dist_comp_atTop (0 : ℝ) ?_
  have h : Filter.Tendsto (fun T : ℝ => T / (2 * π)) Filter.atTop Filter.atTop := by
    have h0 : Filter.Tendsto (fun T : ℝ => (1 / (2 * π)) * T) Filter.atTop
        Filter.atTop := by
      exact (Filter.tendsto_const_mul_atTop_of_pos
        (by positivity : 0 < (1 / (2 * π) : ℝ))).2 Filter.tendsto_id
    simpa [one_div, div_eq_mul_inv, mul_comm] using h0
  have hn : Filter.Tendsto (fun T : ℝ => ‖T / (2 * π)‖) Filter.atTop Filter.atTop :=
    tendsto_norm_atTop_atTop.comp h
  simpa [dist_eq_norm, neg_div, norm_neg, norm_div,
    abs_of_pos (by positivity : 0 < (2 * π : ℝ))] using hn

/-- Riemann-Lebesgue on the scaled positive-frequency ray. -/
theorem fourier_tendsto_atTop_scaled (f : ℝ → E) :
    Filter.Tendsto (fun T : ℝ => 𝓕 f (T / (2 * π))) Filter.atTop (nhds 0) := by
  exact (Real.zero_at_infty_fourier f).comp tendsto_div_two_pi_atTop_cocompact

/-- Riemann-Lebesgue on the scaled negative-frequency ray. -/
theorem fourier_tendsto_atTop_neg_scaled (f : ℝ → E) :
    Filter.Tendsto (fun T : ℝ => 𝓕 f (-T / (2 * π))) Filter.atTop (nhds 0) := by
  exact (Real.zero_at_infty_fourier f).comp tendsto_neg_div_two_pi_atTop_cocompact

/-- The negative complex exponential integral tends to zero on the positive height ray. -/
theorem tendsto_integral_exp_neg_mul_I_smul_atTop (f : ℝ → E) :
    Filter.Tendsto (fun T : ℝ => ∫ v : ℝ,
      Complex.exp (-(((T * v : ℝ) : ℂ) * I)) • f v) Filter.atTop (nhds 0) := by
  have h := fourier_tendsto_atTop_scaled (E := E) f
  refine h.congr' ?_
  filter_upwards with T
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr with v
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- The positive complex exponential integral tends to zero on the positive height ray. -/
theorem tendsto_integral_exp_pos_mul_I_smul_atTop (f : ℝ → E) :
    Filter.Tendsto (fun T : ℝ => ∫ v : ℝ,
      Complex.exp (((T * v : ℝ) : ℂ) * I) • f v) Filter.atTop (nhds 0) := by
  have h := fourier_tendsto_atTop_neg_scaled (E := E) f
  refine h.congr' ?_
  filter_upwards with T
  rw [Real.fourier_real_eq_integral_exp_smul]
  congr with v
  congr 1
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Multiplying an integrable function by a negative unit-modulus exponential preserves
integrability. -/
lemma integrable_exp_neg_mul_I_smul {f : ℝ → E} (hf : Integrable f) (T : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (-(((T * v : ℝ) : ℂ) * I)) • f v) := by
  refine hf.mono ?_ ?_
  · exact (by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (-(((T * v : ℝ) : ℂ) * I))))
      |>.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · filter_upwards with v
    rw [norm_smul]
    have harg : -(((T * v : ℝ) : ℂ) * I) = (((-(T * v) : ℝ) : ℂ) * I) := by
      push_cast
      ring
    rw [harg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Multiplying an integrable function by a positive unit-modulus exponential preserves
integrability. -/
lemma integrable_exp_pos_mul_I_smul {f : ℝ → E} (hf : Integrable f) (T : ℝ) :
    Integrable (fun v : ℝ => Complex.exp (((T * v : ℝ) : ℂ) * I) • f v) := by
  refine hf.mono ?_ ?_
  · exact (by fun_prop : Continuous (fun v : ℝ =>
        Complex.exp (((T * v : ℝ) : ℂ) * I)))
      |>.aestronglyMeasurable.smul hf.aestronglyMeasurable
  · filter_upwards with v
    rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Riemann-Lebesgue in sine-integral form. This is the oscillatory cancellation
brick used by the non-L1 principal-value Laplace inversion route. -/
theorem tendsto_integral_sin_mul_smul_atTop {f : ℝ → E} (hf : Integrable f) :
    Filter.Tendsto (fun T : ℝ => ∫ v : ℝ, (Real.sin (T * v) : ℂ) • f v)
      Filter.atTop (nhds 0) := by
  let c : ℂ := (2 : ℂ)⁻¹ * I
  have hneg := tendsto_integral_exp_neg_mul_I_smul_atTop (E := E) f
  have hpos := tendsto_integral_exp_pos_mul_I_smul_atTop (E := E) f
  have hdiff : Filter.Tendsto
      (fun T : ℝ => (∫ v : ℝ, Complex.exp (-(((T * v : ℝ) : ℂ) * I)) • f v) -
        ∫ v : ℝ, Complex.exp (((T * v : ℝ) : ℂ) * I) • f v)
      Filter.atTop (nhds (0 - 0)) := hneg.sub hpos
  have hscaled : Filter.Tendsto
      (fun T : ℝ => c • ((∫ v : ℝ,
          Complex.exp (-(((T * v : ℝ) : ℂ) * I)) • f v) -
        ∫ v : ℝ, Complex.exp (((T * v : ℝ) : ℂ) * I) • f v))
      Filter.atTop (nhds 0) := by
    simpa [c] using hdiff.const_smul c
  refine hscaled.congr' ?_
  filter_upwards with T
  have hneg_int := integrable_exp_neg_mul_I_smul (E := E) hf T
  have hpos_int := integrable_exp_pos_mul_I_smul (E := E) hf T
  rw [← integral_sub hneg_int hpos_int]
  rw [← integral_smul]
  congr with v
  rw [← sub_smul]
  rw [← smul_assoc]
  congr 1
  dsimp [c]
  change ((2 : ℂ)⁻¹ * I) *
      (Complex.exp (-(((T * v : ℝ) : ℂ) * I)) - Complex.exp (((T * v : ℝ) : ℂ) * I)) =
    (Real.sin (T * v) : ℂ)
  symm
  rw [show (Real.sin (T * v) : ℂ) = Complex.sin ((T * v : ℝ) : ℂ) by simp]
  field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc] using (Complex.two_sin ((T * v : ℝ) : ℂ))

theorem sin_div_kernel_sub_eq_sin_smul_quotient
    (f : ℝ → E) (x T u : ℝ) :
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
        (f (x - u) - f x) =
      (Real.sin (T * u) : ℂ) •
        (if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)) := by
  by_cases hu : u = 0
  · simp [hu]
  · rw [if_neg hu, if_neg hu, ← smul_assoc]
    congr 1
    simp only [div_eq_mul_inv]
    ring

theorem local_quotient_eq_dslope
    (f : ℝ → E) (x : ℝ) {u : ℝ} (hu : u ≠ 0) :
    ((-1 / π : ℂ) • dslope f x (x - u)) =
      (if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)) := by
  rw [if_neg hu]
  have hne : x - u ≠ x := by
    intro h
    have : u = 0 := by linarith
    exact hu this
  rw [dslope_of_ne f hne]
  rw [slope_def_module]
  let r : ℝ := (x - u - x)⁻¹
  change (-1 / π : ℂ) • (r • (f (x - u) - f x)) =
    (1 / (π * u) : ℂ) • (f (x - u) - f x)
  rw [← smul_comm r ((-1 / π : ℂ))]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ) (E := E)]
  rw [← smul_assoc]
  congr 1
  dsimp [r]
  push_cast
  field_simp [hu, Real.pi_ne_zero]
  ring

/-- Differentiability at the target point makes the local sine-error quotient
interval-integrable on every positive window. -/
theorem intervalIntegrable_local_quotient_of_differentiableAt
    {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hf_cont : ContinuousOn f (Set.Icc (x - R) (x + R)))
    (hf_diff : DifferentiableAt ℝ f x) :
    IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R := by
  let qds : ℝ → E := fun u => (-1 / π : ℂ) • dslope f x (x - u)
  have hmem : Set.Icc (x - R) (x + R) ∈ nhds x := by
    exact Icc_mem_nhds (by linarith) (by linarith)
  have hds : ContinuousOn (dslope f x) (Set.Icc (x - R) (x + R)) :=
    (continuousOn_dslope hmem).2 ⟨hf_cont, hf_diff⟩
  have hmap : MapsTo (fun u : ℝ => x - u) (Set.Icc (-R) R) (Set.Icc (x - R) (x + R)) := by
    intro u hu
    rw [Set.mem_Icc] at hu ⊢
    constructor <;> linarith
  have hcomp : ContinuousOn (fun u : ℝ => dslope f x (x - u)) (Set.Icc (-R) R) := by
    exact hds.comp (by fun_prop) hmap
  have hqds_cont : ContinuousOn qds (Set.Icc (-R) R) :=
    hcomp.const_smul (-1 / π : ℂ)
  have hle : -R ≤ R := by linarith
  have hqds_int : IntervalIntegrable qds volume (-R) R :=
    ContinuousOn.intervalIntegrable_of_Icc hle hqds_cont
  refine hqds_int.congr_ae ?_
  rw [Filter.EventuallyEq]
  rw [ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [show ∀ᵐ u : ℝ, u ≠ 0 by simp [ae_iff, measure_singleton]]
    with u hu _hu_mem
  dsimp [qds]
  exact local_quotient_eq_dslope (E := E) f x hu

/-- Local quotient integrability gives interval-integrability of the finite
sine-kernel error term. -/
theorem intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
    {f : ℝ → E} {x R : ℝ}
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R)
    (T : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x))
      volume (-R) R := by
  let q : ℝ → E := fun u =>
    if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)
  have hsinq : IntervalIntegrable (fun u : ℝ => (Real.sin (T * u) : ℂ) • q u)
      volume (-R) R := by
    refine hq.continuousOn_smul ?_
    fun_prop
  refine hsinq.congr ?_
  intro u _hu
  dsimp [q]
  exact (sin_div_kernel_sub_eq_sin_smul_quotient (E := E) f x T u).symm

/-- Local quotient integrability gives the finite-window Riemann-Lebesgue
cancellation for the sine-kernel error term. -/
theorem tendsto_intervalIntegral_sin_div_kernel_error_of_intervalIntegrable_quotient
    {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0) := by
  let q : ℝ → E := fun u =>
    if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x)
  let qWindow : ℝ → E := Set.Ioc (-R) R |>.indicator q
  have hle : -R ≤ R := by linarith
  have hqIoc : IntegrableOn q (Set.Ioc (-R) R) := by
    simpa [q] using (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).1 hq
  have hqWindow : Integrable qWindow := by
    exact hqIoc.integrable_indicator measurableSet_Ioc
  have hlim := tendsto_integral_sin_mul_smul_atTop (E := E) hqWindow
  refine hlim.congr' ?_
  filter_upwards with T
  have hinterval :
      (∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x)) =
        ∫ u in (-R)..R, (Real.sin (T * u) : ℂ) • q u := by
    apply intervalIntegral.integral_congr
    intro u _hu
    dsimp [q]
    exact sin_div_kernel_sub_eq_sin_smul_quotient (E := E) f x T u
  rw [hinterval, intervalIntegral.integral_of_le hle]
  dsimp [qWindow]
  rw [← integral_indicator measurableSet_Ioc]
  congr with u
  by_cases hu : u ∈ Set.Ioc (-R) R
  · simp [Set.indicator_of_mem hu]
  · simp [Set.indicator_of_notMem hu]

/-- The removable sine kernel is bounded by its height. -/
theorem norm_sin_div_kernel_le_abs_height (T u : ℝ) :
    ‖(if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))‖ ≤
      |T| / π := by
  by_cases hu : u = 0
  · rw [if_pos hu]
    simpa using (div_nonneg (abs_nonneg T) Real.pi_pos.le)
  · rw [if_neg hu]
    rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
    simp only [Real.norm_eq_abs]
    have hsin : |Real.sin (T * u)| ≤ |T| * |u| := by
      simpa [abs_mul] using (Real.abs_sin_le_abs (x := T * u))
    calc
      |Real.sin (T * u)| / (|π| * |u|)
          ≤ (|T| * |u|) / (|π| * |u|) :=
            div_le_div_of_nonneg_right hsin
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |T| / π := by
        rw [abs_of_pos Real.pi_pos]
        field_simp [abs_pos.mpr hu, Real.pi_ne_zero]

/-- The sine kernel times an integrable source remains integrable. -/
theorem integrable_sin_div_kernel_smul_of_integrable
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) :
    Integrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) := by
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  let C : ℂ := (|T| / π : ℝ)
  have hC_nonneg : 0 ≤ |T| / π := div_nonneg (abs_nonneg T) Real.pi_pos.le
  have hboundInt : Integrable (fun u : ℝ => C • f (x - u)) := hfx.smul C
  refine hboundInt.mono ?_ ?_
  · have hscalar_meas : Measurable
        (fun u : ℝ =>
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) := by
      refine Measurable.ite measurableSet_eq measurable_const ?_
      fun_prop
    exact hscalar_meas.aestronglyMeasurable.smul hfx.aestronglyMeasurable
  · filter_upwards with u
    rw [norm_smul, norm_smul]
    have hCnorm : ‖C‖ = |T| / π := by
      rw [show C = ((|T| / π : ℝ) : ℂ) by rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC_nonneg]
    rw [hCnorm]
    exact mul_le_mul (norm_sin_div_kernel_le_abs_height T u) le_rfl
      (norm_nonneg _) hC_nonneg

/-- Outside `(-R, R]`, a positive radius is a lower bound for `|u|`. -/
lemma le_abs_of_notMem_Ioc_neg_pos {R u : ℝ} (hR : 0 < R)
    (hu : u ∉ Set.Ioc (-R) R) :
    R ≤ |u| := by
  rw [Set.mem_Ioc] at hu
  by_cases hleft : -R < u
  · have hRu : R < u := lt_of_not_ge (fun huR : u ≤ R => hu ⟨hleft, huR⟩)
    exact le_trans hRu.le (le_abs_self u)
  · have hule : u ≤ -R := le_of_not_gt hleft
    have hneg : R ≤ -u := by linarith
    have hu_nonpos : u ≤ 0 := by linarith
    exact hneg.trans_eq (abs_of_nonpos hu_nonpos).symm

/-- The fixed-window tail quotient is bounded by an integrable translate. -/
lemma norm_tail_quotient_le
    {f : ℝ → E} (x : ℝ) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    ‖(Set.Ioc (-R) R)ᶜ.indicator
        (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
          f (x - u)) u‖ ≤
      (1 / (π * R)) * ‖f (x - u)‖ := by
  by_cases huSet : u ∈ (Set.Ioc (-R) R)ᶜ
  · rw [Set.indicator_of_mem huSet]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using huSet
    have hR_abs : R ≤ |u| := le_abs_of_notMem_Ioc_neg_pos hR hu_not
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := by
        exact ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [if_neg hu_ne, norm_smul]
    have hscalar : ‖(1 / (π * u) : ℂ)‖ ≤ 1 / (π * R) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs, one_div]
      rw [abs_of_pos Real.pi_pos]
      have hden : π * R ≤ π * |u| :=
        mul_le_mul_of_nonneg_left hR_abs Real.pi_pos.le
      have hden_pos : 0 < π * R := mul_pos Real.pi_pos hR
      simpa [mul_comm, mul_left_comm, mul_assoc] using inv_anti₀ hden_pos hden
    exact mul_le_mul hscalar le_rfl (norm_nonneg _)
      (div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le)
  · rw [Set.indicator_of_notMem huSet]
    simpa using mul_nonneg (div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le)
      (norm_nonneg (f (x - u)))

/-- The fixed-window tail quotient is integrable for every integrable source. -/
theorem integrable_tail_quotient_of_integrable
    {f : ℝ → E} (hf : Integrable f) (x : ℝ) {R : ℝ} (hR : 0 < R) :
    Integrable ((Set.Ioc (-R) R)ᶜ.indicator
      (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
        f (x - u))) := by
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  let C : ℂ := (1 / (π * R) : ℝ)
  have hC_nonneg : 0 ≤ 1 / (π * R) :=
    div_nonneg zero_le_one (mul_pos Real.pi_pos hR).le
  have hboundInt : Integrable (fun u : ℝ => C • f (x - u)) := hfx.smul C
  refine hboundInt.mono ?_ ?_
  · have hscalar_meas : Measurable
        (fun u : ℝ => if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) := by
      refine Measurable.ite measurableSet_eq measurable_const ?_
      fun_prop
    exact (hscalar_meas.aestronglyMeasurable.smul hfx.aestronglyMeasurable).indicator
      measurableSet_Ioc.compl
  · filter_upwards with u
    rw [norm_smul]
    have hCnorm : ‖C‖ = 1 / (π * R) := by
      rw [show C = ((1 / (π * R) : ℝ) : ℂ) by rfl, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hC_nonneg]
    rw [hCnorm]
    exact norm_tail_quotient_le (E := E) x hR u

/-- Pointwise tail algebra for the sine kernel. -/
lemma tail_indicator_sin_div_eq_sin_smul_quotient
    (f : ℝ → E) (x T : ℝ) {R : ℝ} (hR : 0 < R) (u : ℝ) :
    (Set.Ioc (-R) R)ᶜ.indicator
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) u =
      (Real.sin (T * u) : ℂ) •
        (Set.Ioc (-R) R)ᶜ.indicator
          (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
            f (x - u)) u := by
  by_cases huSet : u ∈ (Set.Ioc (-R) R)ᶜ
  · rw [Set.indicator_of_mem huSet, Set.indicator_of_mem huSet]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using huSet
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := by
        exact ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [if_neg hu_ne, if_neg hu_ne, ← smul_assoc]
    congr 1
    simp only [div_eq_mul_inv]
    ring
  · rw [Set.indicator_of_notMem huSet, Set.indicator_of_notMem huSet, smul_zero]

/-- The fixed-window tail of the sine kernel tends to zero for integrable
sources. -/
theorem tendsto_sin_div_kernel_tail_of_integrable
    {f : ℝ → E} (hf : Integrable f) {x R : ℝ} (hR : 0 < R) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0) := by
  let qTail : ℝ → E := (Set.Ioc (-R) R)ᶜ.indicator
    (fun u : ℝ => (if u = 0 then (0 : ℂ) else (1 / (π * u) : ℂ)) •
      f (x - u))
  have hqTail : Integrable qTail := by
    simpa [qTail] using integrable_tail_quotient_of_integrable (E := E) hf x hR
  have hlim := tendsto_integral_sin_mul_smul_atTop (E := E) hqTail
  refine hlim.congr' ?_
  filter_upwards with T
  let k : ℝ → E := fun u =>
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f (x - u)
  have hk : Integrable k :=
    integrable_sin_div_kernel_smul_of_integrable (E := E) hf x T
  have hle : -R ≤ R := by linarith
  symm
  calc
    (∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) -
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)
        = ∫ u in (Set.Ioc (-R) R)ᶜ, k u := by
          rw [intervalIntegral.integral_of_le hle]
          have hdecomp := integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hk
          dsimp [k] at hdecomp
          rw [← hdecomp]
          abel
    _ = ∫ u : ℝ, (Set.Ioc (-R) R)ᶜ.indicator k u := by
          rw [integral_indicator measurableSet_Ioc.compl]
    _ = ∫ u : ℝ, (Real.sin (T * u) : ℂ) • qTail u := by
          apply integral_congr_ae
          filter_upwards with u
          dsimp [k, qTail]
          exact tail_indicator_sin_div_eq_sin_smul_quotient (E := E) f x T hR u

/-- Uniform fixed-window tail bound for the sine kernel. Outside `(-R, R]`,
the denominator gives a `1 / (π R)` bound, independent of the height and
translation. -/
theorem norm_sin_div_kernel_tail_le_integral_norm
    {f : ℝ → E} (hf : Integrable f) (x T : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖(∫ u : ℝ,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) -
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)‖ ≤
      (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
  let k : ℝ → E := fun u =>
    (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f (x - u)
  have hk : Integrable k :=
    integrable_sin_div_kernel_smul_of_integrable (E := E) hf x T
  have hle : -R ≤ R := by linarith
  have htail_eq :
      (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u) =
        ∫ u in (Set.Ioc (-R) R)ᶜ, k u := by
    rw [intervalIntegral.integral_of_le hle]
    have hdecomp := integral_add_compl (s := Set.Ioc (-R) R) measurableSet_Ioc hk
    dsimp [k] at hdecomp
    rw [← hdecomp]
    abel
  rw [htail_eq]
  let C : ℝ := 1 / (π * R)
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hfx : Integrable (fun u : ℝ => f (x - u)) := hf.comp_sub_left x
  have hbound_int : Integrable (fun u : ℝ => C * ‖f (x - u)‖) :=
    hfx.norm.const_mul C
  have hmono : ∀ᵐ u ∂(volume.restrict (Set.Ioc (-R) R)ᶜ),
      ‖k u‖ ≤ C * ‖f (x - u)‖ := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioc.compl] with u hucomp
    dsimp [k, C]
    have hu_not : u ∉ Set.Ioc (-R) R := by simpa using hucomp
    have hR_abs : R ≤ |u| := le_abs_of_notMem_Ioc_neg_pos hR hu_not
    have hu_ne : u ≠ 0 := by
      intro h0
      apply hu_not
      have hzmem : (0 : ℝ) ∈ Set.Ioc (-R) R := ⟨by linarith, hR.le⟩
      simpa [h0] using hzmem
    rw [if_neg hu_ne, norm_smul]
    have hscalar : ‖(Real.sin (T * u) / (π * u) : ℂ)‖ ≤ C := by
      dsimp [C]
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs]
      rw [abs_of_pos Real.pi_pos]
      have hsin : |Real.sin (T * u)| ≤ 1 := Real.abs_sin_le_one (T * u)
      have hden : π * R ≤ π * |u| :=
        mul_le_mul_of_nonneg_left hR_abs Real.pi_pos.le
      have hden_pos : 0 < π * R := mul_pos Real.pi_pos hR
      calc
        |Real.sin (T * u)| / (π * |u|) ≤ 1 / (π * |u|) := by
          exact div_le_div_of_nonneg_right hsin
            (mul_nonneg Real.pi_pos.le (abs_nonneg u))
        _ ≤ 1 / (π * R) := by
          simpa [one_div] using inv_anti₀ hden_pos hden
    exact mul_le_mul hscalar le_rfl (norm_nonneg _) hC_nonneg
  have hnorm_le : ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖ ≤
      ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
    calc
      ‖∫ u in (Set.Ioc (-R) R)ᶜ, k u‖
          ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, ‖k u‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖ := by
        exact integral_mono_ae (hk.norm.mono_measure Measure.restrict_le_self)
          (hbound_int.mono_measure Measure.restrict_le_self) hmono
  have hset_le : (∫ u in (Set.Ioc (-R) R)ᶜ, C * ‖f (x - u)‖) ≤
      ∫ u : ℝ, C * ‖f (x - u)‖ := by
    exact integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun _u => mul_nonneg hC_nonneg (norm_nonneg _)) hbound_int
  have htranslate : (∫ u : ℝ, C * ‖f (x - u)‖) = C * ∫ u : ℝ, ‖f u‖ := by
    rw [integral_const_mul]
    congr 1
    calc
      (∫ u : ℝ, ‖f (x - u)‖) = ∫ u : ℝ, ‖f (x + u)‖ := by
        simpa [sub_eq_add_neg] using
          integral_neg_eq_self (f := fun u : ℝ => ‖f (x + u)‖) (μ := volume)
      _ = ∫ u : ℝ, ‖f u‖ := by
        simpa using integral_add_left_eq_self (μ := volume) (fun u : ℝ => ‖f u‖) x
  exact hnorm_le.trans (hset_le.trans_eq htranslate)

/-- Finite symmetric-window split for the `sin (T * u) / (π * u)` kernel.
This is the valid algebraic surface for the principal-value mass term before
taking an improper limit. -/
theorem intervalIntegral_sin_div_kernel_split
    [CompleteSpace E]
    (f : ℝ → E) (x T R : ℝ)
    (hconst : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      volume (-R) R)
    (herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x))
      volume (-R) R) :
    (∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) =
      (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
  calc
    (∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u))
        = ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x) := by
          apply intervalIntegral.integral_congr
          intro u _hu
          change
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                f (x - u) =
              (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
                (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                  (f (x - u) - f x)
          rw [show f (x - u) = f x + (f (x - u) - f x) by abel]
          rw [smul_add]
          congr 1
          abel_nf
    _ = (∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x) +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
          rw [intervalIntegral.integral_add hconst herr]
    _ = (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x) := by
          rw [intervalIntegral.integral_smul_const]

/-- A scalar finite-window Dirichlet mass limit immediately gives the
corresponding vector-valued mass limit. -/
theorem tendsto_intervalIntegral_sin_div_kernel_smul_of_scalar_mass
    (z : E) {R : ℝ}
    (hmass : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • z)
      Filter.atTop (nhds z) := by
  simpa using hmass.smul_const z

/-- Scaling reduces the finite-window mass of `sin (T * u) / (π * u)` to the
normalized symmetric sine integral at height `T * R`. -/
theorem intervalIntegral_sin_div_kernel_scalar_mass_eq_scaled (T R : ℝ) :
    (∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) =
      (1 / (π : ℂ)) *
        ∫ v in (T * (-R))..(T * R),
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
  let g : ℝ → ℂ := fun v => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)
  have hpoint : (fun u : ℝ =>
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) =
      fun u : ℝ => (1 / (π : ℂ)) * (T • g (T * u)) := by
    funext u
    by_cases hT : T = 0
    · simp [hT, g]
    by_cases hu : u = 0
    · simp [hu, g]
    have hTu : T * u ≠ 0 := mul_ne_zero hT hu
    simp [g, hu, hTu]
    field_simp [Real.pi_ne_zero, hT, hu]
  calc
    (∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
        = ∫ u in (-R)..R, (1 / (π : ℂ)) * (T • g (T * u)) := by
          rw [hpoint]
    _ = (1 / (π : ℂ)) * ∫ u in (-R)..R, T • g (T * u) := by
          rw [intervalIntegral.integral_const_mul]
    _ = (1 / (π : ℂ)) * (T • ∫ u in (-R)..R, g (T * u)) := by
          rw [intervalIntegral.integral_smul]
    _ = (1 / (π : ℂ)) * ∫ v in (T * (-R))..(T * R), g v := by
          rw [intervalIntegral.smul_integral_comp_mul_left]
    _ = (1 / (π : ℂ)) *
        ∫ v in (T * (-R))..(T * R),
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
          rfl

/-- The sine-over-argument kernel is interval-integrable on finite intervals;
the value at zero is irrelevant by the removable singularity of `Real.sinc`. -/
theorem intervalIntegrable_sin_div_kernel (a b : ℝ) :
    IntervalIntegrable
      (fun v : ℝ => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      volume a b := by
  let g : ℝ → ℂ := fun v => (Real.sinc v : ℂ)
  have hg : IntervalIntegrable g volume a b := by
    exact (Complex.continuous_ofReal.comp Real.continuous_sinc).intervalIntegrable a b
  refine hg.congr_ae ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ v : ℝ ∂volume, v ≠ 0 by simp [ae_iff, measure_singleton]]
    with v hv
  simp [g, Real.sinc_of_ne_zero hv, hv]

/-- The scaled sine kernel is interval-integrable on finite intervals; its value
at zero is again irrelevant. -/
theorem intervalIntegrable_scaled_sin_div_kernel (T a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ => if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      volume a b := by
  let g : ℝ → ℂ := fun u => (((T / π : ℝ) * Real.sinc (T * u) : ℝ) : ℂ)
  have hg : IntervalIntegrable g volume a b := by
    apply Continuous.intervalIntegrable
    dsimp [g]
    fun_prop
  refine hg.congr_ae ?_
  refine ae_restrict_of_ae ?_
  filter_upwards [show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by simp [ae_iff, measure_singleton]]
    with u hu
  by_cases hT : T = 0
  · simp [g, hT, hu]
  · have hTu : T * u ≠ 0 := mul_ne_zero hT hu
    simp [g, hu, Real.sinc_of_ne_zero hTu]
    field_simp [Real.pi_ne_zero, hT, hu]

/-- Multiplying the finite sine kernel by a constant vector preserves
interval-integrability. -/
theorem intervalIntegrable_sin_div_kernel_smul_const
    (z : E) (T a b : ℝ) :
    IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • z)
      volume a b := by
  have h := intervalIntegrable_scaled_sin_div_kernel T a b
  constructor
  · exact h.1.smul_const z
  · exact h.2.smul_const z

/-- Windowed bound for finite-height Fourier inversion. The mass term, local
principal-value window, and far-field tail are separated so applications can
supply uniform bounds for the first two and use the built-in tail estimate. -/
theorem norm_fourierInvTrunc_le_of_windowed_sin_div_bounds
    [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) {x T R B L M : ℝ}
    (hT : 0 ≤ T) (hR : 0 < R)
    (hfx : ‖f x‖ ≤ B)
    (hmass : ‖∫ u in (-R)..R,
      if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)‖ ≤ M)
    (herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x)) volume (-R) R)
    (hlocal : ‖∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          (f (x - u) - f x)‖ ≤ L) :
    ‖fourierInvTrunc (𝓕 f) x T‖ ≤
      M * B + L + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
  let K : ℝ → ℂ := fun u =>
    if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)
  have hwhole : fourierInvTrunc (𝓕 f) x T = ∫ u : ℝ, K u • f (x - u) := by
    rw [fourierInvTrunc_fourier_eq_sinc_kernel (E := E) hf x T hT]
    simpa [K] using normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae (E := E) f x T
  have hconst : IntervalIntegrable (fun u : ℝ => K u • f x) volume (-R) R := by
    simpa [K] using intervalIntegrable_sin_div_kernel_smul_const (E := E) (f x) T (-R) R
  have hsplit := intervalIntegral_sin_div_kernel_split (E := E) f x T R hconst
    (by simpa [K] using herr)
  have hwindow_bound : ‖∫ u in (-R)..R, K u • f (x - u)‖ ≤ M * B + L := by
    calc
      ‖∫ u in (-R)..R, K u • f (x - u)‖
          = ‖(∫ u in (-R)..R, K u) • f x +
              ∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := by
            rw [show (∫ u in (-R)..R, K u • f (x - u)) =
                (∫ u in (-R)..R, K u) • f x +
                ∫ u in (-R)..R, K u • (f (x - u) - f x) by simpa [K] using hsplit]
      _ ≤ ‖(∫ u in (-R)..R, K u) • f x‖ +
            ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ := norm_add_le _ _
      _ ≤ M * B + L := by
        have hM_nonneg : 0 ≤ M := le_trans (norm_nonneg _) hmass
        have hterm : ‖(∫ u in (-R)..R, K u) • f x‖ ≤ M * B := by
          rw [norm_smul]
          exact mul_le_mul (by simpa [K] using hmass) hfx (norm_nonneg _) hM_nonneg
        have hloc : ‖∫ u in (-R)..R, K u • (f (x - u) - f x)‖ ≤ L := by
          simpa [K] using hlocal
        linarith
  have htail := norm_sin_div_kernel_tail_le_integral_norm (E := E) hf x T hR
  rw [hwhole]
  let W : E := ∫ u in (-R)..R, K u • f (x - u)
  let Tail : E := (∫ u : ℝ, K u • f (x - u)) - W
  have hdecomp : (∫ u : ℝ, K u • f (x - u)) = W + Tail := by
    dsimp [W, Tail]
    abel
  calc
    ‖∫ u : ℝ, K u • f (x - u)‖ = ‖W + Tail‖ := by rw [hdecomp]
    _ ≤ ‖W‖ + ‖Tail‖ := norm_add_le _ _
    _ ≤ (M * B + L) + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
      have hW : ‖W‖ ≤ M * B + L := by simpa [W] using hwindow_bound
      have hTail : ‖Tail‖ ≤ (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by
        dsimp [Tail, W, K]
        simpa [K] using htail
      linarith
    _ = M * B + L + (1 / (π * R)) * ∫ u : ℝ, ‖f u‖ := by ring

/-- The negative half of the finite sine integral equals the positive half. -/
theorem intervalIntegral_sin_div_kernel_neg_zero_eq_zero_to (A : ℝ) :
    (∫ v in (-A)..0,
      if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)) =
      ∫ v in 0..A,
        if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
  let k : ℝ → ℂ := fun v => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)
  have h := intervalIntegral.integral_comp_neg (f := k) (a := 0) (b := A)
  rw [neg_zero] at h
  rw [← h]
  refine intervalIntegral.integral_congr ?_
  intro v _hv
  by_cases hv : v = 0
  · simp [k, hv]
  · have hneg : -v ≠ 0 := neg_ne_zero.mpr hv
    simp [k, hv, hneg]

/-- The symmetric finite sine integral is twice its positive half. -/
theorem intervalIntegral_sin_div_kernel_symmetric_eq_two_mul_zero_to (A : ℝ) :
    (∫ v in (-A)..A,
      if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)) =
      2 * ∫ v in 0..A,
        if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ) := by
  let k : ℝ → ℂ := fun v => if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)
  have hleft : (∫ v in (-A)..0, k v) = ∫ v in 0..A, k v := by
    exact intervalIntegral_sin_div_kernel_neg_zero_eq_zero_to A
  have hsplit : (∫ v in (-A)..0, k v) + (∫ v in 0..A, k v) =
      ∫ v in (-A)..A, k v := by
    exact intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_sin_div_kernel (-A) 0)
      (intervalIntegrable_sin_div_kernel 0 A)
  calc
    (∫ v in (-A)..A, k v) = (∫ v in (-A)..0, k v) + (∫ v in 0..A, k v) := by
      rw [hsplit]
    _ = (∫ v in 0..A, k v) + (∫ v in 0..A, k v) := by
      rw [hleft]
    _ = 2 * ∫ v in 0..A, k v := by ring

/-- A one-sided Dirichlet integral limit gives the symmetric sine integral
limit. -/
theorem tendsto_intervalIntegral_sin_div_kernel_symmetric_of_one_sided
    (hdir : Filter.Tendsto
      (fun A : ℝ =>
        ∫ v in 0..A,
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      Filter.atTop (nhds ((π / 2 : ℝ) : ℂ))) :
    Filter.Tendsto
      (fun A : ℝ =>
        ∫ v in (-A)..A,
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      Filter.atTop (nhds (π : ℂ)) := by
  have htwo := hdir.const_mul (2 : ℂ)
  convert htwo.congr' ?_ using 1
  · norm_num
    ring
  · filter_upwards with A
    rw [intervalIntegral_sin_div_kernel_symmetric_eq_two_mul_zero_to]

/-- A normalized symmetric Dirichlet integral limit gives the scalar
finite-window mass at every positive radius. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_dirichlet
    {R : ℝ} (hR : 0 < R)
    (hdir : Filter.Tendsto
      (fun A : ℝ =>
        (1 / (π : ℂ)) * ∫ v in (-A)..A,
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      Filter.atTop (nhds (1 : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  have hTR : Filter.Tendsto (fun T : ℝ => T * R) Filter.atTop Filter.atTop := by
    simpa [mul_comm] using
      ((Filter.tendsto_const_mul_atTop_of_pos (f := fun T : ℝ => T) hR).2
        Filter.tendsto_id)
  have hcomp := hdir.comp hTR
  refine hcomp.congr' ?_
  filter_upwards with T
  rw [intervalIntegral_sin_div_kernel_scalar_mass_eq_scaled]
  rw [show T * (-R) = -(T * R) by ring]
  rfl

/-- The classical symmetric sine integral limit, with value `π`, gives the
scalar finite-window mass at every positive radius. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_symmetric_sine_integral
    {R : ℝ} (hR : 0 < R)
    (hdir : Filter.Tendsto
      (fun A : ℝ =>
        ∫ v in (-A)..A,
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      Filter.atTop (nhds (π : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  refine tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_dirichlet hR ?_
  have hnorm := hdir.const_mul (1 / (π : ℂ))
  convert hnorm using 1
  field_simp [Real.pi_ne_zero]

/-- The one-sided Dirichlet integral limit gives the scalar finite-window mass
at every positive radius. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_one_sided_sine_integral
    {R : ℝ} (hR : 0 < R)
    (hdir : Filter.Tendsto
      (fun A : ℝ =>
        ∫ v in 0..A,
          if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ))
      Filter.atTop (nhds ((π / 2 : ℝ) : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  exact tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_symmetric_sine_integral hR
    (tendsto_intervalIntegral_sin_div_kernel_symmetric_of_one_sided hdir)

/-- The one-sided sine-over-argument integral agrees with the integral of
`Real.sinc`; the only difference is the chosen singleton value at zero. -/
theorem intervalIntegral_sin_div_kernel_zero_to_eq_sinc (A : ℝ) :
    (∫ v in 0..A,
      if v = 0 then (0 : ℂ) else (Real.sin v / v : ℂ)) =
      ∫ v in 0..A, (Real.sinc v : ℂ) := by
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [show ∀ᵐ v : ℝ ∂volume, v ≠ 0 by simp [ae_iff, measure_singleton]]
    with v hv _hv_mem
  simp [Real.sinc_of_ne_zero hv, hv]

/-- A complex-valued one-sided sinc integral limit gives the scalar
finite-window mass at every positive radius. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_sinc_integral
    {R : ℝ} (hR : 0 < R)
    (hsinc : Filter.Tendsto
      (fun A : ℝ => ∫ v in 0..A, (Real.sinc v : ℂ))
      Filter.atTop (nhds ((π / 2 : ℝ) : ℂ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  refine tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_one_sided_sine_integral hR ?_
  exact hsinc.congr' (by
    filter_upwards with A
    rw [intervalIntegral_sin_div_kernel_zero_to_eq_sinc])

/-- A real-valued one-sided sinc integral limit gives the scalar finite-window
mass at every positive radius. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_real_sinc_integral
    {R : ℝ} (hR : 0 < R)
    (hsinc : Filter.Tendsto
      (fun A : ℝ => ∫ v in 0..A, Real.sinc v)
      Filter.atTop (nhds (π / 2 : ℝ))) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  refine tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_sinc_integral hR ?_
  simpa [Function.comp_def, intervalIntegral.integral_ofReal] using
    (Complex.continuous_ofReal.tendsto (π / 2 : ℝ)).comp hsinc

/-- Integration by parts for the positive sinc tail on a finite interval. -/
theorem intervalIntegral_sinc_tail_eq_ibp {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, Real.sinc x =
      (-Real.cos b / b + Real.cos a / a) -
        ∫ x in a..b, Real.cos x / x ^ 2 := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hsinc :
      (∫ x in a..b, Real.sinc x) = ∫ x in a..b, x⁻¹ * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    rw [Real.sinc_of_ne_zero hx0]
    ring
  have hu : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x := by
    intro x hx
    exact hasDerivAt_inv (hpos_uIcc x hx).ne'
  have hv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _hx
    simpa using (Real.hasDerivAt_cos x).neg
  have hu' : IntervalIntegrable (fun x : ℝ => -(x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne').neg
  have hv' : IntervalIntegrable (fun x : ℝ => Real.sin x) volume a b :=
    Real.continuous_sin.intervalIntegrable a b
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => x⁻¹) (v := fun x : ℝ => -Real.cos x)
    (u' := fun x : ℝ => -(x ^ 2)⁻¹) (v' := fun x : ℝ => Real.sin x)
    hu hv hu' hv'
  have hint :
      (∫ x in a..b, (-(x ^ 2)⁻¹) * -Real.cos x) =
        ∫ x in a..b, Real.cos x / x ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x _hx
    field_simp [sq]
  rw [hsinc, hIBP, hint]
  ring_nf

/-- The finite inverse-square integral on a positive interval. -/
theorem intervalIntegral_inv_sq_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ x in a..b, (x ^ 2)⁻¹ = a⁻¹ - b⁻¹ := by
  have hpos_uIcc : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact ha.trans_le hx.1
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => -y⁻¹) ((x ^ 2)⁻¹) x := by
    intro x hx
    have h := (hasDerivAt_inv (hpos_uIcc x hx).ne').neg
    convert h using 1
    ring
  have hint : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x (by simpa [Set.uIcc_of_le hab] using hx)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Uniform finite-tail control for the one-sided sinc integral. -/
theorem norm_intervalIntegral_sinc_tail_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∫ x in a..b, Real.sinc x‖ ≤ 3 * a⁻¹ := by
  have ha_pos : 0 < a := zero_lt_one.trans_le ha
  have hb_pos : 0 < b := ha_pos.trans_le hab
  have hpos_uIcc : ∀ x ∈ Set.Icc a b, 0 < x := by
    intro x hx
    exact ha_pos.trans_le hx.1
  have hboundary : ‖-Real.cos b / b + Real.cos a / a‖ ≤ 2 * a⁻¹ := by
    calc
      ‖-Real.cos b / b + Real.cos a / a‖
          = |(-Real.cos b / b) + (Real.cos a / a)| := by rw [Real.norm_eq_abs]
      _ ≤ |-Real.cos b / b| + |Real.cos a / a| := abs_add_le _ _
      _ ≤ b⁻¹ + a⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.cos b / b| = |Real.cos b| / b := by
                  rw [abs_div, abs_neg, abs_of_pos hb_pos]
                _ ≤ 1 / b := div_le_div_of_nonneg_right (Real.abs_cos_le_one b) hb_pos.le
                _ = b⁻¹ := by rw [one_div]
            · calc
                |Real.cos a / a| = |Real.cos a| / a := by
                  rw [abs_div, abs_of_pos ha_pos]
                _ ≤ 1 / a := div_le_div_of_nonneg_right (Real.abs_cos_le_one a) ha_pos.le
                _ = a⁻¹ := by rw [one_div]
      _ ≤ a⁻¹ + a⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le ha_pos hab) le_rfl
      _ = 2 * a⁻¹ := by ring
  have hnormInt : IntervalIntegrable (fun x : ℝ => ‖Real.cos x / x ^ 2‖) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact ((Real.continuous_cos.continuousOn).div (continuousOn_pow 2) fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne').norm
  have hinvInt : IntervalIntegrable (fun x : ℝ => (x ^ 2)⁻¹) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    exact (continuousOn_pow 2).inv₀ fun x hx => by
      exact pow_ne_zero 2 (hpos_uIcc x hx).ne'
  have hJ : ‖∫ x in a..b, Real.cos x / x ^ 2‖ ≤ a⁻¹ := by
    calc
      ‖∫ x in a..b, Real.cos x / x ^ 2‖
          ≤ ∫ x in a..b, ‖Real.cos x / x ^ 2‖ :=
            intervalIntegral.norm_integral_le_integral_norm hab
      _ ≤ ∫ x in a..b, (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hab hnormInt hinvInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_uIcc x hx
            calc
              ‖Real.cos x / x ^ 2‖ = |Real.cos x| / x ^ 2 := by
                rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hx_pos 2)]
              _ ≤ 1 / x ^ 2 :=
                div_le_div_of_nonneg_right (Real.abs_cos_le_one x) (sq_nonneg x)
              _ = (x ^ 2)⁻¹ := by rw [one_div]
      _ = a⁻¹ - b⁻¹ := intervalIntegral_inv_sq_of_pos ha_pos hab
      _ ≤ a⁻¹ := sub_le_self _ (inv_nonneg.mpr hb_pos.le)
  rw [intervalIntegral_sinc_tail_eq_ibp ha_pos hab]
  calc
    ‖(-Real.cos b / b + Real.cos a / a) - ∫ x in a..b, Real.cos x / x ^ 2‖
        ≤ ‖-Real.cos b / b + Real.cos a / a‖ +
            ‖∫ x in a..b, Real.cos x / x ^ 2‖ := norm_sub_le _ _
    _ ≤ 2 * a⁻¹ + a⁻¹ := add_le_add hboundary hJ
    _ = 3 * a⁻¹ := by ring

theorem cauchySeq_intervalIntegral_real_sinc_atTop :
    CauchySeq (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x) := by
  refine Metric.cauchySeq_iff.2 ?_
  intro ε hε
  have hlim : Filter.Tendsto (fun M : ℝ => 3 * M⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
      (fun M : ℝ => 3 * M⁻¹) Filter.atTop (nhds (3 * 0)))
  have hsmall : ∀ᶠ M : ℝ in Filter.atTop, 3 * M⁻¹ < ε :=
    hlim.eventually (gt_mem_nhds hε)
  have hlarge : ∀ᶠ M : ℝ in Filter.atTop, 1 ≤ M := Filter.eventually_ge_atTop 1
  rcases Filter.eventually_atTop.1 (hsmall.and hlarge) with ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro A hA B hB
  have hMsmall : 3 * M⁻¹ < ε := (hM M le_rfl).1
  have hM_one : 1 ≤ M := (hM M le_rfl).2
  have hM_pos : 0 < M := zero_lt_one.trans_le hM_one
  have hA_one : 1 ≤ A := hM_one.trans hA
  have hB_one : 1 ≤ B := hM_one.trans hB
  by_cases hAB : A ≤ B
  · have hsub :
        (∫ x in (0 : ℝ)..B, Real.sinc x) -
          (∫ x in (0 : ℝ)..A, Real.sinc x) =
            ∫ x in A..B, Real.sinc x := by
      exact intervalIntegral.integral_interval_sub_left
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)
    have hinv : A⁻¹ ≤ M⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hM_pos hA
    calc
      dist (∫ x in (0 : ℝ)..A, Real.sinc x) (∫ x in (0 : ℝ)..B, Real.sinc x)
          = dist (∫ x in (0 : ℝ)..B, Real.sinc x) (∫ x in (0 : ℝ)..A, Real.sinc x) :=
            dist_comm _ _
      _ = ‖(∫ x in (0 : ℝ)..B, Real.sinc x) -
            (∫ x in (0 : ℝ)..A, Real.sinc x)‖ := by
            rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖∫ x in A..B, Real.sinc x‖ := by rw [hsub]
      _ ≤ 3 * A⁻¹ := norm_intervalIntegral_sinc_tail_le hA_one hAB
      _ ≤ 3 * M⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ < ε := hMsmall
  · have hBA : B ≤ A := le_of_not_ge hAB
    have hsub :
        (∫ x in (0 : ℝ)..A, Real.sinc x) -
          (∫ x in (0 : ℝ)..B, Real.sinc x) =
            ∫ x in B..A, Real.sinc x := by
      exact intervalIntegral.integral_interval_sub_left
        (Real.continuous_sinc.intervalIntegrable _ _)
        (Real.continuous_sinc.intervalIntegrable _ _)
    have hinv : B⁻¹ ≤ M⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le hM_pos hB
    calc
      dist (∫ x in (0 : ℝ)..A, Real.sinc x) (∫ x in (0 : ℝ)..B, Real.sinc x)
          = ‖(∫ x in (0 : ℝ)..A, Real.sinc x) -
            (∫ x in (0 : ℝ)..B, Real.sinc x)‖ := by
            rw [Real.dist_eq, Real.norm_eq_abs]
      _ = ‖∫ x in B..A, Real.sinc x‖ := by rw [hsub]
      _ ≤ 3 * B⁻¹ := norm_intervalIntegral_sinc_tail_le hB_one hBA
      _ ≤ 3 * M⁻¹ := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ < ε := hMsmall

/-- Existence of the improper one-sided sinc integral as a finite-window limit. -/
theorem exists_tendsto_intervalIntegral_real_sinc_atTop :
    ∃ L : ℝ,
      Filter.Tendsto (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x)
        Filter.atTop (nhds L) :=
  cauchySeq_tendsto_of_complete cauchySeq_intervalIntegral_real_sinc_atTop

/-- Exact integral of the derivative of `-exp (-a * x)` on a finite interval. -/
theorem intervalIntegral_exp_neg_mul_const_mul_self (a R B : ℝ) :
    ∫ x in R..B, a * Real.exp (-a * x) =
      Real.exp (-a * R) - Real.exp (-a * B) := by
  have hderiv : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.exp (-a * y)) (a * Real.exp (-a * x)) x := by
    intro x _hx
    have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have h := (Real.hasDerivAt_exp (-a * x)).comp x hlin
    have hneg := h.neg
    convert hneg using 1
    ring_nf
  have hint : IntervalIntegrable (fun x : ℝ => a * Real.exp (-a * x)) volume R B := by
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- Uniform finite-tail control for the damped one-sided sinc integral. -/
theorem norm_intervalIntegral_exp_neg_mul_sinc_tail_le
    {a R B : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hRB : R ≤ B) :
    ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hB_pos : 0 < B := hR_pos.trans_le hRB
  have hpos_uIcc : ∀ x ∈ Set.uIcc R B, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hRB] at hx
    exact hR_pos.trans_le hx.1
  have hpos_Icc : ∀ x ∈ Set.Icc R B, 0 < x := by
    intro x hx
    exact hR_pos.trans_le hx.1
  have hsinc :
      (∫ x in R..B, Real.exp (-a * x) * Real.sinc x) =
        ∫ x in R..B, (Real.exp (-a * x) * x⁻¹) * Real.sin x := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    simp only [Real.sinc_of_ne_zero hx0]
    ring
  have hu : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => Real.exp (-a * y) * y⁻¹)
        (-(a * Real.exp (-a * x) * x⁻¹) - Real.exp (-a * x) * (x ^ 2)⁻¹) x := by
    intro x hx
    have hx0 : x ≠ 0 := (hpos_uIcc x hx).ne'
    have hlin : HasDerivAt (fun y : ℝ => -a * y) (-a) x := by
      simpa using (hasDerivAt_id x).const_mul (-a)
    have hexp := (Real.hasDerivAt_exp (-a * x)).comp x hlin
    have hinv := hasDerivAt_inv hx0
    have hmul := hexp.mul hinv
    convert hmul using 1
    simp
    ring_nf
  have hv : ∀ x ∈ Set.uIcc R B,
      HasDerivAt (fun y : ℝ => -Real.cos y) (Real.sin x) x := by
    intro x _hx
    simpa using (Real.hasDerivAt_cos x).neg
  have hu' : IntervalIntegrable
      (fun x : ℝ => -(a * Real.exp (-a * x) * x⁻¹) -
        Real.exp (-a * x) * (x ^ 2)⁻¹) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc R B) :=
      continuousOn_id.inv₀ fun x hx => (hpos_Icc x hx).ne'
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact (((continuousOn_const.mul hcont_exp).mul hcont_inv).neg.sub
      (hcont_exp.mul hcont_inv_sq))
  have hv' : IntervalIntegrable (fun x : ℝ => Real.sin x) volume R B :=
    Real.continuous_sin.intervalIntegrable R B
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => Real.exp (-a * x) * x⁻¹) (v := fun x : ℝ => -Real.cos x)
    (u' := fun x : ℝ => -(a * Real.exp (-a * x) * x⁻¹) -
      Real.exp (-a * x) * (x ^ 2)⁻¹)
    (v' := fun x : ℝ => Real.sin x) hu hv hu' hv'
  have hint :
      (∫ x in R..B,
        (-(a * Real.exp (-a * x) * x⁻¹) - Real.exp (-a * x) * (x ^ 2)⁻¹) *
          -Real.cos x) =
        ∫ x in R..B,
          (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
            Real.cos x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    ring
  have hrepr :
      ∫ x in R..B, Real.exp (-a * x) * Real.sinc x =
        (-Real.exp (-a * B) * B⁻¹ * Real.cos B +
            Real.exp (-a * R) * R⁻¹ * Real.cos R) -
          ∫ x in R..B,
            (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
              Real.cos x := by
    rw [hsinc, hIBP, hint]
    ring
  have hboundary :
      ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
          Real.exp (-a * R) * R⁻¹ * Real.cos R‖ ≤ 2 * R⁻¹ := by
    calc
      ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
          Real.exp (-a * R) * R⁻¹ * Real.cos R‖
          = |(-Real.exp (-a * B) * B⁻¹ * Real.cos B) +
              (Real.exp (-a * R) * R⁻¹ * Real.cos R)| := by rw [Real.norm_eq_abs]
      _ ≤ |-Real.exp (-a * B) * B⁻¹ * Real.cos B| +
            |Real.exp (-a * R) * R⁻¹ * Real.cos R| := abs_add_le _ _
      _ ≤ B⁻¹ + R⁻¹ := by
            refine add_le_add ?_ ?_
            · calc
                |-Real.exp (-a * B) * B⁻¹ * Real.cos B|
                    = Real.exp (-a * B) * B⁻¹ * |Real.cos B| := by
                      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
                        abs_of_pos (inv_pos.mpr hB_pos)]
                  _ ≤ 1 * B⁻¹ * 1 := by
                      gcongr
                      · exact Real.exp_le_one_iff.mpr (by
                          have hmul : 0 ≤ a * B := mul_nonneg ha.le hB_pos.le
                          nlinarith)
                      · exact Real.abs_cos_le_one B
                  _ = B⁻¹ := by ring
            · calc
                |Real.exp (-a * R) * R⁻¹ * Real.cos R|
                    = Real.exp (-a * R) * R⁻¹ * |Real.cos R| := by
                      rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
                        abs_of_pos (inv_pos.mpr hR_pos)]
                  _ ≤ 1 * R⁻¹ * 1 := by
                      gcongr
                      · exact Real.exp_le_one_iff.mpr (by
                          have hmul : 0 ≤ a * R := mul_nonneg ha.le hR_pos.le
                          nlinarith)
                      · exact Real.abs_cos_le_one R
                  _ = R⁻¹ := by ring
      _ ≤ R⁻¹ + R⁻¹ := by
            exact add_le_add (by
              simpa [one_div] using one_div_le_one_div_of_le hR_pos hRB) le_rfl
      _ = 2 * R⁻¹ := by ring
  have hnormInt : IntervalIntegrable
      (fun x : ℝ =>
        ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc R B) :=
      continuousOn_id.inv₀ fun x hx => (hpos_Icc x hx).ne'
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact ((((continuousOn_const.mul hcont_exp).mul hcont_inv).add
      (hcont_exp.mul hcont_inv_sq)).mul Real.continuous_cos.continuousOn).norm
  have hboundInt : IntervalIntegrable
      (fun x : ℝ => R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹) volume R B := by
    apply ContinuousOn.intervalIntegrable_of_Icc hRB
    have hcont_exp : ContinuousOn (fun x : ℝ => Real.exp (-a * x)) (Set.Icc R B) := by
      fun_prop
    have hcont_inv_sq : ContinuousOn (fun x : ℝ => (x ^ 2)⁻¹) (Set.Icc R B) :=
      (continuousOn_pow 2).inv₀ fun x hx => pow_ne_zero 2 (hpos_Icc x hx).ne'
    exact ((continuousOn_const.mul (continuousOn_const.mul hcont_exp)).add hcont_inv_sq)
  have hJ :
      ‖∫ x in R..B,
        (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖ ≤ 2 * R⁻¹ := by
    calc
      ‖∫ x in R..B,
        (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
          Real.cos x‖
          ≤ ∫ x in R..B,
              ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖ :=
            intervalIntegral.norm_integral_le_integral_norm hRB
      _ ≤ ∫ x in R..B, R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹ := by
            refine intervalIntegral.integral_mono_on hRB hnormInt hboundInt ?_
            intro x hx
            have hx_pos : 0 < x := hpos_Icc x hx
            have hR_inv : x⁻¹ ≤ R⁻¹ := by
              simpa [one_div] using one_div_le_one_div_of_le hR_pos hx.1
            calc
              ‖(a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖
                  ≤ |a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹| := by
                    rw [Real.norm_eq_abs, abs_mul]
                    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one x)
              _ = a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹ := by
                    rw [abs_of_nonneg]
                    positivity
              _ ≤ R⁻¹ * (a * Real.exp (-a * x)) + (x ^ 2)⁻¹ := by
                    refine add_le_add ?_ ?_
                    · calc
                        a * Real.exp (-a * x) * x⁻¹
                            = (a * Real.exp (-a * x)) * x⁻¹ := by ring
                        _ ≤ (a * Real.exp (-a * x)) * R⁻¹ :=
                            mul_le_mul_of_nonneg_left hR_inv
                              (mul_nonneg ha.le (Real.exp_pos _).le)
                        _ = R⁻¹ * (a * Real.exp (-a * x)) := by ring
                    · calc
                        Real.exp (-a * x) * (x ^ 2)⁻¹
                            ≤ 1 * (x ^ 2)⁻¹ := by
                              exact mul_le_mul_of_nonneg_right
                                (Real.exp_le_one_iff.mpr (by
                                  have hmul : 0 ≤ a * x := mul_nonneg ha.le hx_pos.le
                                  nlinarith))
                                (inv_nonneg.mpr (sq_nonneg x))
                        _ = (x ^ 2)⁻¹ := by ring
      _ = R⁻¹ * (∫ x in R..B, a * Real.exp (-a * x)) +
            ∫ x in R..B, (x ^ 2)⁻¹ := by
            rw [intervalIntegral.integral_add]
            · rw [intervalIntegral.integral_const_mul]
            · exact (Continuous.intervalIntegrable (by fun_prop) R B).const_mul _
            · apply ContinuousOn.intervalIntegrable_of_Icc hRB
              exact (continuousOn_pow 2).inv₀ fun x hx =>
                pow_ne_zero 2 (hpos_Icc x hx).ne'
      _ = R⁻¹ * (Real.exp (-a * R) - Real.exp (-a * B)) + (R⁻¹ - B⁻¹) := by
            rw [intervalIntegral_exp_neg_mul_const_mul_self a R B,
              intervalIntegral_inv_sq_of_pos hR_pos hRB]
      _ ≤ R⁻¹ * 1 + R⁻¹ := by
            gcongr
            · exact (sub_le_self _ (Real.exp_pos _).le).trans
                (Real.exp_le_one_iff.mpr (by
                  have hmul : 0 ≤ a * R := mul_nonneg ha.le hR_pos.le
                  nlinarith))
            · exact sub_le_self _ (inv_nonneg.mpr hB_pos.le)
      _ = 2 * R⁻¹ := by ring
  rw [hrepr]
  calc
    ‖(-Real.exp (-a * B) * B⁻¹ * Real.cos B +
        Real.exp (-a * R) * R⁻¹ * Real.cos R) -
        ∫ x in R..B,
          (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
            Real.cos x‖
        ≤ ‖-Real.exp (-a * B) * B⁻¹ * Real.cos B +
            Real.exp (-a * R) * R⁻¹ * Real.cos R‖ +
            ‖∫ x in R..B,
              (a * Real.exp (-a * x) * x⁻¹ + Real.exp (-a * x) * (x ^ 2)⁻¹) *
                Real.cos x‖ := norm_sub_le _ _
    _ ≤ 2 * R⁻¹ + 2 * R⁻¹ := add_le_add hboundary hJ
    _ = 4 * R⁻¹ := by ring

theorem integral_Ioi_exp_neg_mul_sin (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x = 1 / (a ^ 2 + 1) := by
  let z : ℂ := (-(a : ℂ)) + Complex.I
  have hzre : z.re < 0 := by simp [z, ha]
  have hint : Integrable (fun x : ℝ => Complex.exp (z * x)) (volume.restrict (Set.Ioi 0)) := by
    exact integrableOn_exp_mul_complex_Ioi (a := z) hzre 0
  have him := integral_im (μ := volume.restrict (Set.Ioi 0)) hint
  have hpoint : (fun x : ℝ => Real.exp (-a * x) * Real.sin x) =
      fun x : ℝ => (Complex.exp (z * x)).im := by
    funext x
    simp [z, Complex.exp_im, mul_add, mul_comm]
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sin x
        = ∫ x : ℝ in Set.Ioi 0, (Complex.exp (z * x)).im := by
          rw [hpoint]
    _ = (∫ x : ℝ in Set.Ioi 0, Complex.exp (z * x)).im := by
          simpa using him
    _ = (-Complex.exp (z * (0 : ℝ)) / z).im := by
          rw [integral_exp_mul_complex_Ioi (a := z) hzre 0]
    _ = 1 / (a ^ 2 + 1) := by
          simp [z, Complex.div_im, Complex.normSq]
          ring

/-- The arctangent tail integral in the denominator shape used by the damped
sine computation. -/
theorem integral_Ioi_one_div_one_add_sq_eq_pi_div_two_sub_arctan (a : ℝ) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) = π / 2 - Real.arctan a := by
  simpa [one_div, add_comm] using integral_Ioi_inv_one_add_sq (i := a)

/-- For a positive lower endpoint, the arctangent tail integral is
`arctan (1/a)`. -/
theorem integral_Ioi_one_div_one_add_sq_eq_arctan_inv (a : ℝ) (ha : 0 < a) :
    ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) = Real.arctan a⁻¹ := by
  rw [integral_Ioi_one_div_one_add_sq_eq_pi_div_two_sub_arctan]
  exact (Real.arctan_inv_of_pos ha).symm

/-- The exponentially damped sinc function is integrable on the positive
half-line. -/
theorem integrableOn_exp_neg_mul_sinc (a : ℝ) (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi 0) := by
  change Integrable (fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
    (volume.restrict (Set.Ioi 0))
  have h_exp : Integrable (fun x : ℝ => Real.exp (-a * x))
      (volume.restrict (Set.Ioi 0)) := by
    simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
  refine h_exp.mono ?_ ?_
  · exact (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (volume.restrict (Set.Ioi 0)))
  · filter_upwards with x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one x)

/-- Uniform half-line tail control for the damped one-sided sinc integral. -/
theorem norm_integral_Ioi_exp_neg_mul_sinc_tail_le
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) :
    ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
  have hR_pos : 0 < R := zero_lt_one.trans_le hR
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-a * x) * Real.sinc x) (Set.Ioi R) := by
    exact (integrableOn_exp_neg_mul_sinc a ha).mono_set (Set.Ioi_subset_Ioi hR_pos.le)
  have htend :=
    intervalIntegral_tendsto_integral_Ioi
      (f := fun x : ℝ => Real.exp (-a * x) * Real.sinc x)
      (a := R) (b := fun B : ℝ => B) hint Filter.tendsto_id
  have hnorm :
      Filter.Tendsto
        (fun B : ℝ => ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖)
        Filter.atTop
        (nhds ‖∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x‖) :=
    continuous_norm.tendsto
      (∫ x : ℝ in Set.Ioi R, Real.exp (-a * x) * Real.sinc x) |>.comp htend
  have hbound : ∀ᶠ B : ℝ in Filter.atTop,
      ‖∫ x in R..B, Real.exp (-a * x) * Real.sinc x‖ ≤ 4 * R⁻¹ := by
    filter_upwards [Filter.eventually_ge_atTop R] with B hRB
    exact norm_intervalIntegral_exp_neg_mul_sinc_tail_le ha hR hRB
  exact le_of_tendsto hnorm hbound

/-- On a fixed finite window, damping tends back to the undamped sinc integral. -/
theorem tendsto_intervalIntegral_exp_neg_mul_sinc_nhdsGT_zero (R : ℝ) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x in (0 : ℝ)..R, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ x in (0 : ℝ)..R, Real.sinc x)) := by
  let f : ℝ → ℝ → ℝ := fun a x => Real.exp (-a * x) * Real.sinc x
  have hf : Continuous f.uncurry := by
    dsimp [f, Function.uncurry]
    fun_prop
  have hcont : Continuous fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (μ := volume) (f := f) hf (0 : ℝ) R
  have ht : Filter.Tendsto (fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x)
      (𝓝 (0 : ℝ)) (nhds (∫ x in (0 : ℝ)..R, f 0 x)) :=
    hcont.tendsto (0 : ℝ)
  have ht' : Filter.Tendsto (fun a : ℝ => ∫ x in (0 : ℝ)..R, f a x)
      (𝓝[>] (0 : ℝ)) (nhds (∫ x in (0 : ℝ)..R, f 0 x)) :=
    ht.mono_left nhdsWithin_le_nhds
  simpa [f] using ht'

/-- Abel comparison: any finite-window sinc limit agrees with the damped
half-line limit. -/
theorem tendsto_integral_Ioi_exp_neg_mul_sinc_of_tendsto_interval
    {L : ℝ}
    (hL : Filter.Tendsto
      (fun R : ℝ => ∫ x in (0 : ℝ)..R, Real.sinc x)
      Filter.atTop (nhds L)) :
    Filter.Tendsto
      (fun a : ℝ => ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ)) (nhds L) := by
  rw [Metric.tendsto_nhds] at hL ⊢
  intro ε hε
  let η : ℝ := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hL_event : ∀ᶠ R : ℝ in Filter.atTop,
      dist (∫ x in (0 : ℝ)..R, Real.sinc x) L < η :=
    hL η hη
  have htail_lim : Filter.Tendsto (fun R : ℝ => 4 * R⁻¹) Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul tendsto_inv_atTop_zero : Filter.Tendsto
      (fun R : ℝ => 4 * R⁻¹) Filter.atTop (nhds (4 * 0)))
  have htail_event : ∀ᶠ R : ℝ in Filter.atTop, 4 * R⁻¹ < η :=
    htail_lim.eventually (gt_mem_nhds hη)
  have hlarge : ∀ᶠ R : ℝ in Filter.atTop, 1 ≤ R := Filter.eventually_ge_atTop 1
  rcases Filter.eventually_atTop.1 (hL_event.and (htail_event.and hlarge)) with ⟨R, hR⟩
  have hFR_dist : dist (∫ x in (0 : ℝ)..R, Real.sinc x) L < η := (hR R le_rfl).1
  have htail_small : 4 * R⁻¹ < η := (hR R le_rfl).2.1
  have hR_one : 1 ≤ R := (hR R le_rfl).2.2
  have hR_pos : 0 < R := zero_lt_one.trans_le hR_one
  have hfinite_event :
      ∀ᶠ a : ℝ in 𝓝[>] (0 : ℝ),
        dist (∫ x in (0 : ℝ)..R, Real.exp (-a * x) * Real.sinc x)
          (∫ x in (0 : ℝ)..R, Real.sinc x) < η :=
    Metric.tendsto_nhds.mp (tendsto_intervalIntegral_exp_neg_mul_sinc_nhdsGT_zero R) η hη
  filter_upwards [hfinite_event, self_mem_nhdsWithin] with a hfinite ha_mem
  have ha : 0 < a := ha_mem
  let g : ℝ → ℝ := fun x => Real.exp (-a * x) * Real.sinc x
  let D : ℝ := ∫ x in (0 : ℝ)..R, g x
  let F : ℝ := ∫ x in (0 : ℝ)..R, Real.sinc x
  let T : ℝ := ∫ x : ℝ in Set.Ioi R, g x
  let G : ℝ := ∫ x : ℝ in Set.Ioi 0, g x
  have hg0 : IntegrableOn g (Set.Ioi 0) := by
    dsimp [g]
    exact integrableOn_exp_neg_mul_sinc a ha
  have hgR : IntegrableOn g (Set.Ioi R) := by
    exact hg0.mono_set (Set.Ioi_subset_Ioi hR_pos.le)
  have hsplit : D + T = G := by
    dsimp [D, T, G, g]
    exact intervalIntegral.integral_interval_add_Ioi hg0 hgR
  have hfinite_norm : ‖D - F‖ < η := by
    simpa [D, F, g, Real.dist_eq, Real.norm_eq_abs] using hfinite
  have hFR_norm : ‖F - L‖ < η := by
    simpa [F, Real.dist_eq, Real.norm_eq_abs] using hFR_dist
  have htail_norm : ‖T‖ < η := by
    have htail_le : ‖T‖ ≤ 4 * R⁻¹ := by
      dsimp [T, g]
      exact norm_integral_Ioi_exp_neg_mul_sinc_tail_le ha hR_one
    exact lt_of_le_of_lt htail_le htail_small
  have htriangle :
      ‖G - L‖ ≤ ‖D - F‖ + ‖T‖ + ‖F - L‖ := by
    calc
      ‖G - L‖ = ‖(D - F) + T + (F - L)‖ := by
        rw [← hsplit]
        congr 1
        ring
      _ ≤ ‖(D - F) + T‖ + ‖F - L‖ := norm_add_le _ _
      _ ≤ (‖D - F‖ + ‖T‖) + ‖F - L‖ := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (norm_add_le (D - F) T) ‖F - L‖
      _ = ‖D - F‖ + ‖T‖ + ‖F - L‖ := by ring
  have hsum : ‖D - F‖ + ‖T‖ + ‖F - L‖ < ε := by
    have hsum_eta : ‖D - F‖ + ‖T‖ + ‖F - L‖ < η + η + η := by
      nlinarith [hfinite_norm, htail_norm, hFR_norm]
    have heta : η + η + η < ε := by
      dsimp [η]
      nlinarith [hε]
    exact lt_trans hsum_eta heta
  have hG : dist G L < ε := by
    simpa [Real.dist_eq, Real.norm_eq_abs] using lt_of_le_of_lt htriangle hsum
  simpa [G, g] using hG

/-- Positive half-line exponential tail with a variable decay constant. -/
theorem integral_Ioi_exp_neg_mul_const (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) = Real.exp (-a * x) / x := by
  have h := integral_exp_mul_Ioi (a := -x) (by linarith : -x < 0) a
  calc
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x)
        = ∫ u : ℝ in Set.Ioi a, Real.exp ((-x) * u) := by
          congr with u
          ring_nf
    _ = Real.exp (-a * x) / x := by
          rw [h]
          field_simp [hx.ne']

/-- The pointwise representation of the damped sinc kernel by an exponential
tail integral. -/
theorem integral_Ioi_exp_neg_mul_const_mul_sin (a x : ℝ) (hx : 0 < x) :
    ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x =
      Real.exp (-a * x) * Real.sinc x := by
  rw [integral_mul_const]
  rw [integral_Ioi_exp_neg_mul_const a x hx]
  rw [Real.sinc_of_ne_zero hx.ne']
  field_simp [hx.ne']

/-- Evaluation of the damped sinc integral from the one remaining Fubini swap.
The hypothesis is the exact product-integrability/swap term left to prove. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_integral_swap
    (a : ℝ) (ha : 0 < a)
    (hswap :
      (∫ x : ℝ in Set.Ioi 0,
        ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
      ∫ u : ℝ in Set.Ioi a,
        ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ := by
  calc
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x
        = ∫ x : ℝ in Set.Ioi 0,
            ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
          exact (integral_Ioi_exp_neg_mul_const_mul_sin a x hx).symm
    _ = ∫ u : ℝ in Set.Ioi a,
          ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := hswap
    _ = ∫ u : ℝ in Set.Ioi a, (1 / (u ^ 2 + 1) : ℝ) := by
          refine integral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
          exact integral_Ioi_exp_neg_mul_sin u (lt_trans ha hu)
    _ = Real.arctan a⁻¹ := integral_Ioi_one_div_one_add_sq_eq_arctan_inv a ha

/-- The standard Fubini theorem gives the damped-sinc swap once the product
kernel is integrable. -/
theorem integral_Ioi_exp_neg_mul_sinc_integral_swap_of_integrable
    (a : ℝ)
    (hprod : Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a)))) :
    (∫ x : ℝ in Set.Ioi 0,
      ∫ u : ℝ in Set.Ioi a, Real.exp (-u * x) * Real.sin x) =
    ∫ u : ℝ in Set.Ioi a,
      ∫ x : ℝ in Set.Ioi 0, Real.exp (-u * x) * Real.sin x := by
  simpa [Function.uncurry] using integral_integral_swap hprod

/-- Evaluation of the damped sinc integral from product-integrability of the
Fubini kernel. This is the canonical remaining input for the regularized sinc
route. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_product_integrable
    (a : ℝ) (ha : 0 < a)
    (hprod : Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a)))) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ :=
  integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_integral_swap a ha
    (integral_Ioi_exp_neg_mul_sinc_integral_swap_of_integrable a hprod)

/-- Product-integrability of the damped sine kernel on `(0,∞) × (a,∞)`.
The proof integrates the `u`-tail first and bounds the inner norm by
`exp (-a*x)` using `|sin x| ≤ x` for `x > 0`. -/
theorem integrable_exp_neg_mul_sin_prod_Ioi (a : ℝ) (ha : 0 < a) :
    Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi a))) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  let ν := volume.restrict (Set.Ioi a)
  change Integrable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν)
  have hsm : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν) := by
    exact (by fun_prop : AEStronglyMeasurable
      (Function.uncurry
        (fun x u : ℝ => Real.exp (-u * x) * Real.sin x)) (μ.prod ν))
  rw [integrable_prod_iff hsm]
  constructor
  · dsimp [μ]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change Integrable (fun u : ℝ => Real.exp (-u * x) * Real.sin x) ν
    have h_exp : Integrable (fun u : ℝ => Real.exp (-u * x)) ν := by
      dsimp [ν]
      simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx) a
    exact h_exp.mul_const (Real.sin x)
  · have h_exp_a : Integrable (fun x : ℝ => Real.exp (-a * x)) μ := by
      dsimp [μ]
      simpa [mul_comm] using exp_neg_integrableOn_Ioi (0 : ℝ) (b := a) ha
    refine h_exp_a.mono ?_ ?_
    · exact hsm.norm.integral_prod_right'
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hx0 : 0 < x := hx
      have h_exp_x : Integrable (fun y : ℝ => Real.exp (-y * x)) ν := by
        dsimp [ν]
        simpa [mul_comm] using integrableOn_exp_mul_Ioi (a := -x) (neg_lt_zero.mpr hx0) a
      have h_lhs : Integrable
          (fun y : ℝ => ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖) ν := by
        simpa [Function.uncurry] using (h_exp_x.mul_const (Real.sin x)).norm
      have h_rhs : Integrable (fun y : ℝ => Real.exp (-y * x) * x) ν :=
        h_exp_x.mul_const x
      calc
        ‖∫ y : ℝ, ‖Function.uncurry
            (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν‖
            = ∫ y : ℝ, ‖Function.uncurry
                (fun x u : ℝ => Real.exp (-u * x) * Real.sin x) (x, y)‖ ∂ν := by
              rw [Real.norm_eq_abs, abs_of_nonneg]
              exact integral_nonneg fun y => norm_nonneg _
        _ ≤ ∫ y : ℝ, Real.exp (-y * x) * x ∂ν := by
              refine integral_mono_ae h_lhs h_rhs ?_
              filter_upwards with y
              rw [Function.uncurry, Real.norm_eq_abs, abs_mul,
                abs_of_pos (Real.exp_pos _)]
              exact mul_le_mul_of_nonneg_left
                (by simpa [abs_of_pos hx0] using (Real.abs_sin_le_abs (x := x)))
                (Real.exp_pos _).le
        _ = Real.exp (-a * x) := by
              dsimp [ν]
              rw [integral_mul_const]
              rw [integral_Ioi_exp_neg_mul_const a x hx0]
              field_simp [hx0.ne']
        _ = ‖Real.exp (-a * x)‖ := by
              rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The Laplace-regularized one-sided sinc integral. This is the Abelian input
for the classical `∫₀ᴬ sinc -> π/2` route. -/
theorem integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv (a : ℝ) (ha : 0 < a) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x =
      Real.arctan a⁻¹ :=
  integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv_of_product_integrable a ha
    (integrable_exp_neg_mul_sin_prod_Ioi a ha)

/-- Abel limit of the Laplace-regularized sinc integral as the damping tends
to zero from the right. -/
theorem tendsto_integral_Ioi_exp_neg_mul_sinc_nhdsGT_zero :
    Filter.Tendsto
      (fun a : ℝ => ∫ x : ℝ in Set.Ioi 0, Real.exp (-a * x) * Real.sinc x)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) := by
  have hinv : Filter.Tendsto (fun a : ℝ => a⁻¹) (𝓝[>] (0 : ℝ)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have harctan : Filter.Tendsto (fun a : ℝ => Real.arctan a⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 (π / 2 : ℝ)) :=
    (Real.tendsto_arctan_atTop.comp hinv).mono_right nhdsWithin_le_nhds
  refine harctan.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (integral_Ioi_exp_neg_mul_sinc_eq_arctan_inv a ha).symm

/-- The classical one-sided sinc integral tends to `π / 2`. -/
theorem tendsto_intervalIntegral_real_sinc_atTop :
    Filter.Tendsto
      (fun A : ℝ => ∫ x in (0 : ℝ)..A, Real.sinc x)
      Filter.atTop (nhds (π / 2 : ℝ)) := by
  rcases exists_tendsto_intervalIntegral_real_sinc_atTop with ⟨L, hL⟩
  have hAbelL := tendsto_integral_Ioi_exp_neg_mul_sinc_of_tendsto_interval hL
  have hlim : L = π / 2 :=
    tendsto_nhds_unique hAbelL tendsto_integral_Ioi_exp_neg_mul_sinc_nhdsGT_zero
  simpa [hlim] using hL

/-- Scalar finite-window mass of the principal-value sine kernel. -/
theorem tendsto_intervalIntegral_sin_div_kernel_scalar_mass {R : ℝ} (hR : 0 < R) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ))
      Filter.atTop (nhds (1 : ℂ)) := by
  exact tendsto_intervalIntegral_sin_div_kernel_scalar_mass_of_real_sinc_integral hR
    tendsto_intervalIntegral_real_sinc_atTop

/-- The scalar finite-window sine-kernel mass is eventually bounded by `2`. -/
theorem eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two
    {R : ℝ} (hR : 0 < R) :
    ∀ᶠ T in Filter.atTop,
      ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ 2 := by
  have hlim := tendsto_intervalIntegral_sin_div_kernel_scalar_mass hR
  have hnear : ∀ᶠ T in Filter.atTop,
      dist (∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) (1 : ℂ) < 1 :=
    hlim.eventually (Metric.ball_mem_nhds (1 : ℂ) zero_lt_one)
  filter_upwards [hnear] with T hT
  have hnorm_sub : ‖(∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
        (1 : ℂ)‖ < 1 := by
    simpa [dist_eq_norm] using hT
  calc
    ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖
        = ‖(1 : ℂ) + ((∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
            (1 : ℂ))‖ := by
          congr 1
          abel
    _ ≤ ‖(1 : ℂ)‖ + ‖(∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) -
            (1 : ℂ)‖ := norm_add_le _ _
    _ ≤ 2 := by
      norm_num at hnorm_sub ⊢
      linarith

/-- Windowed principal-value convergence for the sinc kernel. This avoids
treating the non-integrable constant kernel mass as a whole-line Bochner
integral: the remaining analytic work is split into a finite-window mass limit,
a finite-window local error limit, and a tail-control limit. -/
theorem sinc_kernel_tendsto_of_windowed_pv
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ}
    (hconst : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
        volume (-R) R)
    (herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R)
    (hmass : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      Filter.atTop (nhds (f x)))
    (herror : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have hsplit : (fun T : ℝ =>
      ∫ u in (-R)..R,
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
          f (x - u)) =ᶠ[Filter.atTop]
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x)) := by
    filter_upwards [hconst, herrInt] with T hconstT herrT
    exact intervalIntegral_sin_div_kernel_split (E := E) f x T R hconstT herrT
  have hwindowSum : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x +
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x))
      Filter.atTop (nhds (f x)) := by
    simpa using hmass.add herror
  have hwindow : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u))
      Filter.atTop (nhds (f x)) := by
    exact hwindowSum.congr' hsplit.symm
  have hwhole : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u))
      Filter.atTop (nhds (f x)) := by
    have hsum : Filter.Tendsto
        (fun T : ℝ =>
          (∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u)) +
            ((∫ u : ℝ,
              (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                f (x - u)) -
              ∫ u in (-R)..R,
                (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
                  f (x - u)))
        Filter.atTop (nhds (f x)) := by
      simpa using hwindow.add htail
    refine hsum.congr' ?_
    filter_upwards with T
    abel
  refine hwhole.congr' ?_
  filter_upwards with T
  exact (normalized_sinc_kernel_integral_comp_sub_left_sin_div_ae (E := E) f x T).symm

/-- Windowed principal-value convergence with the finite-window mass discharged
by the scalar sinc limit. -/
theorem sinc_kernel_tendsto_of_windowed_pv_of_pos_radius
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R)
    (herror : Filter.Tendsto
      (fun T : ℝ =>
        ∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
      Filter.atTop (nhds 0))
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have hmass : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u in (-R)..R,
          if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
      Filter.atTop (nhds (f x)) :=
    tendsto_intervalIntegral_sin_div_kernel_smul_of_scalar_mass (E := E) (f x)
      (tendsto_intervalIntegral_sin_div_kernel_scalar_mass hR)
  have hconst : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) • f x)
        volume (-R) R := by
    exact Filter.Eventually.of_forall fun T =>
      intervalIntegrable_sin_div_kernel_smul_const (E := E) (f x) T (-R) R
  exact sinc_kernel_tendsto_of_windowed_pv (E := E) hconst herrInt hmass herror htail

/-- Windowed principal-value convergence from local quotient integrability and
tail control. -/
theorem sinc_kernel_tendsto_of_windowed_pv_of_local_quotient
    [CompleteSpace E] {f : ℝ → E} {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R)
    (htail : Filter.Tendsto
      (fun T : ℝ =>
        (∫ u : ℝ,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            f (x - u)) -
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              f (x - u))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  have herrInt : ∀ᶠ T in Filter.atTop,
      IntervalIntegrable
        (fun u : ℝ =>
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
            (f (x - u) - f x))
        volume (-R) R := by
    exact Filter.Eventually.of_forall
      (intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
        (E := E) hq)
  have herror :
      Filter.Tendsto
        (fun T : ℝ =>
          ∫ u in (-R)..R,
            (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (π * u) : ℂ)) •
              (f (x - u) - f x))
        Filter.atTop (nhds 0) :=
    tendsto_intervalIntegral_sin_div_kernel_error_of_intervalIntegrable_quotient
      (E := E) hR hq
  exact sinc_kernel_tendsto_of_windowed_pv_of_pos_radius (E := E) hR
    herrInt herror htail

/-- Principal-value convergence for the sinc kernel from source integrability
and local quotient integrability at the target point. -/
theorem sinc_kernel_tendsto_of_integrable_local_quotient
    [CompleteSpace E] {f : ℝ → E} (hf : Integrable f) {x R : ℝ} (hR : 0 < R)
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (π * u) : ℂ) • (f (x - u) - f x))
      volume (-R) R) :
    Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ, (2 * T * Real.sinc (T * (x - y)) : ℂ) • f y)
      Filter.atTop (nhds (f x)) := by
  exact sinc_kernel_tendsto_of_windowed_pv_of_local_quotient (E := E) hR hq
    (tendsto_sin_div_kernel_tail_of_integrable (E := E) hf hR)

theorem laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc
    (sigma : ℝ) (f : ℝ → E) (x T : ℝ) :
    laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  unfold laplaceInvLineTrunc fourierInvTrunc
  simp_rw [laplaceTransformBilateral_eq_fourier]
  simp only [one_div, mul_inv_rev, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, neg_mul, add_im, mul_im, zero_add]
  rw [show (π⁻¹ * 2⁻¹ : ℝ) = (1 / (2 * π) : ℝ) by ring]
  change (1 / (2 * π) : ℝ) •
      ∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
        𝓕 g (t / (2 * π)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) •
        ((1 / (2 * π) : ℝ) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) •
            𝓕 g (t / (2 * π)))
  have hsplit :
      (∫ t in (-T)..T, Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) •
          𝓕 g (t / (2 * π))) =
        Complex.exp ((sigma : ℂ) * (x : ℂ)) •
          ∫ t in (-T)..T, Complex.exp (((t * x : ℝ) : ℂ) * I) • 𝓕 g (t / (2 * π)) := by
    rw [← intervalIntegral.integral_smul]
    congr with t
    rw [← smul_assoc]
    congr 1
    change Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (x : ℂ)) =
      Complex.exp ((sigma : ℂ) * (x : ℂ)) * Complex.exp (((t * x : ℝ) : ℂ) * I)
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring_nf
  rw [hsplit]
  rw [SMulCommClass.smul_comm (M := ℝ) (N := ℂ) (α := E)]

/-- Principal-value Laplace inversion reduced to the corresponding truncated
Fourier convergence theorem for the exponentially weighted source. -/
theorem laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (sigma : ℝ) (f : ℝ → E) {x : ℝ}
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y)) x T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (x : ℂ))) • f x))) :
    Filter.Tendsto
      (fun T : ℝ => laplaceInvLineTrunc sigma (laplaceTransformBilateral f) x T)
      Filter.atTop (nhds (f x)) := by
  let g : ℝ → E := fun y => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y
  have hlim' : Filter.Tendsto (fun T : ℝ => fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (g x)) := by
    simpa [g] using hlim
  have hscaled : Filter.Tendsto
      (fun T : ℝ =>
        Complex.exp ((sigma : ℂ) * (x : ℂ)) • fourierInvTrunc (𝓕 g) x T)
      Filter.atTop (nhds (Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x)) :=
    hlim'.const_smul (Complex.exp ((sigma : ℂ) * (x : ℂ)))
  have htarget : Complex.exp ((sigma : ℂ) * (x : ℂ)) • g x = f x := by
    simp [g, ← smul_assoc, ← Complex.exp_add]
  rw [htarget] at hscaled
  refine hscaled.congr' ?_
  filter_upwards with T
  exact (laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc sigma f x T).symm

theorem Complex.exp_mul_log_of_pos_eq_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    Complex.exp (s * (Real.log x : ℂ)) = (x : ℂ) ^ s := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [Complex.ofReal_log hx.le]
  congr 1
  ring

/-- The truncated multiplication-form inverse Laplace integral is the truncated
vector-valued inverse Laplace line integral at `log x`. -/
theorem laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) (T : ℝ) :
    laplaceIntegralCpowTrunc f sigma x T =
      laplaceInvLineTrunc sigma (laplaceTransformBilateral f) (Real.log x) T := by
  unfold laplaceIntegralCpowTrunc laplaceInvLineTrunc
  simp_rw [laplaceIntegral_eq_laplaceTransformBilateral, smul_eq_mul]
  rw [RCLike.real_smul_eq_coe_mul]
  congr 1
  · push_cast
    field_simp [Real.pi_ne_zero]
    rfl
  · apply intervalIntegral.integral_congr
    intro t _ht
    change laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I) *
        (x : ℂ) ^ ((sigma : ℂ) + (t : ℂ) * I) =
      Complex.exp (((sigma : ℂ) + (t : ℂ) * I) * (Real.log x : ℂ)) *
        laplaceTransformBilateral f ((sigma : ℂ) + (t : ℂ) * I)
    rw [← Complex.exp_mul_log_of_pos_eq_cpow hx ((sigma : ℂ) + (t : ℂ) * I)]
    ring

/-- Principal-value Laplace inversion in the multiplication `x^s` form, reduced
to truncated Fourier convergence for the exponentially weighted source. -/
theorem laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  have hlim' : Filter.Tendsto
      (fun T : ℝ =>
        fourierInvTrunc
          (𝓕 (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) • f y))
          (Real.log x) T)
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) • f (Real.log x))) := by
    simpa [smul_eq_mul] using hlim
  have hcore := laplaceInvLineTrunc_tendsto_laplaceTransformBilateral_eq
    (E := ℂ) sigma f (x := Real.log x) hlim'
  refine hcore.congr' ?_
  filter_upwards with T
  exact (laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma f hx T).symm

theorem laplaceIntegralCpowTrunc_tendsto_of_sinc_kernel
    (sigma : ℝ) (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hdir : Filter.Tendsto
      (fun T : ℝ =>
        (1 / (2 * π) : ℝ) •
          ∫ y : ℝ,
            (2 * T * Real.sinc (T * (Real.log x - y)) : ℂ) •
              (Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
      Filter.atTop
      (nhds (Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  exact laplaceIntegralCpowTrunc_tendsto_of_fourierInvTrunc sigma f hx
    (fourierInvTrunc_tendsto_of_sinc_kernel (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y) hg hdir)

theorem laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
    (sigma : ℝ) (f : ℝ → ℂ) {x R : ℝ} (hx : 0 < x) (hR : 0 < R)
    (hg : Integrable (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y))
    (hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (π * u) : ℂ) •
            (Complex.exp (-((sigma : ℂ) * ((Real.log x - u : ℝ) : ℂ))) *
                f (Real.log x - u) -
              Complex.exp (-((sigma : ℂ) * (Real.log x : ℂ))) * f (Real.log x)))
      volume (-R) R) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc f sigma x T)
      Filter.atTop (nhds (f (Real.log x))) := by
  exact laplaceIntegralCpowTrunc_tendsto_of_sinc_kernel sigma f hx hg
    (sinc_kernel_tendsto_of_integrable_local_quotient (E := ℂ)
      (f := fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * f y)
      (x := Real.log x) (R := R) hg hR hq)
