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
