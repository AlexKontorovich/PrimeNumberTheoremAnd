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
