/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Algebra.Order.Floor.Ring
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Basic
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real
public import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PrimeNumberTheoremAnd.Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Fractional-part kernel for the Abel zeta formula

`K_s(u) = {u} · u^{-s-1}` and its integrability / domination lemmas, used in
`RiemannZetaPartialSum` and `RiemannZetaAbelContinuation`.

## Main results

* `zetaAbelFractKernel`, `norm_zetaAbelFractKernel_le`
* `ZetaAbelFractKernel.intervalIntegrable`, `integrableOn_Ioi`, `tendsto_integral_Ioi`
* `ZetaAbelFractKernel.hasDerivAt_in_param`, `kernel_deriv_norm_bound_on_ball`
* `ZetaAbelFractKernel.integral_analytic`
-/

@[expose] public section

open scoped Topology
open Real Set Filter Topology MeasureTheory Complex

/-- Fractional-part kernel `{u} · u^{-s-1}` (`K_s` in the Abel formula). -/
noncomputable def zetaAbelFractKernel (s : ℂ) (u : ℝ) : ℂ :=
  ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)

/-- `{u} · u^{-s-1}` is dominated by `u^{- re s - 1}` for `u ≥ 1`. -/
theorem norm_zetaAbelFractKernel_le (u : ℝ) (hu : 1 ≤ u) (s : ℂ) :
    ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) := by
  have hu0 : 0 < u := one_pos.trans_le hu
  have hfract_le1 : ‖((Int.fract u : ℝ) : ℂ)‖ ≤ 1 := by simpa using Int.fract_abs_le_one u
  have hle : ‖zetaAbelFractKernel s u‖ ≤ ‖(u : ℂ) ^ (-s - 1)‖ := by
    calc
      _ = ‖((Int.fract u : ℝ) : ℂ)‖ * ‖(u : ℂ) ^ (-s - 1)‖ := by rw [zetaAbelFractKernel, norm_mul]
      _ ≤ 1 * ‖(u : ℂ) ^ (-s - 1)‖ := by
        exact mul_le_mul_of_nonneg_right hfract_le1 (norm_nonneg _)
      _ = ‖(u : ℂ) ^ (-s - 1)‖ := one_mul _
  have hb : ‖(u : ℂ) ^ (-s - 1)‖ = u ^ (-s.re - 1) := by
    have hre : (-s - 1).re = -s.re - 1 := by
      simp [sub_eq_add_neg]
    simpa [hre] using Complex.norm_cpow_eq_rpow_re_of_pos hu0 (-s - 1)
  exact hle.trans_eq hb

namespace ZetaAbelFractKernel

lemma aestronglyMeasurable (s : ℂ) (S : Set ℝ) (_ : MeasurableSet S) :
    AEStronglyMeasurable (fun u => zetaAbelFractKernel s u) (volume.restrict S) := by
  refine (measurable_fract.complex_ofReal.mul ?_).aestronglyMeasurable
  simpa using Complex.measurable_ofReal.pow_const (-s - 1)

lemma ae_bound_Ioi (s : ℂ) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))),
      ‖zetaAbelFractKernel s u‖ ≤ u ^ (-s.re - 1) :=
  ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
    norm_zetaAbelFractKernel_le u (le_of_lt hu) s

lemma intervalIntegrable (s : ℂ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => zetaAbelFractKernel s u) volume a b := by
  let μ := volume.restrict (Icc a b)
  set g : ℝ → ℝ := fun u => ‖(u : ℂ) ^ (-s - 1)‖
  have hmeas := aestronglyMeasurable s (Icc a b) measurableSet_Icc
  have hbound_ae : ∀ᵐ u ∂μ, ‖zetaAbelFractKernel s u‖ ≤ g u := by
    refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ ?_)
    intro u huIcc
    have hu0 : 0 < u := lt_of_lt_of_le one_pos (ha.trans huIcc.1)
    have hg_eq : g u = u ^ (-s.re - 1) := by
      simp [g, Complex.norm_cpow_eq_rpow_re_of_pos hu0, sub_eq_add_neg]
    exact (norm_zetaAbelFractKernel_le u (ha.trans huIcc.1) s).trans (le_of_eq hg_eq.symm)
  have hg : Integrable g μ := by
    simpa [μ, g] using!
      (Complex.continuousOn_ofReal_cpow (ha := one_pos.trans_le ha)).norm.integrableOn_compact
        isCompact_Icc
  have hf0 : Integrable (fun _ : ℝ => (0 : ℂ)) μ := by simp [μ]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2 <|
    integrable_of_norm_sub_le hmeas hf0 hg
      (hbound_ae.mono fun u hu => by simpa [sub_eq_add_neg, μ, g] using hu)

theorem tendsto_integral_Ioi (s : ℂ) (hs : 1 < s.re) :
    Tendsto (fun N : ℕ => ∫ u in (1 : ℝ)..N, zetaAbelFractKernel s u) atTop
      (𝓝 (∫ u in Ioi (1 : ℝ), zetaAbelFractKernel s u)) :=
  intervalIntegral.tendsto_integral_Ioi_of_ae_norm_le (f := fun u => zetaAbelFractKernel s u)
    (g := fun u => u ^ (-s.re - 1)) 1
    (aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi) (ae_bound_Ioi s)
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos)

theorem integrableOn_Ioi (s : ℂ) (hs : 0 < s.re) :
    Integrable (fun u => zetaAbelFractKernel s u) (volume.restrict (Ioi (1 : ℝ))) := by
  set ε : ℝ := s.re / 2
  set g : ℝ → ℝ := fun u => u ^ (-1 - ε)
  have hfm := aestronglyMeasurable s (Ioi (1 : ℝ)) measurableSet_Ioi
  have hε : 0 < ε := half_pos hs
  have hεle : ε ≤ s.re := half_le_self (le_of_lt hs)
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ‖zetaAbelFractKernel s u‖ ≤ g u :=
    ae_restrict_iff' measurableSet_Ioi |>.2 <| ae_of_all _ fun u hu =>
      (norm_zetaAbelFractKernel_le u (le_of_lt hu) s).trans
        (Real.rpow_le_rpow_of_exponent_le (le_of_lt hu) (by linarith [hεle]))
  simpa [IntegrableOn] using
    IntegrableOn.mono' (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos) hfm hbound

lemma aestronglyMeasurable_param_deriv (z : ℂ) :
    AEStronglyMeasurable (fun u : ℝ => -((Real.log u) : ℂ) * zetaAbelFractKernel z u)
      (volume.restrict (Ioi (1 : ℝ))) := by
  have hmeas : Measurable (fun u : ℝ => zetaAbelFractKernel z u) :=
    (measurable_fract.complex_ofReal.mul <| by simpa using Complex.measurable_ofReal.pow_const (-z - 1))
  simpa only [neg_mul] using
    (Real.measurable_log.complex_ofReal.fun_mul hmeas).fun_neg.aestronglyMeasurable

lemma eventually_aestronglyMeasurable_param (s : ℂ) :
    ∀ᶠ z in 𝓝 s,
      AEStronglyMeasurable (fun u : ℝ => zetaAbelFractKernel z u) (volume.restrict (Ioi (1 : ℝ))) :=
  Eventually.of_forall fun z => aestronglyMeasurable z (Ioi (1 : ℝ)) measurableSet_Ioi

theorem hasDerivAt_in_param (u : ℝ) (hu : 1 < u) (z : ℂ) :
    HasDerivAt (fun w => zetaAbelFractKernel w u)
      (-((Real.log u) : ℂ) * zetaAbelFractKernel z u) z := by
  have h := HasDerivAt.const_mul_ofReal_cpow_neg_sub_one ((Int.fract u : ℝ) : ℂ)
    (lt_trans zero_lt_one hu) z
  have hfun : (fun w => zetaAbelFractKernel w u) = fun w => ((Int.fract u : ℝ) : ℂ) * (u : ℂ) ^ (-w - 1) := by
    ext w; simp [zetaAbelFractKernel]
  exact (h.congr_of_eventuallyEq (EventuallyEq.of_eq hfun)).congr_deriv (by
    simp [zetaAbelFractKernel, Complex.ofReal_log (x := u) (hx := le_of_lt (lt_trans zero_lt_one hu)),
      mul_comm, mul_assoc, mul_left_comm])

theorem kernel_deriv_norm_bound_on_ball (ε : ℝ) (u : ℝ) (hu : 1 < u) (x : ℂ) (hx : ε ≤ x.re) :
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖ ≤ Real.log u * u ^ (-1 - ε) := by
  have hu1 : (1 : ℝ) ≤ u := le_of_lt hu
  have hinner : ‖zetaAbelFractKernel x u‖ ≤ u ^ (-1 - ε) :=
    (norm_zetaAbelFractKernel_le u hu1 x).trans (Real.rpow_le_rpow_of_exponent_le hu1 (by linarith))
  have hlognorm : ‖-((Real.log u) : ℂ)‖ = Real.log u := by
    have hnonneg : 0 ≤ Real.log u := le_of_lt (Real.log_pos hu)
    simp [norm_neg, Complex.norm_real, abs_of_nonneg hnonneg]
  calc
    ‖-((Real.log u) : ℂ) * zetaAbelFractKernel x u‖
        = Real.log u * ‖zetaAbelFractKernel x u‖ := by rw [norm_mul, hlognorm]
    _ ≤ Real.log u * u ^ (-1 - ε) := mul_le_mul_of_nonneg_left hinner (le_of_lt (Real.log_pos hu))

private lemma ae_on_Ioi_of_all {p : ℝ → Prop} (h : ∀ u ∈ Ioi (1 : ℝ), p u) :
    ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), p u :=
  ae_restrict_iff' measurableSet_Ioi |>.2 (ae_of_all _ fun u hu => h u hu)

private lemma dist_lt_of_mem_ball_half {z s : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball s (δ / 2)) (hδ : 0 < δ) :
    dist z s < δ :=
  lt_trans (Metric.mem_ball.mp hz) (half_lt_self hδ)

/-- Dominated differentiation under `∫_{(1,∞)} F z`. -/
lemma hasDerivAt_integral_param_dominated_Ioi
  (F F' : ℂ → ℝ → ℂ) (s : ℂ) (δ : ℝ) (hδ : 0 < δ)
  (hmeas : ∀ᶠ z in 𝓝 s, AEStronglyMeasurable (F z) (volume.restrict (Ioi (1 : ℝ))))
  (hFint : Integrable (F s) (volume.restrict (Ioi (1 : ℝ))))
  (hF'meas : AEStronglyMeasurable (F' s) (volume.restrict (Ioi (1 : ℝ))))
  (bound : ℝ → ℝ) (hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))))
  (hbound : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ, ‖F' z u‖ ≤ bound u)
  (hderiv : ∀ᵐ u ∂(volume.restrict (Ioi (1 : ℝ))), ∀ z ∈ Metric.ball s δ,
    HasDerivAt (fun w => F w u) (F' z u) z) :
  HasDerivAt (fun z => ∫ u in Ioi (1 : ℝ), F z u) (∫ u in Ioi (1 : ℝ), F' s u) s := by
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Ioi (1 : ℝ))) (F := F) (F' := F') (x₀ := s)
      (s := Metric.ball s δ) (bound := bound) (Metric.ball_mem_nhds s hδ)
      (hF_meas := hmeas) (hF_int := hFint) (hF'_meas := hF'meas)
      (h_bound := hbound) (bound_integrable := hbound_int) (h_diff := hderiv)
  rcases h with ⟨_, hDeriv⟩
  exact hDeriv

/-- `∫_{(1,∞)} K_z` is analytic in `z` for `re z > 0`. -/
theorem integral_analytic (s : ℂ) (hs : 0 < s.re) :
    AnalyticAt ℂ (fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u) s := by
  set ε : ℝ := s.re / 2
  have hεpos : 0 < ε := half_pos hs
  obtain ⟨δ, hδpos, hδprop⟩ :=
    Complex.exists_pos_radius_forall_mem_ball_re_ge (z₀ := s) (a := ε) (half_lt_self hs)
  set F : ℂ → ℝ → ℂ := zetaAbelFractKernel
  set F' : ℂ → ℝ → ℂ := fun z u => -((Real.log u) : ℂ) * F z u
  set bound : ℝ → ℝ := fun u => (2 / ε) * u ^ (-1 - ε / 2)
  have hbound_int : Integrable bound (volume.restrict (Ioi (1 : ℝ))) := by
    simpa [bound, IntegrableOn] using
      (integrableOn_Ioi_rpow_of_lt (by linarith [half_pos hεpos]) one_pos).const_mul (2 / ε)
  have hDiff : ∀ᶠ z in 𝓝 s, DifferentiableAt ℂ (fun z0 => ∫ u in Ioi (1 : ℝ), F z0 u) z := by
    refine Filter.eventually_of_mem (Metric.ball_mem_nhds s (half_pos hδpos)) ?_
    intro z hz
    set δ' : ℝ := δ / 2
    have hz_lt : dist z s < δ := dist_lt_of_mem_ball_half hz hδpos
    have hRe : ∀ y ∈ Metric.ball z δ', ε ≤ y.re := fun y hy =>
      hδprop z y hz_lt (dist_lt_of_mem_ball_half hy hδpos)
    have hzRe : ε ≤ z.re := hδprop s z (by simpa [dist_self] using hδpos) hz_lt
    exact (hasDerivAt_integral_param_dominated_Ioi F F' z δ' (half_pos hδpos)
      (eventually_aestronglyMeasurable_param z)
      (by simpa using integrableOn_Ioi z (lt_of_lt_of_le hεpos hzRe))
      (by simpa [F, F'] using aestronglyMeasurable_param_deriv z)
      bound hbound_int
      (ae_on_Ioi_of_all fun u hu w hw =>
        (kernel_deriv_norm_bound_on_ball ε u hu w (hRe w hw)).trans
          (by simpa [bound] using Real.log_mul_rpow_neg_le_two_div_mul_rpow_neg hεpos hu))
      (ae_on_Ioi_of_all fun u hu w hw => by simpa [F, F'] using hasDerivAt_in_param u hu w)).differentiableAt
  exact (Complex.analyticAt_iff_eventually_differentiableAt
    (f := fun z => ∫ u in Ioi (1 : ℝ), zetaAbelFractKernel z u)).2 hDiff

end ZetaAbelFractKernel
