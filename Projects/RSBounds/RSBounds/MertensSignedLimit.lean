import RSBounds.MertensZeroPotential
import RSBounds.MertensEndpointLeft
import RSBounds.PolynomialPsiFromZeroSums

/-!
# The improper signed psi tail

This module identifies the limit of the finite integrals, not an unjustified
Bochner integral over an infinite interval. Absolute integrability of the
signed psi integrand requires an additional effective-decay argument.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.MertensSignedLimit

open TernaryGoldbach.Explicit PolynomialExplicit MertensIntervalKernel
  MertensZeroPotential MertensSignedInterval MertensEndpointLeft

theorem finite_integral_eq {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) =
      potential a - potential b - leftRemainder a b -
        Complex.log (2 * π) * (1 / a - 1 / b : ℝ) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  have hs := (sum_tendsto_potential (ha.trans hab) hT).sub
    (sum_tendsto_potential ha hT)
  have heq (k : ℕ) :
      (∑ ρ ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) ρ : ℂ) *
          ((b : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)))) -
        (∑ ρ ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) ρ : ℂ) *
          ((a : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)))) =
      ∑ ρ ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) ρ : ℂ) *
        (((b : ℂ) ^ (ρ - 1) - (a : ℂ) ^ (ρ - 1)) / (ρ * (ρ - 1))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro ρ _
    ring
  simp_rw [heq] at hs
  have h := tendsto_nhds_unique hs (MertensSignedInterval.explicit_formula_at_heights ha hab hT)
  linear_combination h

/-- The value of the convergent improper integral of `(ψ(t)-t)/t²`. -/
noncomputable def signedLimit (a : ℝ) : ℂ :=
  potential a + F a - Complex.log (2 * π) / (a : ℂ)

theorem tendsto_signed_integral_complex {a : ℝ} (ha : 1 ≤ a) :
    Tendsto (fun b : ℝ => ((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ))
      atTop (𝓝 (signedLimit a)) := by
  have ha0 : 0 < a := by linarith
  have hInvReal : Tendsto (fun b : ℝ => 1 / b) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_inv_atTop_zero : Tendsto (fun b : ℝ => b⁻¹) atTop (𝓝 0))
  have hInv : Tendsto (fun b : ℝ => ((1 / b : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.ofReal_zero] using
      (Complex.continuous_ofReal.tendsto 0).comp hInvReal
  have hPa : Tendsto (fun _ : ℝ => potential a) atTop (𝓝 (potential a)) :=
    tendsto_const_nhds
  have hIa : Tendsto (fun _ : ℝ => ((1 / a : ℝ) : ℂ)) atTop
      (𝓝 ((1 / a : ℝ) : ℂ)) := tendsto_const_nhds
  have h := ((hPa.sub potential_tendsto_zero).sub
    (tendsto_leftRemainder_atTop ha0)).sub
      ((hIa.sub hInv).const_mul (Complex.log (2 * π)))
  have heq : ∀ᶠ b : ℝ in atTop,
      (potential a - potential b - leftRemainder a b -
        Complex.log (2 * π) * (((1 / a : ℝ) : ℂ) - ((1 / b : ℝ) : ℂ))) =
      ((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) := by
    filter_upwards [eventually_ge_atTop a] with b hb
    rw [finite_integral_eq ha hb, Complex.ofReal_sub]
  have h' := h.congr' heq
  convert h' using 1
  congr 1
  unfold signedLimit
  push_cast
  ring

/-- A real-valued improper-integral convergence statement. -/
theorem tendsto_signed_integral {a : ℝ} (ha : 1 ≤ a) :
    Tendsto (fun b : ℝ => ∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2)
      atTop (𝓝 (signedLimit a).re) := by
  simpa only [Function.comp_def, Complex.ofReal_re] using
    (Complex.continuous_re.tendsto _).comp (tendsto_signed_integral_complex ha)

theorem signedLimit_im_eq_zero {a : ℝ} (ha : 1 ≤ a) : (signedLimit a).im = 0 := by
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_signed_integral_complex ha)
  have h0 : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 (signedLimit a).im) := by
    apply h.congr'
    filter_upwards [] with b
    simp
  exact tendsto_nhds_unique h0 tendsto_const_nhds

/-- Explicit endpoint-remainder bound; quantitative zero-potential bounds can
be supplied independently, with their finite-RH premise still visible. -/
theorem norm_signedLimit_le {a : ℝ} (ha : 1 ≤ a) :
    ‖signedLimit a‖ ≤ ‖potential a‖ + 6000 * a ^ (-3 / 2 : ℝ) +
      Real.log (2 * Real.pi) / a := by
  have ha0 : 0 < a := by linarith
  have hlog : ‖Complex.log (2 * π)‖ = Real.log (2 * Real.pi) :=
    PolynomialPsiFromZeroSums.norm_log_two_pi
  unfold signedLimit
  calc
    _ ≤ ‖potential a + F a‖ + ‖Complex.log (2 * π) / (a : ℂ)‖ := norm_sub_le _ _
    _ ≤ (‖potential a‖ + ‖F a‖) + ‖Complex.log (2 * π) / (a : ℂ)‖ := by
      gcongr
      exact norm_add_le _ _
    _ ≤ _ := by
      rw [norm_div, hlog, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
      linarith [norm_F_le ha0]

end TernaryGoldbach.RSBounds.MertensSignedLimit
