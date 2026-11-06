import RSBounds.BacklundCountHalving
import RSBounds.BacklundCountMultiplicity
import RSBounds.BacklundCountPole
import RSBounds.BacklundGammaPhaseBase

/-!
# Exact Riemann--von Mangoldt identity at ordinate-free heights

The count is the actual positive-ordinate multiplicity sum. The argument
term is the logarithmic-derivative integral with anchor `5/4`, and the gamma
phase is normalized continuously by its integral from height zero.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

private theorem continuousAt_logDeriv_zeta {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) : ContinuousAt (logDeriv riemannZeta) s := by
  have ha : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs
  exact ha.deriv.continuousAt.div ha.continuousAt hz

private theorem continuous_zeta_vertical :
    Continuous (fun t : ℝ => logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
  · apply continuousAt_logDeriv_zeta
    · intro h
      have hh := congrArg Complex.re h
      norm_num at hh
    · exact riemannZeta_ne_zero_of_one_lt_re (by norm_num)
  · fun_prop

private theorem continuous_zeta_horizontal {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv riemannZeta ((σ : ℂ) + T * I)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
  · apply continuousAt_logDeriv_zeta
    · intro h
      have hh := congrArg Complex.im h
      simp at hh
      linarith
    · intro hz
      exact hg _ hz (by simp)
  · fun_prop

theorem logDeriv_xi_factorization {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    logDeriv xiF s = poleKernel s - (Real.log Real.pi : ℂ) / 2 +
      (1 / 2 : ℂ) * Complex.digamma (s / 2) + logDeriv riemannZeta s := by
  have hx : xiF s ≠ 0 := by
    rw [xiF_eq hs hs1, zetaF_of_ne hs1]
    apply mul_ne_zero
    · apply mul_ne_zero
      · intro h
        simp [h] at hs
      · exact Gammaℝ_ne_zero_of_re_pos hs
    · exact mul_ne_zero (sub_ne_zero.mpr hs1) hz
  rw [logDeriv_xiF hs hs1 hx, logDeriv_zetaF_eq hs1 hz,
    ← Complex.ofReal_log Real.pi_pos.le]
  unfold poleKernel
  push_cast
  ring

private theorem continuous_pole_vertical :
    Continuous (fun t : ℝ => poleKernel ((5 / 4 : ℂ) + t * I)) := by
  unfold poleKernel
  apply Continuous.add
  · apply continuous_const.div (by fun_prop)
    intro t h
    have hh := congrArg Complex.re h
    norm_num at hh
  · apply continuous_const.div (by fun_prop)
    intro t h
    have hh := congrArg Complex.re h
    norm_num at hh

private theorem continuous_pole_horizontal {T : ℝ} (hT : 0 < T) :
    Continuous (fun σ : ℝ => poleKernel ((σ : ℂ) + T * I)) := by
  unfold poleKernel
  apply Continuous.add
  · apply continuous_const.div (by fun_prop)
    intro σ h
    have hh := congrArg Complex.im h
    simp at hh
    linarith
  · apply continuous_const.div (by fun_prop)
    intro σ h
    have hh := congrArg Complex.im h
    simp at hh
    linarith

/-- Exact evaluation of the xi factors on the upper-right arc. -/
theorem xiArcVar_eq_pi_add_theta_add_zetaArgVar {T : ℝ}
    (hT : 0 < T) (hg : zetaGoodHeight T) :
    xiArcVar T = Real.pi + riemannSiegelTheta T + zetaArgVar T := by
  have hpv := (Complex.continuous_re.comp continuous_pole_vertical).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hgv := (Complex.continuous_re.comp
    (BacklundGammaPhase.continuous_digamma_line (by norm_num : (0 : ℝ) < 5 / 4))).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hzv := (Complex.continuous_re.comp continuous_zeta_vertical).intervalIntegrable (μ := volume) (0 : ℝ) T
  have hph := (Complex.continuous_im.comp (continuous_pole_horizontal hT)).intervalIntegrable (μ := volume) (1 / 2 : ℝ) (5 / 4)
  have hgh : IntervalIntegrable (fun σ : ℝ =>
      (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) volume (1 / 2) (5 / 4) := by
    apply ContinuousOn.intervalIntegrable
    apply Complex.continuous_im.comp_continuousOn
    apply (BacklundGammaPhase.continuousOn_digamma_horizontal T).mono
    intro σ hσ
    rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
    exact lt_of_lt_of_le (by norm_num) hσ.1
  have hzh := (Complex.continuous_im.comp (continuous_zeta_horizontal hT hg)).intervalIntegrable (μ := volume)
    (1 / 2 : ℝ) (5 / 4)
  dsimp only [Function.comp_def] at hpv hgv hzv hph hzh
  norm_num only [ofReal_div, ofReal_ofNat] at hgv
  have hv : (∫ t in (0 : ℝ)..T, (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re) =
      (∫ t in (0 : ℝ)..T, (poleKernel ((5 / 4 : ℂ) + t * I)).re) - T / 2 * Real.log Real.pi +
      (1 / 2) * (∫ t in (0 : ℝ)..T, (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re) +
      (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re) := by
    have he (t : ℝ) : (logDeriv xiF ((5 / 4 : ℂ) + t * I)).re =
        (poleKernel ((5 / 4 : ℂ) + t * I)).re - Real.log Real.pi / 2 +
        (1 / 2) * (Complex.digamma (((5 / 4 : ℂ) + t * I) / 2)).re +
        (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re := by
      rw [logDeriv_xi_factorization (by norm_num) (by
        intro h; have hh := congrArg Complex.re h; norm_num at hh)
        (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
      simp [add_re, sub_re, mul_re, div_ofNat_re]
    simp_rw [he]
    rw [intervalIntegral.integral_add ((hpv.sub intervalIntegrable_const).add (hgv.const_mul _)) hzv,
      intervalIntegral.integral_add (hpv.sub intervalIntegrable_const) (hgv.const_mul _),
      intervalIntegral.integral_sub hpv intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  have hh : (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv xiF ((σ : ℂ) + T * I)).im) =
      (∫ σ in (1 / 2 : ℝ)..(5 / 4), (poleKernel ((σ : ℂ) + T * I)).im) +
      (1 / 2) * (∫ σ in (1 / 2 : ℝ)..(5 / 4), (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) +
      (∫ σ in (1 / 2 : ℝ)..(5 / 4), (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) := by
    have he : EqOn (fun σ : ℝ => (logDeriv xiF ((σ : ℂ) + T * I)).im)
        (fun σ : ℝ => (poleKernel ((σ : ℂ) + T * I)).im +
          (1 / 2) * (Complex.digamma (((σ : ℂ) + T * I) / 2)).im +
          (logDeriv riemannZeta ((σ : ℂ) + T * I)).im) [[(1 / 2 : ℝ), 5 / 4]] := by
      intro σ hσ
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4)] at hσ
      have hs : 0 < (((σ : ℂ) + T * I)).re := by simp; linarith [hσ.1]
      have hs1 : ((σ : ℂ) + T * I) ≠ 1 := by
        intro h; have hi := congrArg Complex.im h; simp at hi; linarith
      have hz : riemannZeta ((σ : ℂ) + T * I) ≠ 0 := by
        intro hz; exact hg _ hz (by simp)
      dsimp only
      rw [logDeriv_xi_factorization hs hs1 hz]
      simp [add_im, sub_im, mul_im, div_ofNat_im]
    rw [intervalIntegral.integral_congr he,
      intervalIntegral.integral_add (hph.add (hgh.const_mul _)) hzh,
      intervalIntegral.integral_add hph (hgh.const_mul _), intervalIntegral.integral_const_mul]
  have hp := pole_arc_eq_pi (by norm_num : (1 : ℝ) < 5 / 4) hT
  have hgamma := BacklundGammaPhase.digamma_rectangle (by norm_num : (1 / 2 : ℝ) ≤ 5 / 4) T
  unfold xiArcVar arcVariation
  norm_num only [ofReal_div, ofReal_ofNat]
  rw [hv, hh]
  unfold zetaArgVar arcVariation riemannSiegelTheta BacklundGammaPhase.phaseIntegral at *
  norm_num only [ofReal_div, ofReal_ofNat] at *
  linarith

/-- The exact Riemann--von Mangoldt identity with a continuously normalized
Gamma phase and positive-ordinate multiplicities. -/
theorem count_identity {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    (N T : ℝ) = 1 + riemannSiegelTheta T / Real.pi + zetaArgVar T / Real.pi := by
  have h := pi_mul_N_eq_xiArcVar hT hg
  rw [xiArcVar_eq_pi_add_theta_add_zetaArgVar hT hg] at h
  field_simp
  nlinarith

noncomputable def mainTerm (T : ℝ) : ℝ :=
  T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8

noncomputable def gammaStirlingRemainder (T : ℝ) : ℝ :=
  BacklundGammaPhase.phaseIntegral T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8

/-- The count identity in the form used by Rosser's explicit estimate. -/
theorem count_identity_mainTerm {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    (N T : ℝ) = mainTerm T + zetaArgVar T / Real.pi +
      gammaStirlingRemainder T / Real.pi := by
  rw [count_identity hT hg]
  have hlog : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
    rw [show T / (2 * Real.pi) = (T / 2) / Real.pi by ring,
      Real.log_div (by positivity : T / 2 ≠ 0) Real.pi_ne_zero]
  rw [show riemannSiegelTheta T = BacklundGammaPhase.phaseIntegral T -
    T / 2 * Real.log Real.pi from rfl]
  unfold mainTerm gammaStirlingRemainder
  rw [hlog]
  field_simp
  ring

end TernaryGoldbach.RSBounds.BacklundCountIdentity
