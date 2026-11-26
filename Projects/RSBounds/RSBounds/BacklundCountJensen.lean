import RSBounds.BacklundCountIdentity
import RSBounds.BacklundAnchor
import RSBounds.BacklundZetaPhase
import RSBounds.BacklundGammaPhaseEstimate

/-!
# Rosser's count-versus-circle-average inequality

This assembly uses the actual positive-ordinate zero multiplicities,
constructive reflected crossings, the certified center denominator, and
the continuously normalized gamma phase. The circle majorant is still
an explicit input; this theorem does not assert the numerical Rosser bound.
-/

open Complex MeasureTheory Real
open scoped Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

theorem count_le_circle_majorant {T R : ℝ} {B : ℂ → ℝ}
    (hT : 1 ≤ T) (hgood : zetaGoodHeight T)
    (hR : 3 / 4 < R) (hRT : R < T)
    (hB : CircleIntegrable B (5 / 4 : ℂ) R)
    (hB0 : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R, 0 ≤ B z)
    (hfb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z + T * I)‖ ≤ Real.exp (B z))
    (hgb : ∀ z ∈ Metric.sphere (5 / 4 : ℂ) R,
      ‖riemannZeta (z - T * I)‖ ≤ Real.exp (B z)) :
    |(N T : ℝ) - mainTerm T| ≤
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 1 / 2 +
        2 / (Real.pi * T) + 1 / (4 * Real.pi * T) := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hq : 0 < Real.log (R / (3 / 4)) :=
    Real.log_pos ((one_lt_div (by norm_num)).mpr hR)
  have hhor := BacklundZetaPhase.horizontal_argument_bound hT hgood hR hRT hB hB0 hfb hgb
  have hcenter : -Real.log (3.426 : ℝ) ≤
      Real.log ‖riemannZeta ((5 / 4 : ℂ) + T * I)‖ := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 3.426)
      (zeta_norm_lower_five_fourths_3426 T)
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hh
    simpa only [Real.log_div one_ne_zero (by norm_num : (3.426 : ℝ) ≠ 0),
      Real.log_one, zero_sub] using hh
  have hhor' :
      |∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).im| / Real.pi ≤
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
    apply hhor.trans
    gcongr
    linarith
  have hv := BacklundAnchor.abs_vertical_integral_le T
  have ha : |zetaArgVar T| / Real.pi ≤
      1 / 2 +
      (circleAverage B (5 / 4 : ℂ) R + Real.log (3.426 : ℝ)) /
        (2 * Real.log (R / (3 / 4))) + 2 / (Real.pi * T) := by
    unfold zetaArgVar arcVariation
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
    have hh := abs_sub_le
      (∫ t in (0 : ℝ)..T, (logDeriv riemannZeta ((5 / 4 : ℂ) + t * I)).re)
      (0 : ℝ)
      (∫ σ in (1 / 2 : ℝ)..(5 / 4 : ℝ),
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).im)
    simp only [sub_zero, zero_sub, abs_neg] at hh
    have hd := div_le_div_of_nonneg_right hh hp.le
    have hv' := div_le_div_of_nonneg_right hv hp.le
    have he : (Real.pi / 2) / Real.pi = (1 / 2 : ℝ) := by field_simp
    rw [he] at hv'
    rw [add_div] at hd
    linarith
  have hg := div_le_div_of_nonneg_right
    (BacklundGammaPhase.gamma_phase_remainder_bound hT0) hp.le
  change |gammaStirlingRemainder T| / Real.pi ≤ (1 / (4 * T)) / Real.pi at hg
  rw [count_identity_mainTerm hT0 hgood]
  have hh := abs_add_le (zetaArgVar T / Real.pi) (gammaStirlingRemainder T / Real.pi)
  rw [abs_div, abs_div, abs_of_pos hp] at hh
  have he : (1 / (4 * T)) / Real.pi = 1 / (4 * Real.pi * T) := by ring
  rw [he] at hg
  have he' : mainTerm T + zetaArgVar T / Real.pi + gammaStirlingRemainder T / Real.pi -
      mainTerm T = zetaArgVar T / Real.pi + gammaStirlingRemainder T / Real.pi := by ring
  rw [he']
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
