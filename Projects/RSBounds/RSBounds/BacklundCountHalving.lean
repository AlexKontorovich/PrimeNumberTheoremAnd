/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0; see licenses/Gersh-LICENSE.
Adapted for the upper-half rectangle and anchor 5/4.
-/
import RSBounds.BacklundCountRectangle

/-!
# Halving the upper rectangle by xi symmetry

The upper rectangle avoids a conjugate-multiplicity argument: its residue
sum already counts only positive ordinates. The proof adapts the boundary
folding method of Gershon Bialer's `BacklundXiHalvingProof.lean`
(`27df23af6a712895f22204d0d81102baa74f0ebe`), using calr's existing xi
symmetries and the upper rectangle with anchor `5/4`.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology Interval ComplexConjugate

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem continuous_logDeriv_xi_vertical :
    Continuous (fun t : ℝ => logDeriv xiF ((5 / 4 : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  apply ContinuousAt.comp (f := fun t : ℝ => (5 / 4 : ℂ) + t * I)
  · exact continuousAt_logDeriv_xiF (xiF_ne_zero_of_one_le_re (by norm_num))
  · fun_prop

theorem continuous_logDeriv_xi_horizontal {T : ℝ} (hg : zetaGoodHeight T) :
    Continuous (fun σ : ℝ => logDeriv xiF ((σ : ℂ) + T * I)) := by
  rw [continuous_iff_continuousAt]
  intro σ
  apply ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I)
  · exact continuousAt_logDeriv_xiF (xiF_ne_zero_of_goodHeight hg (by simp))
  · fun_prop

private theorem logDeriv_xi_reflect (σ T : ℝ) :
    logDeriv xiF (((1 - σ : ℝ) : ℂ) + T * I) =
      -conj (logDeriv xiF ((σ : ℂ) + T * I)) := by
  have he : (((1 - σ : ℝ) : ℂ) + T * I) = 1 - conj ((σ : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [he, logDeriv_xiF_one_sub, logDeriv_xiF_conj]

theorem im_rectangle_eq_two_xiArcVar {T : ℝ} (hg : zetaGoodHeight T) :
    (rectInt (logDeriv xiF) lowerCorner (upperCorner T)).im = 2 * xiArcVar T := by
  set F := logDeriv xiF
  set A : ℂ := ∫ σ in (1 / 2 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)
  set B : ℂ := ∫ t in (0 : ℝ)..T, F ((5 / 4 : ℂ) + t * I)
  have ht : ∀ a b : ℝ, IntervalIntegrable
      (fun σ : ℝ => F ((σ : ℂ) + T * I)) volume a b :=
    (continuous_logDeriv_xi_horizontal hg).intervalIntegrable
  have hv := continuous_logDeriv_xi_vertical.intervalIntegrable (μ := volume) (0 : ℝ) T
  have hbottom : (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)).im = 0 := by
    have hc : conj (∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) =
        ∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ) := by
      rw [← intervalIntegral.intervalIntegral_conj]
      apply intervalIntegral.integral_congr
      intro x _
      exact (logDeriv_xiF_conj (x : ℂ)).symm.trans (by simp [F])
    have hh := congrArg Complex.im hc
    simp only [conj_im] at hh
    linarith
  have hleft : (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I)) = -conj B := by
    rw [← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t _
    simpa only [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num, ofReal_div,
      ofReal_neg, ofReal_one, ofReal_ofNat] using logDeriv_xi_reflect (5 / 4) t
  have htopLeft : (∫ σ in (-1 / 4 : ℝ)..(1 / 2), F ((σ : ℂ) + T * I)) =
      -conj A := by
    have hs := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := 5 / 4)
      (fun σ : ℝ => F ((σ : ℂ) + T * I)) 1
    rw [show (1 : ℝ) - 5 / 4 = -1 / 4 by norm_num,
      show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at hs
    rw [← hs, ← intervalIntegral.intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro σ _
    exact logDeriv_xi_reflect σ T
  have htop : (∫ σ in (-1 / 4 : ℝ)..(5 / 4), F ((σ : ℂ) + T * I)) =
      A - conj A := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (ht (-1 / 4) (1 / 2))
      (ht (1 / 2) (5 / 4)), htopLeft]
    change -conj A + A = A - conj A
    ring
  have hAim : A.im = ∫ σ in (1 / 2 : ℝ)..(5 / 4),
      (F ((σ : ℂ) + T * I)).im := by
    exact (Complex.imCLM.intervalIntegral_comp_comm (ht (1 / 2) (5 / 4))).symm
  have hBre : B.re = ∫ t in (0 : ℝ)..T, (F ((5 / 4 : ℂ) + t * I)).re := by
    exact (Complex.reCLM.intervalIntegral_comp_comm hv).symm
  unfold rectInt
  simp only [lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
    ofReal_zero, zero_mul, add_zero, smul_eq_mul,
    ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat]
  change ((∫ x in (-1 / 4 : ℝ)..(5 / 4), F (x : ℂ)) -
      (∫ x in (-1 / 4 : ℝ)..(5 / 4), F ((x : ℂ) + T * I)) +
      I * B - I * (∫ t in (0 : ℝ)..T, F ((-1 / 4 : ℂ) + t * I))).im = _
  rw [htop, hleft]
  simp only [sub_im, add_im, I_mul_im, neg_re, conj_re, conj_im, hbottom]
  unfold xiArcVar arcVariation
  norm_num only [ofReal_div, ofReal_ofNat]
  rw [← hBre, ← hAim]
  ring

/-- Exact count/argument connection at an ordinate-free positive height. -/
theorem pi_mul_N_eq_xiArcVar {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    Real.pi * (N T : ℝ) = xiArcVar T := by
  have hr := congrArg Complex.im (rectangle_count_identity hT hg)
  rw [im_rectangle_eq_two_xiArcVar hg] at hr
  simp only [mul_im, mul_re, ofReal_re, ofReal_im, natCast_re, natCast_im,
    I_re, I_im, mul_zero, zero_mul, sub_zero, add_zero, zero_add] at hr
  norm_num at hr
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
