/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0; see licenses/Gersh-LICENSE.
Adapted for the upper-half rectangle and anchor 5/4.
-/
import RSBounds.BacklundCountDefinitions
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
# The elementary pole-factor contribution to Backlund's identity

Along the upper-right arc, the argument change of `s(s-1)` is exactly pi.
The proof uses explicit arctangent antiderivatives, as in the extracted
Gershon Bialer count proof, with the general anchor `a > 1`.
-/

open Complex MeasureTheory Set
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity

noncomputable def poleKernel (s : ℂ) : ℂ := 1 / s + 1 / (s - 1)

theorem integral_re_inv_vertical {b : ℝ} (hb : 0 < b) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (1 / ((b : ℂ) + t * I)).re) = Real.arctan (T / b) := by
  have hpt (t : ℝ) : (1 / ((b : ℂ) + t * I)).re = b / (b ^ 2 + t ^ 2) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply]
    simp
    ring_nf
  simp_rw [hpt]
  have hd : ∀ t ∈ [[(0 : ℝ), T]], HasDerivAt (fun t : ℝ => Real.arctan (t / b))
      (b / (b ^ 2 + t ^ 2)) t := by
    intro t _
    have hh := (Real.hasDerivAt_arctan (t / b)).comp t ((hasDerivAt_id t).div_const b)
    change HasDerivAt (fun u : ℝ => Real.arctan (u / b))
      ((1 / (1 + (t / b) ^ 2)) * (1 / b)) t at hh
    apply hh.congr_deriv
    field_simp <;> ring
  have hc : Continuous (fun t : ℝ => b / (b ^ 2 + t ^ 2)) :=
    continuous_const.div (by fun_prop) (fun _ => by positivity)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  simp

theorem integral_re_pole_vertical {a : ℝ} (ha : 1 < a) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (poleKernel ((a : ℂ) + t * I)).re) =
      Real.arctan (T / a) + Real.arctan (T / (a - 1)) := by
  have he (t : ℝ) : ((a : ℂ) + t * I) - 1 = ((a - 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  have hc (b : ℝ) (hb : 0 < b) : Continuous (fun t : ℝ => (1 / ((b : ℂ) + t * I)).re) := by
    apply Complex.continuous_re.comp
    apply continuous_const.div (by fun_prop)
    intro t h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  simp only [poleKernel, add_im, add_re, he]
  rw [intervalIntegral.integral_add ((hc a (by linarith)).intervalIntegrable _ _)
    ((hc (a - 1) (by linarith)).intervalIntegrable _ _),
    integral_re_inv_vertical (by linarith), integral_re_inv_vertical (by linarith)]

theorem integral_im_pole_horizontal {T : ℝ} (hT : 0 < T) (a : ℝ) :
    (∫ σ in (1 / 2 : ℝ)..a, (poleKernel ((σ : ℂ) + T * I)).im) =
      -(Real.arctan (a / T) + Real.arctan ((a - 1) / T)) := by
  have hpt (σ : ℝ) : (poleKernel ((σ : ℂ) + T * I)).im =
      -(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2) := by
    rw [poleKernel, add_im, one_div, one_div, inv_im, inv_im, normSq_apply, normSq_apply]
    simp
    ring_nf
  simp_rw [hpt]
  have hd : ∀ σ ∈ [[(1 / 2 : ℝ), a]],
      HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
        (-(T / (σ ^ 2 + T ^ 2)) - T / ((σ - 1) ^ 2 + T ^ 2)) σ := by
    intro σ _
    have h1 := (Real.hasDerivAt_arctan (σ / T)).comp σ ((hasDerivAt_id σ).div_const T)
    have h2 := (Real.hasDerivAt_arctan ((σ - 1) / T)).comp σ
      (((hasDerivAt_id σ).sub_const 1).div_const T)
    have hh : HasDerivAt (fun u : ℝ => -Real.arctan (u / T) - Real.arctan ((u - 1) / T))
        (-(1 / (1 + (σ / T) ^ 2) * (1 / T)) -
          (1 / (1 + ((σ - 1) / T) ^ 2) * (1 / T))) σ := h1.neg.sub h2
    apply hh.congr_deriv
    field_simp
    ring
  have hc : Continuous (fun σ : ℝ => -(T / (σ ^ 2 + T ^ 2)) -
      T / ((σ - 1) ^ 2 + T ^ 2)) := by
    have c1 : Continuous (fun σ : ℝ => T / (σ ^ 2 + T ^ 2)) :=
      continuous_const.div (by fun_prop) (fun _ => by positivity)
    have c2 : Continuous (fun σ : ℝ => T / ((σ - 1) ^ 2 + T ^ 2)) :=
      continuous_const.div (by fun_prop) (fun _ => by positivity)
    exact c1.neg.sub c2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hc.intervalIntegrable _ _)]
  rw [show ((1 : ℝ) / 2 - 1) / T = -((1 / 2) / T) by ring, Real.arctan_neg]
  ring

theorem pole_arc_eq_pi {a T : ℝ} (ha : 1 < a) (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, (poleKernel ((a : ℂ) + t * I)).re) -
      (∫ σ in (1 / 2 : ℝ)..a, (poleKernel ((σ : ℂ) + T * I)).im) = Real.pi := by
  rw [integral_re_pole_vertical ha, integral_im_pole_horizontal hT]
  have h1 := Real.arctan_inv_of_pos (show 0 < T / a by positivity)
  have h2 := Real.arctan_inv_of_pos (show 0 < T / (a - 1) by positivity)
  rw [inv_div] at h1 h2
  linarith

end TernaryGoldbach.RSBounds.BacklundCountIdentity
