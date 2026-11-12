/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import TernaryGoldbach.Explicit.RectResidue2
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# A weighted logarithmic-derivative residue formula with a pole at zero

For a holomorphic numerator `H`, the weight `H(s)/s` contributes the residue
`logDeriv f(0) * H(0)` at zero, in addition to the residues at the zeros of `f`.
The proof combines the two rectangle residue identities already proved in the
pinned dependency, using the holomorphic divided difference `dslope H 0`.

This is a finite contour identity. No RH, zero-count envelope, limiting contour
estimate, or numerical Chebyshev bound is assumed or asserted here.
-/

open Complex Set MeasureTheory Metric
open scoped Real Interval
open TernaryGoldbach.Explicit

namespace TernaryGoldbach.RSBounds

/-- Multiplication by `f'/f` preserves integrability on the four sides when
`f` is entire and has no zero on the boundary. -/
theorem rectIntegrable_logDeriv_mul {f H : ℂ → ℂ}
    (hf : Differentiable ℂ f) {z w : ℂ} (hbd : NoZerosOnSides f z w)
    (hH : RectIntegrable H z w) :
    RectIntegrable (fun s => logDeriv f s * H s) z w := by
  have hderiv : Continuous (deriv f) := continuous_iff_continuousAt.mpr
    (fun s => (hf.analyticAt s).deriv.continuousAt)
  have hcont (φ : ℝ → ℂ) (hφ : Continuous φ) {a b : ℝ}
      (hnz : ∀ t ∈ [[a, b]], f (φ t) ≠ 0) :
      ContinuousOn (fun t => logDeriv f (φ t)) [[a, b]] := by
    change ContinuousOn (fun t => deriv f (φ t) / f (φ t)) [[a, b]]
    exact (hderiv.comp hφ).continuousOn.div (hf.continuous.comp hφ).continuousOn hnz
  exact ⟨hH.1.continuousOn_mul (hcont _ (by fun_prop) hbd.1),
    hH.2.1.continuousOn_mul (hcont _ (by fun_prop) hbd.2.1),
    hH.2.2.1.continuousOn_mul (hcont _ (by fun_prop) hbd.2.2.1),
    hH.2.2.2.continuousOn_mul (hcont _ (by fun_prop) hbd.2.2.2)⟩

/-- The residue theorem for the weight `H(s)/s`. The rectangle contains zero
strictly, and `f(0) != 0`, so its extra residue is separate from the zero sum. -/
theorem rectInt_logDeriv_mul_div_zero {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {c : ℂ} {R : ℝ} (hR : 0 < R) (hfc : f c ≠ 0)
    {z w : ℂ} (hzw1 : z.re < w.re) (hzw2 : z.im < w.im)
    (hrect : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ ball c (R / 2))
    (hbd : NoZerosOnSides f z w)
    (h01 : z.re < 0) (h02 : 0 < w.re) (h03 : z.im < 0) (h04 : 0 < w.im)
    (hf0 : f 0 ≠ 0)
    {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hsubU : [[z.re, w.re]] ×ℂ [[z.im, w.im]] ⊆ U)
    (hH : DifferentiableOn ℂ H U) :
    rectInt (fun s => logDeriv f s * (H s / s)) z w =
      2 * Real.pi * I *
        ((∑ u ∈ (zerosIn f c R (R / 2)).filter
            (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
            ((divB f c R u).toNat : ℂ) * (H u / u)) +
          logDeriv f 0 * H 0) := by
  classical
  have h0rect : (0 : ℂ) ∈ [[z.re, w.re]] ×ℂ [[z.im, w.im]] :=
    mem_reProdIm.mpr ⟨Set.mem_uIcc.mpr (Or.inl ⟨h01.le, h02.le⟩),
      Set.mem_uIcc.mpr (Or.inl ⟨h03.le, h04.le⟩)⟩
  have h0U : (0 : ℂ) ∈ U := hsubU h0rect
  have hds : DifferentiableOn ℂ (dslope H 0) U :=
    (Complex.differentiableOn_dslope (hU.mem_nhds h0U)).mpr hH
  have hdres := rectInt_logDeriv_mul hf hR hfc hzw1 hzw2 hrect hbd hU hsubU hds
  have hires := rectInt_logDeriv_inv_sub hf hR hfc hzw1 hzw2 hrect hbd
    (p := 0) h01 h02 h03 h04 hf0
  obtain ⟨b1, b2, b3, b4⟩ := mem_rect_boundary_ne
    (ρ := 0) h01 h02 h03 h04
  have hdec (s : ℂ) (hs : s ≠ 0) :
      logDeriv f s * (H s / s) =
        logDeriv f s * dslope H 0 s + H 0 * (logDeriv f s * (s - 0)⁻¹) := by
    rw [dslope_of_ne _ hs, slope_def_field]
    simp only [sub_zero]
    field_simp
    <;> ring
  have hdint : RectIntegrable (fun s => logDeriv f s * dslope H 0 s) z w :=
    rectIntegrable_logDeriv_mul hf hbd
      (rectIntegrable_of_continuousOn (hds.continuousOn.mono hsubU))
  have hiint : RectIntegrable (fun s => logDeriv f s * (s - 0)⁻¹) z w :=
    rectIntegrable_logDeriv_mul hf hbd
      (rect_sides_integrable_inv (ρ := 0) h01 h02 h03 h04)
  rw [rectInt_congr (g := fun s => logDeriv f s * dslope H 0 s +
      H 0 * (logDeriv f s * (s - 0)⁻¹))
      (fun x => hdec _ (b1 x)) (fun x => hdec _ (b2 x))
      (fun y => hdec _ (b3 y)) (fun y => hdec _ (b4 y)),
    rectInt_add' hdint (hiint.const_mul (H 0)), rectInt_const_mul, hdres, hires]
  have h0c : (0 : ℂ) ∈ closedBall c R :=
    ball_subset_closedBall ((ball_subset_ball (by linarith : R / 2 ≤ R)) (hrect h0rect))
  have hnz0 : (0 : ℂ) ∉ zerosIn f c R (R / 2) := by
    intro hzero
    have hdiv := (mem_zerosIn hzero).2
    rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun s _ => hf.analyticAt s : AnalyticOnNhd ℂ f (closedBall c R)) h0c] at hdiv
    rw [(hf.analyticAt 0).analyticOrderAt_eq_zero.mpr hf0] at hdiv
    simp at hdiv
  have hsum :
      (∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * dslope H 0 u) +
      H 0 * (∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * (u - 0)⁻¹) =
      ∑ u ∈ (zerosIn f c R (R / 2)).filter
        (fun u => z.re < u.re ∧ u.re < w.re ∧ z.im < u.im ∧ u.im < w.im),
        ((divB f c R u).toNat : ℂ) * (H u / u) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u hu => ?_
    have hu0 : u ≠ 0 := by
      intro heq
      apply hnz0
      simpa only [heq] using (Finset.mem_filter.mp hu).1
    rw [dslope_of_ne _ hu0, slope_def_field]
    simp only [sub_zero]
    field_simp
    <;> ring
  rw [← hsum]
  ring

end TernaryGoldbach.RSBounds
