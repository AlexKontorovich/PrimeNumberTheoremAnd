/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in ../licenses/.

The rectangle argument is adapted from BacklundXiArcVariation.lean in
gersh/ternary-goldbach-lean, revision 27df23af6a712895f22204d0d81102baa74f0ebe.
Changes: use IEANTN's established digamma analyticity, and allow any right
endpoint at least 1/2. No principal logarithm of Gamma is used.
-/
import RSBounds.IEANTNDigamma
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex Real MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

/-- The continuous Gamma phase, normalized to zero at height zero. -/
noncomputable def phaseIntegral (T : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..(T / 2), (Complex.digamma (1 / 4 + t * Complex.I)).re

theorem differentiableAt_digamma {z : ℂ} (hz : 0 < z.re) :
    DifferentiableAt ℂ Complex.digamma z :=
  (GammaSolution.analyticOnNhd_digamma z hz).differentiableAt

theorem digamma_ofReal_im_zero {x : ℝ} (hx : 0 < x) :
    (Complex.digamma (x : ℂ)).im = 0 := by
  rw [GammaSolution.digamma_ofReal hx]
  rfl

theorem continuous_digamma_line {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ ↦ Complex.digamma (((a : ℂ) + t * I) / 2)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hp : 0 < (((a : ℂ) + t * I) / 2).re := by
    simp [Complex.div_ofNat_re]
    positivity
  exact ContinuousAt.comp (g := Complex.digamma)
    (f := fun t : ℝ ↦ ((a : ℂ) + t * I) / 2) (x := t)
    (differentiableAt_digamma hp).continuousAt (by fun_prop)

theorem continuousOn_digamma_horizontal (T : ℝ) :
    ContinuousOn (fun a : ℝ ↦ Complex.digamma (((a : ℂ) + T * I) / 2))
      (Set.Ioi 0) := by
  intro a ha
  change 0 < a at ha
  have hp : 0 < (((a : ℂ) + T * I) / 2).re := by
    simpa [Complex.div_ofNat_re] using div_pos ha (by norm_num : (0 : ℝ) < 2)
  exact (ContinuousAt.comp (g := Complex.digamma)
    (f := fun a : ℝ ↦ ((a : ℂ) + T * I) / 2) (x := a)
    (differentiableAt_digamma hp).continuousAt (by fun_prop)).continuousWithinAt

private theorem integral_im {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).im = ∫ t in a..b, (f t).im := by
  exact (Complex.imCLM.intervalIntegral_comp_comm hf).symm

private theorem integral_re {f : ℝ → ℂ} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    (∫ t in a..b, f t).re = ∫ t in a..b, (f t).re := by
  exact (Complex.reCLM.intervalIntegral_comp_comm hf).symm

/-- The Gamma contribution on an L-shaped path equals the continuously
normalized phase on the line `Re z = 1/4`. This also fixes the branch in
the zero-count identity. -/
theorem digamma_rectangle {a : ℝ} (ha : 1 / 2 ≤ a) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, (Complex.digamma (((a : ℂ) + t * I) / 2)).re) -
      (∫ σ in (1 / 2 : ℝ)..a, (Complex.digamma (((σ : ℂ) + T * I) / 2)).im) =
      2 * phaseIntegral T := by
  let f : ℂ → ℂ := fun s ↦ Complex.digamma (s / 2)
  have hhalf : (0 : ℝ) < 1 / 2 := by norm_num
  have ha0 : 0 < a := hhalf.trans_le ha
  have hc : Set.uIcc (1 / 2 : ℝ) a = Set.Icc (1 / 2 : ℝ) a := Set.uIcc_of_le ha
  have hdiff : DifferentiableOn ℂ f
      (Set.uIcc ((1 / 2 : ℂ).re) (((a : ℂ) + T * I).re) ×ℂ
        Set.uIcc ((1 / 2 : ℂ).im) (((a : ℂ) + T * I).im)) := by
    intro s hs
    rw [Complex.mem_reProdIm] at hs
    have hre : 1 / 2 ≤ s.re := by
      have hsr : s.re ∈ Set.uIcc (1 / 2 : ℝ) a := by simpa using hs.1
      rw [hc] at hsr
      exact hsr.1
    have hp : 0 < (s / 2).re := by
      rw [Complex.div_ofNat_re]
      linarith
    exact ((differentiableAt_digamma hp).comp s
      (differentiableAt_id.div_const 2)).differentiableWithinAt
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f (1 / 2 : ℂ) ((a : ℂ) + T * I) hdiff
  have hsub : Set.uIcc (1 / 2 : ℝ) a ⊆ Set.Ioi 0 := by
    intro t ht
    rw [hc] at ht
    exact hhalf.trans_le ht.1
  have htop : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + T * I)) volume (1 / 2) a :=
    ((continuousOn_digamma_horizontal T).mono hsub).intervalIntegrable
  have hbot : IntervalIntegrable (fun σ : ℝ ↦ f ((σ : ℂ) + (0 : ℂ) * I))
      volume (1 / 2) a :=
    ((continuousOn_digamma_horizontal 0).mono hsub).intervalIntegrable
  have hright : IntervalIntegrable (fun t : ℝ ↦ f ((a : ℂ) + t * I)) volume 0 T :=
    (continuous_digamma_line ha0).intervalIntegrable 0 T
  have hleft : IntervalIntegrable (fun t : ℝ ↦ f ((1 / 2 : ℂ) + t * I)) volume 0 T :=
    by simpa [f] using (continuous_digamma_line hhalf).intervalIntegrable 0 T
  have him := congrArg Complex.im hrect
  simp only [Complex.div_ofNat_re, Complex.one_re, Complex.div_ofNat_im,
    Complex.one_im, zero_div, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re,
    Complex.ofReal_im, sub_zero, Complex.add_im, Complex.mul_I_im, zero_add,
    neg_zero, add_zero] at him
  norm_num only [Complex.ofReal_zero, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at him
  rw [Complex.sub_im, Complex.add_im, Complex.sub_im, Complex.zero_im,
    smul_eq_mul, smul_eq_mul, Complex.I_mul_im, Complex.I_mul_im,
    integral_im hbot, integral_im htop, integral_re hright, integral_re hleft] at him
  have hbot0 : (∫ σ in (1 / 2 : ℝ)..a, (f ((σ : ℂ) + (0 : ℂ) * I)).im) = 0 := by
    calc
      _ = ∫ _σ in (1 / 2 : ℝ)..a, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro σ hσ
        have hσ0 : 0 < σ := hsub hσ
        have he : ((σ : ℂ) + (0 : ℂ) * I) / 2 = ((σ / 2 : ℝ) : ℂ) := by
          push_cast
          ring
        dsimp [f]
        rw [he]
        exact digamma_ofReal_im_zero (by positivity)
      _ = 0 := by simp
  rw [hbot0] at him
  have hl : (∫ t in (0 : ℝ)..T, (f ((1 / 2 : ℂ) + t * I)).re) =
      2 * phaseIntegral T := by
    have he : (fun t : ℝ ↦ (f ((1 / 2 : ℂ) + t * I)).re) =
        (fun t : ℝ ↦ (Complex.digamma (1 / 4 + (t / 2 : ℝ) * I)).re) := by
      funext t
      dsimp [f]
      congr 2
      push_cast
      ring
    rw [he, intervalIntegral.integral_comp_div
      (fun u : ℝ ↦ (Complex.digamma (1 / 4 + u * I)).re) (two_ne_zero)]
    simp [phaseIntegral, smul_eq_mul]
  rw [hl] at him
  dsimp [f] at him
  linarith

end TernaryGoldbach.RSBounds.BacklundGammaPhase
