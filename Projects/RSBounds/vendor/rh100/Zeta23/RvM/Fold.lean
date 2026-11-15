module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Fold.lean — the symmetry fold of the argument-principle rectangle onto its right half
(used for MainTerm.lean's N_eq_halfContour_completedZeta).

With F := Λ'/Λ (Λ = completedRiemannZeta), A_T := ∫_{1/2}^{2} F(σ+iT)dσ, B := ∫_{T₁}^{T₂} F(2+it)dt:
the functional equation Λ(1−w) = Λ(w) and the reflection Λ(w̄) = conj Λ(w) give F(1−s̄) = −conj F(s)
on the right half-path, hence ∫_{−1}^{1/2}F(σ+iT)dσ = −conj A_T, ∫_{T₁}^{T₂}F(−1+it)dt = −conj B, and
    ∮_{∂([−1,2]×[T₁,T₂])} F = (A_{T₁} − conj A_{T₁}) − (A_{T₂} − conj A_{T₂}) + I(B + conj B)
                           = 2i·Im(A_{T₁} + B·i − A_{T₂}) = 2i·Im(halfContour F T₁ T₂).
Combined with Zeta23.RvM.rectangleIntegral'_logDeriv_completedZeta_eq_Ncount (CountByIntegral.lean):
    N(T₁,T₂) = (1/π)·Im(halfContour (logDeriv Λ) T₁ T₂)   for good heights 1 ≤ T₁ < T₂.
The conj-symmetry lemmas for Gammaℝ and Λ'/Λ (section ConjSymmetry) live here rather than in
MainTerm.lean so that both files can use them.
-/
public import Zeta23.RvM.Defs
public import Zeta23.RvM.CountByIntegral
public import Zeta23.WeilEF.XiLogDeriv
public import Zeta23.FromPNTPlus.ZetaConj

@[expose] public section

open Complex MeasureTheory Set intervalIntegral

noncomputable section

namespace Zeta23.RvM

section ConjSymmetry

/-- (x : ℂ)^(conj w) = conj ((x : ℂ)^w) for real x > 0. -/
lemma cpow_ofReal_conj {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ (starRingEnd ℂ w) = starRingEnd ℂ ((x : ℂ) ^ w) := by
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hx0, ← Complex.exp_conj, map_mul,
    ← Complex.ofReal_log hx.le, Complex.conj_ofReal]

/-- Γℝ(s̄) = conj Γℝ(s). -/
lemma Gammaℝ_conj (s : ℂ) : Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (Complex.Gammaℝ s) := by
  have h1 : -(starRingEnd ℂ s) / 2 = starRingEnd ℂ (-s / 2) := by
    simp [map_div₀, map_neg, map_ofNat]
  have h2 : starRingEnd ℂ s / 2 = starRingEnd ℂ (s / 2) := by
    simp [map_div₀, map_ofNat]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, h1, h2, cpow_ofReal_conj Real.pi_pos,
    Complex.Gamma_conj, map_mul]

lemma deriv_Gammaℝ_conj (s : ℂ) :
    deriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (deriv Complex.Gammaℝ s) := by
  have h : ∀ z : ℂ, starRingEnd ℂ (Complex.Gammaℝ (starRingEnd ℂ z)) = Complex.Gammaℝ z := by
    intro z
    rw [Gammaℝ_conj, Complex.conj_conj]
  simp [← deriv_conj_conj' Complex.Gammaℝ, h]

lemma logDeriv_Gammaℝ_conj (s : ℂ) :
    logDeriv Complex.Gammaℝ (starRingEnd ℂ s) = starRingEnd ℂ (logDeriv Complex.Gammaℝ s) := by
  rw [logDeriv_apply, logDeriv_apply, deriv_Gammaℝ_conj, Gammaℝ_conj, ← map_div₀]

/-- Conjugation symmetry of Λ'/Λ at points with Re > 0 where ζ ≠ 0. -/
lemma logDeriv_completedZeta_conj {s : ℂ} (hre : 0 < s.re) (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hcre : 0 < (starRingEnd ℂ s).re := by rwa [Complex.conj_re]
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  have hζc : riemannZeta (starRingEnd ℂ s) ≠ 0 := by
    rw [_root_.riemannZeta_conj]
    exact (map_ne_zero _).mpr hζs
  rw [Zeta23.WeilEF.logDeriv_completedZeta _ hc1 hζc hcre,
    Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζs hre, map_add, logDeriv_Gammaℝ_conj,
    logDerivZeta_conj']

/-- The fold symmetry: Λ'/Λ(1 − s̄) = −conj(Λ'/Λ(s)) (Re s > 0, s ≠ 1, ζ(s) ≠ 0). -/
lemma logDeriv_completedZeta_one_sub_conj {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1)
    (hζs : riemannZeta s ≠ 0) :
    logDeriv completedRiemannZeta (1 - starRingEnd ℂ s)
      = -starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hre
  have hc0 : starRingEnd ℂ s ≠ 0 := (map_ne_zero _).mpr hs0
  have hc1 : starRingEnd ℂ s ≠ 1 := fun h => hs1 (by rw [← Complex.conj_conj s, h, map_one])
  rw [Zeta23.WeilEF.logDeriv_completedZeta_one_sub _ hc0 hc1,
    logDeriv_completedZeta_conj hre hs0 hs1 hζs]

end ConjSymmetry

/-- Facts at a point of the closed right half-strip at a good height ≥ 1. -/
lemma path_point_facts {s : ℂ} (hre : 0 < s.re) (him : 1 ≤ s.im)
    (hgood : GoodHeight s.im) : s ≠ 1 ∧ riemannZeta s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro hh; rw [hh] at him; simp at him; linarith
  refine ⟨hs1, fun hz => ?_⟩
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, hre, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- Λ'/Λ is continuous at every point of height T whenever T ≥ 1 is a good height. -/
lemma continuousAt_logDeriv_completedZeta {s : ℂ} (him : 1 ≤ s.im) (hgood : GoodHeight s.im) :
    ContinuousAt (logDeriv completedRiemannZeta) s := by
  have hs0 : s ≠ 0 := by intro hh; rw [hh] at him; simp at him; linarith
  have hs1 : s ≠ 1 := by intro hh; rw [hh] at him; simp at him; linarith
  have hΛ := analyticAt_completedRiemannZeta hs0 hs1
  have hne : completedRiemannZeta s ≠ 0 := fun h =>
    hgood s (completedRiemannZeta_eq_zero_iff.mp h) rfl
  exact hΛ.deriv.continuousAt.div hΛ.continuousAt hne

/-- Horizontal fold at a good height T ≥ 1:  ∫_{−1}^{2} F(σ+iT)dσ = 2i·Im ∫_{1/2}^{2} F(σ+iT)dσ. -/
lemma horizontal_fold {T : ℝ} (hT : 1 ≤ T) (hgood : GoodHeight T) :
    ∫ σ in (-1 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)
      = 2 * I * ((∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T * I)).im : ℂ) := by
  set F := logDeriv completedRiemannZeta with hF
  have hcont : Continuous fun σ : ℝ => F (σ + T * I) := by
    refine continuous_iff_continuousAt.mpr fun σ => ?_
    have h := continuousAt_logDeriv_completedZeta (s := σ + T * I) (by simpa using hT)
      (by simpa using hgood)
    exact ContinuousAt.comp (f := fun σ : ℝ => (σ : ℂ) + T * I) h (by fun_prop)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (μ := volume) (-1) (1 / 2))
    (hcont.intervalIntegrable (μ := volume) (1 / 2) 2)
  rw [← hsplit]
  set A := ∫ σ in (1 / 2 : ℝ)..2, F (σ + T * I) with hA
  -- the left piece is −conj A
  have hleft : ∫ σ in (-1 : ℝ)..(1 / 2), F (σ + T * I) = -starRingEnd ℂ A := by
    have hsub := intervalIntegral.integral_comp_sub_left (f := fun x : ℝ => F (x + T * I))
      (a := (1 / 2 : ℝ)) (b := 2) (1 : ℝ)
    norm_num at hsub
    -- hsub : ∫ x in 1/2..2, F (↑(1 - x) + T I) = ∫ x in -1..1/2, F (x + T I)   (up to cast shape)
    rw [← hsub, hA, ← intervalIntegral_conj, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num)] at hx
    have hxpos : 0 < x := by linarith [hx.1]
    obtain ⟨hs1, hζ⟩ := path_point_facts (s := x + T * I) (by simpa using hxpos)
      (by simpa using hT) (by simpa using hgood)
    have key := logDeriv_completedZeta_one_sub_conj (s := x + T * I) (by simpa using hxpos) hs1 hζ
    have e : (1 : ℂ) - starRingEnd ℂ (x + T * I) = 1 - (x : ℂ) + T * I := by
      simp [Complex.ext_iff]
    simp only [hF] at key ⊢
    rw [← e, key]
  rw [hleft, neg_add_eq_sub, Complex.sub_conj]
  push_cast
  ring

/-- Vertical fold:  ∫_{T₁}^{T₂} F(−1+it)dt = −conj ∫_{T₁}^{T₂} F(2+it)dt  (1 ≤ T₁ ≤ T₂). -/
lemma vertical_fold {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ ≤ T₂) :
    ∫ t in T₁..T₂, logDeriv completedRiemannZeta (-1 + t * I)
      = -starRingEnd ℂ (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) := by
  rw [← intervalIntegral_conj, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le h12] at ht
  have ht1 : 1 ≤ t := le_trans h1 ht.1
  have hs1 : (2 : ℂ) + t * I ≠ 1 := by
    intro hh; have := congrArg Complex.re hh; simp at this
  have hζ : riemannZeta (2 + t * I) ≠ 0 := riemannZeta_ne_zero_of_one_le_re (by simp)
  have key := logDeriv_completedZeta_one_sub_conj (s := 2 + t * I) (by simp) hs1 hζ
  have e : (1 : ℂ) - starRingEnd ℂ (2 + t * I) = -1 + t * I := by
    simp [Complex.ext_iff]; norm_num
  show logDeriv completedRiemannZeta (-1 + t * I)
    = -starRingEnd ℂ (logDeriv completedRiemannZeta (2 + t * I))
  rw [← e, key]

/-- **The fold.** For good heights 1 ≤ T₁ < T₂:
∮_{∂([−1,2]×[T₁,T₂])} Λ'/Λ = 2i · Im(halfContour (Λ'/Λ) T₁ T₂). -/
theorem rectangleIntegral_logDeriv_completedZeta_eq_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁)
    (h12 : T₁ < T₂) (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    RectangleIntegral (logDeriv completedRiemannZeta) (-1 + T₁ * I) (2 + T₂ * I)
      = 2 * I * ((halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℂ) := by
  have hre1 : (-1 + T₁ * I).re = -1 := by simp
  have him1 : (-1 + T₁ * I).im = T₁ := by simp
  have hre2 : (2 + T₂ * I : ℂ).re = 2 := by simp
  have him2 : (2 + T₂ * I : ℂ).im = T₂ := by simp
  simp only [RectangleIntegral, HIntegral, VIntegral, hre1, him1, hre2, him2, smul_eq_mul,
    Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [horizontal_fold h1 hg1, horizontal_fold (by linarith) hg2, vertical_fold h1 h12.le]
  simp only [halfContour, Complex.add_im, Complex.sub_im, Complex.mul_I_im]
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₁ * I)) = A₁
  generalize (∫ σ in (1 / 2 : ℝ)..2, logDeriv completedRiemannZeta (σ + T₂ * I)) = A₂
  generalize (∫ t in T₁..T₂, logDeriv completedRiemannZeta (2 + t * I)) = B
  have e1 : 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * B - I * -starRingEnd ℂ B
      = 2 * I * (A₁.im : ℂ) - 2 * I * (A₂.im : ℂ) + I * (B + starRingEnd ℂ B) := by ring
  rw [e1, Complex.add_conj]
  push_cast
  ring

/-- **N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ** for good heights 1 ≤ T₁ < T₂ (this is MainTerm.lean's
N_eq_halfContour_completedZeta). -/
theorem Ncount_eq_im_halfContour {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ)
      = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im := by
  have h := rectangleIntegral'_logDeriv_completedZeta_eq_Ncount (by linarith) h12.le hg1 hg2
  change (1 / (2 * Real.pi * I)) • RectangleIntegral _ _ _ = _ at h
  rw [rectangleIntegral_logDeriv_completedZeta_eq_halfContour h1 h12 hg1 hg2, smul_eq_mul] at h
  have h' : ((Ncount T₁ T₂ : ℝ) : ℂ)
      = (((1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im : ℝ) : ℂ) := by
    push_cast
    rw [← h]
    field_simp
  exact_mod_cast h'

end Zeta23.RvM
