module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/MainTerm.lean — the main term N(T,2T) = (T/2π)·ell1 T + O(log T).
The statements here are assembled into Zeta23.RvM.riemannVonMangoldt in Zeta23/RvM/Statement.lean.

Inputs (from other files):
 * Zeta23.RvM.zetaZeroConfig_local_count (LocalCount.lean, proved): local count.
 * Zeta23/Analytic/RectangleLogDeriv.lean: ∮_{∂Rect} g·f'/f = 2πi Σ m_ρ g(ρ) (PNT+ RectangleIntegral'
   conventions) — use with g ≡ 1, f = completedRiemannZeta (or riemannZeta·Gammaℝ) on [−1,2]×[T₁,T₂]
   (mind Λ's poles at s = 0, 1: for T₁ > 0 the rectangle avoids them).
 * Zeta23/WeilEF/XiLogDeriv.lean: logDeriv Λ = logDeriv ζ + logDeriv Gammaℝ (Re s > 0, away from
   zeros/pole); conj-symmetry Λ(conj s) = conj Λ(s); Λ(1−s) = Λ(s) (Mathlib completedRiemannZeta_one_sub).
 * Zeta23/RvM/Backlund.lean: backlund_horizontal (∃ C T₀, ∀ T ≥ T₀, GoodHeight T →
   |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T) and vertical_two (|Im ∫_{T₁}^{T₂} ζ'/ζ(2+it)·i dt| ≤ 2 log 3).
 * Zeta23/RvM/GammaSide.lean: gamma_side : 0 < T₁ ≤ T₂ → (1/π)·(halfContour (logDeriv Gammaℝ) T₁ T₂).im
   = ∫ t in T₁..T₂, mu t.
 * GammaFacts.int_mu, GammaFacts.stirling (μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²) ⇒ μ ≪ log on [T−1,2T+1]).
The assembly is proved once as the constant-parametric `rvM_main_param`; `rvM_main_aux` /
`rvM_main` are its ∃-corollaries; MainTermExplicit.lean keeps only the numeric inputs and `rvM_main_explicit`.
-/
public import Zeta23.RvM.Defs
public import Zeta23.RvM.LocalCount
public import Zeta23.Hypotheses
public import Zeta23.WeilEF.XiLogDeriv
public import Zeta23.Analytic.RectangleLogDeriv
public import Zeta23.RvM.GammaSide
public import Zeta23.RvM.Backlund
public import Zeta23.RvM.Fold
public import Zeta23.RvM.NcountWindow

@[expose] public section

open Complex MeasureTheory

attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23.RvM


/-- (M2)+(M3): the folded argument principle. For zero-free ordinates 1 ≤ T₁ < T₂:
N(T₁,T₂) = (1/π)·Im ∫_L Λ'/Λ ds, L the right half-contour.  [Tit86 §9.3; fold by Λ(1−s̄) = conj Λ(s)] -/
theorem N_eq_halfContour_completedZeta {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    (Ncount T₁ T₂ : ℝ) = (1 / Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im :=
  Ncount_eq_im_halfContour h1 h12 hg1 hg2

/-- Points on the half-contour: ζ and Γℝ facts packaged. -/
private lemma contour_point_facts {s : ℂ} (hre1 : 1/2 ≤ s.re) (_hre2 : s.re ≤ 2)
    (him : 1 ≤ s.im) (hgood : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ s.im) :
    s ≠ 0 ∧ s ≠ 1 ∧ riemannZeta s ≠ 0 ∧ 0 < s.re := by
  have hs0 : s ≠ 0 := by
    intro hh
    rw [hh] at him
    simp only [Complex.zero_im] at him
    linarith
  have hs1 : s ≠ 1 := by
    intro hh
    rw [hh] at him
    simp only [Complex.one_im] at him
    linarith
  refine ⟨hs0, hs1, ?_, by linarith⟩
  intro hz
  rcases lt_or_ge s.re 1 with hlt | hge
  · exact hgood s ⟨hz, by linarith, hlt⟩ rfl
  · exact riemannZeta_ne_zero_of_one_le_re hge hz

/-- logDeriv ζ is continuous at good points. -/
private lemma continuousAt_logDeriv_zeta {s : ℂ} (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    ContinuousAt (logDeriv riemannZeta) s := by
  have ha := Zeta23.WeilEF.analyticAt_riemannZeta hs1
  exact (ha.deriv.continuousAt).div ha.continuousAt hζ

private lemma continuousAt_logDeriv_Gammaℝ {s : ℂ} (hre : 0 < s.re) :
    ContinuousAt (logDeriv Complex.Gammaℝ) s := by
  have ha := Zeta23.WeilEF.analyticAt_Gammaℝ hre
  exact (ha.deriv.continuousAt).div ha.continuousAt (Gammaℝ_ne_zero_of_re_pos hre)

theorem halfContour_completedZeta_split {T₁ T₂ : ℝ} (h1 : 1 ≤ T₁) (h12 : T₁ < T₂)
    (hg1 : GoodHeight T₁) (hg2 : GoodHeight T₂) :
    halfContour (logDeriv completedRiemannZeta) T₁ T₂ =
      halfContour (logDeriv riemannZeta) T₁ T₂ + halfContour (logDeriv Complex.Gammaℝ) T₁ T₂ := by
  have hmem : ∀ σ : ℝ, σ ∈ Set.uIcc (1/2:ℝ) 2 → 1/2 ≤ σ ∧ σ ≤ 2 := by
    intro σ hσ
    rw [Set.uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 2)] at hσ
    exact ⟨hσ.1, hσ.2⟩
  -- facts at horizontal-segment points
  have hseg : ∀ (T : ℝ), 1 ≤ T → GoodHeight T → ∀ σ ∈ Set.uIcc (1/2:ℝ) 2,
      ((σ:ℂ) + T*I ≠ 0 ∧ (σ:ℂ) + T*I ≠ 1 ∧ riemannZeta ((σ:ℂ) + T*I) ≠ 0
        ∧ 0 < ((σ:ℂ) + T*I).re) := by
    intro T hT hg σ hσ
    obtain ⟨ha, hb'⟩ := hmem σ hσ
    have hre : ((σ:ℂ) + T*I).re = σ := by simp
    have him : ((σ:ℂ) + T*I).im = T := by simp
    refine contour_point_facts ?_ ?_ ?_ ?_
    · rw [hre]; exact ha
    · rw [hre]; exact hb'
    · rw [him]; exact hT
    · rw [him]; exact fun ρ hρ => hg ρ hρ
  -- facts at vertical-segment points (σ = 2)
  have hvert : ∀ t : ℝ, t ∈ Set.uIcc T₁ T₂ →
      ((2:ℂ) + t*I ≠ 0 ∧ (2:ℂ) + t*I ≠ 1 ∧ riemannZeta ((2:ℂ) + t*I) ≠ 0
        ∧ 0 < ((2:ℂ) + t*I).re) := by
    intro t _
    have hre : ((2:ℂ) + t*I).re = 2 := by simp
    refine ⟨?_, ?_, riemannZeta_ne_zero_of_one_le_re (by rw [hre]; norm_num), by rw [hre]; norm_num⟩
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
    · intro hh
      have := congrArg Complex.re hh
      rw [hre] at this
      simp at this
  -- pointwise splitting along the three segments
  have keyb : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₁*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₁*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₁*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₁ h1 hg1 σ hσ
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyt : Set.EqOn (fun σ : ℝ => logDeriv completedRiemannZeta ((σ:ℂ) + T₂*I))
      (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T₂*I)
        + logDeriv Complex.Gammaℝ ((σ:ℂ) + T₂*I)) (Set.uIcc (1/2:ℝ) 2) := by
    intro σ hσ
    obtain ⟨hs0, hs1, hζ, hre⟩ := hseg T₂ (by linarith) hg2 σ hσ
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  have keyr : Set.EqOn (fun t : ℝ => logDeriv completedRiemannZeta ((2:ℂ) + t*I))
      (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I)
        + logDeriv Complex.Gammaℝ ((2:ℂ) + t*I)) (Set.uIcc T₁ T₂) := by
    intro t ht
    obtain ⟨hs0, hs1, hζ, hre⟩ := hvert t ht
    simp only
    rw [Zeta23.WeilEF.logDeriv_completedZeta _ hs1 hζ hre]
    ring
  -- integrability of the ζ and Γℝ pieces on each segment
  have hintb : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, hs1, hζ, _⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintbΓ : ∀ (T : ℝ), 1 ≤ T → GoodHeight T →
      IntervalIntegrable (fun σ : ℝ => logDeriv Complex.Gammaℝ ((σ:ℂ) + T*I))
        MeasureTheory.volume (1/2) 2 := by
    intro T hT hg
    apply ContinuousOn.intervalIntegrable
    intro σ hσ
    obtain ⟨_, _, _, hre⟩ := hseg T hT hg σ hσ
    have hparam : ContinuousAt (fun σ : ℝ => (σ:ℂ) + T*I) σ := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun σ : ℝ => (σ:ℂ) + T*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  have hintr : IntervalIntegrable (fun t : ℝ => logDeriv riemannZeta ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, hs1, hζ, _⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv riemannZeta) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_zeta hs1 hζ) hparam)
  have hintrΓ : IntervalIntegrable (fun t : ℝ => logDeriv Complex.Gammaℝ ((2:ℂ) + t*I))
      MeasureTheory.volume T₁ T₂ := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    obtain ⟨_, _, _, hre⟩ := hvert t ht
    have hparam : ContinuousAt (fun t : ℝ => (2:ℂ) + t*I) t := by fun_prop
    exact ContinuousAt.continuousWithinAt
      (ContinuousAt.comp (g := logDeriv Complex.Gammaℝ) (f := fun t : ℝ => (2:ℂ) + t*I)
        (continuousAt_logDeriv_Gammaℝ hre) hparam)
  -- assemble
  unfold halfContour
  rw [intervalIntegral.integral_congr keyb, intervalIntegral.integral_congr keyt,
    intervalIntegral.integral_congr keyr,
    intervalIntegral.integral_add (hintb T₁ h1 hg1) (hintbΓ T₁ h1 hg1),
    intervalIntegral.integral_add (hintb T₂ (by linarith) hg2) (hintbΓ T₂ (by linarith) hg2),
    intervalIntegral.integral_add hintr hintrΓ]
  ring


/-- Zero-free ordinates are dense enough: every interval [a, a+1] (a ≥ 0) contains one
(finitely many ordinates per window, Zeta23.zerosIn_finite). -/
theorem exists_goodHeight (a : ℝ) : ∃ T ∈ Set.Icc a (a + 1), GoodHeight T := by
  have hfin : ((fun ρ : ℂ => ρ.im) '' zerosIn a (a + 1)).Finite :=
    (zerosIn_finite a (a + 1)).image _
  have hinf : (Set.Ioo a (a + 1)).Infinite := Set.Ioo_infinite (by linarith)
  obtain ⟨T, hT⟩ := (hinf.sdiff hfin).nonempty
  obtain ⟨hT, hTnot⟩ := hT
  refine ⟨T, ⟨hT.1.le, hT.2.le⟩, ?_⟩
  intro ρ hρ him
  apply hTnot
  refine ⟨ρ, ⟨hρ, ?_, ?_⟩, him⟩
  · rw [him]; exact hT.1
  · rw [him]; exact hT.2.le

/-! (window arithmetic Ncount_add / Ncount_mono: Zeta23/Statement/SeamClosed.lean) -/

set_option maxHeartbeats 1000000 in
/-- **rvM_main, parametric in all constants**: the five constant sources —
Backlund CB TB, local count A₀, int_mu Cμ Tμ, μ ≪ log CM, continuity of μ — are explicit parameters, so numeric
inputs give a numeric C_N. -/
theorem rvM_main_param {CB TB A₀ Cμ Tμ CM : ℝ}
    (hB : ∀ T : ℝ, TB ≤ T → (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ CB * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi)
    (hA₀1 : 1 ≤ A₀) (hA₀ : ∀ t : ℝ, (Ncount t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (hCμ : ∀ T : ℝ, Tμ ≤ T →
      |(∫ τ in T..(2 * T), mu τ) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T)
    (hCM0 : 0 < CM) (hCM : ∀ τ : ℝ, 1 ≤ τ → |mu τ| ≤ CM * Real.log (τ + 3))
    (hμc : Continuous mu) :
    ∀ T : ℝ, max (max (TB + 1) (Tμ + 1)) 4 ≤ T →
      |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T|
        ≤ (3 * |CB| + 4 * A₀ + 4 * CM + |Cμ| + 1) * Real.log T := by
  have hA₀0 : 0 ≤ A₀ := by linarith
  intro T hT
  have hT4 : 4 ≤ T := le_trans (le_max_right _ _) hT
  have hTB : TB + 1 ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hTμ : Tμ + 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hlogT : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (le_trans (by linarith [Real.exp_one_lt_d9]) le_rfl)
  have hlogT0 : 0 < Real.log T := by linarith
  -- good heights straddling [T, 2T]
  obtain ⟨T₁, hT₁mem, hg1⟩ := exists_goodHeight (T - 1)
  obtain ⟨T₂, hT₂mem, hg2⟩ := exists_goodHeight (2 * T)
  have hT₁a : T - 1 ≤ T₁ := hT₁mem.1
  have hT₁b : T₁ ≤ T := by have := hT₁mem.2; linarith
  have hT₂a : 2 * T ≤ T₂ := hT₂mem.1
  have hT₂b : T₂ ≤ 2 * T + 1 := hT₂mem.2
  have h1T₁ : 1 ≤ T₁ := by linarith
  have h12 : T₁ < T₂ := by linarith
  -- argument principle + split + Γ-side
  have hN := N_eq_halfContour_completedZeta h1T₁ h12 hg1 hg2
  have hsplit := halfContour_completedZeta_split h1T₁ h12 hg1 hg2
  have hgam := gamma_side (T₁ := T₁) (T₂ := T₂) (by linarith) (by linarith)
  -- window arithmetic
  have hadd : (Ncount T₁ T₂ : ℝ)
      = (Ncount T₁ T : ℝ) + (Ncount T (2*T) : ℝ) + (Ncount (2*T) T₂ : ℝ) := by
    have e1 := Zeta23.Ncount_add (a := T₁) (b := T) (c := T₂) hT₁b (by linarith)
    have e2 := Zeta23.Ncount_add (a := T) (b := 2*T) (c := T₂) (by linarith) hT₂a
    rw [e1, e2]
    push_cast
    ring
  -- small windows are O(log T)
  have hlogsq : ∀ x : ℝ, 0 < x → x + 3 ≤ T ^ 2 → Real.log (x + 3) ≤ 2 * Real.log T := by
    intro x hx hxT
    calc Real.log (x + 3) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) hxT
      _ = 2 * Real.log T := by
          rw [Real.log_pow]
          push_cast
          ring
  have hw1 : (Ncount T₁ T : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount T₁ T ≤ Ncount T₁ (T₁ + 1) :=
      Zeta23.Ncount_mono le_rfl (by linarith)
    calc (Ncount T₁ T : ℝ) ≤ (Ncount T₁ (T₁ + 1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|T₁| + 3) := hA₀ T₁
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < T₁)]
          exact hlogsq T₁ (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  have hw2 : (Ncount (2*T) T₂ : ℝ) ≤ 2 * A₀ * Real.log T := by
    have hsub : Ncount (2*T) T₂ ≤ Ncount (2*T) (2*T + 1) :=
      Zeta23.Ncount_mono le_rfl hT₂b
    calc (Ncount (2*T) T₂ : ℝ) ≤ (Ncount (2*T) (2*T+1) : ℝ) := by exact_mod_cast hsub
      _ ≤ A₀ * Real.log (|2*T| + 3) := hA₀ (2*T)
      _ ≤ A₀ * (2 * Real.log T) := by
          refine mul_le_mul_of_nonneg_left ?_ hA₀0
          rw [abs_of_pos (by linarith : 0 < 2*T)]
          exact hlogsq (2*T) (by linarith) (by nlinarith)
      _ = 2 * A₀ * Real.log T := by ring
  -- the ζ half-contour is O(log T)
  have hbk1 := hB T₁ (by linarith) hg1
  have hbk2 := hB T₂ (by linarith) hg2
  have hvert := vertical_two T₁ T₂
  have hζbound : |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
    have hlog₁0 : 0 ≤ Real.log T₁ := Real.log_nonneg h1T₁
    have hlog₂0 : 0 ≤ Real.log T₂ := Real.log_nonneg (by linarith)
    unfold halfContour
    have eim : ((∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I))
        + (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I
        - ∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im
        = (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [eim]
    have hmulI : ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
        = (∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im :=
      congrArg Complex.im (intervalIntegral.integral_mul_const (μ := MeasureTheory.volume) I
        (fun t : ℝ => logDeriv riemannZeta (2 + t * I))).symm
    have h1 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im| ≤ |CB| * Real.log T₁ :=
      hbk1.trans (by
        have : CB * Real.log T₁ ≤ |CB| * Real.log T₁ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₁0
        linarith)
    have h2 : |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| ≤ |CB| * Real.log T₂ :=
      hbk2.trans (by
        have : CB * Real.log T₂ ≤ |CB| * Real.log T₂ :=
          mul_le_mul_of_nonneg_right (le_abs_self CB) hlog₂0
        linarith)
    calc |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im
          + ((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im
          - (∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im|
        ≤ |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₁ * I)).im|
          + |((∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I)) * I).im|
          + |(∫ σ in (1/2:ℝ)..2, logDeriv riemannZeta (σ + T₂ * I)).im| := by
          exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ |CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂ := by
          rw [hmulI]
          have := hvert
          linarith
  -- μ-integral bookkeeping
  have hμint : ∀ a b : ℝ, IntervalIntegrable mu MeasureTheory.volume a b :=
    fun a b => hμc.intervalIntegrable a b
  have hμsplit : (∫ t in T₁..T₂, mu t)
      = (∫ t in T₁..T, mu t) + (∫ t in T..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t := by
    have e1 : (∫ t in T₁..(2*T), mu t) = (∫ t in T₁..T, mu t) + ∫ t in T..(2*T), mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ T) (hμint T (2*T))).symm
    have e2 : (∫ t in T₁..T₂, mu t) = (∫ t in T₁..(2*T), mu t) + ∫ t in (2*T)..T₂, mu t :=
      (intervalIntegral.integral_add_adjacent_intervals (hμint T₁ (2*T)) (hμint (2*T) T₂)).symm
    rw [e2, e1]
  have hμwin : ∀ a b : ℝ, 1 ≤ a → a ≤ b → b ≤ 2*T + 1 → |b - a| ≤ 1 →
      |∫ t in a..b, mu t| ≤ 2 * CM * Real.log T := by
    intro a b ha hab hb hba
    have hbound : ∀ t ∈ Set.uIoc a b, ‖mu t‖ ≤ CM * Real.log (2*T + 4) := by
      intro t ht
      rw [Set.uIoc_of_le hab] at ht
      have ht1 : 1 ≤ t := le_trans ha ht.1.le
      have ht2 : t ≤ 2*T + 1 := le_trans ht.2 hb
      rw [Real.norm_eq_abs]
      refine (hCM t ht1).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCM0.le
      exact Real.log_le_log (by linarith) (by linarith)
    have := intervalIntegral.norm_integral_le_of_norm_le_const hbound
    rw [Real.norm_eq_abs] at this
    have hlog24 : Real.log (2*T + 4) ≤ 2 * Real.log T := by
      calc Real.log (2*T + 4) ≤ Real.log (T ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
        _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
    calc |∫ t in a..b, mu t| ≤ CM * Real.log (2*T+4) * |b - a| := this
      _ ≤ CM * (2 * Real.log T) * 1 := by
          refine mul_le_mul ?_ hba (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hlog24 hCM0.le
      _ = 2 * CM * Real.log T := by ring
  have hμ1 : |∫ t in T₁..T, mu t| ≤ 2 * CM * Real.log T :=
    hμwin T₁ T h1T₁ hT₁b (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hμ2 : |∫ t in (2*T)..T₂, mu t| ≤ 2 * CM * Real.log T :=
    hμwin (2*T) T₂ (by linarith) hT₂a (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hintmu := hCμ T (by linarith)
  have hT0 : (0:ℝ) < T := by linarith
  have hCμT : Cμ / T ≤ |Cμ| := by
    calc Cμ / T ≤ |Cμ| / T := by gcongr; exact le_abs_self _
      _ ≤ |Cμ| / 1 := by
          apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos
          linarith
      _ = |Cμ| := div_one _
  -- final assembly
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have hπ1 : (1:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hkey : (Ncount T (2*T) : ℝ) - T * ell1 T / (2 * Real.pi)
      = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have hΛim : (1/Real.pi) * (halfContour (logDeriv completedRiemannZeta) T₁ T₂).im
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + (1/Real.pi) * (halfContour (logDeriv Complex.Gammaℝ) T₁ T₂).im := by
      rw [hsplit, Complex.add_im]
      ring
    have h5 : (Ncount T₁ T₂ : ℝ)
        = (1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
          + ∫ t in T₁..T₂, mu t := by
      rw [hN, hΛim, hgam]
    rw [hμsplit] at h5
    have h6 := hadd
    linarith
  have hlogT₁ : Real.log T₁ ≤ Real.log T := Real.log_le_log (by linarith) hT₁b
  have hlogT₂ : Real.log T₂ ≤ 2 * Real.log T := by
    calc Real.log T₂ ≤ Real.log (T^2) := Real.log_le_log (by linarith) (by nlinarith)
      _ = 2 * Real.log T := by rw [Real.log_pow]; push_cast; ring
  -- bound each piece
  have hNc1 : (0:ℝ) ≤ (Ncount T₁ T : ℝ) := Nat.cast_nonneg _
  have hNc2 : (0:ℝ) ≤ (Ncount (2*T) T₂ : ℝ) := Nat.cast_nonneg _
  have hA : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
      ≤ 3 * |CB| * Real.log T + 1 := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1/Real.pi)]
    have step1 : (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁ + Real.pi + |CB| * Real.log T₂) := by
      exact mul_le_mul_of_nonneg_left hζbound (by positivity)
    have hfrac : (1:ℝ)/Real.pi ≤ 1 := by
      rw [div_le_one hπ]
      exact hπ1
    have e1 : (1/Real.pi) * (|CB| * Real.log T₁) ≤ |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₁) ≤ 1 * (|CB| * Real.log T₁) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg h1T₁)
        _ = |CB| * Real.log T₁ := one_mul _
        _ ≤ |CB| * Real.log T := mul_le_mul_of_nonneg_left hlogT₁ (abs_nonneg _)
    have e2 : (1/Real.pi) * Real.pi = 1 := by field_simp
    have e3 : (1/Real.pi) * (|CB| * Real.log T₂) ≤ 2 * |CB| * Real.log T := by
      calc (1/Real.pi) * (|CB| * Real.log T₂) ≤ 1 * (|CB| * Real.log T₂) := by
            apply mul_le_mul_of_nonneg_right hfrac
            exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
        _ = |CB| * Real.log T₂ := one_mul _
        _ ≤ |CB| * (2 * Real.log T) := mul_le_mul_of_nonneg_left hlogT₂ (abs_nonneg _)
        _ = 2 * |CB| * Real.log T := by ring
    calc (1/Real.pi) * |(halfContour (logDeriv riemannZeta) T₁ T₂).im|
        ≤ (1/Real.pi) * (|CB| * Real.log T₁) + (1/Real.pi) * Real.pi
          + (1/Real.pi) * (|CB| * Real.log T₂) := by
          rw [← mul_add, ← mul_add]
          exact step1
      _ ≤ |CB| * Real.log T + 1 + 2 * |CB| * Real.log T := by
          rw [e2]
          linarith
      _ = 3 * |CB| * Real.log T + 1 := by ring
  have hD : |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ |Cμ| * Real.log T := by
    calc |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)| ≤ Cμ / T := hintmu
      _ ≤ |Cμ| := hCμT
      _ = |Cμ| * 1 := (mul_one _).symm
      _ ≤ |Cμ| * Real.log T := mul_le_mul_of_nonneg_left hlogT (abs_nonneg _)
  -- put it together
  simp only [zetaZeroConfig_N]
  rw [show T / (2 * Real.pi) * ell1 T = T * ell1 T / (2 * Real.pi) by ring, hkey]
  have htri : |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
        - ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ))|
      ≤ |(1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im|
        + (|∫ t in T₁..T, mu t| + |∫ t in (2*T)..T₂, mu t|
        + |(∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)|)
        + ((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)) := by
    have t1 := abs_sub (((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im
        + ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))))
      (((Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)))
    have t2 := abs_add_le ((1/Real.pi) * (halfContour (logDeriv riemannZeta) T₁ T₂).im)
      ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t)
        + ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi)))
    have t3 := abs_add_le ((∫ t in T₁..T, mu t) + (∫ t in (2*T)..T₂, mu t))
      ((∫ t in T..(2*T), mu t) - T * ell1 T / (2 * Real.pi))
    have t4 := abs_add_le (∫ t in T₁..T, mu t) (∫ t in (2*T)..T₂, mu t)
    have t5 : |(Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ)|
        = (Ncount T₁ T : ℝ) + (Ncount (2*T) T₂ : ℝ) := abs_of_nonneg (by positivity)
    linarith
  refine htri.trans ?_
  linarith [hA, hμ1, hμ2, hD, hw1, hw2]

/-- The assembly, stated against the two Backlund bounds as explicit hypotheses (∃-form; from
`rvM_main_param` instantiated with the ∃-witnesses of Backlund, the local count, H-Γ's int_mu, μ ≪ log, continuity). -/
theorem rvM_main_aux (hΓ : GammaFacts)
    (backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
      |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T)
    (vertical_two : ∀ T₁ T₂ : ℝ,
      |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T := by
  obtain ⟨CB, TB, hB⟩ := backlund_horizontal
  obtain ⟨A₀, hA₀1, hA₀⟩ := zeta_local_zero_count
  obtain ⟨Cμ, Tμ, hCμ⟩ := hΓ.int_mu
  obtain ⟨CM, hCM0, hCM⟩ := mu_le_log hΓ
  exact ⟨_, _, rvM_main_param hB vertical_two hA₀1 hA₀ hCμ hCM0 hCM (mu_continuous hΓ)⟩

set_option maxHeartbeats 1000000 in
/-- (M7)+assembly: H-RvM's main clause for ζ, conditional on the Γ-facts.
[Tit86, Thm 9.4]: N(T,2T) = (T/2π)(log(T/2π) + 2 log 2 − 1) + O(log T). -/
theorem rvM_main (hΓ : GammaFacts) : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    |(zetaZeroConfig.N T (2 * T) : ℝ) - T / (2 * Real.pi) * ell1 T| ≤ C * Real.log T :=
  rvM_main_aux hΓ backlund_horizontal vertical_two

end Zeta23.RvM
