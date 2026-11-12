/-
Copyright (c) 2026. All rights reserved.
Released under the MIT license as described in the file LICENSE.
Authors: OpenAI
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Weighted sums from zero-count envelopes

This is the finite-ordinate partial-summation step used in Rosser--Schoenfeld
(1975), Lemma 7, equations (3.1)--(3.3). The count-envelope hypothesis is explicit;
this file does not assert the sharp Rosser zero-count estimate for zeta zeros.
An indexed finite set allows repeated ordinates, so multiplicities are retained.
-/

open Set MeasureTheory
open scoped BigOperators

namespace TernaryGoldbach.RSBounds

/-- Counting ordinates, with multiplicity represented by their indices. -/
noncomputable def ordinateCount {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ s, if γ i ≤ t then 1 else 0

private theorem intervalIntegrable_step {a b c : ℝ} {f : ℝ → ℝ}
    (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => if c ≤ t then f t else 0) volume a b := by
  have h₁ := hf.1.indicator (measurableSet_Ici (a := c))
  have h₂ := hf.2.indicator (measurableSet_Ici (a := c))
  exact ⟨h₁, h₂⟩

private theorem integral_step {a b c : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} :
    (∫ t in a..b, if c ≤ t then f t else 0) =
      ∫ t in max a c..max b c, f t := by
  have heq : (∫ t in a..b, if c ≤ t then f t else 0) =
      ∫ t in a..b, (Ioi c).indicator f t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ c by exact ae_iff.mpr (by simp)] with t ht _
    have hlt : c ≤ t ↔ c < t :=
      ⟨fun h => lt_of_le_of_ne h (Ne.symm ht), le_of_lt⟩
    simp only [indicator_apply, mem_Ioi, hlt]
  rw [heq]
  by_cases hcb : c ≤ b
  · rw [max_eq_left hcb, intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le (max_le hab hcb), integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi]
    rw [inter_comm, Ioc_inter_Ioi]
  · have hbc : b < c := lt_of_not_ge hcb
    rw [max_eq_right (hab.trans hbc.le), max_eq_right hbc.le,
      intervalIntegral.integral_same]
    apply intervalIntegral.integral_zero_ae
    filter_upwards [] with t ht
    rw [uIoc_of_le hab] at ht
    exact indicator_of_notMem (not_lt.mpr (ht.2.trans hbc.le)) f

/-- Partial summation for an arbitrary finite family of real ordinates. -/
theorem weighted_ordinate_sum_eq {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    {a b : ℝ} (hab : a ≤ b) {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume a b) :
    (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) =
      ordinateCount s γ b * φ b - ordinateCount s γ a * φ a -
        ∫ t in a..b, ordinateCount s γ t * φ' t := by
  classical
  have hi (i : ι) : IntervalIntegrable (fun t => if γ i ≤ t then φ' t else 0)
      volume a b := intervalIntegrable_step hφ'
  have hstep (i : ι) :
      (if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) =
        (if γ i ≤ b then 1 else 0) * φ b -
        (if γ i ≤ a then 1 else 0) * φ a -
        ∫ t in a..b, if γ i ≤ t then φ' t else 0 := by
    rw [integral_step hab]
    by_cases hia : γ i ≤ a
    · rw [max_eq_left hia, max_eq_left (hia.trans hab)]
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hφ t (by simpa [uIcc_of_le hab] using ht)) hφ']
      simp [hia, hia.trans hab, not_lt.mpr hia]
    · have hai : a ≤ γ i := (lt_of_not_ge hia).le
      by_cases hib : γ i ≤ b
      · rw [max_eq_right hai, max_eq_left hib,
          intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun t ht => hφ t (by
              rw [uIcc_of_le hib] at ht
              exact ⟨hai.trans ht.1, ht.2⟩))
            (hφ'.mono_set (by
              rw [uIcc_of_le hib, uIcc_of_le hab]
              exact Icc_subset_Icc hai le_rfl))]
        simp [hia, hib, lt_of_not_ge hia]
      · simp [hia, hib, max_eq_right hai, max_eq_right (le_of_not_ge hib)]
  simp only [ordinateCount, Finset.sum_mul]
  simp_rw [ite_mul, one_mul, zero_mul]
  rw [intervalIntegral.integral_finsetSum (fun i _ => hi i)]
  simp_rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => by simpa only [ite_mul, one_mul, zero_mul] using hstep i)

/-- The counting function times an integrable weight derivative is integrable. -/
theorem intervalIntegrable_ordinateCount_mul {ι : Type*} (s : Finset ι) (γ : ι → ℝ)
    {a b : ℝ} {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => ordinateCount s γ t * f t) volume a b := by
  have h := IntervalIntegrable.sum s (fun i _ => intervalIntegrable_step (c := γ i) hf)
  have heq : (fun t => ordinateCount s γ t * f t) =
      ∑ i ∈ s, fun t => if γ i ≤ t then f t else 0 := by
    funext t
    simp only [ordinateCount, Finset.sum_mul, ite_mul, one_mul, zero_mul,
      Finset.sum_apply]
  rw [heq]
  exact h

private theorem weighted_ordinate_sum_le_of_product {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    {φ φ' G G' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hG : ∀ t ∈ Icc a b, HasDerivAt G (G' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hG' : IntervalIntegrable G' volume a b)
    (hprod : ∀ t ∈ Ioo a b, G t * φ' t ≤ ordinateCount s γ t * φ' t) :
    (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) ≤
      (∫ t in a..b, G' t * φ t) +
        (ordinateCount s γ b - G b) * φ b -
        (ordinateCount s γ a - G a) * φ a := by
  have hGc : ContinuousOn G (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun t ht => (hG t ht).continuousAt.continuousWithinAt
  have hi := intervalIntegral.integral_mono_on_of_le_Ioo hab
    (hφ'.continuousOn_mul hGc) (intervalIntegrable_ordinateCount_mul s γ hφ') hprod
  have hp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (fun t ht => hG t (by simpa [uIcc_of_le hab] using ht))
    (fun t ht => hφ t (by simpa [uIcc_of_le hab] using ht)) hG' hφ'
  rw [weighted_ordinate_sum_eq s γ hab hφ hφ']
  linarith

/-- Increasing weights use the lower counting envelope `F - R`.
This is the integration-by-parts estimate in RS75 Lemma 7, case `j = 1`,
before replacing the derivative of `R` by an explicit logarithmic bound. -/
theorem weighted_ordinate_sum_le_increasing {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    {φ φ' F F' R R' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hR : ∀ t ∈ Icc a b, HasDerivAt R (R' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hF' : IntervalIntegrable F' volume a b)
    (hR' : IntervalIntegrable R' volume a b)
    (hmono : ∀ t ∈ Ioo a b, 0 ≤ φ' t)
    (hcount : ∀ t ∈ Icc a b, F t - R t ≤ ordinateCount s γ t) :
    (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) ≤
      (∫ t in a..b, (F' t - R' t) * φ t) +
        (ordinateCount s γ b - F b + R b) * φ b -
        (ordinateCount s γ a - F a + R a) * φ a := by
  have h := weighted_ordinate_sum_le_of_product s γ hab hφ
    (fun t ht => (hF t ht).sub (hR t ht)) hφ' (hF'.sub hR')
    (fun t ht => mul_le_mul_of_nonneg_right (hcount t ⟨ht.1.le, ht.2.le⟩) (hmono t ht))
  convert h using 1
  dsimp only [Pi.sub_apply]
  ring

/-- Decreasing weights use the upper counting envelope `F + R`.
Unlike a bound on the number of zeros by a multiple of `t * log t`, this retains
the sharp count error and both endpoint corrections. -/
theorem weighted_ordinate_sum_le_decreasing {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) {a b : ℝ} (hab : a ≤ b)
    {φ φ' F F' R R' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hR : ∀ t ∈ Icc a b, HasDerivAt R (R' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hF' : IntervalIntegrable F' volume a b)
    (hR' : IntervalIntegrable R' volume a b)
    (hmono : ∀ t ∈ Ioo a b, φ' t ≤ 0)
    (hcount : ∀ t ∈ Icc a b, ordinateCount s γ t ≤ F t + R t) :
    (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) ≤
      (∫ t in a..b, (F' t + R' t) * φ t) +
        (ordinateCount s γ b - F b - R b) * φ b -
        (ordinateCount s γ a - F a - R a) * φ a := by
  have h := weighted_ordinate_sum_le_of_product s γ hab hφ
    (fun t ht => (hF t ht).add (hR t ht)) hφ' (hF'.add hR')
    (fun t ht => mul_le_mul_of_nonpos_right (hcount t ⟨ht.1.le, ht.2.le⟩) (hmono t ht))
  simpa only [Pi.add_apply, sub_add_eq_sub_sub] using h

/-- The count-envelope step for a weight increasing up to `Y` and decreasing
thereafter. This retains the signed `R'` integrals; RS75 Lemma 7 obtains its
stated form by bounding them with the explicit derivative of Rosser's error.
No zero-count theorem is assumed implicitly. -/
theorem weighted_ordinate_sum_le_unimodal {ι : Type*}
    (s : Finset ι) (γ : ι → ℝ) {a Y b : ℝ} (haY : a ≤ Y) (hYb : Y ≤ b)
    {φ φ' F F' R R' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hF : ∀ t ∈ Icc a b, HasDerivAt F (F' t) t)
    (hR : ∀ t ∈ Icc a b, HasDerivAt R (R' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hF' : IntervalIntegrable F' volume a b)
    (hR' : IntervalIntegrable R' volume a b)
    (hinc : ∀ t ∈ Ioo a Y, 0 ≤ φ' t)
    (hdec : ∀ t ∈ Ioo Y b, φ' t ≤ 0)
    (hcount : ∀ t ∈ Icc a b, |ordinateCount s γ t - F t| ≤ R t) :
    (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) ≤
      (∫ t in a..b, F' t * φ t) - (∫ t in a..Y, R' t * φ t) +
        (∫ t in Y..b, R' t * φ t) + 2 * R Y * φ Y +
        (ordinateCount s γ b - F b - R b) * φ b -
        (ordinateCount s γ a - F a + R a) * φ a := by
  classical
  have hab := haY.trans hYb
  have hleft : Icc a Y ⊆ Icc a b := Icc_subset_Icc le_rfl hYb
  have hright : Icc Y b ⊆ Icc a b := Icc_subset_Icc haY le_rfl
  have subleft : uIcc a Y ⊆ uIcc a b := by simpa [uIcc_of_le haY, uIcc_of_le hab] using hleft
  have subright : uIcc Y b ⊆ uIcc a b := by simpa [uIcc_of_le hYb, uIcc_of_le hab] using hright
  have hi := weighted_ordinate_sum_le_increasing s γ haY
    (fun t ht => hφ t (hleft ht)) (fun t ht => hF t (hleft ht))
    (fun t ht => hR t (hleft ht)) (hφ'.mono_set subleft)
    (hF'.mono_set subleft) (hR'.mono_set subleft) hinc
    (fun t ht => by have := (abs_le.mp (hcount t (hleft ht))).1; linarith)
  have hd := weighted_ordinate_sum_le_decreasing s γ hYb
    (fun t ht => hφ t (hright ht)) (fun t ht => hF t (hright ht))
    (fun t ht => hR t (hright ht)) (hφ'.mono_set subright)
    (hF'.mono_set subright) (hR'.mono_set subright) hdec
    (fun t ht => by have := (abs_le.mp (hcount t (hright ht))).2; linarith)
  have hφc : ContinuousOn φ (uIcc a b) := by
    rw [uIcc_of_le hab]
    exact fun t ht => (hφ t ht).continuousAt.continuousWithinAt
  have hiF := hF'.mul_continuousOn hφc
  have hiR := hR'.mul_continuousOn hφc
  have heql : (∫ t in a..Y, (F' t - R' t) * φ t) =
      (∫ t in a..Y, F' t * φ t) - ∫ t in a..Y, R' t * φ t := by
    simp_rw [sub_mul]
    exact intervalIntegral.integral_sub (hiF.mono_set subleft) (hiR.mono_set subleft)
  have heqr : (∫ t in Y..b, (F' t + R' t) * φ t) =
      (∫ t in Y..b, F' t * φ t) + ∫ t in Y..b, R' t * φ t := by
    simp_rw [add_mul]
    exact intervalIntegral.integral_add (hiF.mono_set subright) (hiR.mono_set subright)
  rw [heql] at hi
  rw [heqr] at hd
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hiF.mono_set subleft) (hiF.mono_set subright)
  have hsplit :
      (∑ i ∈ s, if a < γ i ∧ γ i ≤ b then φ (γ i) else 0) =
      (∑ i ∈ s, if a < γ i ∧ γ i ≤ Y then φ (γ i) else 0) +
      (∑ i ∈ s, if Y < γ i ∧ γ i ≤ b then φ (γ i) else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hia : a < γ i
    · by_cases hiy : γ i ≤ Y
      · simp [hia, hiy, hiy.trans hYb, not_lt.mpr hiy]
      · have hyi : Y < γ i := lt_of_not_ge hiy
        simp [hia, hiy, hyi]
    · have hyi : ¬ Y < γ i := by intro h; exact hia (haY.trans_lt h)
      simp [hia, hyi]
  rw [hsplit]
  linarith

/-- The main term in Rosser's zero-count estimate. -/
noncomputable def rosserF (t : ℝ) : ℝ :=
  t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8

/-- The error-envelope shape. No bound on the actual zeta count is asserted. -/
noncomputable def rosserR (C t : ℝ) : ℝ :=
  0.137 * Real.log t + 0.443 * Real.log (Real.log t) + C

/-- Exact derivative of the main term. -/
theorem hasDerivAt_rosserF {t : ℝ} (ht : 0 < t) :
    HasDerivAt rosserF (Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) t := by
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hq : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht.ne' hp
  have hdiv := (hasDerivAt_id t).div_const (2 * Real.pi)
  have hh := ((hdiv.mul (hdiv.log hq)).sub hdiv).add_const (7 / 8 : ℝ)
  convert hh using 1
  · rfl
  · dsimp only [id_eq]
    field_simp [hp, ht.ne']
    <;> ring

/-- Exact derivative of the logarithmic error envelope. -/
theorem hasDerivAt_rosserR (C : ℝ) {t : ℝ} (ht : 1 < t) :
    HasDerivAt (rosserR C) ((0.137 + 0.443 / Real.log t) / t) t := by
  have ht0 : 0 < t := by linarith
  have hl0 : 0 < Real.log t := Real.log_pos ht
  have hlog := Real.hasDerivAt_log ht0.ne'
  have hh := ((hlog.const_mul 0.137).add ((hlog.log hl0.ne').const_mul 0.443)).add_const C
  convert hh using 1
  · rfl
  · field_simp [ht0.ne', hl0.ne']
    <;> ring

end TernaryGoldbach.RSBounds
