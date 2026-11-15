import RSBounds.BacklundCountRealAxis

/-!
# The upper-half rectangle counts positive ordinates with multiplicities

The proof instantiates calr's checked rectangle residue theorem for the
actual entire xi function, with constant weight one. The lower side lies
on the real axis, which was proved zero-free in `BacklundCountRealAxis`.
-/

open Complex MeasureTheory Set Filter Metric
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

noncomputable def lowerCorner : ℂ := -1 / 4
noncomputable def upperCorner (T : ℝ) : ℂ := 5 / 4 + T * I

@[simp] theorem lowerCorner_re : lowerCorner.re = -1 / 4 := by norm_num [lowerCorner]
@[simp] theorem lowerCorner_im : lowerCorner.im = 0 := by norm_num [lowerCorner]
@[simp] theorem upperCorner_re (T : ℝ) : (upperCorner T).re = 5 / 4 := by simp [upperCorner]
@[simp] theorem upperCorner_im (T : ℝ) : (upperCorner T).im = T := by simp [upperCorner]

theorem xi_analyticOrderAt_ne_top (ρ : ℂ) : analyticOrderAt xiF ρ ≠ ⊤ := by
  have h2 : xiF 2 ≠ 0 := xiF_ne_zero_of_one_le_re (by norm_num)
  have hc : analyticOrderAt xiF 2 ≠ ⊤ := by
    rw [(differentiable_xiF.analyticAt 2).analyticOrderAt_eq_zero.mpr h2]
    simp
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF univ)
    isPreconnected_univ (mem_univ 2) (mem_univ ρ) hc

theorem mem_positiveZeros_iff {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ positiveZeros T ↔ xiF ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T := by
  classical
  constructor
  · intro h
    obtain ⟨hz, him0, himT⟩ := Finset.mem_filter.mp h
    exact ⟨eq_zero_of_mem_zerosIn differentiable_xiF hz, him0, himT⟩
  · rintro ⟨hz, him0, himT⟩
    have hre := xiF_zero_re_strip hz
    have hnorm : ‖ρ - 2‖ < RT T / 2 := by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [sub_re, sub_im]
      norm_num only [re_ofNat, im_ofNat, sub_zero]
      rw [abs_of_neg (by linarith : ρ.re - 2 < 0), abs_of_pos him0]
      unfold RT
      linarith
    have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
      rw [mem_closedBall, dist_eq_norm]
      unfold RT at *
      linarith
    have han : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T)) :=
      fun z _ => differentiable_xiF.analyticAt z
    have hdiv : divB xiF 2 (RT T) ρ ≠ 0 := by
      rw [divB, MeromorphicOn.AnalyticOnNhd.divisor_apply han hρR]
      have horder : analyticOrderAt xiF ρ ≠ 0 := by
        rw [Ne, (differentiable_xiF.analyticAt ρ).analyticOrderAt_eq_zero]
        exact not_not.mpr hz
      have hfinite := xi_analyticOrderAt_ne_top ρ
      cases ho : analyticOrderAt xiF ρ with
      | top => exact absurd ho hfinite
      | coe n => simpa [ho] using horder
    rw [positiveZeros, Finset.mem_filter, zerosIn, Finset.mem_filter,
      Set.Finite.mem_toFinset, Function.mem_support]
    exact ⟨⟨hdiv, hnorm⟩, him0, himT⟩

theorem mult_positiveZeros_eq_analyticOrder {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ positiveZeros T) :
    multRectD xiF T ρ = (analyticOrderAt xiF ρ).toNat := by
  have hz := (Finset.mem_filter.mp hρ).1
  have hnorm := (mem_zerosIn hz).1
  have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
    rw [mem_closedBall, dist_eq_norm]
    unfold RT at *
    linarith
  rw [multRectD, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => differentiable_xiF.analyticAt z : AnalyticOnNhd ℂ xiF (closedBall 2 (RT T))) hρR]
  cases ho : analyticOrderAt xiF ρ <;> simp

theorem N_eq_sum_analyticOrder {T : ℝ} (hT : 0 < T) :
    N T = ∑ ρ ∈ positiveZeros T, (analyticOrderAt xiF ρ).toNat := by
  unfold N
  exact Finset.sum_congr rfl (fun ρ hρ => mult_positiveZeros_eq_analyticOrder hT hρ)

theorem rectangle_filter_eq_positiveZeros {T : ℝ} (hT : 0 < T) :
    (zerosIn xiF 2 (RT T) (RT T / 2)).filter
      (fun ρ => lowerCorner.re < ρ.re ∧ ρ.re < (upperCorner T).re ∧
        lowerCorner.im < ρ.im ∧ ρ.im < (upperCorner T).im) = positiveZeros T := by
  classical
  apply Finset.ext
  intro ρ
  simp only [Finset.mem_filter, lowerCorner_re, lowerCorner_im, upperCorner_re,
    upperCorner_im, positiveZeros]
  constructor
  · rintro ⟨hz, _, _, h0, hT⟩
    exact ⟨hz, h0, hT⟩
  · rintro ⟨hz, h0, hT⟩
    have hre := xiF_zero_re_strip (eq_zero_of_mem_zerosIn differentiable_xiF hz)
    exact ⟨hz, by linarith [hre.1], by linarith [hre.2], h0, hT⟩

theorem noZerosOnSides_xi {T : ℝ} (hg : zetaGoodHeight T) :
    NoZerosOnSides xiF lowerCorner (upperCorner T) := by
  unfold NoZerosOnSides
  simp only [lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
    ofReal_zero, zero_mul, add_zero]
  refine ⟨fun x _ => xiF_ne_zero_real x, ?_, ?_, ?_⟩
  · intro x _
    exact xiF_ne_zero_of_goodHeight hg (by simp)
  · intro y _
    exact xiF_ne_zero_of_one_le_re (by norm_num)
  · intro y _
    exact xiF_ne_zero_of_re_nonpos (by norm_num)

theorem rectangle_count_identity {T : ℝ} (hT : 0 < T) (hg : zetaGoodHeight T) :
    rectInt (logDeriv xiF) lowerCorner (upperCorner T) =
      2 * Real.pi * I * (N T : ℂ) := by
  have hR : 0 < RT T := by unfold RT; linarith
  have hrect : [[lowerCorner.re, (upperCorner T).re]] ×ℂ
      [[lowerCorner.im, (upperCorner T).im]] ⊆ ball 2 (RT T / 2) := by
    intro s hs
    rw [mem_reProdIm, lowerCorner_re, lowerCorner_im, upperCorner_re, upperCorner_im,
      Set.uIcc_of_le (by norm_num : (-1 / 4 : ℝ) ≤ 5 / 4),
      Set.uIcc_of_le hT.le] at hs
    rw [mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
    simp only [sub_re, sub_im]
    norm_num only [re_ofNat, im_ofNat, sub_zero]
    rw [abs_of_neg (by linarith [hs.1.2] : s.re - 2 < 0), abs_of_nonneg hs.2.1]
    unfold RT
    linarith [hs.1.1, hs.2.2]
  have hh := rectInt_logDeriv_mul differentiable_xiF hR
    (xiF_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 : ℂ).re))
    (by norm_num : lowerCorner.re < (upperCorner T).re)
    (by simpa using hT : lowerCorner.im < (upperCorner T).im)
    hrect (noZerosOnSides_xi hg) isOpen_univ (subset_univ _)
    (differentiableOn_const (c := (1 : ℂ)))
  simp only [mul_one] at hh
  rw [rectangle_filter_eq_positiveZeros hT] at hh
  simpa only [N, Nat.cast_sum, multRectD] using hh

end TernaryGoldbach.RSBounds.BacklundCountIdentity
