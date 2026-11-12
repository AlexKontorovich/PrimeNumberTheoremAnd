import RSBounds.PolynomialZetaFormula
import RSBounds.BacklundCountEndpoint
import Zeta23.ZetaReflect

/-!
# The polynomial contour zeros in the actual zeta count

The rectangle uses the entire regularization `(s-1)*zeta(s)`, while the
counting theorem uses actual zeta zeros and analytic multiplicities. These
finite-set bridges identify them without RH or simple-zero assumptions.
Conjugation and reflection orders reuse the replayed `Zeta23.ZetaReflect`
theorems; no symmetry is supplied as a hypothesis.
-/

open Complex Set Filter Metric
open scoped Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.PolynomialZeroCountBridge

open TernaryGoldbach.Explicit BacklundCountIdentity

private theorem zetaF_zero_of_xiF_zero {ρ : ℂ} (hρ : xiF ρ = 0) : zetaF ρ = 0 := by
  have hre := xiF_zero_re_strip hρ
  have h1 : ρ ≠ 1 := by intro h; simp [h] at hre
  rw [zetaF_of_ne h1, (xiF_eq_zero_iff hre.1 hre.2).mp hρ, mul_zero]

/-- Rectangle membership expressed through the entire xi function. -/
theorem mem_zerosRectD_zetaF_iff_xi {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ zerosRectD zetaF T ↔ xiF ρ = 0 ∧ |ρ.im| < T := by
  constructor
  · intro hρ
    obtain ⟨hz, hc⟩ := zerosRectD_zetaF_cases hρ
    have h0 : ρ ≠ 0 := by
      intro h
      rw [h, zetaF_of_ne (by norm_num), riemannZeta_zero] at hz
      norm_num at hz
    obtain ⟨hr0, hr1⟩ := hc.resolve_left h0
    have h1 : ρ ≠ 1 := by intro h; simp [h] at hr1
    have hzeta : riemannZeta ρ = 0 := by
      rw [zetaF_of_ne h1] at hz
      exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr h1)
    have hb := (Finset.mem_filter.mp hρ).2
    simp only [zT_re, zT_im, wT_re, wT_im] at hb
    exact ⟨(xiF_eq_zero_iff hr0 hr1).mpr hzeta, abs_lt.mpr ⟨hb.2.2.1, hb.2.2.2⟩⟩
  · rintro ⟨hxi, him⟩
    have hre := xiF_zero_re_strip hxi
    have hnorm : ‖ρ - 2‖ < RT T / 2 := by
      refine lt_of_le_of_lt (Complex.norm_le_abs_re_add_abs_im _) ?_
      simp only [sub_re, sub_im]
      norm_num only [re_ofNat, im_ofNat, sub_zero]
      rw [abs_of_neg (by linarith : ρ.re - 2 < 0)]
      unfold RT
      linarith
    have hz := mem_zerosIn_of_zeroD ldatum_zeta
      (show RT T / 2 ≤ RT T by unfold RT; linarith) hnorm (zetaF_zero_of_xiF_zero hxi)
    apply Finset.mem_filter.mpr
    refine ⟨hz, ?_⟩
    simp only [zT_re, zT_im, wT_re, wT_im]
    exact ⟨by linarith [hre.1], by linarith [hre.2], (abs_lt.mp him).1, (abs_lt.mp him).2⟩

/-- The rectangle contains precisely the nonreal zeta zeros below its height. -/
theorem mem_zerosRectD_zetaF_iff {T : ℝ} (hT : 0 < T) {ρ : ℂ} :
    ρ ∈ zerosRectD zetaF T ↔
      riemannZeta ρ = 0 ∧ ρ.im ≠ 0 ∧ |ρ.im| < T := by
  rw [mem_zerosRectD_zetaF_iff_xi hT]
  constructor
  · rintro ⟨hxi, him⟩
    have hre := xiF_zero_re_strip hxi
    exact ⟨(xiF_eq_zero_iff hre.1 hre.2).mp hxi, xiF_zero_im_ne_zero hxi, him⟩
  · rintro ⟨hz, him, hbound⟩
    exact ⟨xiF_eq_zero_of_zeta_zero him hz, hbound⟩

/-- Multiplication by the nonvanishing regularizing factor does not change order. -/
theorem analyticOrderAt_zetaF_eq_zeta {ρ : ℂ} (h1 : ρ ≠ 1) :
    analyticOrderAt zetaF ρ = analyticOrderAt riemannZeta ρ := by
  have he : zetaF =ᶠ[𝓝 ρ] fun s : ℂ => (s - 1) * riemannZeta s := by
    filter_upwards [isOpen_ne.mem_nhds h1] with s hs using zetaF_of_ne hs
  have hf : AnalyticAt ℂ (fun s : ℂ => s - 1) ρ := analyticAt_id.sub analyticAt_const
  rw [analyticOrderAt_congr he,
    show (fun s : ℂ => (s - 1) * riemannZeta s) =
      (fun s : ℂ => s - 1) * riemannZeta from rfl,
    analyticOrderAt_mul hf (analyticOn_riemannZeta ρ h1),
    hf.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr h1), zero_add]

/-- The actual natural multiplicity in the contour is zeta's analytic zero order. -/
theorem multRectD_zetaF_eq_analyticOrder {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) :
    multRectD zetaF T ρ = (analyticOrderAt riemannZeta ρ).toNat := by
  have hnorm := (mem_zerosIn (Finset.mem_filter.mp hρ).1).1
  have hρR : ρ ∈ closedBall (2 : ℂ) (RT T) := by
    rw [mem_closedBall, dist_eq_norm]
    unfold RT at *
    linarith
  have he : multRectD zetaF T ρ = (analyticOrderAt zetaF ρ).toNat := by
    rw [multRectD, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
      (fun z _ => differentiable_zetaF.analyticAt z :
        AnalyticOnNhd ℂ zetaF (closedBall 2 (RT T))) hρR]
    cases ho : analyticOrderAt zetaF ρ <;> simp
  have h1 : ρ ≠ 1 := by
    intro h
    have hi := ((mem_zerosRectD_zetaF_iff hT).mp hρ).2.1
    exact hi (by simp [h])
  rw [he, analyticOrderAt_zetaF_eq_zeta h1]

/-- Positive ordinates in the polynomial rectangle give the open count set. -/
theorem positive_filter_eq {T : ℝ} (hT : 0 < T) :
    (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im) = positiveZeros T := by
  classical
  apply Finset.ext
  intro ρ
  rw [Finset.mem_filter, mem_zerosRectD_zetaF_iff hT, mem_positiveZeros_iff_zeta hT]
  constructor
  · rintro ⟨⟨hz, _, him⟩, hp⟩
    exact ⟨hz, hp, (abs_lt.mp him).2⟩
  · rintro ⟨hz, hp, hbound⟩
    exact ⟨⟨hz, hp.ne', by simpa only [abs_of_pos hp] using hbound⟩, hp⟩

/-- Any smaller inclusive cutoff inside the rectangle gives the closed count set. -/
theorem closed_filter_eq {D T : ℝ} (hD : 0 < D) (hDT : D < T) :
    (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ D) =
      closedPositiveZeros D := by
  classical
  apply Finset.ext
  intro ρ
  rw [Finset.mem_filter, mem_zerosRectD_zetaF_iff (hD.trans hDT),
    mem_closedPositiveZeros_iff hD]
  constructor
  · rintro ⟨⟨hz, _, _⟩, hp, hbound⟩
    exact ⟨hz, hp, hbound⟩
  · rintro ⟨hz, hp, hbound⟩
    exact ⟨⟨hz, hp.ne', by simpa only [abs_of_pos hp] using hbound.trans_lt hDT⟩,
      hp, hbound⟩

/-- At a good height the open and closed positive count sets coincide. -/
theorem positiveZeros_eq_closed_of_goodHeight {T : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) : positiveZeros T = closedPositiveZeros T := by
  classical
  apply Finset.ext
  intro ρ
  rw [mem_positiveZeros_iff_zeta hT, mem_closedPositiveZeros_iff hT]
  constructor
  · exact fun ⟨hz, hp, hb⟩ => ⟨hz, hp, hb.le⟩
  · exact fun ⟨hz, hp, hb⟩ => ⟨hz, hp, lt_of_le_of_ne hb (hg ρ hz)⟩

theorem positive_filter_eq_closed_of_goodHeight {T : ℝ} (hT : 0 < T)
    (hg : zetaGoodHeight T) :
    (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im) = closedPositiveZeros T := by
  rw [positive_filter_eq hT, positiveZeros_eq_closed_of_goodHeight hT hg]

/-- The polynomial contour's chosen heights are good for the actual zeta count. -/
theorem zetaGoodHeight_of_goodHeights {T : ℕ → ℝ}
    (hT : PolynomialExplicit.GoodHeights zetaF Bz T) (k : ℕ) :
    zetaGoodHeight (T k) := by
  have hTk : 0 < T k := by
    have hk := (hT.mem k).1
    linarith [Nat.cast_nonneg (α := ℝ) k]
  intro ρ hz he
  have him : ρ.im ≠ 0 := by rw [he]; exact hTk.ne'
  have hxi := xiF_eq_zero_of_zeta_zero him hz
  have hre := xiF_zero_re_strip hxi
  have hs : ρ.re ∈ Set.uIcc (-1 / 2 : ℝ) (3 / 2) := by
    rw [Set.uIcc_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 3 / 2)]
    exact ⟨by linarith [hre.1], by linarith [hre.2]⟩
  have hn := ((hT.bounds k ρ.re hs).1).1
  have hρ : (ρ.re : ℂ) + (T k : ℂ) * I = ρ := by
    apply Complex.ext <;> simp [he]
  rw [hρ] at hn
  exact hn (zetaF_zero_of_xiF_zero hxi)

/-- Exact finite count conversion, retaining multiplicities. -/
theorem sum_multRectD_closed_filter_eq {D T : ℝ} (hD : 0 < D) (hDT : D < T) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ D),
      multRectD zetaF T ρ) = N_le D := by
  classical
  calc
    _ = ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ D),
        (analyticOrderAt riemannZeta ρ).toNat := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact multRectD_zetaF_eq_analyticOrder (hD.trans hDT) (Finset.mem_filter.mp hρ).1
    _ = N_le D := by rw [closed_filter_eq hD hDT]; rfl

/-- Weighted sums at a smaller inclusive cutoff use exactly the count's zero set. -/
theorem sum_multRectD_closed_filter {D T : ℝ} (hD : 0 < D) (hDT : D < T)
    (w : ℂ → ℝ) :
    (∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ D),
      (multRectD zetaF T ρ : ℝ) * w ρ) =
      ∑ ρ ∈ closedPositiveZeros D, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * w ρ := by
  classical
  calc
    _ = ∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 0 < ρ.im ∧ ρ.im ≤ D),
        ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * w ρ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      rw [multRectD_zetaF_eq_analyticOrder (hD.trans hDT) (Finset.mem_filter.mp hρ).1]
    _ = _ := by rw [closed_filter_eq hD hDT]

/-- Conjugation preserves the full polynomial rectangle's zero set. -/
theorem conj_mem_zerosRectD {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) : conj ρ ∈ zerosRectD zetaF T := by
  rw [mem_zerosRectD_zetaF_iff_xi hT] at hρ ⊢
  exact ⟨by rw [xiF_conj, hρ.1, map_zero], by simpa using hρ.2⟩

theorem multRectD_conj {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) :
    multRectD zetaF T (conj ρ) = multRectD zetaF T ρ := by
  have h1 : ρ ≠ 1 := by
    intro h
    exact ((mem_zerosRectD_zetaF_iff hT).mp hρ).2.1 (by simp [h])
  rw [multRectD_zetaF_eq_analyticOrder hT (conj_mem_zerosRectD hT hρ),
    multRectD_zetaF_eq_analyticOrder hT hρ, Zeta23.analyticOrderAt_zeta_conj h1]

/-- Reflection across the critical line preserves the rectangle and ordinate. -/
theorem reflect_mem_zerosRectD {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) : 1 - conj ρ ∈ zerosRectD zetaF T := by
  rw [mem_zerosRectD_zetaF_iff_xi hT] at hρ ⊢
  refine ⟨?_, ?_⟩
  · rw [xiF_one_sub, xiF_conj, hρ.1, map_zero]
  · simpa using hρ.2

theorem multRectD_reflect {T : ℝ} (hT : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ zerosRectD zetaF T) :
    multRectD zetaF T (1 - conj ρ) = multRectD zetaF T ρ := by
  have hxi := ((mem_zerosRectD_zetaF_iff_xi hT).mp hρ).1
  have hre := xiF_zero_re_strip hxi
  have hz := (xiF_eq_zero_iff hre.1 hre.2).mp hxi
  rw [multRectD_zetaF_eq_analyticOrder hT (reflect_mem_zerosRectD hT hρ),
    multRectD_zetaF_eq_analyticOrder hT hρ]
  exact Zeta23.zeta_mult_reflect ρ ⟨hz, hre.1, hre.2⟩

/-- Critical-line reflection also preserves every inclusive positive cutoff. -/
theorem reflect_mem_closedPositiveZeros {D : ℝ} (hD : 0 < D) {ρ : ℂ}
    (hρ : ρ ∈ closedPositiveZeros D) : 1 - conj ρ ∈ closedPositiveZeros D := by
  obtain ⟨hz, hp, hb⟩ := (mem_closedPositiveZeros_iff hD).mp hρ
  have hxi := xiF_eq_zero_of_zeta_zero hp.ne' hz
  have hre := xiF_zero_re_strip hxi
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, hre.1, hre.2⟩
  apply (mem_closedPositiveZeros_iff hD).mpr
  exact ⟨hr.1, by simpa using hp, by simpa using hb⟩

end TernaryGoldbach.RSBounds.PolynomialZeroCountBridge
