import TernaryGoldbach.Explicit.XiPartial
import RSBounds.ZetaZeroTable
import RSBounds.RS75RealAxisNumerics

/-!
# A positive real-axis increment of the xi logarithmic derivative

The already certified first 29 positive zeros and their conjugates provide a
quantitative increment on `[1, 1.03]`. All other zeros contribute nonnegative
increments. The passage to the actual logarithmic derivative uses the proved
finite partial-fraction approximation, without differentiating a zero series.
-/

open Complex Set Filter Finset
open scoped Real Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.RS75XiIncrement
open TernaryGoldbach.Explicit BacklundCountIdentity ZetaZeroTable

noncomputable def kernel (s : ℝ) (ρ : ℂ) : ℝ := (((s : ℂ) - ρ)⁻¹).re

theorem kernel_eq (s : ℝ) (ρ : ℂ) :
    kernel s ρ = (s - ρ.re) / ((s - ρ.re) ^ 2 + ρ.im ^ 2) := by
  simp [kernel, Complex.inv_re, Complex.normSq_apply, pow_two]

theorem first29_height_lower (i : Fin 29) : 14.13 < first29.ordinate i := by
  have h := (first29.bracket (0 : Fin 29)).1
  have h0 : (first29.lower (0 : Fin 29) : ℝ) = 14.13 := by
    norm_num [first29, BacklundLowCount.bracketLower,
      BacklundLowScalar.certificate, BacklundLowScalar.certificates]
  rw [h0] at h
  exact h.trans_le (first29.strictMono.monotone (Fin.zero_le i))

theorem xi_zero_height_lower {ρ : ℂ} (hρ : xiF ρ = 0) : 14.13 < |ρ.im| := by
  have hn := xiF_zero_im_ne_zero hρ
  have hpos : ∀ {z : ℂ}, xiF z = 0 → 0 < z.im → 14.13 < z.im := by
    intro z hz hi
    by_cases h100 : z.im ≤ 100
    · have hs := xiF_zero_re_strip hz
      obtain ⟨i, hi'⟩ := first29.complete z ((xiF_eq_zero_iff hs.1 hs.2).mp hz) hi h100
      rw [hi']
      simpa using first29_height_lower i
    · linarith
  rcases lt_or_gt_of_ne hn with hneg | hpositive
  · have hc : xiF (conj ρ) = 0 := by rw [xiF_conj, hρ, map_zero]
    have h := hpos hc (by simpa using neg_pos.mpr hneg)
    simpa [abs_of_neg hneg] using h
  · simpa [abs_of_pos hpositive] using hpos hρ hpositive

theorem kernel_increment_eq {s : ℝ} {ρ : ℂ} (hγ : ρ.im ≠ 0) :
    kernel s ρ - kernel 1 ρ =
      (s - 1) * (ρ.im ^ 2 - (s - ρ.re) * (1 - ρ.re)) /
        (((s - ρ.re) ^ 2 + ρ.im ^ 2) * ((1 - ρ.re) ^ 2 + ρ.im ^ 2)) := by
  have h1 : 0 < (s - ρ.re) ^ 2 + ρ.im ^ 2 := by positivity
  have h2 : 0 < (1 - ρ.re) ^ 2 + ρ.im ^ 2 := by positivity
  rw [kernel_eq, kernel_eq]
  field_simp
  ring

theorem kernel_increment_nonneg {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03)
    {ρ : ℂ} (hρ : xiF ρ = 0) : 0 ≤ kernel s ρ - kernel 1 ρ := by
  have hr := xiF_zero_re_strip hρ
  have ht := xi_zero_height_lower hρ
  have ht2 : 14.13 ^ 2 < ρ.im ^ 2 := by nlinarith [sq_abs ρ.im]
  rw [kernel_increment_eq (xiF_zero_im_ne_zero hρ)]
  have hprod : (s - ρ.re) * (1 - ρ.re) ≤ 1.03 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ s - ρ.re) hr.1.le]
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr hs) (by linarith)) (by positivity)

noncomputable def headRate (u : ℝ) : ℝ :=
  (u ^ 2 - (0.53 : ℝ) ^ 2) / (u ^ 2 + (0.53 : ℝ) ^ 2) ^ 2

theorem headRate_nonneg {u : ℝ} (hu : 2 ≤ u) : 0 ≤ headRate u := by
  unfold headRate
  apply div_nonneg _ (sq_nonneg _)
  nlinarith

theorem headRate_antitone {t u : ℝ} (ht : 2 ≤ t) (htu : t ≤ u) :
    headRate u ≤ headRate t := by
  have htu2 : t ^ 2 ≤ u ^ 2 := by nlinarith
  have hp : 0 ≤ t ^ 2 * u ^ 2 - 0.53 ^ 2 * (t ^ 2 + u ^ 2) - 3 * (0.53 ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr htu2)
      (by nlinarith : 0 ≤ t ^ 2 - 0.53 ^ 2), sq_nonneg (t ^ 2 - 2)]
  unfold headRate
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have he : (t ^ 2 - 0.53 ^ 2) * (u ^ 2 + 0.53 ^ 2) ^ 2 -
      (u ^ 2 - 0.53 ^ 2) * (t ^ 2 + 0.53 ^ 2) ^ 2 =
      (u ^ 2 - t ^ 2) *
        (t ^ 2 * u ^ 2 - 0.53 ^ 2 * (t ^ 2 + u ^ 2) - 3 * (0.53 ^ 2) ^ 2) := by ring
  have := mul_nonneg (sub_nonneg.mpr htu2) hp
  linarith

theorem kernel_line_increment_lower {s t : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03)
    (ht : 2 ≤ |t|) :
    (s - 1) * headRate |t| ≤
      kernel s ((1 / 2 : ℂ) + t * I) - kernel 1 ((1 / 2 : ℂ) + t * I) := by
  have ht0 : t ≠ 0 := by intro h; norm_num [h] at ht
  rw [kernel_increment_eq (by simpa using ht0)]
  simp only [Complex.add_re, Complex.div_re, Complex.one_re,
    Complex.one_im, mul_zero, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one]
  norm_num
  have ht2 : 4 ≤ t ^ 2 := by nlinarith [sq_abs t]
  have hnum : 0 ≤ t ^ 2 - 0.53 ^ 2 := by linarith
  have hden : ((s - 1 / 2) ^ 2 + t ^ 2) * ((1 - 1 / 2) ^ 2 + t ^ 2) ≤
      (t ^ 2 + 0.53 ^ 2) ^ 2 := by
    have hsq : (s - 1 / 2) ^ 2 ≤ 0.53 ^ 2 := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 0.53 ^ 2 - (s - 1 / 2) ^ 2)
      (by positivity : 0 ≤ t ^ 2 + 1 / 4)]
  have hden0 : 0 < ((s - 1 / 2) ^ 2 + t ^ 2) * ((1 - 1 / 2) ^ 2 + t ^ 2) := by positivity
  unfold headRate
  rw [sq_abs]
  calc
    (s - 1) * ((t ^ 2 - 0.53 ^ 2) / (t ^ 2 + 0.53 ^ 2) ^ 2)
        ≤ (s - 1) * ((t ^ 2 - 0.53 ^ 2) /
          (((s - 1 / 2) ^ 2 + t ^ 2) * ((1 - 1 / 2) ^ 2 + t ^ 2))) := by
            exact mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left hnum hden0 hden) (sub_nonneg.mpr hs)
    _ ≤ (s - 1) * ((t ^ 2 - (s - 1 / 2) * (1 - 1 / 2)) /
          (((s - 1 / 2) ^ 2 + t ^ 2) * ((1 - 1 / 2) ^ 2 + t ^ 2))) := by
            apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hs)
            apply div_le_div_of_nonneg_right _ hden0.le
            nlinarith
    _ = _ := by ring

theorem approx_re {T ε : ℝ} {s : ℝ}
    (h : ‖logDeriv xiF (s : ℂ) +
      ∑ u ∈ sqZeros T, (mult T u : ℂ) * (u - (s : ℂ))⁻¹‖ ≤ ε) :
    |(logDeriv xiF (s : ℂ)).re -
      ∑ u ∈ sqZeros T, (mult T u : ℝ) * kernel s u| ≤ ε := by
  have hr := (Complex.abs_re_le_norm _).trans h
  convert hr using 1
  congr 1
  rw [Complex.add_re, Complex.re_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro u _
  rw [show u - (s : ℂ) = -((s : ℂ) - u) by ring, inv_neg, mul_neg,
    Complex.neg_re]
  simp [kernel, Complex.mul_re]

theorem finite_increment_le {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03)
    (S : Finset ℂ) (hS : ∀ ρ ∈ S, xiF ρ = 0)
    (hM : ∀ ρ ∈ S, ‖ρ - 1 / 2‖ ≤ 102) :
    (∑ ρ ∈ S, (kernel s ρ - kernel 1 ρ)) ≤
      (logDeriv xiF (s : ℂ)).re - (logDeriv xiF 1).re := by
  classical
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, _, happrox, hmem, hzero⟩ :=
    xi_partial_approx (M := 102) (ε := ε / 4) (by norm_num) (by positivity)
  have hsn : ‖(s : ℂ) - 1 / 2‖ ≤ 102 := by
    rw [show (s : ℂ) - 1 / 2 = ((s - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hξs : xiF (s : ℂ) ≠ 0 := xiF_ne_zero_of_one_le_re (by simpa using hs)
  have has := approx_re (happrox (s : ℂ) hsn hξs)
  have ha1 := approx_re (s := 1) (happrox 1 (by norm_num) (by rw [xiF_one]; norm_num))
  have hsub : S ⊆ sqZeros T := fun ρ hρ => (hmem ρ (hS ρ hρ) (hM ρ hρ)).1
  have hweight : (∑ ρ ∈ S, (kernel s ρ - kernel 1 ρ)) ≤
      ∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * (kernel s ρ - kernel 1 ρ) := by
    calc
      _ ≤ ∑ ρ ∈ S, (mult T ρ : ℝ) * (kernel s ρ - kernel 1 ρ) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        have hnat := (hmem ρ (hS ρ hρ) (hM ρ hρ)).2
        have hreal : (1 : ℝ) ≤ mult T ρ := by exact_mod_cast hnat
        have hn := kernel_increment_nonneg hs hs' (hS ρ hρ)
        nlinarith
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun ρ hρ _ => mul_nonneg (Nat.cast_nonneg _)
          (kernel_increment_nonneg hs hs' (hzero ρ hρ)))
  have he : (∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * (kernel s ρ - kernel 1 ρ)) =
      (∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * kernel s ρ) -
        ∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * kernel 1 ρ := by
    simp only [mul_sub, Finset.sum_sub_distrib]
  rw [he] at hweight
  have h1 := (abs_le.mp has).1
  have h2 := (abs_le.mp ha1).2
  norm_num at ha1 h2
  linarith

noncomputable def headPoint (i : Fin 29) (b : Bool) : ℂ :=
  (1 / 2 : ℂ) + (if b then first29.ordinate i else -first29.ordinate i) * I

theorem headPoint_zero (i : Fin 29) (b : Bool) : xiF (headPoint i b) = 0 := by
  have hz : xiF ((1 / 2 : ℂ) + first29.ordinate i * I) = 0 :=
    (xiF_eq_zero_iff (by norm_num) (by norm_num)).mpr (first29.zero i)
  cases b
  · have hc := congrArg (starRingEnd ℂ) hz
    rw [← xiF_conj] at hc
    simpa [headPoint, map_ofNat] using hc
  · simpa [headPoint] using hz

theorem headPoint_norm (i : Fin 29) (b : Bool) : ‖headPoint i b - 1 / 2‖ ≤ 102 := by
  have hi := first29.positive i
  have hi' := first29.le_height i
  cases b <;> simp [headPoint, abs_of_pos hi] <;> linarith

theorem headPoint_injective : Function.Injective (fun p : Fin 29 × Bool => headPoint p.1 p.2) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ he
  have him := congrArg Complex.im he
  cases b <;> cases c <;> simp [headPoint] at him
  · have hij : i = j := first29.strictMono.injective (by linarith)
    simp [hij]
  · linarith [first29.positive i, first29.positive j]
  · linarith [first29.positive i, first29.positive j]
  · have hij : i = j := first29.strictMono.injective him
    simp [hij]

theorem headPoint_increment_lower {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03)
    (i : Fin 29) (b : Bool) :
    (s - 1) * headRate (BacklundLowCount.bracketUpper i : ℝ) ≤
      kernel s (headPoint i b) - kernel 1 (headPoint i b) := by
  have ht := first29_height_lower i
  have hu := (first29.bracket i).2
  change first29.ordinate i < (BacklundLowCount.bracketUpper i : ℝ) at hu
  have hrate := headRate_antitone (by linarith : 2 ≤ first29.ordinate i) hu.le
  have hmul := mul_le_mul_of_nonneg_left hrate (sub_nonneg.mpr hs)
  cases b
  · have hk := kernel_line_increment_lower hs hs'
      (t := -first29.ordinate i) (by rw [abs_neg, abs_of_pos (first29.positive i)]; linarith)
    simp only [abs_neg, abs_of_pos (first29.positive i)] at hk
    simpa [headPoint, abs_of_pos (first29.positive i)] using hmul.trans hk
  · have hk := kernel_line_increment_lower hs hs'
      (t := first29.ordinate i) (by rw [abs_of_pos (first29.positive i)]; linarith)
    rw [abs_of_pos (first29.positive i)] at hk
    simpa [headPoint, abs_of_pos (first29.positive i)] using hmul.trans hk

theorem xi_logDeriv_increment_lower_head {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03) :
    (2 * ∑ i : Fin 29, headRate (BacklundLowCount.bracketUpper i : ℝ)) * (s - 1) ≤
      (logDeriv xiF (s : ℂ)).re - (logDeriv xiF 1).re := by
  classical
  let S := Finset.univ.image (fun p : Fin 29 × Bool => headPoint p.1 p.2)
  have hS : ∀ ρ ∈ S, xiF ρ = 0 := by
    intro ρ hρ
    obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hρ
    exact headPoint_zero i b
  have hM : ∀ ρ ∈ S, ‖ρ - 1 / 2‖ ≤ 102 := by
    intro ρ hρ
    obtain ⟨⟨i, b⟩, _, rfl⟩ := Finset.mem_image.mp hρ
    exact headPoint_norm i b
  apply le_trans _ (finite_increment_le hs hs' S hS hM)
  dsimp only [S]
  rw [Finset.sum_image (fun a _ b _ h => headPoint_injective h)]
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 29 × Bool)))
    (fun p _ => headPoint_increment_lower hs hs' p.1 p.2)
  convert hh using 1
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, ← two_mul, ← Finset.mul_sum]
  ring

/-- A positive quantitative increment, using only the checked first 29 zeros. -/
theorem xi_logDeriv_increment_lower {s : ℝ} (hs : 1 ≤ s) (hs' : s ≤ 1.03) :
    0.03414 * (s - 1) ≤
      (logDeriv xiF (s : ℂ)).re - (logDeriv xiF 1).re := by
  have h := mul_le_mul_of_nonneg_right RS75RealAxisNumerics.headCoefficient_lower_real
    (sub_nonneg.mpr hs)
  rw [RS75RealAxisNumerics.headCoefficient_cast] at h
  exact h.trans (by simpa only [headRate] using xi_logDeriv_increment_lower_head hs hs')

end TernaryGoldbach.RSBounds.RS75XiIncrement
