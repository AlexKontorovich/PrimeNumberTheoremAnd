import RSBounds.BacklundBottomData
import RSBounds.BacklundZetaBoundary

/-! The finite height-50 sum, uniformly for `1/2 ≤ σ ≤ 1`. -/

open Complex Real Finset

namespace TernaryGoldbach.RSBounds.BacklundBottomCertificates

theorem row_checked {n : ℕ} (hn : n ∈ Finset.Icc 1 20) : rowCheck n = true := by
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  have hm : n ∈ List.range' 1 20 := by
    rw [List.mem_range']
    exact ⟨n - 1, by omega, by omega⟩
  exact List.all_eq_true.mp all_rows_checked n hm

theorem amplitude_bounds {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
    {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (amplitudeLo n : ℝ) ≤ (n : ℝ) ^ (-σ) ∧
      (n : ℝ) ^ (-σ) ≤ (amplitudeHi n : ℝ) := by
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : 0 < n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hc := row_checked hn
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hc' := hc.2
  have hu := CenterNumerics.root_upper (n := n) (p := 1) (k := 2)
    (D := 10 ^ 6) (b := amplitudeNumerator n) hn0 (by norm_num) (by norm_num)
    (by norm_num; exact hc'.2)
  constructor
  · have hh := Real.rpow_le_rpow_of_exponent_le hnR (show (-1 : ℝ) ≤ -σ by linarith)
    simpa [amplitudeLo, Real.rpow_neg_one, one_div] using hh
  · have hh := Real.rpow_le_rpow_of_exponent_le hnR (show -σ ≤ -(1 / 2 : ℝ) by linarith)
    apply hh.trans
    norm_num [amplitudeHi] at hu ⊢
    exact hu

theorem interval_product_bounds {A B C D x y : ℝ}
    (hx0 : 0 ≤ x) (hxl : A ≤ x) (hxu : x ≤ B) (hyl : C ≤ y) (hyu : y ≤ D) :
    min (A * C) (B * C) ≤ x * y ∧ x * y ≤ max (A * D) (B * D) := by
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_left hyl hx0)
    by_cases hC : 0 ≤ C
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hxl hC)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hxu (le_of_not_ge hC))
  · apply le_trans (mul_le_mul_of_nonneg_left hyu hx0)
    by_cases hD : 0 ≤ D
    · exact (mul_le_mul_of_nonneg_right hxu hD).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hxl (le_of_not_ge hD)).trans (le_max_left _ _)

theorem power_components {n : ℕ} (hn : 1 ≤ n) (σ : ℝ) :
    ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re =
      (n : ℝ) ^ (-σ) * Real.cos (50 * Real.log n) ∧
    ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im =
      -((n : ℝ) ^ (-σ) * Real.sin (50 * Real.log n)) := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn0.ne'
  have hl : Complex.log (n : ℂ) = (Real.log n : ℂ) := by
    simpa using (Complex.ofReal_log hnR.le).symm
  have he : Complex.log (n : ℂ) * (-((σ : ℂ) + 50 * I)) =
      ((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I := by
    rw [hl]
    push_cast
    ring
  have hp : (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) =
      Complex.exp (((-σ * Real.log n : ℝ) : ℂ) + ((-(50 * Real.log n) : ℝ) : ℂ) * I) := by
    rw [Complex.cpow_def_of_ne_zero hnC, he]
  have hlr : (Complex.log (n : ℂ)).re = Real.log n := by rw [hl]; rfl
  have hli : (Complex.log (n : ℂ)).im = 0 := by rw [hl]; rfl
  constructor <;> rw [hp] <;>
    simp [Complex.exp_re, Complex.exp_im, Real.rpow_def_of_pos hnR, hlr, hli, mul_comm]

theorem term_rectangle {n : ℕ} (hn : n ∈ Finset.Icc 1 20)
    {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    (realLo n : ℝ) ≤ ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ∧
      ((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).re ≤ (realHi n : ℝ) ∧
    (sineLo n : ℝ) ≤ -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ∧
      -((n : ℂ) ^ (-((σ : ℂ) + 50 * I))).im ≤ (sineHi n : ℝ) := by
  have hn1 := (Finset.mem_Icc.mp hn).1
  have hc := row_checked hn
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  have hq : |(reducedAngle n : ℝ)| ≤ 1 := by
    exact_mod_cast hc.2.1
  obtain ⟨hcos, hsin⟩ := trig_approx hn1 hc.1 hq
  rw [abs_le] at hcos hsin
  obtain ⟨ha, hb⟩ := amplitude_bounds hn hσ0 hσ1
  have hnn := Real.rpow_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n) (-σ)
  have hR := interval_product_bounds hnn ha hb
    (show (cosRot (reducedAngle n) (quarterTurns n) : ℝ) - 1 / 10000 ≤
      Real.cos (50 * Real.log n) by linarith)
    (show Real.cos (50 * Real.log n) ≤
      (cosRot (reducedAngle n) (quarterTurns n) : ℝ) + 1 / 10000 by linarith)
  have hI := interval_product_bounds hnn ha hb
    (show (sinRot (reducedAngle n) (quarterTurns n) : ℝ) - 1 / 10000 ≤
      Real.sin (50 * Real.log n) by linarith)
    (show Real.sin (50 * Real.log n) ≤
      (sinRot (reducedAngle n) (quarterTurns n) : ℝ) + 1 / 10000 by linarith)
  obtain ⟨hr, hi⟩ := power_components hn1 σ
  rw [hr, hi, neg_neg]
  exact ⟨by simpa [realLo] using hR.1, by simpa [realHi] using hR.2,
    by simpa [sineLo] using hI.1, by simpa [sineHi] using hI.2⟩

noncomputable def finitePart (σ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 20, (weight n : ℂ) * (n : ℂ) ^ (-((σ : ℂ) + 50 * I))

theorem finitePart_rectangle {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    -(127 / 100 : ℝ) ≤ (finitePart σ).re ∧ (finitePart σ).re ≤ 159 / 100 ∧
      -(125 / 100 : ℝ) ≤ -(finitePart σ).im ∧ -(finitePart σ).im ≤ 125 / 100 := by
  have hw (n : ℕ) : 0 ≤ (weight n : ℝ) := by unfold weight; split_ifs <;> norm_num
  have h1 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realLo n : ℝ)) ≤ (finitePart σ).re := by
    simp only [finitePart, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, sub_zero]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).1 (hw n)
  have h2 : (finitePart σ).re ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realHi n : ℝ) := by
    simp only [finitePart, Complex.re_sum, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, sub_zero]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.1 (hw n)
  have h3 : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineLo n : ℝ)) ≤ -(finitePart σ).im := by
    simp only [finitePart, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.2.1 (hw n)
  have h4 : -(finitePart σ).im ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineHi n : ℝ) := by
    simp only [finitePart, Complex.im_sum, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, zero_mul, add_zero, ← Finset.sum_neg_distrib, ← mul_neg]
    exact Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left
      (term_rectangle hn hσ0 hσ1).2.2.2 (hw n)
  have ha : -(127 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realLo n : ℝ) := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.1
    push_cast at hh
    exact hh
  have hb : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (realHi n : ℝ)) ≤ 159 / 100 := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.1
    push_cast at hh
    exact hh
  have hc : -(125 / 100 : ℝ) ≤ ∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineLo n : ℝ) := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.2.1
    push_cast at hh
    exact hh
  have hd : (∑ n ∈ Finset.Icc 1 20, (weight n : ℝ) * (sineHi n : ℝ)) ≤ 125 / 100 := by
    have hh := Rat.cast_mono (K := ℝ) aggregate_checked.2.2.2
    push_cast at hh
    exact hh
  exact ⟨ha.trans h1, h2.trans hb, hc.trans h3, h4.trans hd⟩

theorem finitePart_norm_le {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖finitePart σ‖ ≤ 2.03 := by
  obtain ⟨hlr, hur, hli, hui⟩ := finitePart_rectangle hσ0 hσ1
  have hr : (finitePart σ).re ^ 2 ≤ (1.59 : ℝ) ^ 2 := by nlinarith
  have hi : (finitePart σ).im ^ 2 ≤ (1.25 : ℝ) ^ 2 := by nlinarith
  have hn := Complex.sq_norm_sub_sq_im (finitePart σ)
  nlinarith [norm_nonneg (finitePart σ)]

theorem finitePart_eq (σ : ℝ) :
    finitePart σ = (∑ n ∈ Finset.range 20, (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) +
      (20 : ℂ) ^ (-((σ : ℂ) + 50 * I)) / 2 := by
  have hs0 : -((σ : ℂ) + 50 * I) ≠ 0 := by
    intro he
    have hh := congrArg Complex.im he
    norm_num at hh
  have hsets : Finset.Icc (1 : ℕ) 20 = insert 20 (Finset.Icc 1 19) := by ext n; simp; omega
  have hsets' : Finset.Icc (1 : ℕ) 19 = Finset.Ico 1 20 := by ext n; simp; omega
  have hsum : (∑ n ∈ Finset.Icc 1 19, (weight n : ℂ) *
      (n : ℂ) ^ (-((σ : ℂ) + 50 * I))) =
      ∑ n ∈ Finset.Icc (1 : ℕ) 19, (n : ℂ) ^ (-((σ : ℂ) + 50 * I)) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hn20 : n ≠ 20 := by have := (Finset.mem_Icc.mp hn).2; omega
    simp [weight, hn20]
  rw [finitePart, hsets, Finset.sum_insert (by decide), hsum, hsets',
    Finset.sum_Ico_eq_sub _ (by decide)]
  simp only [Finset.sum_range_one, Nat.cast_zero, Complex.zero_cpow hs0, sub_zero]
  norm_num [weight, Finset.sum_range_one, hs0]
  ring

/-- Certified finite bottom edge for the sharp convexity argument. -/
theorem zeta_bottom_bound {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + 50 * I)‖ ≤ 3.75 := by
  let s : ℂ := (σ : ℂ) + 50 * I
  have hsr : s.re = σ := by simp [s]
  have hsi : s.im = 50 := by simp [s]
  have hs0 : 0 < s.re := by rw [hsr]; linarith
  have hs1 : s ≠ 1 := by intro he; have := congrArg Complex.im he; simp [hsi] at this
  have hn1 : ‖s‖ ≤ 50.01 := by
    have hh := Complex.sq_norm_sub_sq_im s
    rw [hsr, hsi] at hh
    nlinarith [norm_nonneg s]
  have hn2 : ‖s + 1‖ ≤ 50.04 := by
    have hh := Complex.sq_norm_sub_sq_im (s + 1)
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
      hsr, hsi, add_zero] at hh
    nlinarith [norm_nonneg (s + 1)]
  have hp : ‖s * (s + 1)‖ ≤ 50.01 * 50.04 := by
    rw [norm_mul]
    exact mul_le_mul hn1 hn2 (norm_nonneg _) (by norm_num)
  have ha : (20 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 0.223607 := by
    have hh := (amplitude_bounds (n := 20) (by decide)
      (σ := 1 / 2) (by norm_num) (by norm_num)).2
    norm_num [amplitudeHi, amplitudeNumerator] at hh ⊢
    exact hh
  have hpow : (20 : ℝ) ^ (-σ - 1) ≤ 0.01118035 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
      (show -σ - 1 ≤ -(1 / 2 : ℝ) + -1 by linarith)
    rw [Real.rpow_add (by norm_num), Real.rpow_neg_one] at hh
    nlinarith
  have hmainpow : (20 : ℝ) ^ (1 - σ) ≤ 4.473 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 20)
      (show 1 - σ ≤ (1 / 2 : ℝ) by linarith)
    rw [← Real.sqrt_eq_rpow] at hh
    exact hh.trans ((Real.sqrt_le_left (by norm_num)).mpr (by norm_num))
  have hd : (50 : ℝ) ≤ ‖s - 1‖ := by
    simpa [hsi] using Complex.abs_im_le_norm (s - 1)
  let a : ℂ := (20 : ℂ) ^ (1 - s) / (s - 1)
  let b : ℂ := s * (20 : ℂ) ^ (-s - 1) / 12
  have hpowNorm (z : ℂ) : ‖(20 : ℂ) ^ z‖ = (20 : ℝ) ^ z.re := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 20) z
  have hna : ‖a‖ ≤ 0.08946 := by
    have he : ‖a‖ = (20 : ℝ) ^ (1 - σ) / ‖s - 1‖ := by
      simp [a, norm_div, hpowNorm, hsr]
    rw [he]
    apply (div_le_iff₀ (by linarith : 0 < ‖s - 1‖)).mpr
    nlinarith
  have hnb : ‖b‖ ≤ 0.047 := by
    have he : ‖b‖ = ‖s‖ * (20 : ℝ) ^ (-σ - 1) / 12 := by
      simp [b, norm_div, norm_mul, hpowNorm, hsr]
    rw [he]
    have hh := mul_le_mul hn1 hpow
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
    linarith
  have hcoef : ‖s * (s + 1)‖ / (12 * (σ + 1)) ≤ (50.01 * 50.04 : ℝ) / 18 := by
    apply (div_le_div_iff₀ (by linarith : 0 < 12 * (σ + 1)) (by norm_num)).mpr
    nlinarith
  have htail : ‖s * (s + 1)‖ / (12 * (σ + 1)) * (20 : ℝ) ^ (-σ - 1) ≤ 1.555 := by
    calc
      _ ≤ ((50.01 * 50.04 : ℝ) / 18) * 0.01118035 := mul_le_mul hcoef hpow
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 20) _) (by norm_num)
      _ ≤ _ := by norm_num
  let R : ℂ := riemannZeta s - finitePart σ - a - b
  have hR : ‖R‖ ≤ 1.555 := by
    have hh := BacklundZetaBoundary.zeta_second_order_remainder_explicit_of_pos
      hs0 hs1 (N := 20) (by decide)
    norm_num only [Nat.cast_ofNat] at hh
    rw [hsr] at hh
    have he : riemannZeta s - (∑ k ∈ Finset.range 20, (k : ℂ) ^ (-s)) -
        (20 : ℂ) ^ (-s) / 2 - (20 : ℂ) ^ (1 - s) / (s - 1) -
        s * (20 : ℂ) ^ (-s - 1) / 12 = R := by
      dsimp [R, a, b]
      rw [finitePart_eq]
      dsimp [s]
      ring
    rw [he] at hh
    exact hh.trans htail
  have hH := finitePart_norm_le hσ0 hσ1
  have htri : ‖riemannZeta s‖ ≤ ‖finitePart σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by
    calc
      _ = ‖finitePart σ + a + b + R‖ := by congr 1; dsimp [R]; ring
      _ ≤ ‖finitePart σ + a + b‖ + ‖R‖ := norm_add_le _ _
      _ ≤ ‖finitePart σ + a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ‖finitePart σ‖ + ‖a‖ + ‖b‖ + ‖R‖ := by gcongr; exact norm_add_le _ _
  change ‖riemannZeta s‖ ≤ 3.75
  linarith

theorem norm_zeta_height_fifty_le {σ : ℝ} (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 1) :
    ‖riemannZeta ((σ : ℂ) + (50 : ℂ) * I)‖ ≤ 3.75 :=
  zeta_bottom_bound hσ0 hσ1

end TernaryGoldbach.RSBounds.BacklundBottomCertificates
