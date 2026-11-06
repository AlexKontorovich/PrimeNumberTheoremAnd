import RSBounds.BacklundLowScalarBase

/-!
# Scalar comparison at the original moderate zero-count height

The rounded angular coefficients are compared with Rosser's target for
all `T >= 100`. The error terms decrease sufficiently that only two coarse
logarithmic lower bounds are needed; no asymptotic PNT estimate is used.
-/

open Real

namespace TernaryGoldbach.RSBounds.BacklundFinalScalar
open BacklundLowScalar

lemma log_hundred_gt : (4.6 : ℝ) < Real.log 100 := by
  have h := LogCert.log_gt (c := ⟨6, 16, 9⟩) (by decide)
    (l := (23 / 5 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  exact h

lemma log_four_point_six_gt : (1.5 : ℝ) < Real.log (4.6 : ℝ) := by
  have h := LogCert.log_gt (c := ⟨2, 20, 3⟩) (by decide)
    (l := (3 / 2 : ℚ)) (by decide +kernel)
  norm_num [LogCert.ratio] at h ⊢
  exact h

noncomputable def roundedEnvelope (T : ℝ) : ℝ :=
  0.1361 * Real.log (T + 33 / 25) +
  0.4423 * Real.log (Real.log (T + 33 / 25)) + 1.5803 +
  Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) +
  2 / (Real.pi * T) + 1 / (4 * Real.pi * T)

lemma roundedEnvelope_lt_rosser {T : ℝ} (hT : 100 ≤ T) :
    roundedEnvelope T < rosserR 1.588 T := by
  have hT0 : 0 < T := by linarith
  have hp : 0 < Real.pi := Real.pi_pos
  have hl : (4.6 : ℝ) < Real.log T :=
    log_hundred_gt.trans_le (Real.log_le_log (by norm_num) hT)
  have hl0 : 0 < Real.log T := by linarith
  have hll : (1.5 : ℝ) < Real.log (Real.log T) :=
    log_four_point_six_gt.trans_le (Real.log_le_log (by norm_num) hl.le)
  have hs : Real.log (T + 33 / 25) ≤ Real.log T + (33 / 25) / T := by
    have hf : T + 33 / 25 = T * (1 + (33 / 25) / T) := by field_simp
    rw [hf, Real.log_mul hT0.ne' (by positivity)]
    have hh := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (33 / 25) / T)
    linarith
  have hsp : 0 < Real.log (T + 33 / 25) := Real.log_pos (by linarith)
  have hss : Real.log (Real.log (T + 33 / 25)) ≤
      Real.log (Real.log T) + (33 / 25) / (T * Real.log T) := by
    apply (Real.log_le_log hsp hs).trans
    have hf : Real.log T + (33 / 25) / T =
        Real.log T * (1 + (33 / 25) / (T * Real.log T)) := by
      field_simp
    rw [hf, Real.log_mul hl0.ne' (by positivity)]
    have hh := Real.log_le_sub_one_of_pos
      (by positivity : (0 : ℝ) < 1 + (33 / 25) / (T * Real.log T))
    linarith
  have hA : 0.1361 * Real.log (T + 33 / 25) ≤
      0.1361 * Real.log T + 0.18 / T := by
    calc
      _ ≤ 0.1361 * (Real.log T + (33 / 25) / T) :=
        mul_le_mul_of_nonneg_left hs (by norm_num)
      _ = 0.1361 * Real.log T + (0.1361 * (33 / 25)) / T := by ring
      _ ≤ _ := by gcongr; norm_num
  have hBc : (0.4423 * (33 / 25)) / (T * Real.log T) ≤ 0.13 / T := by
    rw [div_le_div_iff₀ (mul_pos hT0 hl0) hT0]
    nlinarith [mul_nonneg hT0.le (sub_nonneg.mpr hl.le)]
  have hB : 0.4423 * Real.log (Real.log (T + 33 / 25)) ≤
      0.4423 * Real.log (Real.log T) + 0.13 / T := by
    calc
      _ ≤ 0.4423 * (Real.log (Real.log T) + (33 / 25) / (T * Real.log T)) :=
        mul_le_mul_of_nonneg_left hss (by norm_num)
      _ = 0.4423 * Real.log (Real.log T) +
          (0.4423 * (33 / 25)) / (T * Real.log T) := by ring
      _ ≤ _ := add_le_add le_rfl hBc
  let D : ℝ := (T - 33 / 25) ^ 2 - 4
  have hD : 80 * T ≤ D := by
    dsimp [D]
    nlinarith [mul_nonneg (sub_nonneg.mpr hT) hT0.le]
  have hD0 : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hV : Real.log ((T - 33 / 25) ^ 2 / D) ≤ 0.05 / T := by
    have hf : (T - 33 / 25) ^ 2 / D = 1 + 4 / D := by
      calc
        _ = (D + 4) / D := by congr 1; dsimp [D]; ring
        _ = _ := by rw [add_div, div_self hD0.ne']
    rw [hf]
    have hh := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 4 / D)
    have hdiv : 4 / D ≤ 0.05 / T := by
      rw [div_le_div_iff₀ hD0 hT0]
      linarith
    linarith
  have hpi2 : (2 : ℝ) / Real.pi ≤ 0.637 := by
    rw [div_le_iff₀ hp]
    linarith [Real.pi_gt_d2]
  have hG0 : (1 : ℝ) / (4 * Real.pi) ≤ 0.08 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_d2]
  have hP : 2 / (Real.pi * T) ≤ 0.637 / T := by
    convert div_le_div_of_nonneg_right hpi2 hT0.le using 1 <;> ring
  have hG : 1 / (4 * Real.pi * T) ≤ 0.08 / T := by
    convert div_le_div_of_nonneg_right hG0 hT0.le using 1 <;> ring
  have hsmall : (1.1 : ℝ) / T ≤ 0.011 := by
    rw [div_le_iff₀ hT0]
    linarith
  have hrec : 0 < 1 / T := by positivity
  change Real.log ((T - 33 / 25) ^ 2 / ((T - 33 / 25) ^ 2 - 4)) ≤ 0.05 / T at hV
  unfold roundedEnvelope rosserR
  simp only [div_eq_mul_inv] at hA hB hV hP hG hsmall hrec ⊢
  linarith only [hA, hB, hV, hP, hG, hsmall, hrec, hl, hll]

end TernaryGoldbach.RSBounds.BacklundFinalScalar
