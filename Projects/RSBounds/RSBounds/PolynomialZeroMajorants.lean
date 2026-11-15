import RSBounds.PolynomialLeftKernel

/-!
# Pointwise zero-coefficient majorants for both quartic smoothings

All estimates use the already proved normalized kernels and their exact
dilation. Conjugation on positive real bases extends the cancellation band
to either sign of the imaginary part. These are statements about complex
parameters, with no zeta-zero or RH hypotheses.
-/

open Complex
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.PolynomialZeroMajorants
open PolynomialZeroKernel PolynomialLowerKernel PolynomialZeroCancellation
open PolynomialAveraged PolynomialKernelScaling

def delta : ℝ := 0.0000211

theorem delta_pos : 0 < delta := by norm_num [delta]
theorem four_mul_delta_lt_one : 4 * delta < 1 := by norm_num [delta]

/-- `true` selects the lower smoothing and `false` the upper smoothing. -/
noncomputable def coefficient (lower : Bool) (x : ℝ) (ρ : ℂ) : ℂ :=
  zeroCoefficient (if lower then x - 4 * (delta * x) else x) (delta * x) ρ

noncomputable def normalizedKernel (lower : Bool) (ρ : ℂ) : ℂ :=
  if lower then
    forwardDiff delta 4 (antiderivative ρ 4) (1 - 4 * delta) / (delta : ℂ) ^ 4
  else upperKernel delta ρ

theorem coefficient_eq (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    coefficient lower x ρ = (x : ℂ) ^ ρ * normalizedKernel lower ρ := by
  cases lower with
  | false => simpa [coefficient, normalizedKernel] using zeroCoefficient_upper hx delta_pos ρ
  | true => simpa [coefficient, normalizedKernel] using
      zeroCoefficient_lower hx delta_pos four_mul_delta_lt_one ρ

theorem norm_coefficient_eq (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖coefficient lower x ρ‖ = x ^ ρ.re * ‖normalizedKernel lower ρ‖ := by
  rw [coefficient_eq lower hx, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]

theorem rising_conj (ρ : ℂ) (n : ℕ) : rising (conj ρ) n = conj (rising ρ n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rising, ih]

theorem antiderivative_conj {t : ℝ} (ht : 0 < t) (ρ : ℂ) (n : ℕ) :
    antiderivative (conj ρ) n t = conj (antiderivative ρ n t) := by
  have harg : (t : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ht.le]
    exact ne_of_lt Real.pi_pos
  have hp : (t : ℂ) ^ (conj ρ + n) = conj ((t : ℂ) ^ (ρ + n)) := by
    simpa using Complex.cpow_conj (t : ℂ) (ρ + n) harg
  simp only [antiderivative, rising_conj, hp]
  simp

theorem fourth_difference_conj {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) (ρ : ℂ) :
    forwardDiff h 4 (antiderivative (conj ρ) 4) t =
      conj (forwardDiff h 4 (antiderivative ρ 4) t) := by
  simp only [forwardDiff_four]
  rw [antiderivative_conj (by linarith : 0 < t + 4 * h),
    antiderivative_conj (by linarith : 0 < t + 3 * h),
    antiderivative_conj (by linarith : 0 < t + 2 * h),
    antiderivative_conj (by linarith : 0 < t + h), antiderivative_conj ht]
  have h4 : conj (4 : ℂ) = 4 := map_natCast (starRingEnd ℂ) 4
  have h6 : conj (6 : ℂ) = 6 := map_natCast (starRingEnd ℂ) 6
  simp [h4, h6]

theorem zeroCoefficient_conj {t h : ℝ} (ht : 0 < t) (hh : 0 ≤ h) (ρ : ℂ) :
    zeroCoefficient t h (conj ρ) = conj (zeroCoefficient t h ρ) := by
  simp only [zeroCoefficient, fourth_difference_conj ht hh]
  simp

theorem coefficient_conj (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    coefficient lower x (conj ρ) = conj (coefficient lower x ρ) := by
  unfold coefficient
  apply zeroCoefficient_conj
  · split_ifs
    · have hp := mul_pos hx (sub_pos.mpr four_mul_delta_lt_one)
      nlinarith
    · exact hx
  · exact mul_nonneg delta_pos.le hx.le

theorem norm_coefficient_conj (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖coefficient lower x (conj ρ)‖ = ‖coefficient lower x ρ‖ := by
  rw [coefficient_conj lower hx]
  simp

theorem norm_normalizedKernel_le_low (lower : Bool) {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖normalizedKernel lower ρ‖ ≤ (1 + 2 * delta) / ‖ρ‖ := by
  have hn : ρ ≠ 0 := by intro h; simp [h] at hre
  cases lower with
  | false =>
      exact norm_upperKernel_le_low delta_pos (by rw [hre]; norm_num)
        (by rw [hre]; norm_num)
  | true =>
      exact norm_lower_difference_le_low_common delta_pos four_mul_delta_lt_one
        (by rw [hre]; norm_num) hn

theorem norm_coefficient_le_low (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * (1 + 2 * delta) / ‖ρ‖ := by
  rw [norm_coefficient_eq lower hx, hre, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt x * ‖normalizedKernel lower ρ‖ ≤
        Real.sqrt x * ((1 + 2 * delta) / ‖ρ‖) :=
      mul_le_mul_of_nonneg_left (norm_normalizedKernel_le_low lower hre) (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem norm_normalizedKernel_le_high (lower : Bool) {ρ : ℂ}
    (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1) :
    ‖normalizedKernel lower ρ‖ ≤ R4 delta / (delta ^ 4 * ‖rising ρ 4‖) := by
  cases lower with
  | false => exact norm_upperKernel_le_high delta_pos hre1
  | true => exact norm_lower_difference_le_high_common delta_pos four_mul_delta_lt_one hre0

theorem norm_coefficient_le_high (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1) (him : ρ.im ≠ 0) :
    ‖coefficient lower x ρ‖ ≤ x ^ ρ.re * (R4 delta / delta ^ 4) / |ρ.im| ^ 5 := by
  have hR : 0 ≤ R4 delta := by unfold R4; positivity
  have hk : ‖normalizedKernel lower ρ‖ ≤ R4 delta / (delta ^ 4 * |ρ.im| ^ 5) := by
    apply (norm_normalizedKernel_le_high lower hre0 hre1).trans
    exact div_le_div_of_nonneg_left hR
      (mul_pos (pow_pos delta_pos 4) (pow_pos (abs_pos.mpr him) 5))
      (mul_le_mul_of_nonneg_left
        (PolynomialLeftKernel.abs_im_pow_le_norm_rising_four ρ) (by positivity))
  rw [norm_coefficient_eq lower hx]
  calc
    x ^ ρ.re * ‖normalizedKernel lower ρ‖ ≤
        x ^ ρ.re * (R4 delta / (delta ^ 4 * |ρ.im| ^ 5)) :=
      mul_le_mul_of_nonneg_left hk (Real.rpow_nonneg hx.le _)
    _ = _ := by ring

theorem norm_coefficient_le_high_line (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * (R4 delta / delta ^ 4) / |ρ.im| ^ 5 := by
  have h := norm_coefficient_le_high lower hx
    (by rw [hre]; norm_num) (by rw [hre]; norm_num) him
  rwa [hre, ← Real.sqrt_eq_rpow] at h

theorem norm_normalizedKernel_le_band_pos (lower : Bool) {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (hlo : 4 / (3 * delta) ≤ ρ.im) (hhi : ρ.im ≤ 2 * (1 - 4 * delta) / delta) :
    ‖normalizedKernel lower ρ‖ ≤ 0.931 / ρ.im := by
  cases lower with
  | false => exact norm_upperKernel_le_band_rs75 hre hlo hhi
  | true => exact norm_lower_difference_le_band_rs75 hre hlo hhi

theorem norm_coefficient_le_band_pos (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (hlo : 4 / (3 * delta) ≤ ρ.im) (hhi : ρ.im ≤ 2 * (1 - 4 * delta) / delta) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * 0.931 / ρ.im := by
  rw [norm_coefficient_eq lower hx, hre, ← Real.sqrt_eq_rpow]
  calc
    Real.sqrt x * ‖normalizedKernel lower ρ‖ ≤ Real.sqrt x * (0.931 / ρ.im) :=
      mul_le_mul_of_nonneg_left (norm_normalizedKernel_le_band_pos lower hre hlo hhi)
        (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- The common cancellation band, valid for either ordinate sign and either smoothing. -/
theorem norm_coefficient_le_band (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (hlo : 4 / (3 * delta) ≤ |ρ.im|)
    (hhi : |ρ.im| ≤ 2 * (1 - 4 * delta) / delta) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * 0.931 / |ρ.im| := by
  by_cases him : 0 ≤ ρ.im
  · rw [abs_of_nonneg him] at hlo hhi ⊢
    exact norm_coefficient_le_band_pos lower hx hre hlo hhi
  · have habs : |ρ.im| = (conj ρ).im := by
      simp only [Complex.conj_im]
      exact abs_of_neg (lt_of_not_ge him)
    have h := norm_coefficient_le_band_pos lower hx
      (by simpa using hre : (conj ρ).re = 1 / 2)
      (by rwa [← habs]) (by rwa [← habs])
    rw [norm_coefficient_conj lower hx] at h
    simpa only [← habs] using h

end TernaryGoldbach.RSBounds.PolynomialZeroMajorants
