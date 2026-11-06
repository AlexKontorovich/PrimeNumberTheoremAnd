import RSBounds.BacklundRightArcNumerics
import RSBounds.BacklundAngularCoefficients
import RSBounds.BacklundCircleMajorantDef

/-!
# Integration of the actual piecewise circle majorant

All four sector formulas are proved from cosine monotonicity. Endpoint jumps
are handled by equality on open intervals, so no continuity across artificial
sector boundaries is assumed.
-/

open Real Set MeasureTheory
open TernaryGoldbach.RSBounds.BacklundRightArc
open TernaryGoldbach.RSBounds.BacklundAngularCoefficients
open TernaryGoldbach.RSBounds.BacklundCircleMajorant (scalar)

namespace TernaryGoldbach.RSBounds.BacklundAngularAssembly

noncomputable def sigma (θ : ℝ) : ℝ := 5 / 4 + radius * Real.cos θ
noncomputable def arc (H L V θ : ℝ) : ℝ := scalar H L V (sigma θ)

lemma half_pi_le_alpha : Real.pi / 2 ≤ alpha := by
  have h := Real.arccos_le_arccos (show -(25 / 132 : ℝ) ≤ 0 by norm_num)
  simpa only [Real.arccos_zero, alpha] using h

lemma alpha_le_beta : alpha ≤ beta :=
  Real.arccos_le_arccos (by norm_num : -(125 / 132 : ℝ) ≤ -(25 / 132))

lemma beta_le_pi : beta ≤ Real.pi := Real.arccos_le_pi _
lemma alpha_le_pi : alpha ≤ Real.pi := alpha_le_beta.trans beta_le_pi
lemma alpha_nonneg : 0 ≤ alpha := Real.arccos_nonneg _
lemma beta_nonneg : 0 ≤ beta := Real.arccos_nonneg _
lemma cos_alpha : Real.cos alpha = -(25 / 132 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)
lemma cos_beta : Real.cos beta = -(125 / 132 : ℝ) :=
  Real.cos_arccos (by norm_num) (by norm_num)

lemma sigma_gt_one {θ : ℝ} (h0 : 0 ≤ θ) (hα : θ < alpha) : 1 < sigma θ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 alpha_le_pi hα
  rw [cos_alpha] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_lt_one {θ : ℝ} (hπ : θ ≤ Real.pi) (hα : alpha < θ) : sigma θ < 1 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi alpha_nonneg hπ hα
  rw [cos_alpha] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_pos {θ : ℝ} (h0 : 0 ≤ θ) (hβ : θ < beta) : 0 < sigma θ := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi h0 beta_le_pi hβ
  rw [cos_beta] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_neg {θ : ℝ} (hπ : θ ≤ Real.pi) (hβ : beta < θ) : sigma θ < 0 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi beta_nonneg hπ hβ
  rw [cos_beta] at h
  dsimp [sigma, radius]
  linarith

lemma sigma_lt_five_fourths {θ : ℝ} (hπ : θ ≤ Real.pi) (hθ : Real.pi / 2 < θ) :
    sigma θ < 5 / 4 := by
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity : 0 ≤ Real.pi / 2) hπ hθ
  rw [Real.cos_pi_div_two] at h
  dsimp [sigma, radius]
  linarith

lemma sector_one (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    arc H L V θ = arcFunction θ := by
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2.le⟩
  have hs : 5 / 4 ≤ sigma θ := by dsimp [sigma, radius]; linarith
  simp only [arc, scalar, if_pos hs]
  rfl

lemma sector_two (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo (Real.pi / 2) alpha) :
    arc H L V θ = H := by
  have h0 : 0 ≤ θ := by linarith [Real.pi_pos, hθ.1]
  have hπ : θ ≤ Real.pi := hθ.2.le.trans alpha_le_pi
  have hs1 := sigma_gt_one h0 hθ.2
  have hs54 := sigma_lt_five_fourths hπ hθ.1
  have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.2]
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_right (by linarith : 1 - sigma θ ≤ 0),
    max_eq_right (by linarith : -sigma θ ≤ 0), if_neg hstrip,
    add_zero, zero_add, mul_zero]

lemma sector_three (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo alpha beta) :
    arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) + V := by
  have h0 : 0 ≤ θ := alpha_nonneg.trans hθ.1.le
  have hπ : θ ≤ Real.pi := hθ.2.le.trans beta_le_pi
  have hs0 := sigma_pos h0 hθ.2
  have hs1 := sigma_lt_one hπ hθ.1
  have hs54 : sigma θ < 5 / 4 := by linarith
  have hstrip : 0 ≤ sigma θ ∧ sigma θ < 1 := ⟨hs0.le, hs1⟩
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
    max_eq_right (by linarith : -sigma θ ≤ 0), if_pos hstrip, add_zero]
  dsimp [sigma]
  ring

lemma sector_four (H L V : ℝ) {θ : ℝ} (hθ : θ ∈ Ioo beta Real.pi) :
    arc H L V θ = H - L / 2 * (radius * Real.cos θ + 1 / 4) -
      L / 2 * (radius * Real.cos θ + 5 / 4) := by
  have hs0 := sigma_neg hθ.2.le hθ.1
  have hs54 : sigma θ < 5 / 4 := by linarith
  have hstrip : ¬(0 ≤ sigma θ ∧ sigma θ < 1) := by intro h; linarith [h.1]
  simp only [arc, scalar, if_neg (not_le.mpr hs54),
    max_eq_left (by linarith : 0 ≤ 1 - sigma θ),
    max_eq_left (by linarith : 0 ≤ -sigma θ), if_neg hstrip, add_zero]
  dsimp [sigma]
  ring

lemma sector_integrable (H L V : ℝ) :
    IntervalIntegrable (arc H L V) volume 0 (Real.pi / 2) ∧
    IntervalIntegrable (arc H L V) volume (Real.pi / 2) alpha ∧
    IntervalIntegrable (arc H L V) volume alpha beta ∧
    IntervalIntegrable (arc H L V) volume beta Real.pi := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (continuousOn_arcFunction.intervalIntegrable_of_Icc (by positivity)).congr_uIoo
    rw [uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2)]
    exact fun θ hθ => (sector_one H L V hθ).symm
  · apply (intervalIntegrable_const (c := H)).congr_uIoo
    rw [uIoo_of_le half_pi_le_alpha]
    exact fun θ hθ => (sector_two H L V hθ).symm
  · have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) + V) := by fun_prop
    apply (h.intervalIntegrable alpha beta).congr_uIoo
    rw [uIoo_of_le alpha_le_beta]
    exact fun θ hθ => (sector_three H L V hθ).symm
  · have h : Continuous (fun θ => H - L / 2 * (radius * Real.cos θ + 1 / 4) -
        L / 2 * (radius * Real.cos θ + 5 / 4)) := by fun_prop
    apply (h.intervalIntegrable beta Real.pi).congr_uIoo
    rw [uIoo_of_le beta_le_pi]
    exact fun θ hθ => (sector_four H L V hθ).symm

lemma intervalIntegrable_scalar_arc (H L V : ℝ) :
    IntervalIntegrable (arc H L V) volume 0 Real.pi := by
  obtain ⟨h1, h2, h3, h4⟩ := sector_integrable H L V
  exact ((h1.trans h2).trans h3).trans h4

lemma scalar_arc_integral_raw (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) =
      (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) + Real.pi / 2 * H -
      L / 2 * (∫ θ in alpha..Real.pi, (radius * Real.cos θ + 1 / 4)) -
      L / 2 * (∫ θ in beta..Real.pi, (radius * Real.cos θ + 5 / 4)) + (beta - alpha) * V := by
  obtain ⟨h1, h2, h3, h4⟩ := sector_integrable H L V
  have he1 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) (by positivity : (0 : ℝ) ≤ Real.pi / 2)
    (fun θ hθ => sector_one H L V hθ)
  have he2 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) half_pi_le_alpha
    (fun θ hθ => sector_two H L V hθ)
  have he3 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) alpha_le_beta
    (fun θ hθ => sector_three H L V hθ)
  have he4 := intervalIntegral.integral_congr_Ioo_of_le (μ := volume) beta_le_pi
    (fun θ hθ => sector_four H L V hθ)
  have hc1 : Continuous (fun θ => radius * Real.cos θ + 1 / 4) := by fun_prop
  have hc2 : Continuous (fun θ => radius * Real.cos θ + 5 / 4) := by fun_prop
  have hj := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (hc1.intervalIntegrable alpha beta)
    (hc1.intervalIntegrable beta Real.pi)
  rw [← intervalIntegral.integral_add_adjacent_intervals ((h1.trans h2).trans h3) h4,
    ← intervalIntegral.integral_add_adjacent_intervals (h1.trans h2) h3,
    ← intervalIntegral.integral_add_adjacent_intervals h1 h2,
    he1, he2, he3, he4]
  rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) intervalIntegrable_const,
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul, smul_eq_mul]
  rw [← hj]
  ring

/-- Exact upper-semicircle integral of the actual scalar majorant. -/
lemma scalar_arc_integral_eq (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) =
      ((∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi)) / q +
      slopeA * L + slopeB * H + (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [scalar_arc_integral_raw]
  convert angular_integrals_eq
    ((∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi)) L H V using 1 <;>
    field_simp [Real.pi_ne_zero, q_pos.ne'] <;> ring

/-- The actual majorant integral with the numerical right-arc estimate inserted. -/
lemma scalar_arc_integral_le (H L V : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, arc H L V θ) / (2 * Real.pi * q) ≤
      (0.1361 : ℝ) / q + slopeA * L + slopeB * H +
        (beta - alpha) * V / (2 * Real.pi * q) := by
  rw [scalar_arc_integral_eq]
  have h := div_le_div_of_nonneg_right right_arc_integral_lt.le q_pos.le
  linarith

end TernaryGoldbach.RSBounds.BacklundAngularAssembly
