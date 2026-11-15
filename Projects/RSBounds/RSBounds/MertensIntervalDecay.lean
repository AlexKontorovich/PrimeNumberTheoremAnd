import RSBounds.MertensIntervalKernel
import RSBounds.QuadraticContourLimit

/-! Quadratic vertical decay of the cancelled finite-interval kernel. -/

open Complex Set

namespace TernaryGoldbach.RSBounds.MertensIntervalKernel

open QuadraticContourLimit

noncomputable def numeratorBound (a b : ℝ) : ℝ :=
  a ^ (-3 / 2 : ℝ) + a ^ (1 / 2 : ℝ) + b ^ (-3 / 2 : ℝ) + b ^ (1 / 2 : ℝ)

theorem numeratorBound_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    0 ≤ numeratorBound a b := by
  unfold numeratorBound
  positivity

private theorem rpow_le_endpoints {c r : ℝ} (hc : 0 < c)
    (hl : -3 / 2 ≤ r) (hr : r ≤ 1 / 2) :
    c ^ r ≤ c ^ (-3 / 2 : ℝ) + c ^ (1 / 2 : ℝ) := by
  by_cases hc1 : 1 ≤ c
  · exact (Real.rpow_le_rpow_of_exponent_le hc1 hr).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hc.le _))
  · exact (Real.rpow_le_rpow_of_exponent_ge hc (le_of_not_ge hc1) hl).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg hc.le _))

theorem norm_numerator_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hl : -1 / 2 ≤ s.re) (hr : s.re ≤ 3 / 2) :
    ‖numerator a b s‖ ≤ numeratorBound a b := by
  have hla : -3 / 2 ≤ s.re - 1 := by linarith
  have hra : s.re - 1 ≤ 1 / 2 := by linarith
  calc
    ‖numerator a b s‖ ≤ ‖(b : ℂ) ^ (s - 1)‖ + ‖(a : ℂ) ^ (s - 1)‖ :=
      norm_sub_le _ _
    _ = b ^ (s.re - 1) + a ^ (s.re - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hb, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      simp only [sub_re, one_re]
    _ ≤ numeratorBound a b := by
      unfold numeratorBound
      linarith [rpow_le_endpoints ha hla hra, rpow_le_endpoints hb hla hra]

theorem norm_kernel_le_im {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {s : ℂ} (hl : -1 / 2 ≤ s.re) (hr : s.re ≤ 3 / 2) (hi : 0 < |s.im|) :
    ‖kernel a b s‖ ≤ numeratorBound a b / |s.im| ^ 2 := by
  have hn := numeratorBound_nonneg ha hb
  have hs1 : s ≠ 1 := by intro h; simp [h] at hi
  have hns : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
  have hns1 : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
  rw [kernel_eq hs1, norm_div, norm_mul]
  calc
    ‖numerator a b s‖ / (‖s‖ * ‖s - 1‖) ≤
        numeratorBound a b / (‖s‖ * ‖s - 1‖) := by
      gcongr
      exact norm_numerator_le ha hb hl hr
    _ ≤ numeratorBound a b / (|s.im| * |s.im|) := by
      gcongr
    _ = numeratorBound a b / |s.im| ^ 2 := by rw [pow_two]

theorem continuous_kernel_line {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) :
    Continuous (fun t : ℝ => kernel a b ((σ : ℂ) + t * I)) := by
  have hn (t : ℝ) : (σ : ℂ) + t * I ≠ 0 := by
    intro h
    have h0 := congrArg Complex.re h
    simp at h0
    rcases hσ with hσ | hσ <;> linarith
  exact ((differentiable_H ha hb).continuous.comp (by fun_prop)).div
    (by fun_prop) hn

theorem norm_kernel_line_le {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {σ : ℝ} (hσ : σ = -1 / 2 ∨ σ = 3 / 2) (t : ℝ) :
    ‖kernel a b ((σ : ℂ) + t * I)‖ ≤
      (16 * numeratorBound a b) / (1 + |t|) ^ 2 := by
  have hn := numeratorBound_nonneg ha hb
  let s : ℂ := (σ : ℂ) + t * I
  have hre : s.re = σ := by simp [s]
  have him : s.im = t := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have h0 := congrArg Complex.re h
    rw [hre] at h0
    rcases hσ with hσ | hσ <;> norm_num [hσ] at h0
  have hnorm : (1 + |t|) / 4 ≤ ‖s‖ := by
    have hr := Complex.abs_re_le_norm s
    have hi := Complex.abs_im_le_norm s
    rw [hre] at hr
    rw [him] at hi
    rcases hσ with hσ | hσ <;> norm_num [hσ] at hr <;> linarith
  have hnorm1 : (1 + |t|) / 4 ≤ ‖s - 1‖ := by
    have hr := Complex.abs_re_le_norm (s - 1)
    have hi := Complex.abs_im_le_norm (s - 1)
    simp only [sub_re, one_re, hre] at hr
    simp only [sub_im, one_im, sub_zero, him] at hi
    rcases hσ with hσ | hσ <;> norm_num [hσ] at hr <;> linarith
  have hl : -1 / 2 ≤ s.re := by rw [hre]; rcases hσ with hσ | hσ <;> norm_num [hσ]
  have hu : s.re ≤ 3 / 2 := by rw [hre]; rcases hσ with hσ | hσ <;> norm_num [hσ]
  have ht : 0 < (1 + |t|) / 4 := by positivity
  change ‖kernel a b s‖ ≤ _
  rw [kernel_eq hs1, norm_div, norm_mul]
  calc
    ‖numerator a b s‖ / (‖s‖ * ‖s - 1‖) ≤
        numeratorBound a b / (‖s‖ * ‖s - 1‖) := by
      gcongr
      exact norm_numerator_le ha hb hl hu
    _ ≤ numeratorBound a b / (((1 + |t|) / 4) * ((1 + |t|) / 4)) := by
      gcongr
    _ = (16 * numeratorBound a b) / (1 + |t|) ^ 2 := by
      field_simp
      <;> ring

/-- The actual finite-interval kernel meets every quadratic contour hypothesis. -/
theorem decayTwo_kernel {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    DecayTwo (kernel a b) (16 * numeratorBound a b) := by
  have hn := numeratorBound_nonneg ha hb
  refine ⟨by positivity, fun σ hσ => continuous_kernel_line ha hb hσ,
    fun σ hσ t => norm_kernel_line_le ha hb hσ t, ?_⟩
  intro s hl hr hi
  have hi0 : 0 < |s.im| := by linarith
  exact (norm_kernel_le_im ha hb hl hr hi0).trans
    (div_le_div_of_nonneg_right (by linarith) (sq_nonneg _))

end TernaryGoldbach.RSBounds.MertensIntervalKernel
