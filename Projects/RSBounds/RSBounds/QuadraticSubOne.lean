import RSBounds.QuadraticContourLimit

/-!
# The pole contribution for degree-two kernels

This applies the degree-two contour passage to `s - 1`. All heights at
least one are good for this elementary function; the arbitrary supplied
height sequence may therefore also be used for the zeta formula.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.QuadraticSubOne

open TernaryGoldbach.Explicit PolynomialExplicit QuadraticContourLimit

/-- A constant horizontal envelope for the elementary pole factor.
It is used only in `GoodHeights`, not asserted to be a global `LDatum`. -/
noncomputable def poleB (_ : ℝ) : ℝ := 0.355 * Real.exp 1

theorem HkD_poleB_ge_one (k : ℕ) : 1 ≤ HkD poleB k := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h106 : 0 < Real.log (10 / 6 : ℝ) := Real.log_pos (by norm_num)
  have he : poleB ((k : ℝ) + 1) / 0.355 = Real.exp 1 := by
    unfold poleB
    ring
  rw [HkD, he, Real.log_exp]
  have h : 0 ≤ (2 * (2 * 1 / Real.log (10 / 6)) + 2) / Real.log 2 := by positivity
  linarith

theorem tendsto_HkD_poleB_div_sq :
    Tendsto (fun k : ℕ => HkD poleB (k + 1) / ((k : ℝ) + 1) ^ 2)
      atTop (𝓝 0) := by
  have h := (tendsto_const_div_pow (HkD poleB 0) 2 (by norm_num)).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, HkD, poleB] using h

theorem norm_logDeriv_sub_one_horizontal {S : ℝ} (hS : 1 ≤ |S|) (σ : ℝ) :
    ((σ : ℂ) + (S : ℂ) * I - 1 ≠ 0) ∧
      ‖logDeriv (fun s : ℂ => s - 1) ((σ : ℂ) + (S : ℂ) * I)‖ ≤ 1 := by
  have hnorm : 1 ≤ ‖(σ : ℂ) + (S : ℂ) * I - 1‖ := by
    have h := Complex.abs_im_le_norm ((σ : ℂ) + (S : ℂ) * I - 1)
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one,
      I_re, mul_zero, add_zero, zero_add, one_im, sub_zero] at h
    exact hS.trans h
  have hn : (σ : ℂ) + (S : ℂ) * I - 1 ≠ 0 := norm_pos_iff.mp (by linarith)
  refine ⟨hn, ?_⟩
  rw [logDeriv_sub_one, norm_div, norm_one]
  exact (div_le_one (norm_pos_iff.mpr hn)).mpr hnorm

theorem goodHeights_sub_one {T : ℕ → ℝ}
    (hT : ∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :
    GoodHeights (fun s : ℂ => s - 1) poleB T := by
  refine ⟨hT, ?_⟩
  intro k σ hσ
  have ht : 1 ≤ T k := by linarith [(hT k).1, (Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hp := norm_logDeriv_sub_one_horizontal
    (show 1 ≤ |T k| by simpa [abs_of_nonneg (by linarith : 0 ≤ T k)] using ht) σ
  have hm := norm_logDeriv_sub_one_horizontal
    (show 1 ≤ |-T k| by simpa [abs_neg, abs_of_nonneg (by linarith : 0 ≤ T k)] using ht) σ
  exact ⟨⟨hp.1, hm.1⟩, hp.2.trans (HkD_poleB_ge_one _),
    hm.2.trans (HkD_poleB_ge_one _)⟩

theorem integrable_sub_one_contour_left {M : ℂ → ℂ} {K : ℝ}
    (hM : DecayTwo M K) {x : ℝ} (hx : 0 < x) :
    Integrable (fun t : ℝ => contourIntegrand (fun s : ℂ => s - 1) M x
      (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
  have hcont : Continuous (fun t : ℝ => contourIntegrand (fun s : ℂ => s - 1) M x
      (((-1 / 2 : ℝ) : ℂ) + t * I)) := by
    unfold contourIntegrand
    refine (continuous_logDeriv_lineD ldatum_sub_one (-1 / 2) (fun t =>
      ldatum_sub_one.nz_strip _ (by simp; norm_num) (by simp; norm_num))).mul
      ((hM.continuous_line (-1 / 2) (Or.inl rfl)).mul ?_)
    exact continuous_iff_continuousAt.2 fun t =>
      (continuousAt_const_cpow (Complex.ofReal_ne_zero.2 hx.ne')).comp (by fun_prop)
  refine (((hM.integrable_line (Or.inl rfl)).norm).const_mul
    (x ^ (-1 / 2 : ℝ))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  have hbound : ‖logDeriv (fun s : ℂ => s - 1)
      (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ 1 := by
    have hnorm : 1 ≤ ‖((-1 / 2 : ℝ) : ℂ) + t * I - 1‖ := by
      have h := Complex.abs_re_le_norm (((-1 / 2 : ℝ) : ℂ) + t * I - 1)
      norm_num at h ⊢
      linarith
    rw [logDeriv_sub_one, norm_div, norm_one]
    exact (div_le_one (by linarith : 0 < ‖((-1 / 2 : ℝ) : ℂ) + t * I - 1‖)).mpr hnorm
  rw [contourIntegrand, norm_mul, norm_mul, norm_cpow_x hx]
  have hre : (((-1 / 2 : ℝ) : ℂ) + t * I).re = -1 / 2 := by simp
  rw [hre]
  calc
    ‖logDeriv (fun s : ℂ => s - 1) (((-1 / 2 : ℝ) : ℂ) + t * I)‖ *
        (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ))
      ≤ 1 * (‖M (((-1 / 2 : ℝ) : ℂ) + t * I)‖ * x ^ (-1 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

/-- The main-pole term, with the zero-pole correction of `H(s)/s` explicit.
The supplied heights may be the same sequence used for actual zeta. -/
theorem explicit_formula_sub_one_pole_zero_at_heights {H : ℂ → ℂ} {K : ℝ}
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    (hM : DecayTwo (fun s => H s / s) K) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : ∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) :
    Tendsto (fun k => ∑ u ∈ zerosRectD (fun s : ℂ => s - 1) (T k),
      (multRectD (fun s : ℂ => s - 1) (T k) u : ℂ) * (H u / u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (fun s => H s / s) x
          (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (fun s => H s / s) x
            (((-1 / 2 : ℝ) : ℂ) + y * I)) -
          logDeriv (fun s : ℂ => s - 1) 0 * H 0)) :=
  QuadraticContourLimit.contour_limit_of_residue_formula_at_heights hM hx
    (goodHeights_sub_one hT)
    (QuadraticContourLimit.integrable_contour_right ldatum_sub_one hM hx)
    (integrable_sub_one_contour_left hM hx) tendsto_HkD_poleB_div_sq
    (logDeriv (fun s : ℂ => s - 1) 0 * H 0)
    (fun _ hpos hbot htop => rect_identity_pole_zero ldatum_sub_one
      (by norm_num) hH hx hpos hbot htop)

/-- Evaluated main-pole contour identity, with no height sequence in its API. -/
theorem sub_one_contour_difference {H : ℂ → ℂ} {K : ℝ}
    (hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ H s)
    (hM : DecayTwo (fun s => H s / s) K) {x : ℝ} (hx : 0 < x) :
    H 1 * (x : ℂ) = (1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (fun s => H s / s) x
          (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (fun s => H s / s) x
            (((-1 / 2 : ℝ) : ℂ) + y * I)) -
          logDeriv (fun s : ℂ => s - 1) 0 * H 0 := by
  have h := explicit_formula_sub_one_pole_zero_at_heights hH hM hx
    (T := fun k => (k : ℝ) + 1) (by intro k; constructor <;> linarith)
  have heq (k : ℕ) :
      (∑ u ∈ zerosRectD (fun s : ℂ => s - 1) ((k : ℝ) + 1),
        (multRectD (fun s : ℂ => s - 1) ((k : ℝ) + 1) u : ℂ) *
          (H u / u * (x : ℂ) ^ u)) = H 1 * (x : ℂ) := by
    rw [sum_zerosRect_sub_one (by positivity), div_one, Complex.cpow_one]
  simp_rw [heq] at h
  exact tendsto_nhds_unique tendsto_const_nhds h

end TernaryGoldbach.RSBounds.QuadraticSubOne
