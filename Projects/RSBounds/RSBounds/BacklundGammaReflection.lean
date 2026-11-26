import RSBounds.IEANTNDigammaDifference
import RSBounds.BacklundReflection
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A quantitative gamma bound for Backlund reflection

The high-ordinate estimate reuses IEANTN's checked same-height digamma
difference bound. Two applications of the recurrence move the reflected
arguments to real part at least one; a telescoping majorant handles small
positive ordinates.

For `T ≥ 1` and `1/2 ≤ σ ≤ 5/4`, the digamma difference is at most
`16 * (σ - 1/2) / T`. The exact reflected zeta identity contributes a factor
`1/2`, yielding integrated error at most `4 * δ^2 / T < 8 / T` for
`0 ≤ δ ≤ 3/4`. The zeta statements assume nonvanishing only at the points
of the two horizontal segments. Integrability is proved independently.
-/

open Complex Filter Set MeasureTheory
open scoped Real Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaReflection

theorem norm_digamma_sub_le_of_one_le_re {z₁ z₂ : ℂ}
    (h1 : 1 ≤ z₁.re) (h2 : 1 ≤ z₂.re) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ := by
  have hn1 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₁.re))
  have hn2 := GammaSolution.ne_neg_natCast_of_mem
    (GammaSolution.mem_rightHalfPlane_iff.mpr (by linarith : 0 < z₂.re))
  have hs1 := GammaSolution.summable_gaussTerm hn1
  have hs2 := GammaSolution.summable_gaussTerm hn2
  have hdiff : Complex.digamma z₁ - Complex.digamma z₂ =
      ∑' k, (GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k) := by
    rw [GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.digamma_eq_gaussSum (by linarith),
      GammaSolution.gaussSum, GammaSolution.gaussSum, hs1.tsum_sub hs2]
    ring
  have hk : ∀ k : ℕ, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ ≤
      ‖z₁ - z₂‖ * (2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < k + 1 := by positivity
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
    have he : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k =
        (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]
      field_simp
      ring
    have hnz1 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₁‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₁)
      simp only [add_re, natCast_re] at hh
      linarith
    have hnz2 : (k : ℝ) + 1 ≤ ‖(k : ℂ) + z₂‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₂)
      simp only [add_re, natCast_re] at hh
      linarith
    have hp : ((k : ℝ) + 1) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
    have hc : 1 / ((k : ℝ) + 1) ^ 2 ≤
        2 * (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))⁻¹ := by
      change 1 / ((k : ℝ) + 1) ^ 2 ≤
        2 / (((k : ℝ) + 1) * ((k : ℝ) + 1 + 1))
      rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
      nlinarith
    rw [he, norm_div]
    calc
      _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + 1) ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
      _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + 1) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have htele := GammaSolution.hasSum_comparison (t := 1) le_rfl ‖z₁ - z₂‖
  have hsumn : Summable (fun k : ℕ =>
      ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc
    _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
      norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * (2 * (1 : ℝ)⁻¹) := by
      rw [← htele.tsum_eq]
      exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ = _ := by ring

theorem digamma_eq_add_two_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) :
    Complex.digamma z = Complex.digamma (z + 2) - z⁻¹ - (z + 1)⁻¹ := by
  have hn : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m he
    have hh := congrArg Complex.im he
    simp only [neg_im, natCast_im, neg_zero] at hh
    exact hz hh
  have hn1 : ∀ m : ℕ, z + 1 ≠ -(m : ℂ) := by
    intro m he
    have hh := congrArg Complex.im he
    simp only [add_im, one_im, add_zero, neg_im, natCast_im, neg_zero] at hh
    exact hz hh
  have h1 := Complex.digamma_apply_add_one z hn
  have h2 := Complex.digamma_apply_add_one (z + 1) hn1
  rw [show z + 2 = z + 1 + 1 by ring, h2, h1]
  ring

noncomputable def reflectedArg (σ T : ℝ) : ℂ := ((1 - σ : ℝ) + T * I) / 2
noncomputable def directArg (σ T : ℝ) : ℂ := ((σ : ℝ) + T * I) / 2

theorem reflectedArg_im (σ T : ℝ) : (reflectedArg σ T).im = T / 2 := by
  simp [reflectedArg, div_ofNat_im]

theorem directArg_im (σ T : ℝ) : (directArg σ T).im = T / 2 := by
  simp [directArg, div_ofNat_im]

theorem norm_arg_difference {σ T : ℝ} (hσ : 1 / 2 ≤ σ) :
    ‖reflectedArg σ T - directArg σ T‖ = σ - 1 / 2 := by
  have he : reflectedArg σ T - directArg σ T = ((1 / 2 - σ : ℝ) : ℂ) := by
    unfold reflectedArg directArg
    push_cast
    ring
  rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  ring

theorem norm_inverse_difference {z₁ z₂ : ℂ} {b : ℝ}
    (hb : 0 < b) (h1 : z₁.im = b) (h2 : z₂.im = b) :
    ‖z₁⁻¹ - z₂⁻¹‖ ≤ ‖z₁ - z₂‖ / b ^ 2 := by
  have hn1 : b ≤ ‖z₁‖ := by
    simpa only [h1, abs_of_pos hb] using Complex.abs_im_le_norm z₁
  have hn2 : b ≤ ‖z₂‖ := by
    simpa only [h2, abs_of_pos hb] using Complex.abs_im_le_norm z₂
  have hz1 : z₁ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn1)
  have hz2 : z₂ ≠ 0 := norm_pos_iff.mp (hb.trans_le hn2)
  have he : z₁⁻¹ - z₂⁻¹ = (z₂ - z₁) / (z₁ * z₂) := by field_simp
  rw [he, norm_div, norm_sub_rev, norm_mul]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hb)
    (by rw [pow_two]; exact mul_le_mul hn1 hn2 hb.le (norm_nonneg _))

theorem norm_digamma_reflection_le {σ T : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
    ‖Complex.digamma (reflectedArg σ T) - Complex.digamma (directArg σ T)‖ ≤
      16 * (σ - 1 / 2) / T := by
  have hT0 : 0 < T := by linarith
  have hb : 0 < T / 2 := by positivity
  have hσ : 0 ≤ σ - 1 / 2 := by linarith
  have h1re : 1 ≤ (reflectedArg σ T + 2).re := by
    simp [reflectedArg, div_ofNat_re]
    linarith
  have h2re : 1 ≤ (directArg σ T + 2).re := by
    simp [directArg, div_ofNat_re]
    linarith
  have hnorm : ‖(reflectedArg σ T + 2) - (directArg σ T + 2)‖ = σ - 1 / 2 := by
    rw [add_sub_add_right_eq_sub, norm_arg_difference hσ0]
  have hshift : ‖Complex.digamma (reflectedArg σ T + 2) -
      Complex.digamma (directArg σ T + 2)‖ ≤ 8 * (σ - 1 / 2) / T := by
    by_cases hT4 : T ≤ 4
    · have hh := norm_digamma_sub_le_of_one_le_re h1re h2re
      rw [hnorm] at hh
      refine hh.trans ?_
      rw [le_div_iff₀ hT0]
      nlinarith
    · have hh := CH2Section81.norm_digamma_sub_le
        (show 0 < (reflectedArg σ T + 2).re by linarith)
        (show 0 < (directArg σ T + 2).re by linarith)
        (by simp [reflectedArg_im, directArg_im])
        (by simp [reflectedArg_im]; linarith : 2 ≤ (reflectedArg σ T + 2).im)
      rw [hnorm] at hh
      norm_num [reflectedArg_im] at hh
      convert hh using 1; ring
  have hrec0 := norm_inverse_difference hb (reflectedArg_im σ T) (directArg_im σ T)
  rw [norm_arg_difference hσ0] at hrec0
  have hrec1 := norm_inverse_difference hb
    (show (reflectedArg σ T + 1).im = T / 2 by simp [reflectedArg_im])
    (show (directArg σ T + 1).im = T / 2 by simp [directArg_im])
  rw [add_sub_add_right_eq_sub, norm_arg_difference hσ0] at hrec1
  rw [digamma_eq_add_two_of_im_ne_zero (z := reflectedArg σ T) (by rw [reflectedArg_im]; exact hb.ne'),
    digamma_eq_add_two_of_im_ne_zero (z := directArg σ T) (by rw [directArg_im]; exact hb.ne')]
  have he : (Complex.digamma (reflectedArg σ T + 2) - (reflectedArg σ T)⁻¹ -
      (reflectedArg σ T + 1)⁻¹) - (Complex.digamma (directArg σ T + 2) -
      (directArg σ T)⁻¹ - (directArg σ T + 1)⁻¹) =
      (Complex.digamma (reflectedArg σ T + 2) - Complex.digamma (directArg σ T + 2)) -
      ((reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹) -
      ((reflectedArg σ T + 1)⁻¹ - (directArg σ T + 1)⁻¹) := by ring
  rw [he]
  refine (norm_sub_le _ _).trans ?_
  have htri := norm_sub_le (Complex.digamma (reflectedArg σ T + 2) -
    Complex.digamma (directArg σ T + 2)) ((reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹)
  have hsmall : 2 * ((σ - 1 / 2) / (T / 2) ^ 2) ≤ 8 * (σ - 1 / 2) / T := by
    field_simp
    nlinarith
  calc
    _ ≤ (‖Complex.digamma (reflectedArg σ T + 2) -
      Complex.digamma (directArg σ T + 2)‖ +
      ‖(reflectedArg σ T)⁻¹ - (directArg σ T)⁻¹‖) +
      ‖(reflectedArg σ T + 1)⁻¹ - (directArg σ T + 1)⁻¹‖ :=
        add_le_add htri le_rfl
    _ ≤ (8 * (σ - 1 / 2) / T + (σ - 1 / 2) / (T / 2) ^ 2) +
      (σ - 1 / 2) / (T / 2) ^ 2 := add_le_add (add_le_add hshift hrec0) hrec1
    _ = 8 * (σ - 1 / 2) / T + 2 * ((σ - 1 / 2) / (T / 2) ^ 2) := by ring
    _ ≤ 8 * (σ - 1 / 2) / T + 8 * (σ - 1 / 2) / T := add_le_add le_rfl hsmall
    _ = _ := by ring

/-- The real gamma correction appearing in the zeta reflection formula. -/
noncomputable def gammaReflectionDifference (σ T : ℝ) : ℝ :=
  (1 / 2) * (Complex.digamma (reflectedArg σ T) -
    Complex.digamma (directArg σ T)).im

/-- The actual difference of imaginary logarithmic derivatives of zeta. -/
noncomputable def zetaReflectionDifference (σ T : ℝ) : ℝ :=
  (logDeriv riemannZeta ((σ : ℂ) + T * I)).im -
    (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * I)).im

theorem zetaReflectionDifference_eq_gamma {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    zetaReflectionDifference σ T = gammaReflectionDifference σ T :=
  BacklundReflection.im_logDeriv_zeta_reflect_digamma hT σ hζ hζ'

theorem abs_gammaReflectionDifference_le {σ T : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4) :
    |gammaReflectionDifference σ T| ≤ 8 * (σ - 1 / 2) / T := by
  unfold gammaReflectionDifference
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  calc
    _ ≤ (1 / 2) * ‖Complex.digamma (reflectedArg σ T) -
        Complex.digamma (directArg σ T)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (by norm_num)
    _ ≤ (1 / 2) * (16 * (σ - 1 / 2) / T) :=
      mul_le_mul_of_nonneg_left (norm_digamma_reflection_le hT hσ0 hσ1) (by norm_num)
    _ = _ := by ring

theorem abs_zetaReflectionDifference_le {σ T : ℝ}
    (hT : 1 ≤ T) (hσ0 : 1 / 2 ≤ σ) (hσ1 : σ ≤ 5 / 4)
    (hζ : riemannZeta ((σ : ℂ) + T * I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    |zetaReflectionDifference σ T| ≤ 8 * (σ - 1 / 2) / T := by
  rw [zetaReflectionDifference_eq_gamma (by linarith) σ hζ hζ']
  exact abs_gammaReflectionDifference_le hT hσ0 hσ1

private theorem continuousAt_digamma_comp_of_add_two {f : ℝ → ℂ} {a : ℝ}
    (hf : ContinuousAt f a) (hfim : ∀ t, (f t).im ≠ 0)
    (hfre : 0 < (f a + 2).re) : ContinuousAt (fun t => Complex.digamma (f t)) a := by
  have hg : ContinuousAt (fun t => Complex.digamma (f t + 2)) a :=
    (GammaSolution.analyticOnNhd_digamma _
      (GammaSolution.mem_rightHalfPlane_iff.mpr hfre)).continuousAt.comp
      (f := fun t => f t + 2) (hf.add continuousAt_const)
  have h0 : f a ≠ 0 := fun h => hfim a (by rw [h]; rfl)
  have h1 : f a + 1 ≠ 0 := by
    intro h
    apply hfim a
    simpa using congrArg Complex.im h
  have he : (fun t => Complex.digamma (f t)) =
      fun t => Complex.digamma (f t + 2) - (f t)⁻¹ - (f t + 1)⁻¹ := by
    funext t
    exact digamma_eq_add_two_of_im_ne_zero (hfim t)
  rw [he]
  exact (hg.sub (hf.inv₀ h0)).sub ((hf.add continuousAt_const).inv₀ h1)

theorem continuousOn_gammaReflectionDifference {T : ℝ} (hT : T ≠ 0) :
    ContinuousOn (fun σ => gammaReflectionDifference σ T) (Icc (1 / 2) (5 / 4)) := by
  intro σ hσ
  have hr : ContinuousAt (fun u => Complex.digamma (reflectedArg u T)) σ := by
    apply continuousAt_digamma_comp_of_add_two
    · unfold reflectedArg
      fun_prop
    · intro u
      rw [reflectedArg_im]
      exact div_ne_zero hT (by norm_num)
    · simp [reflectedArg, div_ofNat_re]
      linarith [hσ.2]
  have hd : ContinuousAt (fun u => Complex.digamma (directArg u T)) σ := by
    apply continuousAt_digamma_comp_of_add_two
    · unfold directArg
      fun_prop
    · intro u
      rw [directArg_im]
      exact div_ne_zero hT (by norm_num)
    · simp [directArg, div_ofNat_re]
      linarith [hσ.1]
  exact (continuousAt_const.mul (Complex.continuous_im.continuousAt.comp
    (hr.sub hd))).continuousWithinAt

theorem intervalIntegrable_gammaReflectionDifference {T δ : ℝ}
    (hT : T ≠ 0) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    IntervalIntegrable (fun σ => gammaReflectionDifference σ T) volume
      (1 / 2) (1 / 2 + δ) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)]
  exact (continuousOn_gammaReflectionDifference hT).mono
    (fun σ hσ => ⟨hσ.1, by linarith [hσ.2]⟩)

theorem integral_linear_majorant (T δ : ℝ) :
    (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), 8 * (σ - 1 / 2) / T) =
      4 * δ ^ 2 / T := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      (f := fun σ : ℝ => σ) (g := fun _ => (1 / 2 : ℝ))
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const]
  ring

theorem abs_integral_gammaReflectionDifference_le {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), gammaReflectionDifference σ T| ≤
      4 * δ ^ 2 / T := by
  rw [← Real.norm_eq_abs, ← integral_linear_majorant]
  apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
  · filter_upwards [] with σ hσ
    rw [Real.norm_eq_abs]
    exact abs_gammaReflectionDifference_le hT hσ.1.le (by linarith [hσ.2])
  · exact (show Continuous (fun σ : ℝ => 8 * (σ - 1 / 2) / T) by
      fun_prop).intervalIntegrable _ _

/-- Nonvanishing is assumed only on the two horizontal segments being integrated. -/
theorem intervalIntegrable_zetaReflectionDifference {T δ : ℝ}
    (hT : T ≠ 0) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hζ : ∀ σ ∈ Icc (1 / 2) (1 / 2 + δ),
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
      riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    IntervalIntegrable (fun σ => zetaReflectionDifference σ T) volume
      (1 / 2) (1 / 2 + δ) := by
  have he : EqOn (fun σ => zetaReflectionDifference σ T)
      (fun σ => gammaReflectionDifference σ T) (Ι (1 / 2) (1 / 2 + δ)) := by
    rw [uIoc_of_le (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)]
    intro σ hσ
    exact zetaReflectionDifference_eq_gamma hT σ
      (hζ σ ⟨hσ.1.le, hσ.2⟩).1 (hζ σ ⟨hσ.1.le, hσ.2⟩).2
  exact (intervalIntegrable_congr he).mpr
    (intervalIntegrable_gammaReflectionDifference hT hδ0 hδ1)

theorem abs_integral_zetaReflectionDifference_le {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hζ : ∀ σ ∈ Icc (1 / 2) (1 / 2 + δ),
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
      riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), zetaReflectionDifference σ T| ≤
      4 * δ ^ 2 / T := by
  have he : (∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), zetaReflectionDifference σ T) =
      ∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), gammaReflectionDifference σ T := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le (by linarith : (1 / 2 : ℝ) ≤ 1 / 2 + δ)]
    intro σ hσ
    exact zetaReflectionDifference_eq_gamma (by linarith) σ (hζ σ hσ).1 (hζ σ hσ).2
  rw [he]
  exact abs_integral_gammaReflectionDifference_le hT hδ0 hδ1

theorem abs_integral_zetaReflectionDifference_lt {T δ : ℝ}
    (hT : 1 ≤ T) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 3 / 4)
    (hζ : ∀ σ ∈ Icc (1 / 2) (1 / 2 + δ),
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
      riemannZeta (((1 - σ : ℝ) : ℂ) + T * I) ≠ 0) :
    |∫ σ in (1 / 2 : ℝ)..(1 / 2 + δ), zetaReflectionDifference σ T| < 8 / T := by
  refine (abs_integral_zetaReflectionDifference_le hT hδ0 hδ1 hζ).trans_lt ?_
  apply div_lt_div_of_pos_right _ (by linarith : 0 < T)
  nlinarith

end TernaryGoldbach.RSBounds.BacklundGammaReflection
