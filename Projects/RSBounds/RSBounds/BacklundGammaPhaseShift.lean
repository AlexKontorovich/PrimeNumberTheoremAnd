import RSBounds.BacklundGammaPhaseBase

open Complex Filter Set MeasureTheory
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem norm_digamma_sub_le_of_re_ge {N : ℝ} (hN : 1 ≤ N) {z₁ z₂ : ℂ}
    (h1 : N ≤ z₁.re) (h2 : N ≤ z₂.re) :
    ‖Complex.digamma z₁ - Complex.digamma z₂‖ ≤ 2 * ‖z₁ - z₂‖ / N := by
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
      ‖z₁ - z₂‖ * (2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹) := by
    intro k
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hk1 : (0 : ℝ) < k + N := by linarith
    have hz1 : ((k : ℂ) + z₁) ≠ 0 := fun h => hn1 k (by linear_combination h)
    have hz2 : ((k : ℂ) + z₂) ≠ 0 := fun h => hn2 k (by linear_combination h)
    have he : GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k =
        (z₁ - z₂) / (((k : ℂ) + z₁) * ((k : ℂ) + z₂)) := by
      simp only [GammaSolution.gaussTerm]
      field_simp
      ring
    have hnz1 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₁‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₁)
      simp only [add_re, natCast_re] at hh
      linarith
    have hnz2 : (k : ℝ) + N ≤ ‖(k : ℂ) + z₂‖ := by
      have hh := Complex.re_le_norm ((k : ℂ) + z₂)
      simp only [add_re, natCast_re] at hh
      linarith
    have hp : ((k : ℝ) + N) ^ 2 ≤ ‖((k : ℂ) + z₁) * ((k : ℂ) + z₂)‖ := by
      rw [norm_mul, pow_two]
      exact mul_le_mul hnz1 hnz2 hk1.le (norm_nonneg _)
    have hc : 1 / ((k : ℝ) + N) ^ 2 ≤
        2 * (((k : ℝ) + N) * ((k : ℝ) + N + 1))⁻¹ := by
      change 1 / ((k : ℝ) + N) ^ 2 ≤
        2 / (((k : ℝ) + N) * ((k : ℝ) + N + 1))
      rw [div_le_div_iff₀ (sq_pos_of_pos hk1) (by positivity)]
      nlinarith
    rw [he, norm_div]
    calc
      _ ≤ ‖z₁ - z₂‖ / ((k : ℝ) + N) ^ 2 :=
        div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_pos hk1) hp
      _ = ‖z₁ - z₂‖ * (1 / ((k : ℝ) + N) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  have htele := GammaSolution.hasSum_comparison (t := N) hN ‖z₁ - z₂‖
  have hsumn : Summable (fun k : ℕ =>
      ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hk htele.summable
  rw [hdiff]
  calc
    _ ≤ ∑' k, ‖GammaSolution.gaussTerm z₁ k - GammaSolution.gaussTerm z₂ k‖ :=
      norm_tsum_le_tsum_norm hsumn
    _ ≤ ‖z₁ - z₂‖ * (2 * N⁻¹) := by
      rw [← htele.tsum_eq]
      exact Summable.tsum_le_tsum hk hsumn htele.summable
    _ = _ := by simp only [div_eq_mul_inv]; ring

noncomputable def phaseAt (a τ : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..τ, (Complex.digamma ((a : ℂ) + t * I)).re

theorem continuous_digamma_unscaled {a : ℝ} (ha : 0 < a) :
    Continuous (fun t : ℝ ↦ Complex.digamma ((a : ℂ) + t * I)) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_digamma (by simpa using ha)).continuousAt.comp
    (by fun_prop : ContinuousAt (fun t : ℝ ↦ (a : ℂ) + t * I) t)

/-- IEANTN's real estimate and Gauss series control the shifted phase
without introducing a branch of the principal logarithm of Gamma. -/
theorem digamma_quarter_shift_re_error {N t : ℝ} (hN : 1 ≤ N) (ht : 0 ≤ t) :
    |(Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N| ≤
      (2 * t + 5 / 4) / N := by
  have hN0 : 0 < N := by linarith
  have hx : 0 < N + 1 / 4 := by linarith
  have hd := norm_digamma_sub_le_of_re_ge hN
    (z₁ := (((N + 1 / 4 : ℝ) : ℂ) + t * I))
    (z₂ := ((N + 1 / 4 : ℝ) : ℂ))
    (by simp) (by simp)
  have hnorm : ‖(((N + 1 / 4 : ℝ) : ℂ) + t * I) - ((N + 1 / 4 : ℝ) : ℂ)‖ = t := by
    simp [norm_mul, Real.norm_eq_abs, abs_of_nonneg ht]
  rw [hnorm] at hd
  have hreal : |(Complex.digamma ((N + 1 / 4 : ℝ) : ℂ)).re - Real.log (N + 1 / 4)| ≤
      1 / (N + 1 / 4) := by
    rw [GammaSolution.digamma_ofReal hx, Complex.ofReal_re]
    exact GammaSolution.abs_deriv_log_Gamma_sub_log_le hx
  have hi : 1 / (N + 1 / 4) ≤ 1 / N :=
    one_div_le_one_div_of_le hN0 (by linarith)
  have hlog : |Real.log (N + 1 / 4) - Real.log N| ≤ (1 / 4) / N := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hN0 (by linarith)))]
    have hh := Real.log_le_sub_one_of_pos (div_pos hx hN0)
    rw [Real.log_div hx.ne' hN0.ne'] at hh
    have he : (N + 1 / 4) / N - 1 = (1 / 4) / N := by field_simp; ring
    rwa [he] at hh
  have hre := (Complex.abs_re_le_norm
    (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I) -
      Complex.digamma ((N + 1 / 4 : ℝ) : ℂ))).trans hd
  rw [Complex.sub_re] at hre
  have he : (2 * t + 5 / 4) / N = 2 * t / N + 1 / N + (1 / 4) / N := by ring
  rw [he, abs_le]
  rcases abs_le.mp hre with ⟨hrelo, hrehi⟩
  rcases abs_le.mp hreal with ⟨hrlo, hrhi⟩
  rcases abs_le.mp hlog with ⟨hllo, hlhi⟩
  constructor <;> linarith

theorem phaseAt_quarter_shift_error {N τ : ℝ} (hN : 1 ≤ N) (hτ : 0 ≤ τ) :
    |phaseAt (N + 1 / 4) τ - τ * Real.log N| ≤
      τ * (2 * τ + 5 / 4) / N := by
  have hx : 0 < N + 1 / 4 := by linarith
  have hi : IntervalIntegrable
      (fun t : ℝ ↦ (Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re) volume 0 τ :=
    (Complex.continuous_re.comp (continuous_digamma_unscaled hx)).intervalIntegrable 0 τ
  have he : phaseAt (N + 1 / 4) τ - τ * Real.log N =
      ∫ t in (0 : ℝ)..τ,
        ((Complex.digamma (((N + 1 / 4 : ℝ) : ℂ) + t * I)).re - Real.log N) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const]
    simp [phaseAt, smul_eq_mul]
  rw [he, ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ _t in (0 : ℝ)..τ, (2 * τ + 5 / 4) / N := by
      apply intervalIntegral.norm_integral_le_of_norm_le hτ
      · filter_upwards with t ht
        rw [Real.norm_eq_abs]
        exact (digamma_quarter_shift_re_error hN ht.1.le).trans
          (div_le_div_of_nonneg_right (by linarith [ht.2]) (by linarith))
      · exact intervalIntegrable_const
    _ = _ := by simp [smul_eq_mul]; ring

theorem tendsto_phaseAt_quarter_shift {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun N : ℕ ↦ phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N)
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (g := fun N : ℕ ↦ τ * (2 * τ + 5 / 4) / (N : ℝ))
    (Filter.Eventually.of_forall (fun _ ↦ norm_nonneg _))
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [Real.norm_eq_abs]
    exact phaseAt_quarter_shift_error (by exact_mod_cast hN) hτ
  · exact tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop


end TernaryGoldbach.RSBounds.BacklundGammaPhase
