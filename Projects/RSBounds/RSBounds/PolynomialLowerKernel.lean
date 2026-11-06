import RSBounds.PolynomialZeroCancellation

/-! Basic low- and high-zero estimates for the lower additive average.
These complement the upper bounds in `PolynomialZeroKernel` without changing
that previously checked module. -/

open Complex MeasureTheory Set
open TernaryGoldbach.RSBounds.PolynomialZeroKernel
open TernaryGoldbach.RSBounds.PolynomialZeroCancellation

namespace TernaryGoldbach.RSBounds.PolynomialLowerKernel

theorem norm_forwardDiff_le_const_on {h : ℝ} (hh : 0 ≤ h)
    (f : ℝ → ℂ) (C : ℝ) (n : ℕ) :
    ∀ x, (∀ t ∈ Icc x (x + n * h), ‖f t‖ ≤ C) →
      ‖forwardDiff h n f x‖ ≤ 2 ^ n * C := by
  induction n with
  | zero =>
    intro x hf
    simpa [forwardDiff] using hf x (by simp)
  | succ n ih =>
    intro x hf
    have hleft : ‖forwardDiff h n f x‖ ≤ 2 ^ n * C := by
      apply ih x
      intro t ht
      apply hf t
      constructor
      · exact ht.1
      · simp only [Nat.cast_add, Nat.cast_one]
        nlinarith [ht.2]
    have hright : ‖forwardDiff h n f (x + h)‖ ≤ 2 ^ n * C := by
      apply ih (x + h)
      intro t ht
      apply hf t
      constructor
      · linarith [ht.1]
      · simp only [Nat.cast_add, Nat.cast_one]
        nlinarith [ht.2]
    change ‖forwardDiff h n f (x + h) - forwardDiff h n f x‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [pow_succ]
    linarith

/-- The lower average has low-zero coefficient at most `1/|rho|`. -/
theorem norm_lower_difference_le_low {δ : ℝ} (hδ : 0 < δ) (hδ4 : 4 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) (hn : ρ ≠ 0) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4‖ ≤ 1 / ‖ρ‖ := by
  have hx : 0 < 1 - 4 * δ := by linarith
  rw [← zero_term_fourfold_identity_of_neg_one_lt (by linarith : -1 < ρ.re) hn hx hδ.le]
  have hm := norm_iteratedIntegral_le_const_on hδ.le
    (fun t : ℝ => (t : ℂ) ^ ρ / ρ) (1 / ‖ρ‖) 4 (1 - 4 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      exact div_le_div_of_nonneg_right (Real.rpow_le_one ht0.le ht1 hρ) (norm_nonneg _))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  apply (div_le_iff₀ (pow_pos hδ 4)).mpr
  convert hm using 1 <;> ring

/-- The lower finite-difference numerator has coefficient sum `16`. -/
theorem norm_lower_difference_le_high {δ : ℝ} (hδ : 0 < δ) (hδ4 : 4 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4‖ ≤
      16 / (δ ^ 4 * ‖rising ρ 4‖) := by
  have hx : 0 < 1 - 4 * δ := by linarith
  have hm := norm_forwardDiff_le_const_on hδ.le (antiderivative ρ 4)
    (1 / ‖rising ρ 4‖) 4 (1 - 4 * δ) (by
      intro t ht
      have ht0 : 0 < t := hx.trans_le ht.1
      have ht1 : t ≤ 1 := by norm_num at ht; linarith [ht.2]
      rw [antiderivative, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      apply div_le_div_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_one ht0.le ht1
      simpa using (show 0 ≤ ρ.re + 4 by linarith))
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδ]
  calc ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ)‖ / δ ^ 4 ≤
      (2 ^ 4 * (1 / ‖rising ρ 4‖)) / δ ^ 4 := by gcongr
    _ = 16 / (δ ^ 4 * ‖rising ρ 4‖) := by ring

theorem sixteen_le_R4 {δ : ℝ} (hδ : 0 ≤ δ) : 16 ≤ R4 δ := by
  have h1 : (1 : ℝ) ≤ (1 + δ) ^ 5 := one_le_pow₀ (by linarith)
  have h2 : (2 : ℝ) ^ 4 ≤ ((1 + δ) ^ 5 + 1) ^ 4 := by gcongr; linarith
  norm_num [R4] at h2 ⊢
  exact h2

/-- The same `R4` high-zero majorant can therefore be used for both signs. -/
theorem norm_lower_difference_le_high_common {δ : ℝ} (hδ : 0 < δ) (hδ4 : 4 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4‖ ≤
      R4 δ / (δ ^ 4 * ‖rising ρ 4‖) :=
  (norm_lower_difference_le_high hδ hδ4 hρ).trans
    (div_le_div_of_nonneg_right (sixteen_le_R4 hδ.le) (by positivity))

/-- The upper low-zero factor `1+2*delta` also majorizes the lower average. -/
theorem norm_lower_difference_le_low_common {δ : ℝ} (hδ : 0 < δ) (hδ4 : 4 * δ < 1)
    {ρ : ℂ} (hρ : 0 ≤ ρ.re) (hn : ρ ≠ 0) :
    ‖forwardDiff δ 4 (antiderivative ρ 4) (1 - 4 * δ) / (δ : ℂ) ^ 4‖ ≤
      (1 + 2 * δ) / ‖ρ‖ :=
  (norm_lower_difference_le_low hδ hδ4 hρ hn).trans
    (div_le_div_of_nonneg_right (by linarith) (norm_nonneg _))

end TernaryGoldbach.RSBounds.PolynomialLowerKernel
