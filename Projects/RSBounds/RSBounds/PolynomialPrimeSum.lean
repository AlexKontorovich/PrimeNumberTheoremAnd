import TernaryGoldbach.Explicit.ExplicitFormula

/-!
# Prime-sum Mellin inversion using only right-line hypotheses

This extracts the right-line argument of upstream `SsumG_eq_line`. The
weight need only have a convergent Mellin transform on `Re s = 3/2`, with
that transform continuous and integrable along the line. No continuation
across zero or exponential decay is required.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.PolynomialPrimeSum

open TernaryGoldbach.Explicit

/-- Mellin inversion with hypotheses restricted to the right vertical line. -/
theorem eq_mellinInv {φ : ℝ → ℂ}
    (hcont : ∀ y : ℝ, 0 < y → ContinuousAt φ y)
    (hconv : MellinConvergent φ ((3 / 2 : ℝ) : ℂ))
    (hint : Integrable (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    {y : ℝ} (hy : 0 < y) :
    φ y = (1 / (2 * π)) • ∫ t : ℝ,
      (y : ℂ) ^ (-(((3 / 2 : ℝ) : ℂ) + t * I)) •
        mellin φ (((3 / 2 : ℝ) : ℂ) + t * I) := by
  have hvert : Complex.VerticalIntegrable (mellin φ) (3 / 2) := hint
  have h := mellinInv_mellin_eq (3 / 2) φ hy hconv hvert (hcont y hy)
  rw [← h, mellinInv]

theorem eq_integral_Fterm {φ : ℝ → ℂ}
    (hcont : ∀ y : ℝ, 0 < y → ContinuousAt φ y)
    (hconv : MellinConvergent φ ((3 / 2 : ℝ) : ℂ))
    (hint : Integrable (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    φ (n / x) = (1 / (2 * π) : ℂ) * ∫ t, Fterm φ x n t := by
  rw [eq_mellinInv hcont hconv hint (by positivity : (0 : ℝ) < n / x),
    Complex.real_smul]
  congr 1
  push_cast
  ring

theorem integrable_Fterm {φ : ℝ → ℂ}
    (hline : Continuous (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    (hint : Integrable (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : 0 < n) :
    Integrable (Fterm φ x n) := by
  refine (hint.norm.const_mul (((n : ℝ) / x) ^ (-(3 / 2 : ℝ)))).mono' ?_
    (Eventually.of_forall fun t => ?_)
  · refine (Continuous.mul ?_ hline).aestronglyMeasurable
    refine continuous_iff_continuousAt.2 fun t => ?_
    exact (continuousAt_const_cpow (Complex.ofReal_ne_zero.2
      (by positivity : (0 : ℝ) < n / x).ne')).comp (by fun_prop)
  · rw [Fterm, norm_mul, norm_ratio_cpow hn hx]

/-- The prime sum equals the Mellin integral of the logarithmic derivative
on `Re s = 3/2`, assuming only right-line analytic hypotheses. -/
theorem SsumG_eq_line {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {φ : ℝ → ℂ}
    (hcont : ∀ y : ℝ, 0 < y → ContinuousAt φ y)
    (hconv : MellinConvergent φ ((3 / 2 : ℝ) : ℂ))
    (hline : Continuous (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    (hint : Integrable (fun t : ℝ => mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)))
    {x : ℝ} (hx : 0 < x) :
    SsumG χ φ x = (1 / (2 * π) : ℂ) *
      ∫ t : ℝ, Fline χ φ x (((3 / 2 : ℝ) : ℂ) + t * I) := by
  set F : ℕ → ℝ → ℂ := fun n t => (Λ n : ℂ) * χ n * Fterm φ x n t with hF
  have hterm : ∀ n : ℕ, (Λ n : ℂ) * χ n * φ (n / x) =
      (1 / (2 * π) : ℂ) * ∫ t, F n t := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · rw [eq_integral_Fterm hcont hconv hint hx hn, hF]
      simp only
      rw [integral_const_mul]
      ring
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : F 0 = fun _ => 0 := by ext t; simp [hF]
      rw [this]
      exact integrable_zero _ _ _
    · exact (integrable_Fterm hline hint hx hn).const_mul _
  have hFs : Summable fun n => ∫ t, ‖F n t‖ := by
    have hΛ := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := ((3 / 2 : ℝ) : ℂ)) (by norm_num)
    have hΛ' : Summable fun n : ℕ => Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
      refine hΛ.norm.congr fun n => ?_
      rw [LSeries.norm_term_eq]
      split_ifs with h0
      · simp [h0]
      · rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        simp
    refine (hΛ'.mul_right (x ^ (3 / 2 : ℝ) *
      ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖)).of_nonneg_of_le
      (fun n => integral_nonneg fun t => norm_nonneg _) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hF]
    · have e : ∀ t, ‖F n t‖ = (Λ n * ‖χ n‖) * ‖Fterm φ x n t‖ := by
        intro t
        rw [hF]
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      simp_rw [e]
      rw [integral_const_mul, integral_norm_Fterm φ hx hn]
      have hχ : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
      have hG0 : 0 ≤ ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ :=
        integral_nonneg fun t => norm_nonneg _
      have hΛ0 := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      have hn0 : 0 ≤ (n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) := by positivity
      calc
        Λ n * ‖χ n‖ * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖)
          ≤ Λ n * 1 * ((n : ℝ) ^ (-(3 / 2 : ℝ)) * x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖) := by gcongr
        _ = Λ n * (n : ℝ) ^ (-(3 / 2 : ℝ)) * (x ^ (3 / 2 : ℝ) *
            ∫ t : ℝ, ‖mellin φ (((3 / 2 : ℝ) : ℂ) + t * I)‖) := by ring
  rw [SsumG, tsum_congr hterm, tsum_mul_left,
    integral_tsum_of_summable_integral_norm hFi hFs]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  exact tsum_Fterm_eq χ φ hx t

end TernaryGoldbach.RSBounds.PolynomialPrimeSum
