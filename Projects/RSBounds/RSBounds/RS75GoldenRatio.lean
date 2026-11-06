import RSBounds.RS75GoldenTails
import RSBounds.RS75Parameters

/-!
# Golden-ratio real-axis constants for the RS75 zero-free-region argument

The finite root/logarithm certificates are bound to the actual infinite
zeta moments. Positivity of the von Mangoldt series transfers rational-point
bounds to the golden ratio and its right-hand tangent estimate.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.RS75GoldenRatio

open RS75GoldenSeries RS75GoldenNumerics RS75GoldenTails RS75Parameters

theorem upperPoint_logDerivative_lt : logDerivative (233 / 144) < -1.1398 := by
  have hs : (1 : ℝ) < 233 / 144 := by norm_num
  have h0 : moment (233 / 144) 0 < 223829 / 100000 :=
    (moment_le_upper (by norm_num) (by norm_num) 0 (by norm_num)).trans_lt
      upperPoint_zero_upper
  have h1 : (255131 / 100000 : ℝ) < moment (233 / 144) 1 :=
    upperPoint_one_lower.trans_le
      (center_le_moment (by norm_num) (by norm_num) 1 (by norm_num))
  rw [logDerivative_eq_moments hs, neg_div, neg_lt_neg_iff,
    lt_div_iff₀ (moment_zero_pos hs)]
  nlinarith

theorem lowerPoint_slope_lt : RS75GoldenSeries.slope (55 / 34) < 2.5 := by
  have hs : (1 : ℝ) < 55 / 34 := by norm_num
  have h0l : (22393 / 10000 : ℝ) < moment (55 / 34) 0 :=
    lowerPoint_zero_lower.trans_le
      (center_le_moment (by norm_num) (by norm_num) 0 (by norm_num))
  have h0u : moment (55 / 34) 0 < 11197 / 5000 :=
    (moment_le_upper (by norm_num) (by norm_num) 0 (by norm_num)).trans_lt
      lowerPoint_zero_upper
  have h1 : (25547 / 10000 : ℝ) < moment (55 / 34) 1 :=
    lowerPoint_one_lower.trans_le
      (center_le_moment (by norm_num) (by norm_num) 1 (by norm_num))
  have h2 : moment (55 / 34) 2 < 10597 / 1250 :=
    (moment_le_upper (by norm_num) (by norm_num) 2 (by norm_num)).trans_lt
      lowerPoint_two_upper
  have hp := moment_zero_pos hs
  have hlo : (2.5547 / 2.2394 : ℝ) ≤ moment (55 / 34) 1 / moment (55 / 34) 0 := by
    rw [le_div_iff₀ hp]
    nlinarith
  have hhi : moment (55 / 34) 2 / moment (55 / 34) 0 ≤ (8.4776 / 2.2393 : ℝ) := by
    rw [div_le_iff₀ hp]
    nlinarith
  rw [slope_eq_moments hs]
  nlinarith [sq_nonneg (moment (55 / 34) 1 / moment (55 / 34) 0 - (2.5547 / 2.2394 : ℝ))]

theorem goldenRatio_bounds : (55 / 34 : ℝ) < goldenRatio ∧ goldenRatio < 233 / 144 := by
  unfold goldenRatio
  constructor <;> linarith [sqrt_five_bounds.1, sqrt_five_bounds.2]

theorem goldenRatio_gt_one : (1 : ℝ) < goldenRatio := by
  linarith [goldenRatio_bounds.1]

/-- The actual zeta logarithmic derivative at the golden ratio. -/
theorem golden_logDerivative_lt :
    (logDeriv riemannZeta (goldenRatio : ℂ)).re < -1.1398 := by
  change logDerivative goldenRatio < -1.1398
  exact (monotoneOn_logDerivative goldenRatio_gt_one (by norm_num)
    goldenRatio_bounds.2.le).trans_lt upperPoint_logDerivative_lt

/-- The actual von Mangoldt log-weighted series at the golden ratio. -/
theorem golden_slope_lt : RS75GoldenSeries.slope goldenRatio < 2.5 :=
  (antitoneOn_slope (by norm_num) goldenRatio_gt_one goldenRatio_bounds.1.le).trans_lt
    lowerPoint_slope_lt

/-- Its interpretation as the derivative of the actual real-axis logarithmic derivative. -/
theorem golden_deriv_logDerivative_lt : deriv logDerivative goldenRatio < 2.5 := by
  rw [(hasDerivAt_logDerivative goldenRatio_gt_one).deriv]
  exact golden_slope_lt

/-- A uniform right-hand tangent bound, proved by the actual derivative estimate. -/
theorem logDerivative_lt_tangent {u : ℝ} (hu : goldenRatio ≤ u) :
    logDerivative u < -1.1398 + 2.5 * (u - goldenRatio) := by
  have hcont : ContinuousOn logDerivative (Ici goldenRatio) := by
    intro x hx
    exact (hasDerivAt_logDerivative (goldenRatio_gt_one.trans_le hx)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ logDerivative (interior (Ici goldenRatio)) := by
    intro x hx
    have hx0 : goldenRatio ≤ x := interior_subset hx
    exact (hasDerivAt_logDerivative (goldenRatio_gt_one.trans_le hx0)).differentiableAt.differentiableWithinAt
  have hbound : ∀ x ∈ interior (Ici goldenRatio), deriv logDerivative x ≤ 2.5 := by
    intro x hx
    have hx0 : goldenRatio ≤ x := interior_subset hx
    have hx1 := goldenRatio_gt_one.trans_le hx0
    rw [(hasDerivAt_logDerivative hx1).deriv]
    exact (antitoneOn_slope goldenRatio_gt_one hx1 hx0).trans golden_slope_lt.le
  have h := (convex_Ici goldenRatio).image_sub_le_mul_sub_of_deriv_le hcont hdiff hbound
    goldenRatio (by simp) u hu hu
  have hg : logDerivative goldenRatio < -1.1398 := golden_logDerivative_lt
  linarith

/-- The weaker sufficient replacement for RS75 (1.25), with no numerical premise. -/
theorem shifted_real_axis_bound {σ : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03) :
    (logDeriv riemannZeta (sigma0 σ : ℂ)).re < -1.1398 + 3.3606 * (σ - 1) := by
  have hg : goldenRatio ≤ sigma0 σ := by
    have h := sigma0_add_one_ge_golden (x := σ - 1) (by linarith)
    simpa only [show 1 + (σ - 1) = σ by ring] using h
  have ht := logDerivative_lt_tangent hg
  have hd := sigma0_sub_golden_lt hσ hσ'
  change logDerivative (sigma0 σ) < -1.1398 + 3.3606 * (σ - 1)
  nlinarith

end TernaryGoldbach.RSBounds.RS75GoldenRatio
