import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# The variable Stechkin parameters in Rosser--Schoenfeld (1975)

Elementary real algebra only: no zeta, zero table, or analytic hypothesis is
imported. The final cubic lower bound sharpens the paper's quadratic estimate.
The definitions agree with RS75 (1.3)--(1.4).
-/

namespace TernaryGoldbach.RSBounds.RS75Parameters

noncomputable section

def sigma0 (σ : ℝ) : ℝ := (1 + Real.sqrt (8 * σ ^ 2 - 4 * σ + 1)) / 2

def kappa (σ : ℝ) : ℝ := (2 * σ - 1) / (2 * sigma0 σ - 1)

def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

def cubic (x : ℝ) : ℝ := 1 + 4 / 5 * x - 26 / 25 * x ^ 2 + 6 / 5 * x ^ 3

theorem discriminant_pos {σ : ℝ} (hσ : 1 ≤ σ) : 0 < 8 * σ ^ 2 - 4 * σ + 1 := by
  nlinarith [sq_nonneg (σ - 1)]

theorem two_sigma0_sub_one (σ : ℝ) :
    2 * sigma0 σ - 1 = Real.sqrt (8 * σ ^ 2 - 4 * σ + 1) := by
  unfold sigma0
  ring

theorem sigma0_quadratic {σ : ℝ} (hσ : 1 ≤ σ) :
    sigma0 σ * (sigma0 σ - 1) = σ * (2 * σ - 1) := by
  have hs := Real.sq_sqrt (discriminant_pos hσ).le
  unfold sigma0
  nlinarith

theorem sigma0_gt {σ : ℝ} (hσ : 1 ≤ σ) : σ < sigma0 σ := by
  have hs := Real.sq_sqrt (discriminant_pos hσ).le
  have hn := Real.sqrt_nonneg (8 * σ ^ 2 - 4 * σ + 1)
  have hσ0 : 0 < σ := by linarith
  have hp : 0 < σ ^ 2 := by positivity
  have hh : 2 * σ - 1 < Real.sqrt (8 * σ ^ 2 - 4 * σ + 1) := by
    nlinarith
  unfold sigma0
  linarith

theorem sigma0_gt_one {σ : ℝ} (hσ : 1 < σ) : 1 < sigma0 σ :=
  hσ.trans (sigma0_gt hσ.le)

theorem kappa_pos {σ : ℝ} (hσ : 1 ≤ σ) : 0 < kappa σ := by
  unfold kappa
  exact div_pos (by linarith) (by linarith [sigma0_gt hσ])

theorem kappa_lt_one {σ : ℝ} (hσ : 1 ≤ σ) : kappa σ < 1 := by
  unfold kappa
  apply (div_lt_one (by linarith [sigma0_gt hσ] : 0 < 2 * sigma0 σ - 1)).2
  linarith [sigma0_gt hσ]

theorem kappa_eq_half_ratio {σ : ℝ} (hσ : 1 ≤ σ) :
    kappa σ = (σ - 1 / 2) / (sigma0 σ - 1 / 2) := by
  have hd : sigma0 σ - 1 / 2 ≠ 0 := by linarith [sigma0_gt hσ]
  have hd' : 2 * sigma0 σ - 1 ≠ 0 := by linarith [sigma0_gt hσ]
  unfold kappa
  field_simp [hd, hd']
  <;> ring

theorem stechkin_square_condition {σ : ℝ} (hσ : 1 ≤ σ) :
    3 / 2 ≤ (σ - 1 / 2) ^ 2 + (sigma0 σ - 1 / 2) ^ 2 := by
  have hq := sigma0_quadratic hσ
  nlinarith [sq_nonneg (σ - 1)]

theorem sigma0_add_one (x : ℝ) :
    sigma0 (1 + x) = (1 + Real.sqrt (5 + 12 * x + 8 * x ^ 2)) / 2 := by
  have hd : 8 * (1 + x) ^ 2 - 4 * (1 + x) + 1 = 5 + 12 * x + 8 * x ^ 2 := by ring
  simp only [sigma0, hd]

theorem kappa_add_one (x : ℝ) :
    kappa (1 + x) = (1 + 2 * x) / Real.sqrt (5 + 12 * x + 8 * x ^ 2) := by
  unfold kappa
  rw [two_sigma0_sub_one]
  congr 1
  · ring
  · congr 1
    ring

/-- The two reflected denominators collapse to the same quadratic used in RS75. -/
theorem reflected_product {σ β : ℝ} (hσ : 1 ≤ σ) :
    (sigma0 σ - β) * (sigma0 σ - 1 + β) = σ * (2 * σ - 1) + β * (1 - β) := by
  have hq := sigma0_quadratic hσ
  nlinarith

/-- The factor needed to keep the full contribution of one off-line zero. -/
theorem reflected_product_difference {σ β : ℝ} (hσ : 1 ≤ σ) :
    (sigma0 σ - β) * (sigma0 σ - 1 + β) -
      (2 * σ - 1) * (σ - 1 + β) = (1 - β) * (β + 2 * σ - 1) := by
  rw [reflected_product hσ]
  ring

/-- The reflected partner pays for the entire shifted pair. This holds on [0,1]. -/
theorem shifted_pair_le_reflected {σ β : ℝ} (hσ : 1 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    kappa σ * (1 / (sigma0 σ - β) + 1 / (sigma0 σ - 1 + β)) ≤
      1 / (σ - 1 + β) := by
  have hu : 1 < sigma0 σ := sigma0_gt_one hσ
  have h1 : 0 < sigma0 σ - β := by linarith
  have h2 : 0 < sigma0 σ - 1 + β := by linarith
  have h3 : 0 < 2 * sigma0 σ - 1 := by linarith
  have h4 : 0 < σ - 1 + β := by linarith
  have hp : 0 < (sigma0 σ - β) * (sigma0 σ - 1 + β) := mul_pos h1 h2
  have he : kappa σ * (1 / (sigma0 σ - β) + 1 / (sigma0 σ - 1 + β)) =
      (2 * σ - 1) / ((sigma0 σ - β) * (sigma0 σ - 1 + β)) := by
    unfold kappa
    field_simp [h1.ne', h2.ne', h3.ne']
    <;> ring
  rw [he]
  apply (div_le_div_iff₀ hp h4).2
  have hn : 0 ≤ (1 - β) * (β + 2 * σ - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hd := reflected_product_difference (β := β) hσ.le
  nlinarith

/-- A form matching the usual choice of the right member of a reflected pair. -/
theorem shifted_pair_le_reflected_of_half_le {σ β : ℝ} (hσ : 1 < σ)
    (hβ0 : 1 / 2 ≤ β) (hβ1 : β ≤ 1) :
    kappa σ * (1 / (sigma0 σ - β) + 1 / (sigma0 σ - 1 + β)) ≤
      1 / (σ - 1 + β) :=
  shifted_pair_le_reflected hσ (by linarith) hβ1

/-- Exact squared comparison for the improved cubic lower bound. -/
theorem cubic_squared_identity (x : ℝ) :
    5 * (1 + 2 * x) ^ 2 - (5 + 12 * x + 8 * x ^ 2) * cubic x ^ 2 =
      4 * x ^ 3 / 625 *
        (125 - 1925 * x - 4598 * x ^ 2 - 197 * x ^ 3 + 420 * x ^ 4 - 1800 * x ^ 5) := by
  unfold cubic
  ring

theorem cubic_positive {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 0.03) : 0 < cubic x := by
  have h2 := pow_le_pow_left₀ hx hx' 2
  have h3 := pow_nonneg hx 3
  norm_num at h2
  unfold cubic
  linarith

theorem cubic_residual_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 0.03) :
    63 < 125 - 1925 * x - 4598 * x ^ 2 - 197 * x ^ 3 + 420 * x ^ 4 - 1800 * x ^ 5 := by
  have h2 := pow_le_pow_left₀ hx hx' 2
  have h3 := pow_le_pow_left₀ hx hx' 3
  have h4 := pow_nonneg hx 4
  have h5 := pow_le_pow_left₀ hx hx' 5
  norm_num at h2 h3 h5
  linarith

/-- Strong enough for the weaker near-pole and golden-ratio bounds. -/
theorem cubic_kappa_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 0.03) :
    cubic x / Real.sqrt 5 ≤ kappa (1 + x) := by
  rw [kappa_add_one]
  have hD : 0 < 5 + 12 * x + 8 * x ^ 2 := by positivity
  have hDsq := Real.sq_sqrt hD.le
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h5pos : 0 < Real.sqrt (5 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hDpos : 0 < Real.sqrt (5 + 12 * x + 8 * x ^ 2) := Real.sqrt_pos.2 hD
  have hq := cubic_positive hx hx'
  have hp := cubic_residual_lower hx hx'
  have hn : 0 ≤ 4 * x ^ 3 / 625 *
      (125 - 1925 * x - 4598 * x ^ 2 - 197 * x ^ 3 + 420 * x ^ 4 - 1800 * x ^ 5) := by
    exact mul_nonneg (by positivity) (by linarith)
  have hi := cubic_squared_identity x
  have hsq : (cubic x * Real.sqrt (5 + 12 * x + 8 * x ^ 2)) ^ 2 ≤
      ((1 + 2 * x) * Real.sqrt 5) ^ 2 := by
    rw [mul_pow, mul_pow, hDsq, h5sq]
    nlinarith [hi]
  apply (div_le_div_iff₀ h5pos hDpos).2
  exact (sq_le_sq₀ (mul_nonneg hq.le hDpos.le) (by positivity)).1 hsq

/-- Two elementary square-root enclosures used for the golden-ratio transfer. -/
theorem sqrt_five_bounds : (2.23606 : ℝ) < Real.sqrt 5 ∧ Real.sqrt 5 < 2.23608 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  constructor <;> nlinarith

theorem sigma0_add_one_ge_golden {x : ℝ} (hx : 0 ≤ x) :
    goldenRatio ≤ sigma0 (1 + x) := by
  have hd : (5 : ℝ) ≤ 5 + 12 * x + 8 * x ^ 2 := by nlinarith [sq_nonneg x]
  have hs := Real.sqrt_le_sqrt hd
  rw [sigma0_add_one]
  unfold goldenRatio
  linarith

/-- The paper's slope allowance, with closed endpoints. -/
theorem sigma0_add_one_le_golden_add {x : ℝ} (hx : 0 ≤ x) (hx' : x ≤ 0.03) :
    sigma0 (1 + x) ≤ goldenRatio + 1.34424 * x := by
  have hD : 0 ≤ 5 + 12 * x + 8 * x ^ 2 := by positivity
  have hDsq := Real.sq_sqrt hD
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hr := sqrt_five_bounds.1
  have hh : 0 ≤ 2 * (2.68848 : ℝ) * Real.sqrt 5 - 12 + ((2.68848 : ℝ) ^ 2 - 8) * x := by
    nlinarith
  have hp := mul_nonneg hx hh
  have hs : Real.sqrt (5 + 12 * x + 8 * x ^ 2) ≤ Real.sqrt 5 + 2.68848 * x := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    nlinarith
  rw [sigma0_add_one]
  unfold goldenRatio
  linarith

/-- Broad ranges sufficient for the separate frequency estimate. -/
theorem sigma_le_five_fourths {σ : ℝ} (hσ : σ ≤ 1.03) : σ ≤ 5 / 4 := by
  linarith

theorem sigma0_lt_three {σ : ℝ} (hσ : 1 ≤ σ) (hσ' : σ ≤ 1.03) :
    sigma0 σ < 3 := by
  have hσ0 : 0 ≤ σ := by linarith
  have h2 := pow_le_pow_left₀ hσ0 hσ' 2
  have hd := Real.sq_sqrt (discriminant_pos hσ).le
  have hn := Real.sqrt_nonneg (8 * σ ^ 2 - 4 * σ + 1)
  have hs : Real.sqrt (8 * σ ^ 2 - 4 * σ + 1) < 5 := by nlinarith
  unfold sigma0
  linarith

theorem kappa_lt_half {σ : ℝ} (hσ : 1 ≤ σ) (hσ' : σ ≤ 1.03) :
    kappa σ < 1 / 2 := by
  have hσ0 : 0 ≤ σ := by linarith
  have h2 := pow_le_pow_left₀ hσ0 hσ' 2
  have hd := Real.sq_sqrt (discriminant_pos hσ).le
  have hn := Real.sqrt_nonneg (8 * σ ^ 2 - 4 * σ + 1)
  have hp : 0 < Real.sqrt (8 * σ ^ 2 - 4 * σ + 1) :=
    Real.sqrt_pos.2 (discriminant_pos hσ)
  have hs : 4 * σ - 2 < Real.sqrt (8 * σ ^ 2 - 4 * σ + 1) := by nlinarith
  unfold kappa
  rw [two_sigma0_sub_one]
  apply (div_lt_iff₀ hp).2
  linarith

/-- Strict slope transfer for the positive x range used in RS75. -/
theorem sigma0_add_one_lt_golden_add {x : ℝ} (hx : 0 < x) (hx' : x ≤ 0.03) :
    sigma0 (1 + x) < goldenRatio + 1.34424 * x := by
  have hD : 0 ≤ 5 + 12 * x + 8 * x ^ 2 := by positivity
  have hDsq := Real.sq_sqrt hD
  have h5sq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hr := sqrt_five_bounds.1
  have hh : 0 < 2 * (2.68848 : ℝ) * Real.sqrt 5 - 12 + ((2.68848 : ℝ) ^ 2 - 8) * x := by
    nlinarith
  have hp := mul_pos hx hh
  have hs : Real.sqrt (5 + 12 * x + 8 * x ^ 2) < Real.sqrt 5 + 2.68848 * x := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
    nlinarith
  rw [sigma0_add_one]
  unfold goldenRatio
  linarith

theorem sigma0_sub_golden_lt {σ : ℝ} (hσ : 1 < σ) (hσ' : σ < 1.03) :
    sigma0 σ - goldenRatio < 1.34424 * (σ - 1) := by
  have hh := sigma0_add_one_lt_golden_add (x := σ - 1) (by linarith) (by linarith)
  rw [show 1 + (σ - 1) = σ by ring] at hh
  linarith

end
end TernaryGoldbach.RSBounds.RS75Parameters
