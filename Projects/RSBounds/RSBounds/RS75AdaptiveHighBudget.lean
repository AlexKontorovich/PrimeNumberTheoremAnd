import RSBounds.RS75DecayingHighZeros
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The high-zero budget at delta = 1/(50 log x)

For `log x >= 400`, the actual high-zero part of either quartic smoothing
is strictly below `.05*x/log x`. This is only the high-zero contribution:
the low zeros, smoothing main term and contour remainder are separate.
No finite-RH hypothesis occurs in the bounds proved here.
-/

open Complex Finset

namespace TernaryGoldbach.RSBounds.RS75AdaptiveHighBudget

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialAveraged
open PolynomialZeroKernel RS75ZeroPowerDecay RS75DecayingHighZeros

noncomputable def adaptiveDelta (x : ℝ) : ℝ := 1 / (50 * Real.log x)

noncomputable def powerBudget (L : ℝ) : ℝ :=
  (3 / 13600000 : ℝ) * L ^ 5 * Real.exp (-(8 / 9 : ℝ) * Real.sqrt L)

theorem adaptiveDelta_pos {x : ℝ} (hL : 400 ≤ Real.log x) :
    0 < adaptiveDelta x := by
  unfold adaptiveDelta
  have : 0 < Real.log x := by linarith
  positivity

theorem adaptiveDelta_le {x : ℝ} (hL : 400 ≤ Real.log x) :
    adaptiveDelta x ≤ 1 / 20000 := by
  unfold adaptiveDelta
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  linarith

theorem four_adaptiveDelta_lt_one {x : ℝ} (hL : 400 ≤ Real.log x) :
    4 * adaptiveDelta x < 1 := by linarith [adaptiveDelta_le hL]

theorem R4_le_seventeen {δ : ℝ} (hδ : 0 ≤ δ) (hδ' : δ ≤ 1 / 20000) :
    R4 δ ≤ 17 := by
  unfold R4
  calc
    _ ≤ (((1 + 1 / 20000 : ℝ) ^ 5 + 1) ^ 4) := by gcongr
    _ ≤ 17 := by norm_num

/-- A logarithmic tangent bound controls the entire interval above 20. -/
theorem power_exp_le_at_twenty {u : ℝ} (hu : 20 ≤ u) :
    u ^ 10 * Real.exp (-(8 / 9 : ℝ) * u) ≤
      20 ^ 10 * Real.exp (-(160 / 9 : ℝ)) := by
  have hu0 : 0 < u := by linarith
  have hl := Real.log_le_sub_one_of_pos (by positivity : 0 < u / (20 : ℝ))
  rw [Real.log_div hu0.ne' (by norm_num)] at hl
  have ha : 10 * Real.log u - (8 / 9 : ℝ) * u ≤
      10 * Real.log 20 - (160 / 9 : ℝ) := by linarith
  have he := Real.exp_le_exp.mpr ha
  have hue : Real.exp (10 * Real.log u) = u ^ 10 := by
    simpa only [Nat.cast_ofNat, Real.exp_log hu0] using Real.exp_nat_mul (Real.log u) 10
  have h20e : Real.exp (10 * Real.log 20) = (20 : ℝ) ^ 10 := by
    simpa only [Nat.cast_ofNat, Real.exp_log (by norm_num : (0 : ℝ) < 20)] using
      Real.exp_nat_mul (Real.log 20) 10
  simpa only [Real.exp_sub, hue, h20e, Real.exp_log hu0,
    Real.exp_log (by norm_num : (0 : ℝ) < 20), neg_mul, Real.exp_neg,
    div_eq_mul_inv] using he

/-- Closed endpoint certificate; only existing exp(1) and log(2) bounds are used. -/
theorem endpoint_budget_lt :
    (3 / 13600000 : ℝ) * 400 ^ 5 * Real.exp (-(160 / 9 : ℝ)) < 0.05 := by
  have h1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.718) h1 17
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat, mul_one] at hp
  have h2 : (2 : ℝ) ≤ Real.exp (7 / 9) := by
    calc
      _ = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Real.log_two_lt_d9])
  have hm : (2.718 : ℝ) ^ 17 * 2 ≤ Real.exp (160 / 9) := by
    have hh := mul_le_mul hp h2 (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le
    rw [← Real.exp_add] at hh
    convert hh using 1 <;> norm_num
  have hc : (3 / 13600000 : ℝ) * 400 ^ 5 <
      0.05 * ((2.718 : ℝ) ^ 17 * 2) := by norm_num
  rw [Real.exp_neg, ← div_eq_mul_inv]
  apply (div_lt_iff₀ (Real.exp_pos _)).mpr
  exact hc.trans_le (mul_le_mul_of_nonneg_left hm (by norm_num))

theorem powerBudget_lt {L : ℝ} (hL : 400 ≤ L) : powerBudget L < 0.05 := by
  have hL0 : 0 ≤ L := by linarith
  have hs : 20 ≤ Real.sqrt L := by
    have hh := Real.sqrt_le_sqrt hL
    norm_num at hh
    exact hh
  have hp := power_exp_le_at_twenty hs
  have he : (Real.sqrt L) ^ 10 = L ^ 5 := by
    rw [show (10 : ℕ) = 2 * 5 by norm_num, pow_mul, Real.sq_sqrt hL0]
  rw [he] at hp
  have hh := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 3 / 13600000)
  have hbound : powerBudget L ≤
      (3 / 13600000 : ℝ) * 400 ^ 5 * Real.exp (-(160 / 9 : ℝ)) := by
    unfold powerBudget
    convert hh using 1 <;> norm_num <;> ring
  exact hbound.trans_lt endpoint_budget_lt

/-- The actual coefficient prefactor fits strictly inside the `.05/log x` budget. -/
theorem highConstant_budget_lt {x : ℝ} (hx : 1 ≤ x) (hL : 400 ≤ Real.log x) :
    2 * highConstant x (adaptiveDelta x) * 3e-13 < 0.05 * x / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hδ := adaptiveDelta_pos hL
  have hR := R4_le_seventeen hδ.le (adaptiveDelta_le hL)
  have hmul := mul_le_mul_of_nonneg_right hR
    (show 0 ≤ (2 * (3e-13 : ℝ) * 50 ^ 4 / 289) * x * (Real.log x) ^ 4 * decay x by
      exact mul_nonneg (by positivity) (decay_pos x).le)
  have hc : 2 * highConstant x (adaptiveDelta x) * 3e-13 ≤
      (x / Real.log x) * powerBudget (Real.log x) := by
    convert hmul using 1 <;>
      simp only [highConstant, adaptiveDelta, powerBudget, decay] <;>
      field_simp [hL0.ne'] <;> ring
  calc
    _ ≤ (x / Real.log x) * powerBudget (Real.log x) := hc
    _ < (x / Real.log x) * 0.05 :=
      mul_lt_mul_of_pos_left (powerBudget_lt hL) (div_pos hx0 hL0)
    _ = _ := by ring

/-- The actual upper quartic high-zero sum at the variable smoothing step. -/
theorem norm_high_sum_upper_lt {T x : ℝ} (hT : 1894439 ≤ T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hL : 400 ≤ Real.log x) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * zeroCoefficient x (adaptiveDelta x * x) ρ‖ <
      0.05 * x / Real.log x :=
  (RS75DecayingHighZeros.norm_high_sum_upper_lt hT hg hx (adaptiveDelta_pos hL)).trans
    (highConstant_budget_lt hx hL)

/-- The same numerical budget for the actual lower quartic high-zero sum. -/
theorem norm_high_sum_lower_lt {T x : ℝ} (hT : 1894439 ≤ T)
    (hg : zetaGoodHeight T) (hx : 1 ≤ x) (hL : 400 ≤ Real.log x) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) *
        zeroCoefficient (x - 4 * (adaptiveDelta x * x)) (adaptiveDelta x * x) ρ‖ <
      0.05 * x / Real.log x :=
  (RS75DecayingHighZeros.norm_high_sum_lower_lt hT hg hx (adaptiveDelta_pos hL)
    (four_adaptiveDelta_lt_one hL)).trans (highConstant_budget_lt hx hL)

end TernaryGoldbach.RSBounds.RS75AdaptiveHighBudget
