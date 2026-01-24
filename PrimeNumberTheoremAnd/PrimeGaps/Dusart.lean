import PrimeNumberTheoremAnd.PrimeGaps.Provider
import PrimeNumberTheoremAnd.Dusart
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

namespace PrimeGaps
namespace Dusart

abbrev X₀ : ℕ := 89693
@[simp] lemma X₀_eq : X₀ = 89693 := rfl

noncomputable abbrev δ (x : ℝ) : ℝ := 1 / (Real.log x) ^ (3 : ℝ)
@[simp] lemma δ_def (x : ℝ) : δ x = 1 / (Real.log x) ^ (3 : ℝ) := rfl

lemma δ_nonneg {x : ℝ} (hx : (X₀ : ℝ) ≤ x) : 0 ≤ δ x := by
  have hx1 : (1 : ℝ) ≤ x := by
    have hX₀ : (1 : ℝ) ≤ (X₀ : ℝ) := by
      norm_num [X₀]
    exact le_trans hX₀ hx
  have hlog : 0 ≤ Real.log x := by
    exact Real.log_nonneg hx1
  have hpow : 0 ≤ (Real.log x) ^ (3 : ℝ) := by
    exact Real.rpow_nonneg hlog _
  have hδ : 0 ≤ (1 : ℝ) / (Real.log x) ^ (3 : ℝ) := by
    exact div_nonneg (by exact zero_le_one) hpow
  simpa [δ] using hδ

theorem gap_strictly_decreasing {x y : ℝ}
    (hx : (X₀ : ℝ) ≤ x) (hy : (X₀ : ℝ) ≤ y) (hxy : x < y) :
    δ y < δ x := by
  have hX0_gt1 : (1 : ℝ) < (X₀ : ℝ) := by
    norm_num [X₀]
  have hx_gt1 : (1 : ℝ) < x := lt_of_lt_of_le hX0_gt1 hx
  have hy_gt1 : (1 : ℝ) < y := lt_of_lt_of_le hX0_gt1 hy

  have hx_pos : 0 < x := lt_trans (by norm_num) hx_gt1
  have hlog_lt : Real.log x < Real.log y := Real.log_lt_log hx_pos hxy

  have hlogx_pos : 0 < Real.log x := Real.log_pos hx_gt1
  have hpow_lt : (Real.log x) ^ (3 : ℝ) < (Real.log y) ^ (3 : ℝ) := by
    exact Real.rpow_lt_rpow hlogx_pos.le hlog_lt (by norm_num)
  have hpowx_pos : 0 < (Real.log x) ^ (3 : ℝ) :=
    Real.rpow_pos_of_pos hlogx_pos _

  -- `a < b` with `0 < a` gives `1/b < 1/a`.
  have hdiv : (1 : ℝ) / (Real.log y) ^ (3 : ℝ) < (1 : ℝ) / (Real.log x) ^ (3 : ℝ) := by
    simpa [one_div] using (one_div_lt_one_div_of_lt hpowx_pos hpow_lt)
  simpa [δ, one_div] using hdiv


theorem delta_sixth_power_lt_sqrt {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    δ x ^ (6 : ℝ) < Real.sqrt x := by
  have hx_ge3 : (3 : ℝ) ≤ x := by
    have hX₀_ge3 : (3 : ℝ) ≤ (X₀ : ℝ) := by
      norm_num [X₀]
    exact le_trans hX₀_ge3 hx

  have hx_pos : 0 < x := by linarith

  have hlog_gt_one : 1 < Real.log x := by
    refine (Real.lt_log_iff_exp_lt hx_pos).mpr ?_
    have hexp1_lt3 : Real.exp (1 : ℝ) < 3 := by
      simpa using Real.exp_one_lt_three
    exact lt_of_lt_of_le hexp1_lt3 hx_ge3

  have hlog_pow_gt_one : 1 < (Real.log x) ^ (3 : ℝ) := by
    have : (1 : ℝ) ^ (3 : ℝ) < (Real.log x) ^ (3 : ℝ) := by
      exact Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ 1) hlog_gt_one (by norm_num)
    simpa using this

  have hδ_lt_one : δ x < 1 := by
    have : (1 : ℝ) / (Real.log x) ^ (3 : ℝ) < (1 : ℝ) / (1 : ℝ) := by
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hlog_pow_gt_one)
    simpa [δ] using this

  have hδ_nonneg : 0 ≤ δ x := δ_nonneg (x := x) hx

  have hδ_pow_lt_one : δ x ^ (6 : ℝ) < 1 := by
    have : δ x ^ (6 : ℝ) < (1 : ℝ) ^ (6 : ℝ) :=
      Real.rpow_lt_rpow hδ_nonneg hδ_lt_one (by norm_num)
    simpa using this

  have hsqrt_gt_one : 1 < Real.sqrt x := by
    have hx_gt_one : (1 : ℝ) < x := by
      have hX₀_gt_one : (1 : ℝ) < (X₀ : ℝ) := by
        norm_num [X₀]
      exact lt_of_lt_of_le hX₀_gt_one hx
    rw [Real.lt_sqrt]
    · simpa using hx_gt_one
    · linarith

  exact lt_trans hδ_pow_lt_one hsqrt_gt_one

theorem delta_twelfth_power_le_n_pow_3_div_2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + δ (√(n : ℝ))) ^ 12 ≤ n ^ (3 / 2 : ℝ) := by
    sorry




theorem prime_in_Icc {x : ℝ} (hx : (X₀ : ℝ) ≤ x) :
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ x * (1 + δ x) := by
  have hx' : x ≥ (89693 : ℝ) := by simpa [X₀] using hx
  rcases (_root_.Dusart.proposition_5_4 x hx') with ⟨p, hp, hxp, hpU⟩
  refine ⟨p, hp, hxp, ?_⟩
  simpa [δ, mul_add, mul_one, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hpU




noncomputable def provider : PrimeGaps.Provider :=
{ X₀ := X₀
  δ := δ
  δ_nonneg := by
    intro x hx
    exact δ_nonneg hx
  prime_in_Icc := by
    intro x hx
    exact prime_in_Icc (x := x) hx }

end Dusart
end PrimeGaps
