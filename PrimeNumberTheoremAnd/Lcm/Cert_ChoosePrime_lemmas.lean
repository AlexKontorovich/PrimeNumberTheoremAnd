import Architect
import PrimeNumberTheoremAnd.Lcm.Cert

namespace Lcm
namespace ChoosePrime_lemmas

open Finset Nat Real
open scoped BigOperators



class PrimeGap_Criterion where
  h_X₀ : X₀ > 1
  gap_nonneg : ∀ x : ℝ, x ≥ X₀ → 0 ≤ gap.δ x
  gap_decreasing : ∀ x y : ℝ, X₀ ≤ x → X₀ ≤ y → x ≤ y → gap.δ y ≤ gap.δ x
  gap_strict_decreasing: ∀ x y : ℝ, X₀ ≤ x → X₀ ≤ y → x < y → gap.δ y < gap.δ x
  delta_sixth_power_lt_sqrt : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    (1 + gap.δ (√(n : ℝ))) ^ 6 < √(n : ℝ)
  delta_twelfth_power_le_n_pow_3_div_2 : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 ≤ n ^ (3 / 2 : ℝ)
/-- End of structural assumptions -/

/- theorem `exists_p_primes` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ ≥ 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
  3. gap.δ is decreasing for x ≥ X₀
-/

lemma sqrt_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  /- holds when X₀ ≥ 0 -/
  have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
    exact Real.sqrt_le_sqrt hn'
  have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
    exact_mod_cast (Nat.zero_le X₀)
  -- `√(X₀^2) = X₀` since `X₀ ≥ 0`.
  simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

lemma step1_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  /- holds when X₀ ≥ 0 and gap.δ(√n) ≥ 0 for n ≥ X₀^2 -/
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by exact hX0_le_sqrt)
  have h_one_le : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) := by
    exact le_add_of_nonneg_right hδ_nonneg
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := by
    exact Real.sqrt_nonneg (n : ℝ)
  have hsqrt_le : √(n : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) := by
    have := mul_le_mul_of_nonneg_left h_one_le hsqrt_nonneg
    simpa [mul_one] using this
  exact le_trans hX0_le_sqrt hsqrt_le



lemma step2_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  /- holds when X₀ ≥ 0 and gap.δ(√n) ≥ 0 for n ≥ X₀^2 -/
  have hX0_le_sqrt : (X₀ : ℝ) ≤ Real.sqrt (n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (Real.sqrt (n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := Real.sqrt (n : ℝ)) (by simpa using hX0_le_sqrt)
  have h_one_le : (1 : ℝ) ≤ 1 + gap.δ (Real.sqrt (n : ℝ)) := by
    exact le_add_of_nonneg_right hδ_nonneg
  have h0_one_add : (0 : ℝ) ≤ 1 + gap.δ (Real.sqrt (n : ℝ)) := by
    -- since `1 ≤ 1 + δ`
    exact le_trans (by norm_num) h_one_le
  have h_one_le_sq : (1 : ℝ) ≤ (1 + gap.δ (Real.sqrt (n : ℝ))) ^ 2 := by
    -- `1 ≤ a` implies `1 ≤ a^2`
    have h_a_le_a2 : (1 + gap.δ (Real.sqrt (n : ℝ))) ≤ (1 + gap.δ (Real.sqrt (n : ℝ))) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h_one_le h0_one_add
      -- `1 * a ≤ a * a`
      simpa [pow_two] using this
    exact le_trans h_one_le h_a_le_a2
  have hsqrt_nonneg : 0 ≤ Real.sqrt (n : ℝ) := by
    exact Real.sqrt_nonneg (n : ℝ)
  have hsqrt_le : Real.sqrt (n : ℝ) ≤ Real.sqrt (n : ℝ) * (1 + gap.δ (Real.sqrt (n : ℝ))) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h_one_le_sq hsqrt_nonneg
    simpa [mul_one, mul_assoc] using this
  exact le_trans hX0_le_sqrt hsqrt_le


lemma step1_upper [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  /- holds when x, ε ≥ 0 and gap.δ(x * (1 + gap.δ(x))) ≤ gap.δ(x)-/
  /- this holds when gap.δ is decreasing for x ≥ X₀ -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  -- Rewrite the goal in terms of `x` and `ε`.
  -- (After this, the goal is exactly the displayed inequality.)
  -- simp [hx.symm, hε.symm]
  simp only [ge_iff_le]

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x := PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg

  have hx_nonneg : 0 ≤ x := by
    -- `x = √n`
    simpa only [hx] using (Real.sqrt_nonneg (n : ℝ))

  have h_one_add_nonneg : 0 ≤ 1 + ε := by
    exact add_nonneg (by norm_num) hε_nonneg

  have hx_le_y : x ≤ x * (1 + ε) := by
    have := mul_le_mul_of_nonneg_left h_one_le hx_nonneg
    simpa [mul_one, mul_assoc] using this

  have hX0_le_y : (X₀ : ℝ) ≤ x * (1 + ε) := le_trans hX0_le_x hx_le_y

  have hδy_le_δx : gap.δ (x * (1 + ε)) ≤ gap.δ x :=
    PrimeGap_Criterion.gap_decreasing x (x * (1 + ε)) hX0_le_x hX0_le_y hx_le_y

  have hδy_le_ε : gap.δ (x * (1 + ε)) ≤ ε := by
    simpa [hε.symm] using hδy_le_δx

  have h_one_add_le : 1 + gap.δ (x * (1 + ε)) ≤ 1 + ε := by
    simpa [add_comm] using (add_le_add_left hδy_le_ε 1)

  have hmul_nonneg : 0 ≤ x * (1 + ε) := by
    exact mul_nonneg hx_nonneg h_one_add_nonneg

  have hmul : (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ (x * (1 + ε)) * (1 + ε) := by
    exact mul_le_mul_of_nonneg_left h_one_add_le hmul_nonneg

  -- Finish by simplifying the right-hand side.
  simpa [pow_two, mul_assoc] using hmul


lemma step2_upper [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  /- holds when x, ε ≥ 0 and gap.δ(x * (1 + gap.δ(x)) ^ 2) ≤ gap.δ(x) -/
  /- this holds when gap.δ is decreasing for x ≥ X₀ -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  -- Rewrite the goal in terms of `x` and `ε`.
  simp only [ge_iff_le]

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x := PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg

  have hx_nonneg : 0 ≤ x := by
    simp [hx]

  have h_one_add_nonneg : 0 ≤ 1 + ε := by
    exact add_nonneg (by norm_num) hε_nonneg

  -- Show `1 ≤ (1+ε)^2`.
  have h_one_le_sq : (1 : ℝ) ≤ (1 + ε) ^ 2 := by
    have h_a_le_a2 : (1 + ε) ≤ (1 + ε) ^ 2 := by
      have := mul_le_mul_of_nonneg_right h_one_le h_one_add_nonneg
      simpa [pow_two] using this
    exact le_trans h_one_le h_a_le_a2

  have hx_le_y : x ≤ x * (1 + ε) ^ 2 := by
    have := mul_le_mul_of_nonneg_left h_one_le_sq hx_nonneg
    simpa [mul_one, mul_assoc] using this

  have hX0_le_y : (X₀ : ℝ) ≤ x * (1 + ε) ^ 2 := le_trans hX0_le_x hx_le_y

  have hδy_le_δx : gap.δ (x * (1 + ε) ^ 2) ≤ gap.δ x :=
    PrimeGap_Criterion.gap_decreasing x (x * (1 + ε) ^ 2) hX0_le_x hX0_le_y hx_le_y

  have hδy_le_ε : gap.δ (x * (1 + ε) ^ 2) ≤ ε := by
    simpa [hε.symm] using hδy_le_δx

  have h_one_add_le : 1 + gap.δ (x * (1 + ε) ^ 2) ≤ 1 + ε := by
    simpa [add_comm] using (add_le_add_left hδy_le_ε 1)

  have hmul_nonneg : 0 ≤ x * (1 + ε) ^ 2 := by
    exact mul_nonneg hx_nonneg (sq_nonneg (1 + ε))

  have hmul :
      (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2))
        ≤ (x * (1 + ε) ^ 2) * (1 + ε) := by
    exact mul_le_mul_of_nonneg_left h_one_add_le hmul_nonneg

  -- Simplify the RHS: `(x*(1+ε)^2)*(1+ε) = x*(1+ε)^3`.
  simpa [pow_succ, mul_assoc] using hmul

/- End of theorem `exists_p_primes` lemmas-/

instance : PrimeGap_Criterion := by
  refine
    { h_X₀ := by norm_num,
      gap_nonneg := by
        intro x hx
        exact gap.δ_nonneg hx,
      gap_decreasing := ?_,
      gap_strict_decreasing := ?_,
      delta_sixth_power_lt_sqrt := ?_,
      delta_twelfth_power_le_n_pow_3_div_2 := ?_,
      }
  all_goals
    sorry



end ChoosePrime_lemmas
end Lcm
