import Architect
import PrimeNumberTheoremAnd.Lcm.Base

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real
open scoped BigOperators

namespace Numerical


noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


blueprint_comment /--
\subsection{Numerical inequalities to support PrimeGap -> HA Lcm proof}
-/




/-
Complete structural assumptions:
1. X₀ > 1
2. gap.δ(x) ≥ 0 for x ≥ X₀
3. gap.δ(x) is decreasing for x ≥ X₀
4. √n ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2
    -- equivalent to (1 + gap.δ(√n)) ^ 3 ≤ √n when n, gap.δ(√n) ≥ 0
5. (1 + gap.δ (√n)) ^ 6 < √n for n ≥ X₀ ^ 2, this implies 4. when 1 + gap.δ(√n) ≥ 0
6. 4 * (1 + gap.δ (√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2
7. gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2
8. theorem `prod_epsilon_le`
9. theorem `prod_epsilon_ge`
10. theorem `final_comparison`
-/

class PrimeGap_Criterion where
  h_X₀ : X₀ > 1
  gap_nonneg : ∀ x : ℝ, x ≥ X₀ → 0 ≤ gap.δ x
  gap_decreasing : ∀ x y : ℝ, X₀ ≤ x → X₀ ≤ y → x ≤ y → gap.δ y ≤ gap.δ x
  gap_strict_decreasing: ∀ x y : ℝ, X₀ ≤ x → X₀ ≤ y → x < y → gap.δ y < gap.δ x
  delta_sixth_power_lt_sqrt : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    (1 + gap.δ (√(n : ℝ))) ^ 6 < √(n : ℝ)
  delta_twelfth_power_le_n_pow_3_div_2 : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 ≤ n ^ (3 / 2 : ℝ)
  eps_log_bound : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ)
  prod_epsilon_le : ∀ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ) →
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3
  prod_epsilon_ge : ∀ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 :ℝ) →
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2
  final_comparison : ∀ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ) →
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2
/-- End of structural assumptions -/





lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
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






/- End of theorem `exists_p_primes` lemmas-/














/-
Final criterion structure in Main.lean
-/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 1
  2. gap.δ(x) ≥ 0 for x ≥ X₀
  3. (1 + gap.δ (√n)) ^ 6 < √n for n ≥ X₀ ^ 2
  4. 4 * (1 + gap.δ (√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2
-/






/- `h_crit` lemmas -/


lemma delta_ratio_term_nonneg [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  /- holds when 4 * (1 + gap.δ(√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2 -/
  -- From the criterion we have the basic comparison.
  have h_main :
      4 * (1 + gap.δ (√(n : ℝ))) ^ 12 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
    simpa using (PrimeGap_Criterion.delta_twelfth_power_le_n_pow_3_div_2 (n := n) hn)

  -- The denominator is positive since `n ≥ X₀^2` and `X₀ > 1`.
  have hX0_pos_nat : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hden_pos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hn_pos _

  -- Convert `h_main` into `4*(...)/n^(3/2) ≤ 1`.
  have h_div_le_one :
      4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) ≤ (1 : ℝ) := by
    -- Multiply the inequality `h_main` by the nonnegative inverse of the denominator.
    have h_inv_nonneg : 0 ≤ ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
      inv_nonneg.2 (le_of_lt hden_pos)
    have hmul := mul_le_mul_of_nonneg_right h_main h_inv_nonneg
    have hden_ne : (n : ℝ) ^ (3 / 2 : ℝ) ≠ 0 := ne_of_gt hden_pos
    -- Simplify: `a * d⁻¹ = a / d` and `d * d⁻¹ = 1`.
    have hmul' :
        4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
          ≤ (n : ℝ) ^ (3 / 2 : ℝ) * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
      simpa [div_eq_mul_inv, mul_assoc] using hmul
    simpa [hden_ne] using hmul'

  -- Now rewrite the goal as `t ≤ 1`.
  exact (sub_nonneg).2 h_div_le_one

/- End of `h_crit` lemmas-/

/- Lemmas required to prove h_crit: `theorem main_ineq_delta_form` -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2
  2. X₀ > 0 and n > 0
-/
lemma delta_sqrt_le [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  /- This holds when gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2 -/
  /-- (Cert) Numerical bound on the prime-gap delta at √n: `δ(√n) ≤ 0.000675` for `n ≥ X₀^2`. -/
  /- *** Proof idea (Dusart provider) *** :
  - use the monotonicity of `x ↦ δ(x)` for x ≥ X₀ and the numerical estimate at X₀;
  - convert `hn : n ≥ X₀^2` into `√n ≥ X₀`, then finish by monotonicity + `norm_num`.
  -/
  simpa using (PrimeGap_Criterion.eps_log_bound (n := n) hn)

lemma inv_n_pow_3_div_2_le_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  /- This holds when X₀ > 0 and n > 0 -/
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ X₀`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/X₀)`.
  -/
  have hX0_pos_nat : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    exact_mod_cast hX0_pos_nat

  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos_nat

  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hsqrt_pos : (0 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX0_pos hX0_le_sqrt

  -- Convert `n^(3/2)` to `n * √n`.
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)
  have hpow : (n : ℝ) ^ (3 / 2 : ℝ) = (n : ℝ) * √(n : ℝ) := by
    have h_exp : (3 / 2 : ℝ) = (1 : ℝ) + (1 / 2 : ℝ) := by
      norm_num
    calc
      (n : ℝ) ^ (3 / 2 : ℝ)
          = (n : ℝ) ^ ((1 : ℝ) + (1 / 2 : ℝ)) := by
              simp [h_exp]
      _   = (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
              simpa using (Real.rpow_add hn_pos (1 : ℝ) (1 / 2 : ℝ))
      _   = (n : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
              simp
      _   = (n : ℝ) * √(n : ℝ) := by
              -- `x^(1/2) = √x`.
              simpa using congrArg (fun t => (n : ℝ) * t) (by
                -- `Real.sqrt_eq_rpow` is oriented as `√x = x^(1/2)`.
                simpa using (Real.sqrt_eq_rpow (n : ℝ)).symm)

  -- From `√n ≥ X₀`, take reciprocals.
  have h_inv_sqrt_le : (1 : ℝ) / √(n : ℝ) ≤ (1 : ℝ) / (X₀ : ℝ) := by
    -- `a ≤ b` with `0 < a` gives `1/b ≤ 1/a`.
    simpa [one_div] using (one_div_le_one_div_of_le hX0_pos hX0_le_sqrt)

  have hn_inv_nonneg : 0 ≤ (1 : ℝ) / (n : ℝ) := by
    exact div_nonneg (by norm_num) (le_of_lt hn_pos)

  -- Multiply the reciprocal inequality by `1/n`.
  have hmul : ((1 : ℝ) / (n : ℝ)) * ((1 : ℝ) / √(n : ℝ))
      ≤ ((1 : ℝ) / (n : ℝ)) * ((1 : ℝ) / (X₀ : ℝ)) := by
    exact mul_le_mul_of_nonneg_left h_inv_sqrt_le hn_inv_nonneg

  -- Rewrite both sides into the desired form.
  have h_left : (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
      = ((1 : ℝ) / (n : ℝ)) * ((1 : ℝ) / √(n : ℝ)) := by
    calc
      (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
          = (1 : ℝ) / ((n : ℝ) * √(n : ℝ)) := by
              simp [hpow]
      _   = ((n : ℝ) * √(n : ℝ))⁻¹ := by
              simp [one_div]
      _   = (√(n : ℝ))⁻¹ * (n : ℝ)⁻¹ := by
              simp [mul_inv_rev]
      _   = ((1 : ℝ) / (n : ℝ)) * ((1 : ℝ) / √(n : ℝ)) := by
              -- rearrange the inverses into `1/n * 1/√n`
              simp [one_div, mul_comm]

  have h_right : ((1 : ℝ) / (n : ℝ)) * ((1 : ℝ) / (X₀ : ℝ))
      = (1 / (X₀ : ℝ)) * (1 / n) := by
    -- Commute the product and normalize casts.
    simp [mul_comm, one_div]

  -- Final.
  simpa [h_left, h_right, mul_assoc, mul_left_comm, mul_comm] using hmul



lemma inv_n_add_sqrt_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  /- This holds when X₀ > 0 and n > 0 -/
  /- *** Proof idea *** :
  - from `√n ≥ X₀` deduce `√n ≤ (n:ℝ) / X₀` (since `n = (√n)^2`)
  - so `n + √n ≤ n + n/X₀ = (1+1/X₀)*n`
  - invert both sides (positive) to get the lower bound for `1/(n+√n)`
  -/
  -- Positivity facts.
  have hX0_pos_nat : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
    exact_mod_cast hX0_pos_nat

  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos_nat
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos

  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg (n : ℝ)

  -- Bound `√n` by `n/X₀` using `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have h_mul : (√(n : ℝ)) * (X₀ : ℝ) ≤ (n : ℝ) := by
    -- Multiply `X₀ ≤ √n` by `√n ≥ 0`.
    have hmul' : (X₀ : ℝ) * √(n : ℝ) ≤ √(n : ℝ) * √(n : ℝ) := by
      have := mul_le_mul_of_nonneg_right hX0_le_sqrt hsqrt_nonneg
      -- swap the RHS into `√n * √n`.
      simpa [mul_assoc, mul_comm, mul_left_comm] using this
    -- `√n * √n = n`.
    have hsq : √(n : ℝ) * √(n : ℝ) = (n : ℝ) := by
      simp [Real.mul_self_sqrt hn0]
    -- Commute the LHS and rewrite.
    simpa [mul_comm, mul_left_comm, mul_assoc, hsq] using hmul'

  have hsqrt_le_div : √(n : ℝ) ≤ (n : ℝ) / (X₀ : ℝ) := by
    -- `a ≤ b/c` iff `a*c ≤ b` for `0 < c`.
    exact (le_div_iff₀ hX0_pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h_mul)

  -- Therefore `n + √n ≤ (1 + 1/X₀) * n`.
  have hden_le : (n : ℝ) + √(n : ℝ) ≤ (1 + 1 / (X₀ : ℝ)) * (n : ℝ) := by
    calc
      (n : ℝ) + √(n : ℝ) ≤ (n : ℝ) + (n : ℝ) / (X₀ : ℝ) := by
        nlinarith [hsqrt_le_div]
      _ = (1 + 1 / (X₀ : ℝ)) * (n : ℝ) := by
        ring

  have hden_pos : (0 : ℝ) < (n : ℝ) + √(n : ℝ) :=
    add_pos_of_pos_of_nonneg hn_pos hsqrt_nonneg

  -- Take reciprocals.
  have hrecip : (1 : ℝ) / ((1 + 1 / (X₀ : ℝ)) * (n : ℝ))
      ≤ (1 : ℝ) / ((n : ℝ) + √(n : ℝ)) := by
    -- `a ≤ b` with `0 < a` gives `1/b ≤ 1/a`.
    simpa [one_div] using (one_div_le_one_div_of_le hden_pos hden_le)

  -- Rewrite `1/((1+1/X₀)*n)` as `(1/(1+1/X₀))*(1/n)`.
  have hrew : (1 : ℝ) / ((1 + 1 / (X₀ : ℝ)) * (n : ℝ))
      = (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
    calc
      (1 : ℝ) / ((1 + 1 / (X₀ : ℝ)) * (n : ℝ))
          = ((1 + 1 / (X₀ : ℝ)) * (n : ℝ))⁻¹ := by
              simp [one_div]
      _ = (n : ℝ)⁻¹ * (1 + 1 / (X₀ : ℝ))⁻¹ := by
              simp [mul_inv_rev]
      _ = (1 / (n : ℝ)) * (1 / (1 + 1 / (X₀ : ℝ))) := by
              simp [one_div]
      _ = (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
              ac_rfl

  -- Finish.
  have : (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤ (1 : ℝ) / ((n : ℝ) + √(n : ℝ)) := by
    calc
      (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
          = (1 : ℝ) / ((1 + 1 / (X₀ : ℝ)) * (n : ℝ)) := by
              simpa [hrew] using hrew.symm
      _ ≤ (1 : ℝ) / ((n : ℝ) + √(n : ℝ)) := hrecip
  exact this


theorem main_ineq_delta_form_lhs [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤ (∏ i : Fin 3,
        (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))) := by
      /- This holds when gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2 -/
      /- *** Proof idea *** :
        by applying `delta_sqrt_le` to bound `gap.δ (√(n : ℝ))` by `0.000675` -/
  classical
  have hδ_le : gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := delta_sqrt_le (n := n) hn
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by exact hX0_le_sqrt)
  have hbase_le : (1 + gap.δ (√(n : ℝ))) ≤ (1.000675 : ℝ) := by
    nlinarith [hδ_le]
  have hbase_nonneg : 0 ≤ (1 + gap.δ (√(n : ℝ))) := by
    nlinarith [hδ_nonneg]

  -- Positivity of `n` (since `n ≥ X₀^2` and `X₀ > 1`).
  have hX0_pos : 0 < X₀ := lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat

  -- Compare term-by-term, then use monotonicity of finite products.
  have hterm_le :
      ∀ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))
          ≤ 1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ) := by
    intro i
    have hexp_pos : (0 : ℝ) < ((i : ℕ) + 1 : ℝ) := by
      -- `i+1 ≥ 1` for `i : Fin 3`.
      exact_mod_cast (Nat.succ_pos (i : ℕ))
    have hexp_nonneg : (0 : ℝ) ≤ ((i : ℕ) + 1 : ℝ) := le_of_lt hexp_pos
    have hrpow :
        (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ)
          ≤ (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) := by
      -- monotonicity of `x ↦ x^t` for `t ≥ 0`
      exact Real.rpow_le_rpow hbase_nonneg hbase_le hexp_nonneg
    have hdiv :
        (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)
          ≤ (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ) := by
      have h_inv_nonneg : 0 ≤ (1 / (n : ℝ)) := by
        exact le_of_lt (one_div_pos.mpr hn_pos)
      simpa [div_eq_mul_inv] using (mul_le_mul_of_nonneg_right hrpow h_inv_nonneg)
    -- normalize `a + 1` vs `1 + a`
    simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hdiv 1)

  have hterm_nonneg :
      ∀ i : Fin 3,
        0 ≤ (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)) := by
    intro i
    have hbase_pos : 0 < (1 + gap.δ (√(n : ℝ))) := by
      have h_one_le : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) :=
        le_add_of_nonneg_right hδ_nonneg
      exact lt_of_lt_of_le (by norm_num) h_one_le
    have hexp_pos : 0 < ((i : ℕ) + 1 : ℝ) := by
      exact_mod_cast (Nat.succ_pos (i : ℕ))
    have hrpow_pos :
        0 < (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) :=
      Real.rpow_pos_of_pos hbase_pos _
    have hdiv_nonneg :
        0 ≤ (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ) := by
      exact div_nonneg (le_of_lt hrpow_pos) (le_of_lt hn_pos)
    exact add_nonneg (by norm_num) hdiv_nonneg

  -- Convert the binder-style product to a `Finset.univ` product for `prod_le_prod`.
  simpa using
    (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
      (by
        intro i hi
        simpa using (hterm_nonneg i))
      (by
        intro i hi
        simpa using (hterm_le i)))

theorem main_ineq_delta_form_rhs [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
    ≥ (∏ i : Fin 3,
        (1 + 1 /
          ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
      /- This holds when gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2, X₀ > 0, and n > 0 -/
      /- *** Proof idea ***
      applying `delta_sqrt_le`, `inv_n_add_sqrt_ge_X₀`, and `inv_n_pow_3_div_2_le_X₀` to rewrite
      the inequality
      -/
  classical
  -- Abbreviate `δ = gap.δ(√n)` to keep expressions readable.
  set δ : ℝ := gap.δ (√(n : ℝ)) with hδ

  -- Bounds on `δ`.
  have hδ_le : δ ≤ (0.000675 : ℝ) := by
    simpa [hδ] using (delta_sqrt_le (n := n) hn)
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ δ := by
    have : 0 ≤ gap.δ (√(n : ℝ)) :=
      PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by exact hX0_le_sqrt)
    simpa [hδ] using this

  have hbase_pos : 0 < (1 + δ) := by
    have h_one_le : (1 : ℝ) ≤ 1 + δ := le_add_of_nonneg_right hδ_nonneg
    exact lt_of_lt_of_le (by norm_num) h_one_le
  have hbase_nonneg : 0 ≤ (1 + δ) := le_of_lt hbase_pos
  have hbase_le : (1 + δ) ≤ (1.000675 : ℝ) := by
    nlinarith [hδ_le]

  -- Positivity of `n`.
  have hX0_pos : 0 < X₀ := lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat

  -- Lower bound on `1/(n+√n)`.
  have hinv_add :
      (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) ≤ (1 / ((n : ℝ) + √(n : ℝ))) := by
    -- `inv_n_add_sqrt_ge_X₀` is written using `≥` notation, which is definitionaly `≤` with swapped sides.
    simpa using (inv_n_add_sqrt_ge_X₀ (n := n) hn)

  -- Termwise comparison for the product on the RHS.
  have hterm_le :
      ∀ i : Fin 3,
        (1 + 1 /
            ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ))
          ≤
        (1 + 1 /
            ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))) := by
    intro i
    have ht_nonneg : (0 : ℝ) ≤ (2 * (i : ℕ) + 2 : ℝ) := by
      exact_mod_cast (Nat.zero_le (2 * (i : ℕ) + 2))

    have hpow_le :
        (1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)
          ≤ (1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ) := by
      exact Real.rpow_le_rpow hbase_nonneg hbase_le ht_nonneg
    have hpow_pos :
        0 < (1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) :=
      Real.rpow_pos_of_pos hbase_pos _

    -- Taking reciprocals flips the inequality.
    have hone_div_le :
        (1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ))
          ≤ (1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)) := by
      exact one_div_le_one_div_of_le hpow_pos hpow_le

    have hB_nonneg :
        0 ≤ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
      have hX0r_pos : 0 < (X₀ : ℝ) := by exact_mod_cast hX0_pos
      have h1pos : 0 < (1 + 1 / (X₀ : ℝ)) := by
        have : (0 : ℝ) < 1 / (X₀ : ℝ) := one_div_pos.2 hX0r_pos
        nlinarith
      have hA_nonneg : 0 ≤ (1 / (1 + 1 / (X₀ : ℝ))) := one_div_nonneg.2 (le_of_lt h1pos)
      have hC_nonneg : 0 ≤ (1 / (n : ℝ)) := one_div_nonneg.2 (le_of_lt hn_pos)
      exact mul_nonneg hA_nonneg hC_nonneg

    have hA_nonneg :
        0 ≤ (1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)) :=
      one_div_nonneg.2 (le_of_lt (Real.rpow_pos_of_pos hbase_pos _))

    -- Multiply the two component inequalities.
    have hfrac_le :
        ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
            * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)))
          ≤
        ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ))) * (1 / ((n : ℝ) + √(n : ℝ))) := by
      -- First use the reciprocal comparison, then the bound for `1/(n+√n)`.
      have hstep1 :
          ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
              * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)))
            ≤
          ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)))
              * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))) := by
        exact mul_le_mul_of_nonneg_right hone_div_le hB_nonneg
      have hstep2 :
          ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)))
              * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)))
            ≤
          ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ))) * (1 / ((n : ℝ) + √(n : ℝ))) := by
        exact mul_le_mul_of_nonneg_left hinv_add hA_nonneg
      exact le_trans hstep1 hstep2

    -- Rewrite the RHS product of reciprocals as a single reciprocal of a product.
    have hfrac_le' :
        ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
            * (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
          ≤
        (1 : ℝ) /
          (((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)) * ((n : ℝ) + √(n : ℝ))) := by
      -- reassociate the LHS and simplify the RHS
      have hfrac_le'' :
          ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
              * (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
            ≤
          ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ))) * (1 / ((n : ℝ) + √(n : ℝ))) := by
        simpa [mul_assoc] using hfrac_le
      have hsimpr :
          ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ))) * (1 / ((n : ℝ) + √(n : ℝ)))
            = (1 / ((n : ℝ) + √(n : ℝ))) * ((1 : ℝ) / ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ))) := by
        ac_rfl
      -- clean up associativity on the left
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, hsimpr] using hfrac_le''

    -- Add 1 to both sides.
    have : (1 : ℝ) +
          ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
            * (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))
        ≤ (1 : ℝ) +
            (1 : ℝ) /
              (((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ)) * ((n : ℝ) + √(n : ℝ))) := by
      simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_right hfrac_le' 1)

    -- Match the exact shape.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this

  have hterm_nonneg :
      ∀ i : Fin 3,
        0 ≤ (1 + 1 /
            ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)) := by
    intro i
    have hX0r_pos : 0 < (X₀ : ℝ) := by exact_mod_cast hX0_pos
    have h1pos : 0 < (1 + 1 / (X₀ : ℝ)) := by
      have : (0 : ℝ) < 1 / (X₀ : ℝ) := one_div_pos.2 hX0r_pos
      nlinarith
    have hninv_nonneg : 0 ≤ (1 / (n : ℝ)) := one_div_nonneg.2 (le_of_lt hn_pos)
    have hA_nonneg : 0 ≤ (1 / (1 + 1 / (X₀ : ℝ))) := one_div_nonneg.2 (le_of_lt h1pos)
    have hpow_pos : 0 < (1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ) := by
      have : 0 < (1.000675 : ℝ) := by norm_num
      exact Real.rpow_pos_of_pos this _
    have hB_nonneg : 0 ≤ (1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)) :=
      one_div_nonneg.2 (le_of_lt hpow_pos)
    have hfrac_nonneg :
        0 ≤ ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
              * (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
      have : 0 ≤ ((1 : ℝ) / ((1.000675 : ℝ) ^ (2 * (i : ℕ) + 2 : ℝ)))
                * ((1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ))) := by
        exact mul_nonneg hB_nonneg (mul_nonneg hA_nonneg hninv_nonneg)
      simpa [mul_assoc] using this
    exact add_nonneg (by norm_num)
      (by simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfrac_nonneg)

  -- Product inequality: RHS product ≤ LHS product.
  have hprod_le :
      (∏ i : Fin 3,
          (1 + 1 /
            ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))))) := by
    simpa using
      (Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 3)))
        (by
          intro i hi
          simpa using (hterm_nonneg i))
        (by
          intro i hi
          simpa using (hterm_le i)))

  -- Ratio term inequality: `1 - const ≤ 1 - δterm`.
  have hratio_le :
      (1 - 4 * (1.000675 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)))
        ≤ (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    -- First show `δterm ≤ constTerm`.
    have hpow12_le : (1 + δ) ^ 12 ≤ (1.000675 : ℝ) ^ 12 := by
      exact pow_le_pow_left₀ hbase_nonneg hbase_le 12
    have hden_pos : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := by
      exact Real.rpow_pos_of_pos hn_pos _
    have hstep1 :
        4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
          ≤ 4 * (1.000675 : ℝ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
      have hnum_le : 4 * (1 + δ) ^ 12 ≤ 4 * (1.000675 : ℝ) ^ 12 := by
        exact mul_le_mul_of_nonneg_left hpow12_le (by norm_num)
      have hinv_nonneg : 0 ≤ (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        exact le_of_lt (one_div_pos.mpr hden_pos)
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hnum_le hinv_nonneg)

    have hinv_pow :
        (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
      simpa using (inv_n_pow_3_div_2_le_X₀ (n := n) hn)
    have hconst_nonneg : 0 ≤ (4 * (1.000675 : ℝ) ^ 12) := by
      have : 0 ≤ (1.000675 : ℝ) ^ 12 := pow_nonneg (by norm_num) 12
      nlinarith
    have hstep2 :
        4 * (1.000675 : ℝ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
          ≤ 4 * (1.000675 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)) := by
      -- rewrite `a/d` as `a*(1/d)` and use `hinv_pow`.
      have : 4 * (1.000675 : ℝ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
            = (4 * (1.000675 : ℝ) ^ 12) * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
        simp [div_eq_mul_inv, mul_comm]
      -- multiply `hinv_pow` by the nonnegative constant
      have hmul := mul_le_mul_of_nonneg_left hinv_pow hconst_nonneg
      -- clean up
      simpa [this, mul_assoc, mul_left_comm, mul_comm] using hmul

    have hδterm_le :
        4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
          ≤ 4 * (1.000675 : ℝ) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)) := by
      exact le_trans hstep1 hstep2

    -- `δterm ≤ constTerm` implies `1 - constTerm ≤ 1 - δterm`.
    have := sub_le_sub_left hδterm_le 1
    simpa [sub_eq_add_neg, mul_assoc, mul_left_comm, mul_comm] using this

  -- Nonnegativity of the middle factor and δ-ratio term, needed to multiply inequalities.
  have hmid_nonneg : 0 ≤ (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
    have hden_pos : 0 < (8 * (n : ℝ)) := by nlinarith [hn_pos]
    have hfrac_nonneg : 0 ≤ (3 : ℝ) / (8 * (n : ℝ)) := div_nonneg (by norm_num) (le_of_lt hden_pos)
    exact add_nonneg (by norm_num) hfrac_nonneg
  have hratioδ_nonneg :
      0 ≤ (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    -- provided earlier
    simpa [hδ] using (delta_ratio_term_nonneg (n := n) hn)

  -- Prove the desired inequality as `RHS ≤ LHS` and finish.
  have hRHS_le_LHS :
      (∏ i : Fin 3,
          (1 + 1 /
            ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    -- Multiply the ratio inequality by the nonnegative `Prod_const * Mid`.
    have hprod_const_nonneg :
        0 ≤ (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ))) := by
      simpa using
        (Finset.prod_nonneg (s := (Finset.univ : Finset (Fin 3))) (by
          intro i hi
          simpa using (hterm_nonneg i)))
    have hleft_nonneg :
        0 ≤
          (∏ i : Fin 3,
              (1 + 1 /
                ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
            * (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
      exact mul_nonneg hprod_const_nonneg hmid_nonneg
    have h1 :
        (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)))
          ≤
        (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      have := mul_le_mul_of_nonneg_left hratio_le hleft_nonneg
      simpa [mul_assoc] using this

    -- Multiply the product inequality by the nonnegative `Mid*Ratioδ`.
    have hmr_nonneg :
        0 ≤ (1 + (3 : ℝ) / (8 * (n : ℝ))) *
            (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      exact mul_nonneg hmid_nonneg hratioδ_nonneg
    have h2 :
        (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * ((1 + (3 : ℝ) / (8 * (n : ℝ))) *
            (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)))
          ≤
        (∏ i : Fin 3,
            (1 + 1 /
              ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
          * ((1 + (3 : ℝ) / (8 * (n : ℝ))) *
            (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_right hprod_le hmr_nonneg

    -- Reassociate to match the goal.
    have : (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
          ≤
        (∏ i : Fin 3,
            (1 + 1 /
              ((1 + δ) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1 + δ) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      -- `h2` has `Prod * (Mid*Ratio)` form.
      simpa [mul_assoc] using h2
    exact le_trans h1 this

  -- Replace `δ` back with `gap.δ(√n)` and close.
  simpa [hδ] using hRHS_le_LHS




theorem main_ineq_delta_form [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  /-
   *** Proof outline (exactly your write-up) *** :
  1) Use `main_ineq_delta_form_lhs` to bound the LHS by an expression with
     `0.000675` in place of `gap.δ(√n)`.
  2) Use `main_ineq_delta_form_rhs` to bound the RHS by an expression with
     `0.000675` in place of `gap.δ(√n)`, and `1/(1 + 1/X₀)` and `1/X₀` in place of
     `1/(1 + gap.δ(√n))` and `1/n^(3/2)`, respectively.
  3) Use `delta_prod_mul_nonneg` and `delta_ratio_term_nonneg` to ensure
     the RHS expression is nonnegative.
  4) Set `ε := 1/n` and use the hypotheses `0 ≤ ε` and `ε ≤ 1/(X₀^2)` (derived from `hn`).
  5) Apply `prod_epsilon_le`, `prod_epsilon_ge`, and `final_comparison` to finish.
  -/
  -- Step 0: set ε := 1/n and record bounds on ε from `hn`.
  set ε : ℝ := (1 : ℝ) / (n : ℝ) with hε

  have hX0_pos_nat : 0 < X₀ := lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos

  have hε_nonneg : 0 ≤ ε := by
    rw [hε]
    exact one_div_nonneg.2 hn0

  have hX0_sq_pos : (0 : ℝ) < (X₀ ^ 2 : ℝ) := by
    exact_mod_cast hX0_sq_pos_nat
  have hn_cast : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn

  have hε_le : ε ≤ 1 / (X₀ ^ 2 : ℝ) := by
    have h := one_div_le_one_div_of_le hX0_sq_pos hn_cast
    simpa [hε] using h

  have hε_bounds : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ) := ⟨hε_nonneg, hε_le⟩

  -- Arithmetic identity for the `3/(8*n)` factor.
  have hn_ne : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn_pos_nat)
  have h38 : (3 : ℝ) / 8 * ε = (3 : ℝ) / (8 * (n : ℝ)) := by
    simp [hε, div_eq_mul_inv, mul_left_comm, mul_comm]

  -- Rewrite `onePlusEps_log` to the numerical constant used in the bounds.
  have hone : (onePlusEps_log : ℝ) = (1.000675 : ℝ) := by
    simp [onePlusEps_log, eps_log]
    norm_num

  -- Exponent rewrite: `2*(i+1) = 2*i+2` (as reals), useful for `rpow`.
  have hexp (i : Fin 3) : (2 : ℝ) * ((i : ℕ) + 1 : ℝ) = (2 * (i : ℕ) + 2 : ℝ) := by
    nlinarith

  -- Step 1: bound the original LHS using `main_ineq_delta_form_lhs`.
  have hLHS_bound :
      (∏ i : Fin 3,
          (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))) :=
    main_ineq_delta_form_lhs (n := n) hn

  -- Step 2: bound the original RHS from below using `main_ineq_delta_form_rhs`.
  have hRHS_bound :
      (∏ i : Fin 3,
          (1 + 1 /
            ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
    simpa [ge_iff_le, mul_assoc, mul_left_comm, mul_comm] using
      (main_ineq_delta_form_rhs (n := n) hn)

  -- Step 4/5: compare the bounded LHS and bounded RHS using the `ε`-lemmas.
  have hLHS_poly :
      (∏ i : Fin 3,
          (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
    have h := PrimeGap_Criterion.prod_epsilon_le (ε := ε) hε_bounds
    simpa [hε, hone, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

  have hpoly_poly :
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤
        1 + 3.36683 * ε - 0.01 * ε ^ 2 :=
    PrimeGap_Criterion.final_comparison (ε := ε) hε_bounds

  have hpoly_RHS :
      1 + 3.36683 * ε - 0.01 * ε ^ 2 ≤
        (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
    have h := PrimeGap_Criterion.prod_epsilon_ge (ε := ε) hε_bounds
    have h' :
        1 + 3.36683 * ε - 0.01 * ε ^ 2 ≤
          (∏ i : Fin 3,
              (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1 / X₀)))) *
            (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) := by
      simpa [ge_iff_le] using h
    simpa [hε, hone, hexp, h38, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'

  have hLHS_RHSconst :
      (∏ i : Fin 3,
          (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
        (∏ i : Fin 3,
            (1 + 1 /
              ((1.000675) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
          * (1 + (3 : ℝ) / (8 * (n : ℝ)))
          * (1 - 4 * (1.000675) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
    exact le_trans (le_trans hLHS_poly hpoly_poly) hpoly_RHS

  -- Step 6: chain the three inequalities.
  exact le_trans (le_trans hLHS_bound hLHS_RHSconst) hRHS_bound

/- End of lemmas required to prove h_crit: `theorem main_ineq_delta_form` -/


/--
Provide the concrete instance at the end of this file.
Fill in each field using the corresponding proofs for your chosen `gap` and `X₀`.
-/

theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith


theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]


theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith



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
      eps_log_bound := ?_,
      prod_epsilon_le := by
        intro ε hε
        exact prod_epsilon_le hε,
      prod_epsilon_ge := by
        intro ε hε
        exact prod_epsilon_ge hε,
      final_comparison := by
        intro ε hε
        exact final_comparison hε }
  all_goals
    sorry






end Numerical

end Lcm
