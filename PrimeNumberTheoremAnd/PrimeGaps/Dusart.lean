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

/- TO-DO: Some of the lemmas, especially the theorem comparison ones
    can probably be made more elegant by using `Real.rpow` lemmas
    instead of unfolding the definition each time.  -/
lemma h_X₀ : X₀ > 1 := by norm_num [X₀]

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

lemma δ_strictly_decreasing {x y : ℝ}
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



lemma delta_sixth_power_lt_sqrt {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (δ (√(n : ℝ))) ^ (6 : ℝ) < Real.sqrt (n : ℝ) := by
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  -- `√n` is positive (needed to use `lt_log_iff_exp_lt`).
  have hn_pos_nat : 0 < n := by
    have hX0_pos : 0 < X₀ := by
      norm_num [X₀]
    have hX0sq_pos : 0 < X₀ ^ 2 := by
      exact pow_pos hX0_pos _
    exact lt_of_lt_of_le hX0sq_pos hn
  have hsqrt_pos : 0 < √(n : ℝ) := by
    have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_pos_nat
    simpa [Real.sqrt_eq_rpow] using (Real.rpow_pos_of_pos hn_pos (1 / 2 : ℝ))

  -- Show `δ(√n) < 1` by proving `1 < log(√n)`.
  have h3_le_X0 : (3 : ℝ) ≤ (X₀ : ℝ) := by
    norm_num [X₀]
  have h3_le_sqrt : (3 : ℝ) ≤ √(n : ℝ) :=
    le_trans h3_le_X0 hX0_le_sqrt
  have hexp1_lt3 : Real.exp (1 : ℝ) < (3 : ℝ) := by
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp1_lt_sqrt : Real.exp (1 : ℝ) < √(n : ℝ) :=
    lt_of_lt_of_le hexp1_lt3 h3_le_sqrt
  have hlog_gt1 : (1 : ℝ) < Real.log (√(n : ℝ)) := by
    -- `a < log b` iff `exp a < b` when `0 < b`.
    simpa using (Real.lt_log_iff_exp_lt hsqrt_pos).2 hexp1_lt_sqrt

  have hlog_pow_gt1 : (1 : ℝ) < (Real.log (√(n : ℝ))) ^ (3 : ℝ) := by
    have hone_nonneg : (0 : ℝ) ≤ (1 : ℝ) := by norm_num
    have h3pos : (0 : ℝ) < (3 : ℝ) := by norm_num
    have : (1 : ℝ) ^ (3 : ℝ) < (Real.log (√(n : ℝ))) ^ (3 : ℝ) :=
      Real.rpow_lt_rpow hone_nonneg hlog_gt1 h3pos
    simpa using this

  have hδ_lt1 : δ (√(n : ℝ)) < 1 := by
    have : (1 : ℝ) / ((Real.log (√(n : ℝ))) ^ (3 : ℝ)) < (1 : ℝ) := by
      -- `1 < a` with `0 < 1` gives `1/a < 1`.
      simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hlog_pow_gt1)
    simpa [δ] using this

  have hδ_nonneg : 0 ≤ δ (√(n : ℝ)) := by
    exact δ_nonneg hX0_le_sqrt

  have hδ_pow_lt1 : (δ (√(n : ℝ))) ^ (6 : ℕ) < (1 : ℝ) := by
    have hpow : (δ (√(n : ℝ))) ^ (6 : ℕ) < (1 : ℝ) ^ (6 : ℕ) := by
      exact pow_lt_pow_left₀ hδ_lt1 hδ_nonneg (n := 6) (by decide)
    simpa using hpow

  -- Finally, `1 < √n` since `X₀ > 1` and `X₀ ≤ √n`.
  have hsqrt_gt1 : (1 : ℝ) < Real.sqrt (n : ℝ) := by
    have h1_lt_X0 : (1 : ℝ) < (X₀ : ℝ) := by
      norm_num [X₀]
    exact lt_of_lt_of_le h1_lt_X0 hX0_le_sqrt

  have : (δ (√(n : ℝ))) ^ (6 : ℕ) < Real.sqrt (n : ℝ) :=
    lt_trans hδ_pow_lt1 hsqrt_gt1
  simpa [Real.rpow_natCast] using this



lemma delta_twelfth_power_le_n_pow_3_div_2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
     4 * (1 + δ (√(n : ℝ))) ^ 12 ≤ (n : ℝ) ^ (3 / 2 : ℝ) := by
  /- given that delta is 1/log^3(x) so is monotone,
  the proof should reduce to compare the values at X₀
  -/
   sorry


/- Lemmas to prove the final criterion theorem main_ineq_delta_form -/


noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


/- `main_ineq_delta_form_lhs` `main_ineq_delta_form_rhs` sub-lemmas -/
lemma eps_log_bound {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  -- First turn `hn : n ≥ X₀^2` into `X₀ ≤ √n`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := by
    have hn' : (X₀ ^ 2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hsqrt : √(X₀ ^ 2 : ℝ) ≤ √(n : ℝ) := by
      exact Real.sqrt_le_sqrt hn'
    have hX0_nonneg : (0 : ℝ) ≤ (X₀ : ℝ) := by
      exact_mod_cast (Nat.zero_le X₀)
    -- `√(X₀^2) = X₀` since `X₀ ≥ 0`.
    simpa [Nat.cast_pow, Real.sqrt_sq_eq_abs, abs_of_nonneg hX0_nonneg] using hsqrt

  -- Monotonicity: δ is strictly decreasing for `x ≥ X₀`, so δ(√n) ≤ δ(X₀).
  have hδ_le_δX0 : δ (√(n : ℝ)) ≤ δ (X₀ : ℝ) := by
    rcases lt_or_eq_of_le hX0_le_sqrt with hlt | heq
    · have hlt' : δ (√(n : ℝ)) < δ (X₀ : ℝ) := by
        -- Apply strict decreasingness with `x = X₀`, `y = √n`.
        simpa using
          (δ_strictly_decreasing (x := (X₀ : ℝ)) (y := √(n : ℝ))
            (by rfl) (by simpa using hX0_le_sqrt) hlt)
      exact le_of_lt hlt'
    · simp [δ, heq.symm]

  -- Numerical bound at `X₀`: δ(X₀) ≤ 0.000675.
  have hlog_X0_gt : (11.4 : ℝ) < Real.log (X₀ : ℝ) := by
    have hX0_pos : (0 : ℝ) < (X₀ : ℝ) := by
      norm_num [X₀]
    have h5pos : (0 : ℝ) < (5 : ℝ) := by
      norm_num
    have h57_lt : (57 : ℝ) < (5 : ℝ) * Real.log (X₀ : ℝ) := by
      -- Rewrite the RHS as `log (X₀^5)` and compare via `exp`.
      have h57_lt_log : (57 : ℝ) < Real.log ((X₀ : ℝ) ^ (5 : ℕ)) := by
        have hpos : (0 : ℝ) < ((X₀ : ℝ) ^ (5 : ℕ)) := by
          exact pow_pos hX0_pos _
        refine (Real.lt_log_iff_exp_lt hpos).2 ?_
        -- Reduce to a numerical inequality using `exp 1 < 2.7182818286`.
        have hpow_lt : Real.exp (1 : ℝ) ^ (57 : ℕ) < (2.7182818286 : ℝ) ^ (57 : ℕ) := by
          exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos (1 : ℝ)).le (n := 57) (by decide)
        have hnum : (2.7182818286 : ℝ) ^ (57 : ℕ) < ((X₀ : ℝ) ^ (5 : ℕ)) := by
          norm_num [X₀]
        have : Real.exp (1 : ℝ) ^ (57 : ℕ) < ((X₀ : ℝ) ^ (5 : ℕ)) := lt_trans hpow_lt hnum
        simpa [Real.exp_one_pow] using this
      -- Expand `log (X₀^5)`.
      simpa [Real.log_pow, hX0_pos.ne', mul_comm, mul_left_comm, mul_assoc] using h57_lt_log
    have hdiv : (57 : ℝ) / (5 : ℝ) < Real.log (X₀ : ℝ) := by
      exact (div_lt_iff₀ h5pos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using h57_lt)
    have h114 : (11.4 : ℝ) = (57 : ℝ) / (5 : ℝ) := by
      norm_num
    simpa [h114] using hdiv

  have hδX0_le : δ (X₀ : ℝ) ≤ (0.000675 : ℝ) := by
    -- Rewrite δ in terms of a natural power.
    have h11_pos : (0 : ℝ) < (11.4 : ℝ) := by norm_num
    have h11_pow_pos : (0 : ℝ) < (11.4 : ℝ) ^ (3 : ℕ) := by
      exact pow_pos h11_pos _
    have hpow_lt : (11.4 : ℝ) ^ (3 : ℕ) < (Real.log (X₀ : ℝ)) ^ (3 : ℕ) := by
      have h11_nonneg : (0 : ℝ) ≤ (11.4 : ℝ) := by norm_num
      exact pow_lt_pow_left₀ hlog_X0_gt h11_nonneg (n := 3) (by decide)
    have hone_div_lt : (1 : ℝ) / (Real.log (X₀ : ℝ)) ^ (3 : ℕ)
        < (1 : ℝ) / (11.4 : ℝ) ^ (3 : ℕ) := by
      simpa [one_div] using (one_div_lt_one_div_of_lt h11_pow_pos hpow_lt)
    have hone_div_le : (1 : ℝ) / (11.4 : ℝ) ^ (3 : ℕ) ≤ (0.000675 : ℝ) := by
      norm_num
    -- Combine.
    have : (1 : ℝ) / (Real.log (X₀ : ℝ)) ^ (3 : ℕ) ≤ (0.000675 : ℝ) :=
      le_trans (le_of_lt hone_div_lt) hone_div_le
    simpa [δ, Real.rpow_natCast] using this

  exact le_trans hδ_le_δX0 hδX0_le

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
    sorry

lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
    sorry

/- End of `main_ineq_delta_form_lhs` `main_ineq_delta_form_rhs` sub-lemmas -/

lemma main_ineq_delta_form_lhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤ (∏ i : Fin 3,
        (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))) := by
    /- *** Proof idea ***
    We use lemma eps_log_bound to bound δ(√n) by 0.000675,
    and then compare term-by-term in the product (use positivity of all terms).
    -/
    sorry


lemma main_ineq_delta_form_rhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
    ≥ (∏ i : Fin 3,
        (1 + 1 /
          ((onePlusEps_log) ^ (2 * (i : ℕ) + 2 : ℝ)) * 1 / (1 + 1 / (X₀ : ℝ)) * 1 / (n : ℝ)))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (onePlusEps_log) ^ 12 * (1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
    /- *** Proof idea ***
    Compare term-by-term in the product using positivity of all terms
      · first term is positive since δ is nonnegative (δ_nonneg)
      · second term is obvious positive
      · third term is positive using delta_twelfth_power_le_n_pow_3_div_2
    First term uses eps_log_bound and inv_n_add_sqrt_ge_X₀ to bound δ(√n) by 0.000675
    Last term uses delta_twelfth_power_le_n_pow_3_div_2 and inv_n_pow_3_div_2_le_X₀ to bound
      4 * (1 + δ(√n))^12 / n^(3/2) by 4 * (1 + 0.000675)^12 * 1 / (X₀ : ℝ) * 1 / (n : ℝ)
    -/
    sorry


lemma prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith


lemma prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]

lemma final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith

theorem main_ineq_delta_form {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
          (1 + (1 + δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
        ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
        * (1 + (3 : ℝ) / (8 * (n : ℝ)))
        * (1 - 4 * (1 + δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
  /- *** Proof idea ***
    We bound the LHS from above (main_ineq_delta_form_lhs)
    and the RHS from below (main_ineq_delta_form_rhs),
    then reduce to comparing polynomials in ε = 1/n,
    which is done via prod_epsilon_le, prod_epsilon_ge, and final_comparison.
  -/
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
  h_X₀ := by exact h_X₀
  δ_nonneg := by
    intro x hx
    exact δ_nonneg hx
  δ_strictly_decreasing := by
    intro x y hx hy hxy
    exact δ_strictly_decreasing hx hy hxy
  delta_sixth_power_lt_sqrt := by
    intro n hn
    exact delta_sixth_power_lt_sqrt hn
  delta_twelfth_power_le_n_pow_3_div_2 := by
    intro n hn
    exact delta_twelfth_power_le_n_pow_3_div_2 hn
  delta_ineq := by
    intro n hn
    exact main_ineq_delta_form hn
  prime_in_Icc := by
    intro x hx
    exact prime_in_Icc (x := x) hx }

end Dusart
end PrimeGaps
