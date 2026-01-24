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
  delta_ineq : ∀ n : ℕ, n ≥ X₀ ^ 2 →
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ))
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


/- theorem `exists_q_primes` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. √n ≤ n / (1 + gap.δ(√n)) ^ 3
  2. gap.δ is decreasing for x ≥ X₀
  3. gap.δ(x) ≥ 0 for x ≥ X₀
-/
lemma y0_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
  /- this holds when X₀ ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2 -/
  /- and this is automatically true if we can show a stronger version, which would be helpful for the following lemmas
   i.e. √n ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2
  -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    -- `x = √n` and `n ≥ X₀^2`.
    simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg

  have h_one_add_pos : (0 : ℝ) < 1 + ε := by
    exact lt_of_lt_of_le (by norm_num) h_one_le

  have hx_nonneg : 0 ≤ x := by
    simp [hx]

  -- From the criterion: `(1 + δ(√n))^6 < √n`.
  have h6 : (1 + ε) ^ 6 < x := by
    simpa [hx, hε] using (PrimeGap_Criterion.delta_sixth_power_lt_sqrt (n := n) hn)

  -- Since `1 ≤ 1+ε`, we have `(1+ε)^3 ≤ (1+ε)^6`.
  have hpow3_le_pow6 : (1 + ε) ^ 3 ≤ (1 + ε) ^ 6 := by
    exact pow_le_pow_right₀ h_one_le (by decide)

  have hpow3_le_x : (1 + ε) ^ 3 ≤ x := by
    exact le_of_lt (lt_of_le_of_lt hpow3_le_pow6 h6)

  -- Stronger intermediate bound: `x ≤ n / (1+ε)^3`.
  have hx_le_y0 : x ≤ (n : ℝ) / (1 + ε) ^ 3 := by
    have hden_pos : 0 < (1 + ε) ^ 3 := by
      exact pow_pos h_one_add_pos 3
    -- Use `le_div_iff` and prove `x * (1+ε)^3 ≤ n`.
    have hx_mul : x * (1 + ε) ^ 3 ≤ x * x := by
      have := mul_le_mul_of_nonneg_left hpow3_le_x hx_nonneg
      simpa [mul_assoc] using this
    have hx_sq : x * x = (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      -- `x = √n`, so `x*x = (√n)^2 = n`.
      -- We go through `Real.sq_sqrt`.
      simp [hx]
    have hx_mul' : x * (1 + ε) ^ 3 ≤ (n : ℝ) := by
      simpa [hx_sq] using hx_mul
    exact (le_div_iff₀ hden_pos).2 hx_mul'

  exact le_trans hX0_le_x hx_le_y0


lemma y1_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  /- Derived from `y0_ge_X₀` plus the fact that dividing by `(1+ε)^2` is larger than
     dividing by `(1+ε)^3` when `1+ε ≥ 1`. -/
  /- This holds when gap.δ(x) ≥ 0 for x ≥ X₀ -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hX0_le_y0 : (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
    -- `y0_ge_X₀` is written with the same `x`/`ε` definitions.
    simpa [hx, hε] using (y0_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have hX0_le_x : (X₀ : ℝ) ≤ x := by
      simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg
  have h_one_add_pos : (0 : ℝ) < 1 + ε := by
    exact lt_of_lt_of_le (by norm_num) h_one_le

  -- `n/(1+ε)^3 ≤ n/(1+ε)^2` since dividing by an extra positive factor decreases the value.
  have hy0_le_y1 : (n : ℝ) / (1 + ε) ^ 3 ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    have h_nonneg : (0 : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
      -- numerator is nonneg and denominator positive
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      have hpow_pos : (0 : ℝ) < (1 + ε) ^ 2 := by
        exact pow_pos h_one_add_pos 2
      exact div_nonneg hn0 (le_of_lt hpow_pos)
    have h_div_le : ((n : ℝ) / (1 + ε) ^ 2) / (1 + ε) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
      -- `div_le_self` is `a / b ≤ a` when `0 ≤ a` and `1 ≤ b`.
      simpa using (div_le_self h_nonneg h_one_le)
    have hrewrite : ((n : ℝ) / (1 + ε) ^ 2) / (1 + ε) = (n : ℝ) / (1 + ε) ^ 3 := by
      -- `(a/b)/c = a/(b*c)` and `a^3 = a^2*a`.
      simp [div_div, pow_succ, mul_assoc]
    -- Replace the left-hand side by `n/(1+ε)^3`.
    simpa [hrewrite] using h_div_le

  exact le_trans hX0_le_y0 hy0_le_y1

lemma y2_ge_X₀ [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) := by
  /- Same pattern as `y1_ge_X₀`: `n/(1+ε) ≥ n/(1+ε)^2`. -/
  /- This holds when gap.δ(x) ≥ 0 for x ≥ X₀ -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε

  have hX0_le_y1 : (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    simpa [hx, hε] using (y1_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have hX0_le_x : (X₀ : ℝ) ≤ x := by
      simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg
  have h_one_add_pos : (0 : ℝ) < 1 + ε := by
    exact lt_of_lt_of_le (by norm_num) h_one_le

  -- `n/(1+ε)^2 ≤ n/(1+ε)` since dividing by an extra positive factor decreases the value.
  have hy1_le_y2 : (n : ℝ) / (1 + ε) ^ 2 ≤ (n : ℝ) / (1 + ε) := by
    have h_nonneg : (0 : ℝ) ≤ (n : ℝ) / (1 + ε) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      exact div_nonneg hn0 (le_of_lt h_one_add_pos)
    have h_div_le : ((n : ℝ) / (1 + ε)) / (1 + ε) ≤ (n : ℝ) / (1 + ε) := by
      simpa using (div_le_self h_nonneg h_one_le)
    have hrewrite : ((n : ℝ) / (1 + ε)) / (1 + ε) = (n : ℝ) / (1 + ε) ^ 2 := by
      -- `(a/b)/c = a/(b*c)` and `a^2 = a*a`.
      simp [div_div, pow_two]
    -- Replace the left-hand side by `n/(1+ε)^2`.
    simpa [hrewrite] using h_div_le

  exact le_trans hX0_le_y1 hy1_le_y2

lemma y0_mul_one_add_delta_le_y1 [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
    y0 * (1 + gap.δ y0) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and a "stronger" version of
  `lemma y0_ge_X₀`, i.e. n / (1 + ε) ^ 3 ≥ √n for n ≥ X₀ ^ 2
  -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3 with hy0

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := by
    exact le_add_of_nonneg_right hε_nonneg

  have h_one_add_pos : (0 : ℝ) < 1 + ε := by
    exact lt_of_lt_of_le (by norm_num) h_one_le

  have hx_nonneg : 0 ≤ x := by
    simp [hx]

  -- As in `y0_ge_X₀`, we can show the stronger bound `x ≤ y0`.
  have h6 : (1 + ε) ^ 6 < x := by
    simpa [hx, hε] using (PrimeGap_Criterion.delta_sixth_power_lt_sqrt (n := n) hn)

  have hpow3_le_pow6 : (1 + ε) ^ 3 ≤ (1 + ε) ^ 6 := by
    exact pow_le_pow_right₀ h_one_le (by decide)

  have hpow3_le_x : (1 + ε) ^ 3 ≤ x := by
    exact le_of_lt (lt_of_le_of_lt hpow3_le_pow6 h6)

  have hx_le_y0 : x ≤ y0 := by
    -- `x ≤ n/(1+ε)^3` via `le_div_iff` and `x*(1+ε)^3 ≤ x*x = n`.
    have hden_pos : 0 < (1 + ε) ^ 3 := by
      exact pow_pos h_one_add_pos 3
    have hx_mul : x * (1 + ε) ^ 3 ≤ x * x := by
      have := mul_le_mul_of_nonneg_left hpow3_le_x hx_nonneg
      simpa [mul_assoc] using this
    have hx_sq : x * x = (n : ℝ) := by
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Nat.zero_le n)
      simp [hx, hn0]
    have hx_mul' : x * (1 + ε) ^ 3 ≤ (n : ℝ) := by
      simpa [hx_sq] using hx_mul
    -- Convert to a division statement.
    have : x ≤ (n : ℝ) / (1 + ε) ^ 3 := (le_div_iff₀ hden_pos).2 hx_mul'
    -- Finally rewrite `(n)/(1+ε)^3` as `y0`.
    simpa [hy0] using this

  have hX0_le_y0 : (X₀ : ℝ) ≤ y0 := by
    -- from `y0_ge_X₀`
    simpa [hx, hε, hy0] using (y0_ge_X₀ (n := n) hn)

  -- Since `x ≤ y0` and `δ` is decreasing for `≥ X₀`, we have `δ(y0) ≤ δ(x) = ε`.
  have hδy0_le_ε : gap.δ y0 ≤ ε := by
    have hδy0_le_δx : gap.δ y0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_decreasing x y0 hX0_le_x hX0_le_y0 hx_le_y0
    simpa [hε] using hδy0_le_δx

  have hone_add_le : 1 + gap.δ y0 ≤ 1 + ε := by
    simpa [add_comm, add_left_comm, add_assoc] using (add_le_add_left hδy0_le_ε 1)

  have hy0_nonneg : 0 ≤ y0 := by
    -- numerator is nonneg and denominator is positive
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    have hpow_pos : (0 : ℝ) < (1 + ε) ^ 3 := by
      exact pow_pos h_one_add_pos 3
    -- `y0 = n / (1+ε)^3`
    simpa [hy0] using (div_nonneg hn0 (le_of_lt hpow_pos))

  have hmul : y0 * (1 + gap.δ y0) ≤ y0 * (1 + ε) := by
    exact mul_le_mul_of_nonneg_left hone_add_le hy0_nonneg

  -- Simplify `y0*(1+ε) = n/(1+ε)^2`.
  have : y0 * (1 + ε) = (n : ℝ) / (1 + ε) ^ 2 := by
    -- `y0 = n/(1+ε)^3`, so multiplying by `(1+ε)` cancels one power.
    have hone_add_ne : (1 + ε) ≠ 0 := by
      exact ne_of_gt h_one_add_pos
    -- Turn the product into a single fraction and cancel a common factor.
    calc
      y0 * (1 + ε)
          = ((n : ℝ) / (1 + ε) ^ 3) * (1 + ε) := by
              simp [hy0]
      _   = ((n : ℝ) * (1 + ε)) / (1 + ε) ^ 3 := by
              -- `a/b * c = (a*c)/b`
              simp [div_mul_eq_mul_div]
      _   = ((n : ℝ) * (1 + ε)) / ((1 + ε) ^ 2 * (1 + ε)) := by
              -- `a^3 = a^2 * a`
              simp [pow_succ, mul_assoc]
            _   = (n : ℝ) / (1 + ε) ^ 2 := by
              -- cancel the common factor `(1+ε)`
              have hne : (1 + ε) ≠ 0 := ne_of_gt h_one_add_pos
              field_simp [hne, pow_succ, mul_assoc, mul_left_comm, mul_comm]

  -- Finish.
  simpa [this] using hmul

lemma y1_mul_one_add_delta_le_y2 [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
    y1 * (1 + gap.δ y1) ≤ (n : ℝ) / (1 + ε) := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and
  n / (1 + ε) ^ 2 ≥ √n for n ≥ X₀ ^ 2
    -- when n, ε ≥ 0, this holds automatically if `y0_mul_one_add_delta_le_y1` holds.
  -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2 with hy1

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε := le_add_of_nonneg_right hε_nonneg
  have h_one_add_pos : 0 < 1 + ε := lt_of_lt_of_le (by norm_num) h_one_le

  have hpow2_le_pow6 : (1 + ε) ^ 2 ≤ (1 + ε) ^ 6 :=
    pow_le_pow_right₀ h_one_le (by decide)

  have h6 : (1 + ε) ^ 6 < x := by
    simpa [hx, hε] using (PrimeGap_Criterion.delta_sixth_power_lt_sqrt (n := n) hn)

  have hpow2_le_x : (1 + ε) ^ 2 ≤ x :=
    le_of_lt (lt_of_le_of_lt hpow2_le_pow6 h6)

  have hx_nonneg : 0 ≤ x := by
    simpa only [hx] using Real.sqrt_nonneg (n : ℝ)

  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)

  have hx_sq : x * x = (n : ℝ) := by
    simp [hx, hn0]

  have hx_le_y1 : x ≤ y1 := by
    have hden_pos : 0 < (1 + ε) ^ 2 := pow_pos h_one_add_pos 2
    have hx_mul : x * (1 + ε) ^ 2 ≤ (n : ℝ) := by
      have hx_mul_le_xsq : x * (1 + ε) ^ 2 ≤ x * x :=
        mul_le_mul_of_nonneg_left hpow2_le_x hx_nonneg
      simpa [hx_sq] using hx_mul_le_xsq
    have : x ≤ (n : ℝ) / (1 + ε) ^ 2 := (le_div_iff₀ hden_pos).2 hx_mul
    simpa [hy1] using this

  have hX0_le_y1 : (X₀ : ℝ) ≤ y1 := by
    simpa [hx, hε, hy1] using (y1_ge_X₀ (n := n) hn)

  have hδy1_le_δx : gap.δ y1 ≤ gap.δ x :=
    PrimeGap_Criterion.gap_decreasing x y1 hX0_le_x hX0_le_y1 hx_le_y1
  have hδy1_le_ε : gap.δ y1 ≤ ε := by
    simpa [hε] using hδy1_le_δx

  have hone_add_le : 1 + gap.δ y1 ≤ 1 + ε := by
    simpa [add_comm] using (add_le_add_left hδy1_le_ε 1)

  have hy1_nonneg : 0 ≤ y1 := by
    have hden_pos : 0 < (1 + ε) ^ 2 := pow_pos h_one_add_pos 2
    have : 0 ≤ (n : ℝ) / (1 + ε) ^ 2 :=
      div_nonneg hn0 (le_of_lt hden_pos)
    simpa [hy1] using this

  have hmul : y1 * (1 + gap.δ y1) ≤ y1 * (1 + ε) :=
    mul_le_mul_of_nonneg_left hone_add_le hy1_nonneg

  have hy1_mul : y1 * (1 + ε) = (n : ℝ) / (1 + ε) := by
    have hne : (1 + ε) ≠ 0 := ne_of_gt h_one_add_pos
    calc
      y1 * (1 + ε) = ((n : ℝ) / (1 + ε) ^ 2) * (1 + ε) := by
        simp [hy1]
      _ = (n : ℝ) / (1 + ε) := by
        field_simp [hne, pow_succ, mul_assoc, mul_left_comm, mul_comm]

  calc
    y1 * (1 + gap.δ y1) ≤ y1 * (1 + ε) := hmul
    _ = (n : ℝ) / (1 + ε) := hy1_mul

lemma y2_mul_one_add_delta_lt_n [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y2 : ℝ := (n : ℝ) / (1 + ε)
    y2 * (1 + gap.δ y2) < (n : ℝ) := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and
  n / (1 + ε) ≥ √n for n ≥ X₀ ^ 2
    -- when n, ε ≥ 0, this holds automatically if `y0_mul_one_add_delta_le_y1` holds.
  -/
  dsimp
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  set y2 : ℝ := (n : ℝ) / (1 + ε) with hy2

  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx.symm] using (sqrt_ge_X₀ (n := n) hn)

  have hε_nonneg : 0 ≤ ε := by
    have : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)
    simpa [hε] using this

  have h_one_le : (1 : ℝ) ≤ 1 + ε :=
    le_add_of_nonneg_right hε_nonneg
  have h_one_add_pos : 0 < 1 + ε :=
    lt_of_lt_of_le (by norm_num) h_one_le

  -- Positivity of `n` (hence `x = √n > 0`) from `n ≥ X₀^2` and `X₀ > 1`.
  have hX0_pos : 0 < X₀ := lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos_nat

  have hx_pos : 0 < x := by
    simpa [hx] using (Real.sqrt_pos.2 hn_pos)

  -- From the criterion: `(1+ε)^6 < x`.
  have h6 : (1 + ε) ^ 6 < x := by
    simpa [hx, hε] using
      (PrimeGap_Criterion.delta_sixth_power_lt_sqrt (n := n) hn)

  -- Since `1 ≤ 1+ε`, we have `1+ε ≤ (1+ε)^6`.
  have hone_add_le_pow6 : 1 + ε ≤ (1 + ε) ^ 6 := by
    have : (1 + ε) ^ (1 : ℕ) ≤ (1 + ε) ^ 6 :=
      pow_le_pow_right₀ h_one_le (by decide)
    simpa [pow_one] using this

  have hone_add_lt_x : 1 + ε < x :=
    lt_of_le_of_lt hone_add_le_pow6 h6

  -- Convert `hone_add_lt_x` into the strict inequality `x < y2`.
  have hx_sq : x * x = (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    simp [hx, hn0]

  have hx_mul_lt : x * (1 + ε) < (n : ℝ) := by
    have hx_mul_lt_xsq : x * (1 + ε) < x * x :=
      (mul_lt_mul_of_pos_left hone_add_lt_x hx_pos)
    simpa [hx_sq] using hx_mul_lt_xsq

  have hx_lt_y2 : x < y2 := by
    have : x < (n : ℝ) / (1 + ε) :=
      (lt_div_iff₀ h_one_add_pos).2 hx_mul_lt
    simpa [hy2] using this

  have hX0_le_y2 : (X₀ : ℝ) ≤ y2 := by
    simpa [hx, hε, hy2] using (y2_ge_X₀ (n := n) hn)

  -- Strict decreasing gives `δ(y2) < δ(x) = ε`.
  have hδy2_lt_ε : gap.δ y2 < ε := by
    have hδy2_lt_δx : gap.δ y2 < gap.δ x :=
      PrimeGap_Criterion.gap_strict_decreasing x y2 hX0_le_x hX0_le_y2 hx_lt_y2
    simpa [hε] using hδy2_lt_δx

  have hone_add_lt : 1 + gap.δ y2 < 1 + ε := by
    simpa using (add_lt_add_left hδy2_lt_ε 1)

  have hy2_pos : 0 < y2 := by
    have : 0 < (n : ℝ) / (1 + ε) := div_pos hn_pos h_one_add_pos
    simpa [hy2] using this

  have hmul : y2 * (1 + gap.δ y2) < y2 * (1 + ε) :=
    mul_lt_mul_of_pos_left hone_add_lt hy2_pos

  have hy2_mul : y2 * (1 + ε) = (n : ℝ) := by
    have hne : (1 + ε) ≠ 0 := ne_of_gt h_one_add_pos
    calc
      y2 * (1 + ε) = ((n : ℝ) / (1 + ε)) * (1 + ε) := by
        simp [hy2]
      _ = (n : ℝ) := by
        field_simp [hne]

  calc
    y2 * (1 + gap.δ y2) < y2 * (1 + ε) := hmul
    _ = (n : ℝ) := hy2_mul



/- End of theorem `exists_q_primes` lemmas-/


/- theorem `prod_q_ge` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
-/

noncomputable abbrev b (n : ℕ) : ℝ := 1 + gap.δ (√(n : ℝ))
/--
`b(n)` is the “1 + δ(√n)” base that appears everywhere in q-side bounds.
We do *not* export `b` into theorem statements; it’s just a local convenience for Cert lemmas.
Try moving this entirely into `prod_q_ge` if possible.
-/

/- *** This lemma is likely not used *** -/
lemma b_pos [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < b n := by
  /- 1 + δ(√n) ≥ 0 for n ≥ X₀ ^ 2
   This holds when δ(x) ≥ 0 for x ≥ X₀ and X₀ ≥ 0 -/
  have hX0_le_sqrt : (X₀ : ℝ) ≤ Real.sqrt (n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (Real.sqrt (n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := Real.sqrt (n : ℝ)) (by simpa using hX0_le_sqrt)
  have h_one_le : (1 : ℝ) ≤ 1 + gap.δ (Real.sqrt (n : ℝ)) :=
    le_add_of_nonneg_right hδ_nonneg
  have hpos : (0 : ℝ) < 1 + gap.δ (Real.sqrt (n : ℝ)) :=
    lt_of_lt_of_le (by norm_num) h_one_le
  simpa [b] using hpos


lemma prod_q_rhs_reindex [PrimeGap_Criterion] (n : ℕ) :
    (∏ i : Fin 3, (1 + (b n) ^ ((i : ℕ) + 1 : ℝ) / n))
      =
    (∏ i : Fin 3, (1 + (b n) ^ ((3 : ℝ) - (i : ℕ)) / n)) := by
  /-- Reindexing trick for `Fin 3`: convert exponents `i+1` to `3 - i`.
    This is *structural*, but it’s noisy; keeping it in Cert keeps Main clean. -/
  /- *** Proof idea ***:
  exactly your current proof: `rw [Fin.prod_univ_three, Fin.prod_univ_three]` + the `conv` blocks + `ring`,
  just replacing `1 + 1/(log √n)^3` by `b n`.
  copy/paste your existing `Fin.prod_univ_three`/`conv` proof
  with `b n` in place of `(1 + 1/(log √n)^3)`
  -/
  classical
  -- Expand the products over `Fin 3` and simplify the (finite) arithmetic in the exponents.
  have h01 : ((0 : ℕ) + 1 : ℝ) = (1 : ℝ) := by norm_num
  have h11 : ((1 : ℕ) + 1 : ℝ) = (2 : ℝ) := by norm_num
  have h21 : ((2 : ℕ) + 1 : ℝ) = (3 : ℝ) := by norm_num
  have h30 : (3 : ℝ) - (0 : ℕ) = (3 : ℝ) := by norm_num
  have h31 : (3 : ℝ) - (1 : ℕ) = (2 : ℝ) := by norm_num
  have h32 : (3 : ℝ) - (2 : ℕ) = (1 : ℝ) := by norm_num
  have h12 : (1 : ℝ) + 1 = (2 : ℝ) := by norm_num
  have h23 : (2 : ℝ) + 1 = (3 : ℝ) := by norm_num
  have h31' : (3 : ℝ) - 1 = (2 : ℝ) := by norm_num
  have h32' : (3 : ℝ) - 2 = (1 : ℝ) := by norm_num
  -- After expansion, this is just commutativity: the RHS lists the same three factors in reverse.
  simp [Fin.prod_univ_three, h12, h23, h31', h32']
  ac_rfl



lemma inv_le_rpow_div_of_lower_bound [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {t : ℝ} {q : ℕ}
    (hq : (n : ℝ) * (b n) ^ (-t) ≤ (q : ℝ)) :
    (1 : ℝ) / (q : ℝ) ≤ (b n) ^ t / n := by
  /- This is structural, just rearrange the inequality -/
  /- This holds when q ≠ 0 and δ(x) ≥ 0 for x ≥ X₀ and X₀ > 0 -/
  have hX0_pos : 0 < X₀ := lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat

  have hb_pos : 0 < b n := b_pos (n := n) hn
  have hb_rpow_pos : 0 < (b n) ^ (-t) := Real.rpow_pos_of_pos hb_pos (-t)
  have ha_pos : 0 < (n : ℝ) * (b n) ^ (-t) := mul_pos hn_pos hb_rpow_pos

  -- Take reciprocals of the lower bound (positivity is automatic from `ha_pos`).
  have h_recip : (1 : ℝ) / (q : ℝ) ≤ (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t)) := by
    exact one_div_le_one_div_of_le ha_pos hq

  -- Rewrite the reciprocal of `n * (b n)^(-t)` as `(b n)^t / n`.
  have h_simp : (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t)) = (b n) ^ t / n := by
    calc
      (1 : ℝ) / ((n : ℝ) * (b n) ^ (-t))
          = ((n : ℝ) * (b n) ^ (-t))⁻¹ := by
              simp [one_div]
      _ = ((b n) ^ (-t))⁻¹ * (n : ℝ)⁻¹ := by
              simp [mul_inv_rev]
      _ = (b n) ^ t * (n : ℝ)⁻¹ := by
            simp [Real.rpow_neg hb_pos.le]
      _ = (b n) ^ t / n := by
              simp [div_eq_mul_inv, mul_comm]

  simpa [h_simp] using h_recip

/- End of theorem `prod_q_ge` lemmas-/

/- theorem `prod_p_ge` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
-/
lemma one_add_delta_pos [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < (1 + gap.δ (√(n : ℝ))) := by
  /- This holds when δ(x) ≥ 0 for x ≥ X₀ and X₀ > 0-/
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by exact hX0_le_sqrt)
  have h_one_le : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) := by
    exact le_add_of_nonneg_right hδ_nonneg
  exact lt_of_lt_of_le (by norm_num) h_one_le

lemma p_mul_padd1_le_bound [PrimeGap_Criterion]
  {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {p : Fin 3 → ℕ}
    -- (hp_prime : ∀ i, Nat.Prime (p i))
    -- (hp_mono : StrictMono p)
    (hp_ub :
      ∀ i, (p i : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ)) :
    ∀ i : Fin 3,
      ((p i * (p i + 1) : ℕ) : ℝ)
        ≤ (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
  intro i
  set B : ℝ := 1 + gap.δ (√(n : ℝ))

  have hB_pos : 0 < B := by
    simpa [B] using (one_add_delta_pos (n := n) hn)

  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by exact hX0_le_sqrt)
  have h1_le_B : (1 : ℝ) ≤ B := by
    simpa [B] using (add_le_add_left hδ_nonneg 1)

  have hB_nonneg : 0 ≤ B := le_of_lt hB_pos

  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := by
    exact Real.sqrt_nonneg (n : ℝ)
  have hp_nonneg : 0 ≤ (p i : ℝ) := by
    exact_mod_cast (Nat.zero_le (p i))

  have hp_le : (p i : ℝ) ≤ √(n : ℝ) * B ^ (i + 1 : ℝ) := by
    simpa [B] using (hp_ub i)

  have hp_sq_le : (p i : ℝ) ^ 2 ≤ (n : ℝ) * B ^ (2 * (i : ℕ) + 2 : ℝ) := by
    have h_rhs_nonneg : 0 ≤ √(n : ℝ) * B ^ (i + 1 : ℝ) := by
      have hBpow_pos : 0 < B ^ (i + 1 : ℝ) := Real.rpow_pos_of_pos hB_pos _
      exact mul_nonneg hsqrt_nonneg (le_of_lt hBpow_pos)
    have hsq :
        (p i : ℝ) * (p i : ℝ) ≤
          (√(n : ℝ) * B ^ (i + 1 : ℝ)) * (√(n : ℝ) * B ^ (i + 1 : ℝ)) := by
      exact mul_le_mul hp_le hp_le hp_nonneg h_rhs_nonneg
    have hsq' : (p i : ℝ) ^ 2 ≤ (√(n : ℝ) * B ^ (i + 1 : ℝ)) ^ 2 := by
      simpa [pow_two] using hsq
    calc
      (p i : ℝ) ^ 2
          ≤ (√(n : ℝ) * B ^ (i + 1 : ℝ)) ^ 2 := hsq'
      _ = (√(n : ℝ)) ^ 2 * (B ^ (i + 1 : ℝ)) ^ 2 := by
            simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
              (mul_pow (√(n : ℝ)) (B ^ (i + 1 : ℝ)) 2)
      _ = (n : ℝ) * (B ^ (i + 1 : ℝ) * B ^ (i + 1 : ℝ)) := by
            have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
              exact_mod_cast (Nat.zero_le n)
            have hsqrt_sq : (√(n : ℝ)) ^ 2 = (n : ℝ) := by
              simpa only using (Real.sq_sqrt hn0)
            simp [hsqrt_sq, pow_two]
      _ = (n : ℝ) * B ^ ((i + 1 : ℝ) + (i + 1 : ℝ)) := by
        simpa using
          (congrArg (fun t => (n : ℝ) * t)
            (Real.rpow_add hB_pos (i + 1 : ℝ) (i + 1 : ℝ)).symm)
      _ = (n : ℝ) * B ^ (2 * (i : ℕ) + 2 : ℝ) := by
            have : ((i + 1 : ℝ) + (i + 1 : ℝ)) = (2 * (i : ℕ) + 2 : ℝ) := by
              nlinarith
            simp [this]

  have hp_le' : (p i : ℝ) ≤ √(n : ℝ) * B ^ (2 * (i : ℕ) + 2 : ℝ) := by
    have hi1_nonneg : 0 ≤ (i + 1 : ℝ) := by
      have hi_nonneg : (0 : ℝ) ≤ (i : ℝ) := by
        exact_mod_cast (Nat.zero_le (i : ℕ))
      nlinarith
    have h_one_le_Bpow : (1 : ℝ) ≤ B ^ (i + 1 : ℝ) := by
      exact Real.one_le_rpow h1_le_B hi1_nonneg
    have hBpow_nonneg : 0 ≤ B ^ (i + 1 : ℝ) := by
      exact le_of_lt (Real.rpow_pos_of_pos hB_pos _)
    have hBpow_le_sq : B ^ (i + 1 : ℝ) ≤ (B ^ (i + 1 : ℝ)) ^ 2 := by
      have :
          B ^ (i + 1 : ℝ) ≤ B ^ (i + 1 : ℝ) * B ^ (i + 1 : ℝ) :=
        le_mul_of_one_le_right hBpow_nonneg h_one_le_Bpow
      simpa [pow_two] using this
    have hBpow_sq :
        (B ^ (i + 1 : ℝ)) ^ 2 = B ^ ((i + 1 : ℝ) + (i + 1 : ℝ)) := by
      simpa [pow_two] using (Real.rpow_add hB_pos (i + 1 : ℝ) (i + 1 : ℝ)).symm
    have hBpow_le : B ^ (i + 1 : ℝ) ≤ B ^ (2 * (i : ℕ) + 2 : ℝ) := by
      have hBpow_le_sum :
          B ^ (i + 1 : ℝ) ≤ B ^ ((i + 1 : ℝ) + (i + 1 : ℝ)) := by
        simpa [hBpow_sq] using hBpow_le_sq
      have hExp :
          ((i + 1 : ℝ) + (i + 1 : ℝ)) = (2 * (i : ℕ) + 2 : ℝ) := by
        nlinarith
      simpa [hExp] using hBpow_le_sum
    have := mul_le_mul_of_nonneg_left hBpow_le hsqrt_nonneg
    exact le_trans hp_le (by simpa [mul_assoc, mul_left_comm, mul_comm] using this)

  have hmul_cast :
      ((p i * (p i + 1) : ℕ) : ℝ) = (p i : ℝ) * ((p i : ℝ) + 1) := by
    simp [Nat.cast_mul, Nat.cast_add, Nat.cast_one]

  have hmul_as_sum :
      (p i : ℝ) * ((p i : ℝ) + 1) = (p i : ℝ) ^ 2 + (p i : ℝ) := by
    ring

  calc
    ((p i * (p i + 1) : ℕ) : ℝ)
      = (p i : ℝ) ^ 2 + (p i : ℝ) := by
        simp [hmul_cast, hmul_as_sum]
    _ ≤ (n : ℝ) * B ^ (2 * (i : ℕ) + 2 : ℝ) + (√(n : ℝ) * B ^ (2 * (i : ℕ) + 2 : ℝ)) := by
            exact add_le_add hp_sq_le hp_le'
    _ = B ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)) := by
            ring
    _ = (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
            simp [B]

/- End of theorem `prod_p_ge` lemmas-/


/- theorem `pq_ratio_ge` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
-/

lemma n_pos [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) : (0 : ℝ) < (n : ℝ) := by
  /- This holds when X₀ ≠ 0 -/
  -- Since `X₀ > 1`, we have `0 < X₀`, hence `0 < X₀^2 ≤ n`.
  have hX0_pos : 0 < X₀ := lt_trans Nat.zero_lt_one PrimeGap_Criterion.h_X₀
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos hn
  exact_mod_cast hn_pos_nat




lemma pq_ratio_rhs_as_fraction [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
      =
    ((4 : ℝ) * ∏ i : Fin 3,
        (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ))
      /
    (∏ i : Fin 3,
        (n : ℝ) / ((1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ)))) := by
    /- This is structural
     This holds when gap.δ(x) ≥ 0 for x ≥ X₀, and X₀ > 0 -/
    classical
    set x : ℝ := √(n : ℝ) with hx
    set b : ℝ := 1 + gap.δ x with hb

    have hn_pos : (0 : ℝ) < (n : ℝ) := n_pos (n := n) hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos

    have hX0_le_x : (X₀ : ℝ) ≤ x := by
      simpa [hx] using (sqrt_ge_X₀ (n := n) hn)

    have hδ_nonneg : 0 ≤ gap.δ x :=
      PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)

    have hb_pos : 0 < b := by
      have h_one_le : (1 : ℝ) ≤ 1 + gap.δ x := le_add_of_nonneg_right hδ_nonneg
      exact lt_of_lt_of_le (by norm_num) h_one_le

    have hb_ne : b ≠ 0 := ne_of_gt hb_pos

    have hx_pos : 0 < x := by
      simpa [hx] using (Real.sqrt_pos.2 hn_pos)

    have hx_ne : x ≠ 0 := ne_of_gt hx_pos

    have hx_pow : x ^ (3 : ℕ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
      have hcast : x ^ ((3 : ℝ)) = x ^ (3 : ℕ) := by
        simp
      calc
        x ^ (3 : ℕ) = x ^ ((3 : ℝ)) := by
          exact hcast.symm
        _ = (n : ℝ) ^ ((1 / 2 : ℝ) * (3 : ℝ)) := by
          -- rewrite `x = n^(1/2)` and combine exponents
          simp [hx, Real.sqrt_eq_rpow, rpow_mul hn0]
        _ = (n : ℝ) ^ (3 / 2 : ℝ) := by
          norm_num

    have hx_sq : x ^ (2 : ℕ) = (n : ℝ) := by
      simp [hx, Real.sq_sqrt hn0]

    have hn_pow3 : (n : ℝ) ^ (3 : ℕ) = x ^ (6 : ℕ) := by
      calc
        (n : ℝ) ^ (3 : ℕ) = (x ^ (2 : ℕ)) ^ (3 : ℕ) := by
          simp [hx_sq]
        _ = x ^ (2 * 3 : ℕ) := by
          simpa using (pow_mul x 2 3).symm
        _ = x ^ (6 : ℕ) := by
          norm_num

    have hnum :
        (∏ i : Fin 3, x * b ^ ((i : ℕ) + 1 : ℝ))
          = x ^ (3 : ℕ) * b ^ (6 : ℕ) := by
      -- Expand the finite product and convert rpow to nat power.
      have hnum' :
          (∏ i : Fin 3, x * b ^ ((i : ℕ) + 1 : ℝ))
            = (x * b ^ (1 : ℕ)) * (x * b ^ (2 : ℕ)) * (x * b ^ (3 : ℕ)) := by
        rw [Fin.prod_univ_three]
        simp
        norm_num

      have hx3 : x * x * x = x ^ (3 : ℕ) := by
        calc
          x * x * x = x ^ (2 : ℕ) * x := by
            simp [pow_two, mul_assoc]
          _ = x ^ (3 : ℕ) := by
            simp [pow_succ]

      have hb12 : b ^ (1 : ℕ) * b ^ (2 : ℕ) = b ^ (3 : ℕ) := by
        simpa using (pow_add b 1 2).symm

      have hb123 : b ^ (1 : ℕ) * b ^ (2 : ℕ) * b ^ (3 : ℕ) = b ^ (6 : ℕ) := by
        calc
          b ^ (1 : ℕ) * b ^ (2 : ℕ) * b ^ (3 : ℕ)
              = (b ^ (1 : ℕ) * b ^ (2 : ℕ)) * b ^ (3 : ℕ) := by
            simp [mul_assoc]
          _ = b ^ (3 : ℕ) * b ^ (3 : ℕ) := by
            rw [hb12]
          _ = b ^ (3 + 3 : ℕ) := by
                  simpa using (pow_add b 3 3).symm
          _ = b ^ (6 : ℕ) := by
                  norm_num

      calc
        (∏ i : Fin 3, x * b ^ ((i : ℕ) + 1 : ℝ))
            = (x * b ^ (1 : ℕ)) * (x * b ^ (2 : ℕ)) * (x * b ^ (3 : ℕ)) := hnum'
        _ = (x * x * x) * (b ^ (1 : ℕ) * b ^ (2 : ℕ) * b ^ (3 : ℕ)) := by
            ac_rfl
        _ = x ^ (3 : ℕ) * b ^ (6 : ℕ) := by
          rw [hx3, hb123]

    have hden :
        (∏ i : Fin 3, (n : ℝ) / (b ^ ((3 : ℕ) - (i : ℕ))))
          = (n : ℝ) ^ (3 : ℕ) / b ^ (6 : ℕ) := by
      have h30 : (3 : ℕ) - (0 : ℕ) = 3 := by norm_num
      have h31 : (3 : ℕ) - (1 : ℕ) = 2 := by norm_num
      have h32 : (3 : ℕ) - (2 : ℕ) = 1 := by norm_num
      calc
        (∏ i : Fin 3, (n : ℝ) / (b ^ ((3 : ℕ) - (i : ℕ))))
            = (n : ℝ) / b ^ (3 : ℕ) * ((n : ℝ) / b ^ (2 : ℕ)) * ((n : ℝ) / b ^ (1 : ℕ)) := by
          rw [Fin.prod_univ_three]
          simp [h30, h31, h32, mul_assoc]
        _ = ((n : ℝ) * (n : ℝ) * (n : ℝ)) / (b ^ (3 : ℕ) * b ^ (2 : ℕ) * b ^ (1 : ℕ)) := by
          -- combine fractions
          simp [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
        _ = (n : ℝ) ^ (3 : ℕ) / b ^ (6 : ℕ) := by
          have hn3 : (n : ℝ) * (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 : ℕ) := by
            simp [pow_succ, mul_assoc]
          have hb3 : b ^ (3 : ℕ) * b ^ (2 : ℕ) * b ^ (1 : ℕ) = b ^ (6 : ℕ) := by
            calc
              b ^ (3 : ℕ) * b ^ (2 : ℕ) * b ^ (1 : ℕ)
                  = b ^ (3 : ℕ) * (b ^ (2 : ℕ) * b ^ (1 : ℕ)) := by
                      simp [mul_assoc]
              _ = b ^ (3 : ℕ) * b ^ (3 : ℕ) := by
                      have : b ^ (2 : ℕ) * b ^ (1 : ℕ) = b ^ (3 : ℕ) := by
                        simpa using (pow_add b 2 1).symm
                      rw [this]
              _ = b ^ (3 + 3 : ℕ) := by
                      simpa using (pow_add b 3 3).symm
              _ = b ^ (6 : ℕ) := by
                      norm_num
          rw [hn3, hb3]

    have hRHS :
        ((4 : ℝ) * ∏ i : Fin 3, x * b ^ ((i : ℕ) + 1 : ℝ))
          / (∏ i : Fin 3, (n : ℝ) / (b ^ ((3 : ℕ) - (i : ℕ))))
          = 4 * b ^ (12 : ℕ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        ((4 : ℝ) * ∏ i : Fin 3, x * b ^ ((i : ℕ) + 1 : ℝ))
            / (∏ i : Fin 3, (n : ℝ) / (b ^ ((3 : ℕ) - (i : ℕ))))
            = (4 : ℝ) * (x ^ (3 : ℕ) * b ^ (6 : ℕ)) / ((n : ℝ) ^ (3 : ℕ) / b ^ (6 : ℕ)) := by
                simp [hnum, hden]
        _ = (4 : ℝ) * x ^ (3 : ℕ) * b ^ (12 : ℕ) / (n : ℝ) ^ (3 : ℕ) := by
          -- `a / (c / d) = a * d / c` and collect powers
          have hb12' : b ^ (6 : ℕ) * b ^ (6 : ℕ) = b ^ (12 : ℕ) := by
            simpa using (pow_add b 6 6).symm
          calc
            (4 : ℝ) * (x ^ (3 : ℕ) * b ^ (6 : ℕ)) / ((n : ℝ) ^ (3 : ℕ) / b ^ (6 : ℕ))
              = (4 : ℝ) * (x ^ (3 : ℕ) * b ^ (6 : ℕ)) * (b ^ (6 : ℕ) / (n : ℝ) ^ (3 : ℕ)) := by
                simp [div_eq_mul_inv]
            _ = (4 : ℝ) * x ^ (3 : ℕ) * (b ^ (6 : ℕ) * b ^ (6 : ℕ)) / (n : ℝ) ^ (3 : ℕ) := by
              simp [mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv]
            _ = (4 : ℝ) * x ^ (3 : ℕ) * b ^ (12 : ℕ) / (n : ℝ) ^ (3 : ℕ) := by
              simp [hb12', mul_assoc]
        _ = (4 : ℝ) * x ^ (3 : ℕ) * b ^ (12 : ℕ) / x ^ (6 : ℕ) := by
          simp [hn_pow3]
        _ = (4 : ℝ) * b ^ (12 : ℕ) / x ^ (3 : ℕ) := by
                field_simp [hx_ne, mul_assoc, mul_left_comm, mul_comm]
        _ = 4 * b ^ (12 : ℕ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
          simp [hx_pow]

    -- Return to the original notation.
    simpa [hb, hx, mul_assoc, mul_left_comm, mul_comm] using hRHS.symm


/- End of theorem `pq_ratio_ge` lemmas- -/

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


/- `hn` lemmas -/
lemma one_le_X₀_sq [PrimeGap_Criterion] : (1 : ℕ) ≤ X₀ ^ 2 := by
  /- This holds when X₀ > 1 -/
  /-
  Proof idea:
  - for the current `PrimeGaps.latest`, `X₀` is a concrete positive numeral (89693),
    so this is `decide`/`norm_num`.
  -/
  have hX0_pos : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos : 0 < X₀ ^ 2 := pow_pos hX0_pos 2
  -- `Nat.succ_le_iff` with `a = 0` is `1 ≤ b ↔ 0 < b`.
  exact Nat.succ_le_iff.2 hX0_sq_pos
/- End of `hn` lemmas-/


/- `h_ord_2` lemmas -/
lemma ord2_mid [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ)
      <
    (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) := by
  /- This holds when
    1. gap.δ(x) ≥ 0 for x ≥ X₀
    2. X₀ > 0
    3. (1 + gap.δ (√n)) ^ 6 < √n for n ≥ X₀ ^ 2
    4. 4 * (1 + gap.δ (√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2
   -/

  -- Abbreviate `x = √n` and `b = 1 + δ(x)`.
  set x : ℝ := Real.sqrt (n : ℝ) with hx
  set b : ℝ := 1 + gap.δ x with hb

  -- We will use `lt_div_iff₀` with the positive denominator `b^3`.
  have hX0_le_x : (X₀ : ℝ) ≤ x := by
    simpa [hx] using (sqrt_ge_X₀ (n := n) hn)

  have hδ_nonneg : 0 ≤ gap.δ x :=
    PrimeGap_Criterion.gap_nonneg x (by simpa using hX0_le_x)

  have hb_pos : 0 < b := by
    -- `b = 1 + δ(x)` and `δ(x) ≥ 0`.
    simpa [hb] using
      (add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < (1 : ℝ)) hδ_nonneg)

  have hb3_pos : 0 < b ^ (3 : ℕ) := pow_pos hb_pos 3

  -- From `hn` and `X₀ > 1`, we get `n > 0`, hence `x = √n > 0`.
  have hX0_pos_nat : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hx_pos : 0 < x := by
    simpa [hx] using (Real.sqrt_pos.2 hn_pos)

  -- Criterion gives `b^6 < x` (since `b = 1 + δ(√n)` and `x = √n`).
  have h6 : b ^ (6 : ℕ) < x := by
    simpa [hx, hb] using
      (PrimeGap_Criterion.delta_sixth_power_lt_sqrt (n := n) hn)

  -- Multiply `b^6 < x` by the positive number `x` to get `x*b^6 < x*x`.
  have hx_mul6 : x * b ^ (6 : ℕ) < x * x := by
    have := mul_lt_mul_of_pos_left h6 hx_pos
    simpa [mul_assoc] using this

  -- Convert `x*x` into `n` (since `x = √(n)`).
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)
  have hx_sq : x * x = (n : ℝ) := by
    have : x ^ (2 : ℕ) = (n : ℝ) := by
      simpa only [hx] using (Real.sq_sqrt hn0)
    simpa [pow_two] using this

  have hxb6_lt_n : x * b ^ (6 : ℕ) < (n : ℝ) := by
    simpa [hx_sq] using hx_mul6

  -- Rewrite `(x*b^3)*b^3` as `x*b^6` and apply `lt_div_iff₀`.
  have hpow : b ^ (3 : ℕ) * b ^ (3 : ℕ) = b ^ (6 : ℕ) := by
    have : (3 : ℕ) + 3 = 6 := by norm_num
    calc
      b ^ (3 : ℕ) * b ^ (3 : ℕ)
          = b ^ ((3 : ℕ) + 3) := by
              simpa using (pow_add b 3 3).symm
      _   = b ^ (6 : ℕ) := by
              simp [this]

  have hrewrite :
      (x * b ^ (3 : ℕ)) * b ^ (3 : ℕ) = x * b ^ (6 : ℕ) := by
    calc
      (x * b ^ (3 : ℕ)) * b ^ (3 : ℕ)
          = x * (b ^ (3 : ℕ) * b ^ (3 : ℕ)) := by
              simp [mul_assoc]
      _   = x * b ^ (6 : ℕ) := by
              simp [hpow]

  have hmul : (x * b ^ (3 : ℕ)) * b ^ (3 : ℕ) < (n : ℝ) := by
    simpa [hrewrite] using hxb6_lt_n

  have hdiv : x * b ^ (3 : ℕ) < (n : ℝ) / b ^ (3 : ℕ) :=
    (lt_div_iff₀ hb3_pos).2 hmul

  -- Unfold `x` and `b` to match the statement.
  simpa [hx, hb] using hdiv

-- /- End of `h_ord_2` lemmas -/


/- `h_crit` lemmas -/
lemma delta_prod_mul_nonneg [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ)
              * ((n : ℝ) + √(n : ℝ)) )))
        * (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
  /- holds when gap.δ(x) > 0 for x ≥ X₀ and X₀ > 0 -/
  classical

  -- Positivity of `n` (from `hn : n ≥ X₀^2` and `X₀ > 1`).
  have hX0_pos_nat : 0 < X₀ :=
    lt_trans Nat.zero_lt_one (PrimeGap_Criterion.h_X₀)
  have hX0_sq_pos_nat : 0 < X₀ ^ 2 := pow_pos hX0_pos_nat 2
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hX0_sq_pos_nat hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn_pos_nat

  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := Real.sqrt_nonneg (n : ℝ)
  have hsum_pos : 0 < (n : ℝ) + √(n : ℝ) :=
    add_pos_of_pos_of_nonneg hn_pos hsqrt_nonneg

  -- Nonnegativity of `δ(√n)` and hence positivity of `1 + δ(√n)`.
  have hX0_le_sqrt : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    PrimeGap_Criterion.gap_nonneg (x := √(n : ℝ)) (by simpa using hX0_le_sqrt)
  have hb_pos : 0 < (1 + gap.δ (√(n : ℝ))) := by
    -- `1 > 0` and `δ(√n) ≥ 0`.
    exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < (1 : ℝ)) hδ_nonneg

  -- Define the three multiplicative factors to make the `Fin 3` product readable.
  let f : Fin 3 → ℝ := fun i =>
    (1 + 1 /
      ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))))

  have hf_nonneg : ∀ i : Fin 3, 0 ≤ f i := by
    intro i
    have hpow_pos : 0 < (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) :=
      Real.rpow_pos_of_pos hb_pos _
    have hden_pos : 0 <
        (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)) :=
      mul_pos hpow_pos hsum_pos
    have hdiv_nonneg :
        0 ≤ (1 : ℝ) /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ))) := by
      -- A reciprocal of a positive number is nonnegative.
      exact one_div_nonneg.2 (le_of_lt hden_pos)
    -- `1 + (nonneg)` is nonnegative.
    exact add_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ)) hdiv_nonneg

  have hprod_nonneg : 0 ≤ ∏ i : Fin 3, f i := by
    -- Expand the `Fin 3` product into three factors.
    have h01 : 0 ≤ f (0 : Fin 3) * f (1 : Fin 3) :=
      mul_nonneg (hf_nonneg 0) (hf_nonneg 1)
    have h012 : 0 ≤ (f (0 : Fin 3) * f (1 : Fin 3)) * f (2 : Fin 3) :=
      mul_nonneg h01 (hf_nonneg 2)
    simpa [Fin.prod_univ_three, f, mul_assoc] using h012

  have hlast_nonneg : 0 ≤ 1 + (3 : ℝ) / (8 * (n : ℝ)) := by
    have hden_pos : 0 < (8 : ℝ) * (n : ℝ) := mul_pos (by norm_num) hn_pos
    have hdiv_nonneg : 0 ≤ (3 : ℝ) / ((8 : ℝ) * (n : ℝ)) :=
      div_nonneg (by norm_num) (le_of_lt hden_pos)
    exact add_nonneg (by norm_num : (0 : ℝ) ≤ (1 : ℝ)) hdiv_nonneg

  -- Combine the two nonneg factors.
  have : 0 ≤ (∏ i : Fin 3, f i) * (1 + (3 : ℝ) / (8 * (n : ℝ))) :=
    mul_nonneg hprod_nonneg hlast_nonneg
  -- Unfold `f` to match the statement.
  simpa [f] using this

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

theorem main_ineq_delta_form [PrimeGap_Criterion] {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤
    (∏ i : Fin 3,
        (1 + 1 /
          ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * ((n : ℝ) + √(n : ℝ)))))
      * (1 + (3 : ℝ) / (8 * (n : ℝ)))
      * (1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
      exact PrimeGap_Criterion.delta_ineq n hn

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
      delta_ineq := ?_
      }
  all_goals
    sorry



end ChoosePrime_lemmas
end Lcm
