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
\subsection{Reduction to a small epsilon-inequality}
-/



/- Helper lemmas -/
lemma gap_delta_def (x : ℝ) : gap.δ x = 1 / (log x) ^ (3 : ℝ) := by
  -- `gap` is the (latest) Dusart provider; unfolding exposes the concrete `δ`.
  simp [Lcm.gap, PrimeGaps.latest, PrimeGaps.provider, PrimeGaps.Dusart.provider]

lemma gap_delta_nonneg_of_one_lt {x : ℝ} (hx : 1 < x) : 0 ≤ gap.δ x := by
  have hlogpos : 0 < log x := Real.log_pos hx
  have hdenpos : 0 < (log x) ^ (3 : ℝ) := Real.rpow_pos_of_pos hlogpos (3 : ℝ)
  have hpos : 0 < (1 / (log x) ^ (3 : ℝ)) := one_div_pos.mpr hdenpos
  -- rewrite back to `gap.δ`.
  simpa [gap_delta_def] using (le_of_lt hpos)

lemma gap_delta_antitone_of_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    gap.δ b ≤ gap.δ a := by
  -- Since `log` is increasing on `(0,∞)` and `t ↦ t^3` is increasing on `[0,∞)`, the
  -- denominator `(log x)^3` increases with `x`, hence its reciprocal decreases.
  have ha_pos : 0 < a := lt_trans (by norm_num) ha
  have hlog_le : log a ≤ log b := Real.log_le_log ha_pos hab
  have hloga_pos : 0 < log a := Real.log_pos ha
  have hloga_nonneg : 0 ≤ log a := le_of_lt hloga_pos
  have hpow_le : (log a) ^ (3 : ℝ) ≤ (log b) ^ (3 : ℝ) := by
    exact Real.rpow_le_rpow hloga_nonneg hlog_le (by norm_num)
  have hpow_pos : 0 < (log a) ^ (3 : ℝ) := Real.rpow_pos_of_pos hloga_pos (3 : ℝ)
  have hdiv_le : (1 / (log b) ^ (3 : ℝ)) ≤ 1 / (log a) ^ (3 : ℝ) :=
    one_div_le_one_div_of_le hpow_pos hpow_le
  simpa [gap_delta_def] using hdiv_le

lemma gap_delta_le_one_of_three_le {x : ℝ} (hx : (3 : ℝ) ≤ x) : gap.δ x ≤ 1 := by
  have hx_pos : 0 < x := lt_of_lt_of_le (by norm_num) hx

  -- First show `1 < log x` using `exp 1 < 3 ≤ x`.
  have hexp1_lt_x : Real.exp (1 : ℝ) < x := by
    have hexp1_lt_3 : Real.exp (1 : ℝ) < (3 : ℝ) := by
      sorry
      -- simpa using Real.exp_one_lt_d9
    have h3_lt_x : (3 : ℝ) < x := by sorry --linarith
    exact lt_trans hexp1_lt_3 h3_lt_x
  have hlog_gt_one : (1 : ℝ) < log x := (Real.lt_log_iff_exp_lt hx_pos).2 hexp1_lt_x
  have h1le_log : (1 : ℝ) ≤ log x := le_of_lt hlog_gt_one

  -- Hence `(log x)^3 ≥ 1`, so its reciprocal is ≤ 1.
  have hpow_ge : (1 : ℝ) ≤ (log x) ^ (3 : ℝ) := by
    have : (1 : ℝ) ^ (3 : ℝ) ≤ (log x) ^ (3 : ℝ) :=
      Real.rpow_le_rpow (by norm_num) h1le_log (by norm_num)
    simpa using this
  have hdiv : (1 / (log x) ^ (3 : ℝ)) ≤ (1 : ℝ) := by
    have : (1 / (log x) ^ (3 : ℝ)) ≤ 1 / (1 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hpow_ge
    simpa using this

  simpa [gap_delta_def] using hdiv


lemma gap_delta_strict_antitone_of_lt {a b : ℝ} (ha : 1 < a) (hab : a < b) :
    gap.δ b < gap.δ a := by
  have ha_pos : 0 < a := lt_trans (by norm_num) ha
  have hlog_lt : log a < log b := log_lt_log ha_pos hab
  have hloga_pos : 0 < log a := Real.log_pos ha
  have hloga_nonneg : 0 ≤ log a := le_of_lt hloga_pos
  have hpow_lt : (log a) ^ (3 : ℝ) < (log b) ^ (3 : ℝ) := by
    exact Real.rpow_lt_rpow hloga_nonneg hlog_lt (by norm_num)
  have hpow_pos : 0 < (log a) ^ (3 : ℝ) := Real.rpow_pos_of_pos hloga_pos (3 : ℝ)
  have hdiv_lt : (1 / (log b) ^ (3 : ℝ)) < 1 / (log a) ^ (3 : ℝ) :=
    one_div_lt_one_div_of_lt hpow_pos hpow_lt
  simpa [gap_delta_def] using hdiv_lt


/-
Complete structural assumptions:
1. X₀ ≥ 1
2. gap.δ(x) ≥ 0 for x ≥ X₀
3. gap.δ(x) is decreasing for x ≥ X₀
4. √n ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2
    -- equivalent to (1 + gap.δ(√n)) ^ 3 ≤ √n when n, gap.δ(√n) ≥ 0
5. (1 + gap.δ (√n)) ^ 6 < √n for n ≥ X₀ ^ 2, this implies 4. when 1 + gap.δ(√n) ≥ 0
6. 4 * (1 + gap.δ (√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2
-/

/- theorem `exists_p_primes` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ ≥ 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
  3. gap.δ is decreasing for x ≥ X₀
-/

lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  /- holds when X₀ ≥ 0 -/
  sorry

lemma step1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  /- holds when X₀ ≥ 0 and gap.δ(√n) ≥ 0 for n ≥ X₀^2 -/
  sorry


lemma step2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  /- holds when X₀ ≥ 0 and gap.δ(√n) ≥ 0 for n ≥ X₀^2 -/
  sorry


lemma step1_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  /- holds when x, ε ≥ 0 and gap.δ(x * (1 + gap.δ(x))) ≤ gap.δ(x)-/
  /- this holds when gap.δ is decreasing for x ≥ X₀ -/
  sorry


lemma step2_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  /- holds when x, ε ≥ 0 and gap.δ(x * (1 + gap.δ(x)) ^ 2) ≤ gap.δ(x) -/
  /- this holds when gap.δ is decreasing for x ≥ X₀ -/
  sorry

/- End of theorem `exists_p_primes` lemmas-/


/- theorem `exists_q_primes` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. √n ≤ n / (1 + gap.δ(√n)) ^ 3
  2. gap.δ is decreasing for x ≥ X₀
  3. gap.δ(x) ≥ 0 for x ≥ X₀
-/
lemma y0_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
  /- this holds when X₀ ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2 -/
  /- and this is automatically true if we can show a stronger version, which would be helpful for the following lemmas
   i.e. √n ≤ n / (1 + gap.δ(√n)) ^ 3 for n ≥ X₀ ^ 2
  -/
  sorry


lemma y1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  /- Derived from `y0_ge_X₀` plus the fact that dividing by `(1+ε)^2` is larger than
     dividing by `(1+ε)^3` when `1+ε ≥ 1`. -/
  /- This holds when gap.δ(x) ≥ 0 for x ≥ X₀ -/
  sorry

lemma y2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) := by
  /- Same pattern as `y1_ge_X₀`: `n/(1+ε) ≥ n/(1+ε)^2`. -/
  /- This holds when gap.δ(x) ≥ 0 for x ≥ X₀ -/
  sorry

lemma y0_mul_one_add_delta_le_y1 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
    y0 * (1 + gap.δ y0) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and a "stronger" version of
  `lemma y0_ge_X₀`, i.e. n / (1 + ε) ^ 3 ≥ √n for n ≥ X₀ ^ 2
  -/
  sorry

lemma y1_mul_one_add_delta_le_y2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
    y1 * (1 + gap.δ y1) ≤ (n : ℝ) / (1 + ε) := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and
  n / (1 + ε) ^ 2 ≥ √n for n ≥ X₀ ^ 2
    -- when n, ε ≥ 0, this holds automatically if `y0_mul_one_add_delta_le_y1` holds.
  -/
  sorry

lemma y2_mul_one_add_delta_lt_n {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y2 : ℝ := (n : ℝ) / (1 + ε)
    y2 * (1 + gap.δ y2) < (n : ℝ) := by
  /- holds when gap.δ is decreasing for x ≥ X₀ and
  n / (1 + ε) ≥ √n for n ≥ X₀ ^ 2
    -- when n, ε ≥ 0, this holds automatically if `y0_mul_one_add_delta_le_y1` holds.
  -/
  sorry
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
lemma b_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < b n := by
  /- 1 + δ(√n) ≥ 0 for n ≥ X₀ ^ 2
   This holds when δ(x) ≥ 0 for x ≥ X₀ and X₀ ≥ 0 -/
  sorry


lemma prod_q_rhs_reindex (n : ℕ) :
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
  sorry



lemma inv_le_rpow_div_of_lower_bound {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {t : ℝ} {q : ℕ}
    (hq : (n : ℝ) * (b n) ^ (-t) ≤ (q : ℝ)) :
    (1 : ℝ) / (q : ℝ) ≤ (b n) ^ t / n := by
  /- This is structural, just rearrange the inequality -/
  /- This holds when q ≠ 0 and δ(x) ≥ 0 for x ≥ X₀ and X₀ > 0 -/
  sorry

/- End of theorem `prod_q_ge` lemmas-/



/- theorem `prod_p_ge` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
-/
lemma one_add_delta_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < (1 + gap.δ (√(n : ℝ))) := by
  /- This holds when δ(x) ≥ 0 for x ≥ X₀ and X₀ > 0-/
  sorry


lemma p_mul_padd1_le_bound
    {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {p : Fin 3 → ℕ}
    (hp_prime : ∀ i, Nat.Prime (p i))
    (hp_mono : StrictMono p)
    (hp_ub :
      ∀ i, (p i : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (i + 1 : ℝ))
    (hsqrt_lt_p0 : √(n : ℝ) < p 0) :
    ∀ i : Fin 3,
      ((p i * (p i + 1) : ℕ) : ℝ)
        ≤ (1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ) * (n + √n) := by
  /- This holds when δ(x) ≥ 0 for x ≥ X₀ and n > 0, which is true when X₀ > 0 -/
  sorry

/- End of theorem `prod_p_ge` lemmas-/

/- theorem `pq_ratio_ge` lemmas -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. X₀ > 0
  2. gap.δ(x) ≥ 0 for x ≥ X₀
-/

lemma n_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : (0 : ℝ) < (n : ℝ) := by
  /- This holds when X₀ ≠ 0 -/
  sorry



lemma pq_ratio_rhs_as_fraction {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
      =
    ((4 : ℝ) * ∏ i : Fin 3,
        (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ))
      /
    (∏ i : Fin 3,
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ))) := by
    /- This is structural
     This holds when gap.δ(x) ≥ 0 for x ≥ X₀, and X₀ > 0 -/
    sorry
/- End of theorem `pq_ratio_ge` lemmas-/


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
lemma one_le_X₀_sq : (1 : ℕ) ≤ X₀ ^ 2 := by
  /- This holds when X₀ > 1 -/
  /-
  Proof idea:
  - for the current `PrimeGaps.latest`, `X₀` is a concrete positive numeral (89693),
    so this is `decide`/`norm_num`.
  -/
  sorry
/- End of `hn` lemmas-/

/- `h_ord_2` lemmas -/
lemma ord2_mid {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ)
      <
    (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) := by
  /- This holds when
    1. gap.δ(x) ≥ 0 for x ≥ X₀
    2. X₀ > 0
    3. (1 + gap.δ (√n)) ^ 6 < √n for n ≥ X₀ ^ 2
    4. 4 * (1 + gap.δ (√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2
   -/
  sorry
/- End of `h_ord_2` lemmas -/

/- `h_crit` lemmas -/
theorem main_ineq_delta_form {n : ℕ} (hn : n ≥ X₀ ^ 2) :
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
  sorry


lemma delta_prod_mul_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ)
              * ((n : ℝ) + √(n : ℝ)) )))
        * (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
  /- holds when gap.δ(x) > 0 for x ≥ X₀ and X₀ > 0 -/
  sorry

lemma delta_ratio_term_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  /- holds when 4 * (1 + gap.δ(√n)) ^ 12 ≤ n ^ (3 / 2) for n ≥ X₀ ^ 2 -/
  sorry

/- End of `h_crit` lemmas-/

/- Lemmas required to prove h_crit: `theorem main_ineq_delta_form` -/
/- Structural assumptions required
assuming n ≥ X₀ ^ 2 throughout
  1. gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2
  2. X₀ > 0 and n > 0
-/
lemma delta_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  /- This holds when gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2 -/
  /-- (Cert) Numerical bound on the prime-gap delta at √n: `δ(√n) ≤ 0.000675` for `n ≥ X₀^2`. -/
  /- *** Proof idea (Dusart provider) *** :
  - unfold `gap := PrimeGaps.latest` and the definition of δ;
  - use monotonicity of `x ↦ 1/(log x)^3` for x ≥ X₀ and the numerical estimate at X₀;
  - convert `hn : n ≥ X₀^2` into `√n ≥ X₀`, then finish by monotonicity + `norm_num`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  /- This holds when X₀ > 0 and n > 0 -/
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ X₀`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/X₀)`.
  -/
  sorry


lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  /- This holds when X₀ > 0 and n > 0 -/
  /- *** Proof idea *** :
  - from `√n ≥ X₀` deduce `√n ≤ (n:ℝ) / X₀` (since `n = (√n)^2`)
  - so `n + √n ≤ n + n/X₀ = (1+1/X₀)*n`
  - invert both sides (positive) to get the lower bound for `1/(n+√n)`
  -/
  sorry

theorem main_ineq_delta_form_lhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (∏ i : Fin 3,
        (1 + (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ)))
      ≤ (∏ i : Fin 3,
        (1 + (1.000675 : ℝ) ^ ((i : ℕ) + 1 : ℝ) / (n : ℝ))) := by
      /- This holds when gap.δ(√n) ≤ 0.000675 for n ≥ X₀ ^ 2 -/
      /- *** Proof idea *** :
        by applying `delta_sqrt_le` to bound `gap.δ (√(n : ℝ))` by `0.000675` -/
      sorry

theorem main_ineq_delta_form_rhs {n : ℕ} (hn : n ≥ X₀ ^ 2) :
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
      sorry


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

/- End of lemmas required to prove h_crit: `theorem main_ineq_delta_form` -/




/- Lemmas that are `possibly` not useful -/
lemma hx₀_pos : (0 : ℝ) < X₀ := by
    unfold X₀; norm_num
@[simp] lemma X₀_pos : (0 : ℝ) < (X₀ : ℝ) := by
  exact hx₀_pos

lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)

lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  dsimp [X₀]
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

lemma hlog {n : ℕ} (hn : n ≥ X₀ ^ 2) : log √(n : ℝ) ≥ 11.4 := by
  have hpos : (0 : ℝ) < X₀ := by
    -- try without unfolding first
   unfold X₀
   norm_num
  calc log √(n : ℝ) ≥ log (X₀ : ℝ) :=
        log_le_log hpos (hsqrt_ge hn)
    _ ≥ 11.4 := log_X₀_gt.le


lemma hε_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < 1 + 1 / (log √(n : ℝ)) ^ 3 := by
  positivity [hlog hn]

lemma log_X₀_pos : 0 < Real.log X₀ := by linear_combination log_X₀_gt



/- Original Cert lemmas -/



/- End of Original Cert lemmas -/


end Numerical

end Lcm
