import Architect
import PrimeNumberTheoremAnd.Lcm.Base

namespace Lcm

open ArithmeticFunction hiding log
open Finset Nat Real
open scoped BigOperators

namespace Numerical


/-!
`Cert.lean` is the ONLY place with hard-coded numeric constants and proofs about them.

It defines the *numeric contract* that `ChoosePrime.lean` will assume.
-/

/-- Numeric/analytic contract: the properties of `X₀` and `gap.δ` needed for prime selection. -/
structure Criterion where
  /- Whatever properties ChoosePrime needs, but no primes p/q here. -/
  sqrt_ge_X₀ : ∀ {n : ℕ}, n ≥ X₀ ^ 2 → (X₀ : ℝ) ≤ √(n : ℝ)
  eps_nonneg : ∀ {n : ℕ}, n ≥ X₀ ^ 2 → 0 ≤ gap.δ (√(n : ℝ))
  inv_cube_log_sqrt_le :
    ∀ {n : ℕ}, n ≥ X₀ ^ 2 → 1 / (log √(n : ℝ)) ^ 3 ≤ (0.000675 : ℝ)
  /- add the rest of your numeric lemmas here -/
  -- ...



noncomputable abbrev eps_log : ℝ := (0.000675 : ℝ)
noncomputable abbrev onePlusEps_log : ℝ := (1 : ℝ) + eps_log


blueprint_comment /--
\subsection{Reduction to a small epsilon-inequality}
-/


/- theorem `exists_p_primes` lemmas -/
/- vote: 2 -/
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


lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  /-- (C1) `x := √n` is above the provider threshold. -/
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


lemma step1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt_one : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀_one hx₀
  have hδ_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt_one
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := sqrt_nonneg (n : ℝ)
  have h1 : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) := by
    exact le_add_of_nonneg_right hδ_nonneg
  have hsqrt_le : √(n : ℝ) ≤ √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) :=
    le_mul_of_one_le_right hsqrt_nonneg h1
  exact le_trans hx₀ hsqrt_le


lemma step2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  have hstep1 : (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) :=
    step1_ge_X₀ (n := n) hn
  have hx₀ : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hsqrt_one : (1 : ℝ) < √(n : ℝ) := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ gap.δ (√(n : ℝ)) :=
    gap_delta_nonneg_of_one_lt (x := √(n : ℝ)) hsqrt_one
  have h1 : (1 : ℝ) ≤ 1 + gap.δ (√(n : ℝ)) :=
    le_add_of_nonneg_right hε_nonneg
  have hsqrt_nonneg : 0 ≤ √(n : ℝ) := sqrt_nonneg (n : ℝ)
  have honeplus_nonneg : 0 ≤ (1 + gap.δ (√(n : ℝ))) := by
    linarith
  have hprod_nonneg : 0 ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) :=
    mul_nonneg hsqrt_nonneg honeplus_nonneg
  have hmul :
      (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))
        ≤ ((√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))) * (1 + gap.δ (√(n : ℝ))) :=
    le_mul_of_one_le_right hprod_nonneg h1
  have hmul' :
      (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ)))
        ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul
  exact hstep1.trans hmul'


lemma step1_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  have hx₀ : (X₀ : ℝ) ≤ x := by
    have : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
    simpa [hx] using this
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hx_one : (1 : ℝ) < x := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using gap_delta_nonneg_of_one_lt (x := x) hx_one
  have h1 : (1 : ℝ) ≤ 1 + ε := le_add_of_nonneg_right hε_nonneg
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have honeplus_nonneg : 0 ≤ (1 + ε) := by
    linarith
  have hxy : x ≤ x * (1 + ε) :=
    le_mul_of_one_le_right hx_nonneg h1
  have hδ_le : gap.δ (x * (1 + ε)) ≤ ε := by
    have : gap.δ (x * (1 + ε)) ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := x * (1 + ε)) hx_one hxy
    simpa [hε] using this
  have h1' : (1 : ℝ) + gap.δ (x * (1 + ε)) ≤ 1 + ε := by
    linarith
  have hmul_nonneg : 0 ≤ x * (1 + ε) := mul_nonneg hx_nonneg honeplus_nonneg
  have hmul : (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ (x * (1 + ε)) * (1 + ε) :=
    mul_le_mul_of_nonneg_left h1' hmul_nonneg
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hmul


lemma step2_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  dsimp
  set x : ℝ := √(n : ℝ) with hx
  set ε : ℝ := gap.δ x with hε
  have hx₀ : (X₀ : ℝ) ≤ x := by
    have : (X₀ : ℝ) ≤ √(n : ℝ) := sqrt_ge_X₀ (n := n) hn
    simpa [hx] using this
  have hX₀_one : (1 : ℝ) < (X₀ : ℝ) := by
    unfold X₀
    norm_num
  have hx_one : (1 : ℝ) < x := lt_of_lt_of_le hX₀_one hx₀
  have hε_nonneg : 0 ≤ ε := by
    simpa [hε] using gap_delta_nonneg_of_one_lt (x := x) hx_one
  have h1 : (1 : ℝ) ≤ 1 + ε := le_add_of_nonneg_right hε_nonneg
  have hx_nonneg : 0 ≤ x := by
    simpa [hx] using (sqrt_nonneg (n : ℝ))
  have honeplus_nonneg : 0 ≤ (1 + ε) := by
    linarith
  have hpow_one : (1 : ℝ) ≤ (1 + ε) ^ 2 := by
    have hmul : (1 : ℝ) * (1 : ℝ) ≤ (1 + ε) * (1 + ε) :=
      mul_le_mul h1 h1 (by norm_num) honeplus_nonneg
    simpa [pow_two] using hmul
  have hxy : x ≤ x * (1 + ε) ^ 2 :=
    le_mul_of_one_le_right hx_nonneg hpow_one
  have hδ_le : gap.δ (x * (1 + ε) ^ 2) ≤ ε := by
    have : gap.δ (x * (1 + ε) ^ 2) ≤ gap.δ x :=
      gap_delta_antitone_of_le (a := x) (b := x * (1 + ε) ^ 2) hx_one hxy
    simpa [hε] using this
  have h1' : (1 : ℝ) + gap.δ (x * (1 + ε) ^ 2) ≤ 1 + ε := by
    linarith
  have hmul_nonneg : 0 ≤ x * (1 + ε) ^ 2 := by
    exact mul_nonneg hx_nonneg (sq_nonneg (1 + ε))
  have hmul :
      (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2))
        ≤ (x * (1 + ε) ^ 2) * (1 + ε) :=
    mul_le_mul_of_nonneg_left h1' hmul_nonneg
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hmul


/- End of theorem `exists_p_primes` lemmas-/


/- theorem `exists_q_primes` lemmas -/
lemma y0_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
    /- *** Proof idea ***:
    this is your current `hy₀_ge` proof -/
    sorry


lemma y1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    /- *** Proof idea ***:
    derived from y0_ge_X₀ and monotonicity of division by positive numbers
    -/
    sorry

lemma y2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) := by
    /- *** Proof idea ***:
    same pattern as y1_ge_X₀ -/
    sorry

lemma y0_mul_one_add_delta_le_y1 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
    y0 * (1 + gap.δ y0) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    /- Step 0: from y0’s Dusart upper bound to y1. -/
    /- *** Proof idea ***:
    y0 ≥ x  (proved below or inline)
    δ(y0) ≤ ε  (Dusart monotonicity of 1/log^3)
    algebra: y0*(1+ε)= n/(1+ε)^2 -/
    sorry


lemma y1_mul_one_add_delta_le_y2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
    y1 * (1 + gap.δ y1) ≤ (n : ℝ) / (1 + ε) := by
    /-- Step 1: from y1’s upper bound to y2. -/
    /- *** Proof idea ***:
    same pattern-/
    sorry

lemma y2_mul_one_add_delta_lt_n {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y2 : ℝ := (n : ℝ) / (1 + ε)
    y2 * (1 + gap.δ y2) < (n : ℝ) := by
    /- Final strict step: from y2’s upper bound to strictly below n. -/
    /- *** Proof idea ***:
    this is where you currently do the “strict log inequality” work
    i.e. prove δ(y2) < ε using y2 > x, then
    y2*(1+δ y2) < y2*(1+ε) = n -/
    sorry

/- End of theorem `exists_q_primes` lemmas-/


/- theorem `prod_q_ge` lemmas -/
noncomputable abbrev b (n : ℕ) : ℝ := 1 + gap.δ (√(n : ℝ))
/--
`b(n)` is the “1 + δ(√n)” base that appears everywhere in q-side bounds.
We do *not* export `b` into theorem statements; it’s just a local convenience for Cert lemmas.
Try moving this entirely into `prod_q_ge` if possible.
-/

/- *** This lemma is likely not used *** -/
lemma b_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < b n := by
  /-- Positivity of `b(n) = 1 + δ(√n)` for `n ≥ X₀²`. -/
  /- *** Proof idea ***:
  show `0 ≤ gap.δ (√n)` (Dusart: `δ(x)=1/(log x)^3` and `log √n > 0`), then `linarith`.
  use your existing certified `log` bounds in the Dusart instance, or (better)
  a provider-specific lemma `δ_nonneg` exported from the provider/cert layer-/
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
  /- Core inequality used in `prod_q_ge`:
     From a lower bound `n * b(n)^(-t) ≤ q` we get the reciprocal upper bound
     `1/q ≤ b(n)^t / n`. -/
  /- *** Proof idea ***: (this is exactly what your current Main proof does)
  rewrite `b(n)^t / n = 1 / (n / b(n)^t)` (via `field_simp`, using `n>0`, `b(n)>0`)
  apply `one_div_le_one_div_of_le` using positivity of `n / b(n)^t`
  convert `hq` to `n / b(n)^t ≤ q` using `field_simp` + `Real.rpow_add` (or `Real.rpow_neg`).
  -/
  sorry

/- End of theorem `prod_q_ge` lemmas-/



/- theorem `prod_p_ge` lemmas -/
lemma one_add_delta_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < (1 + gap.δ (√(n : ℝ))) := by
  /- Certification lemma: `1 + gap.δ(√n)` is positive once `n ≥ X₀²`. -/
  /- *** Proof idea (Dusart provider): ***
  `gap.δ x = 1/(log x)^3` and for `n ≥ X₀²` we have `√n ≥ X₀`, hence `log √n ≥ log X₀ > 0`,
  so `δ(√n) ≥ 0` and thus `1 + δ(√n) > 0`. -/
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
  /-- Key denominator bound for the `p`-product:
      Given `p : Fin 3 → ℕ` satisfying the same hypotheses as `exists_p_primes` exports,
      we bound `p_i(p_i+1)` above by the RHS denominator.
      No `log` appears in the statement; only `gap.δ`. -/
  /- *** Proof sketch (copy/paste from your old `prod_p_ge` inner proof): ***
  From `hsqrt_lt_p0` and `hp_mono`, deduce `√n < p i` for all `i`.
  From `hp_ub i`, square to get `(p i : ℝ)^2 ≤ (n : ℝ) * (1+δ(√n))^(2*i+2)`.
  From `√n < p i`, show `(p i : ℝ) + 1 ≤ (p i : ℝ) * ((n+√n)/n)`
    via your existing `field_simp; linear_combination` trick.
  Multiply and rearrange, then cast `p i * (p i + 1)` into `ℝ`.
  -/
  sorry

/- End of theorem `prod_p_ge` lemmas-/

/- theorem `pq_ratio_ge` lemmas -/

lemma n_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : (0 : ℝ) < (n : ℝ) := by
  /- Cast-positivity of `n` from the assumption `n ≥ X₀²`. -/
  /- **Proof idea:**
  `X₀ ≥ 1` (or just `X₀^2 > 0`) so `n > 0` in `ℕ`, then cast to `ℝ`. -/
  sorry



lemma pq_ratio_rhs_as_fraction {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
      =
    ((4 : ℝ) * ∏ i : Fin 3,
        (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ))
      /
    (∏ i : Fin 3,
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ))) := by
    /- RHS rewrite for `pq_ratio_ge`** (this is the key “plumbing lemma”).
      It rewrites the analytic bound
      `4 * (1 + δ(√n))^12 / n^(3/2)`
      into a ratio of two *products* that match the pointwise bounds exported by
      `exists_p_primes` and `exists_q_primes`. -/
    /- **Proof idea:** let `b := 1 + gap.δ(√n)` (note `b>0`).
    Compute explicitly over `Fin 3`:
    - `∏ i, √n * b^((i:ℕ)+1) = n^(3/2) * b^6`
    - `∏ i, (n:ℝ) / b^((3:ℕ)-(i:ℕ)) = n^3 * b^(-6)`
    Then combine to get the ratio equals `b^12 / n^(3/2)` and multiply by `4`. -/
  sorry
/- End of theorem `pq_ratio_ge` lemmas-/


/-
Final criterion structure in Main.lean
-/

/- `hn` lemmas -/
lemma one_le_X₀_sq : (1 : ℕ) ≤ X₀ ^ 2 := by
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
  /- (Cert) The key “middle inequality” used in `h_ord_2`: upper bound for `p₂` is below lower bound for `q₀`. -/
  /- *** Proof idea *** :
  - Let b := 1 + δ(√n). From `delta_sqrt_le` get b ≤ 1.000675.
  - Then b^6 ≤ (1.000675)^6 < 2 (checked by `norm_num`).
  - Also from `hn : n ≥ X₀^2` we know √n ≥ X₀, and for the concrete X₀ we have 2 ≤ √n.
  - So b^6 < √n, which is equivalent to √n*b^3 < n/b^3 (algebra, using n = (√n)^2).
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
  1) Use `delta_sqrt_le` to bound `gap.δ(√n) ≤ 0.000675`, hence `1+gap.δ(√n) ≤ 1.000675`.
  2) Use `inv_n_pow_3_div_2_le_X₀` to replace `1/n^(3/2)` by `(1/X₀)*(1/n)`.
  3) Use `inv_n_add_sqrt_ge_X₀` to replace `1/(n+√n)` by `(1/(1+1/X₀))*(1/n)`.
  4) Set `ε := 1/n` and use the hypotheses `0 ≤ ε` and `ε ≤ 1/(X₀^2)` (derived from `hn`).
  5) Apply `prod_epsilon_le`, `prod_epsilon_ge`, and `final_comparison` to finish.
  -/
  sorry


lemma delta_prod_mul_nonneg {n : ℕ} (hn : n ≥ Lcm.X₀ ^ 2) :
    0 ≤
      (∏ i : Fin 3,
          (1 + 1 /
            ((1 + Lcm.gap.δ (√(n : ℝ))) ^ (2 * (i : ℕ) + 2 : ℝ)
              * ((n : ℝ) + √(n : ℝ)) )))
        * (1 + (3 : ℝ) / (8 * (n : ℝ))) := by
  /- *** Proof idea ***:
  1) `hn` ⇒ `0 < (n:ℝ)`; hence also `0 < (n:ℝ) + √(n:ℝ)`.
  2) `one_add_delta_pos hn` ⇒ `0 < 1 + δ(√n)` ⇒ `0 < (1+δ(√n))^(...)` by `Real.rpow_pos_of_pos`.
  3) Therefore the denominator in each factor is positive, so `1 / denom ≥ 0`,
     hence each factor `1 + ... ≥ 0`, so the product is ≥ 0.
  4) Also `1 + 3/(8*n) ≥ 0`. Multiply nonnegatives.
  -/
  sorry

lemma delta_ratio_term_nonneg {n : ℕ} (hn : n ≥ Lcm.X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + Lcm.gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  /- *** Proof idea (in Cert) ***:
  - Use `delta_sqrt_le hn : gap.δ(√n) ≤ 0.000675` so `(1+δ)^12 ≤ (1.000675)^12`.
  - Use `inv_n_pow_3_div_2_le_X₀ hn : 1/n^(3/2) ≤ (1/X₀)*(1/n)`.
  - Combine to show `4*(1+δ)^12 / n^(3/2) ≤ 4*(1.000675)^12*(1/X₀)*(1/n)`.
  - Then use `hn` (so `1/n ≤ 1/X₀^2`) and `norm_num` (after `dsimp [X₀]`)
    to show the RHS ≤ 1.
  - Conclude `0 ≤ 1 - (...)` i.e. the subtracted term is ≤ 1.
  -/
  sorry

/- End of `h_crit` lemmas-/

/- Lemmas that are possibly useful in the intermediate bridge -/
lemma delta_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  /-- (Cert) Numerical bound on the prime-gap delta at √n: `δ(√n) ≤ 0.000675` for `n ≥ X₀^2`. -/
  /- *** Proof idea (Dusart provider) *** :
  - unfold `gap := PrimeGaps.latest` and the definition of δ;
  - use monotonicity of `x ↦ 1/(log x)^3` for x ≥ X₀ and the numerical estimate at X₀;
  - convert `hn : n ≥ X₀^2` into `√n ≥ X₀`, then finish by monotonicity + `norm_num`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / n) := by
  /- (Cert) Bound `1/n^(3/2)` by `(1/89693) * (1/n)` for `n ≥ X₀^2`. -/
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  /- *** Proof idea *** :
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

lemma inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) + √(n : ℝ)) ≥ (1 / (1 + 1 / (89693 : ℝ))) * (1 / n) := by
  /- (Cert) Lower bound for `1/(n+√n)` in terms of `1/n`. -/
  /- *** Proof idea *** :
  - show `n + √n ≤ (1 + 1/89693)*n` using `√n ≤ n/89693` from `√n ≥ 89693`;
  - invert (monotone since positive) to obtain the displayed inequality.
  -/
  sorry

lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  /- *** Proof idea *** :
  - from `√n ≥ X₀` deduce `√n ≤ (n:ℝ) / X₀` (since `n = (√n)^2`)
  - so `n + √n ≤ n + n/X₀ = (1+1/X₀)*n`
  - invert both sides (positive) to get the lower bound for `1/(n+√n)`
  -/
  sorry

lemma inv_n_le_inv_X₀_sq {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (X₀ ^ 2 : ℕ) := by
  /- *** Proof idea *** :
  - cast `hn` to reals: `(X₀^2 : ℝ) ≤ (n : ℝ)`
  - use `one_div_le_one_div_of_le` with positivity of `(X₀^2 : ℝ)`
  -/
  sorry


/- End of lemmas that are possibly useful in the intermediate bridge -/



/- Lemmas that are possibly useful in the proof of theorems in Cert.lean -/
lemma sqrt_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < √(n : ℝ) := by
  /- positivity of `x := √n`. -/
  -- can be `lt_of_lt_of_le (show (0:ℝ) < (X₀:ℝ) from ...) (sqrt_ge_X₀ hn)`
  -- or whatever you currently do
  sorry


lemma eps_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ gap.δ (√(n : ℝ)) := by
  /-- nonnegativity of `ε := δ(x)` at `x := √n`. -/
  -- Dusart: follows from `0 < log x` hence `(log x)^3 > 0` hence `1/(...) ≥ 0`.
  -- Other providers: whatever you can prove.
  sorry


lemma crit_rhs_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + (0.000675 : ℝ)) ^ 12 * ((1 / (X₀ : ℝ)) * (1 / (n : ℝ))) := by
  /-
  Proof idea:
  - Use `hn` to replace `n` by `X₀^2` as worst case (since 1/n decreases with n).
  - Then unfold `X₀` (to 89693) *inside this lemma only* and let `norm_num` finish.
  -/
  -- typical proof outline:
  --   have hx : (1/(n:ℝ)) ≤ 1/((X₀^2:ℕ):ℝ) := inv_n_le_inv_X₀_sq hn
  --   bound the expression using monotonicity in (1/n)
  --   simp [X₀] at the end; norm_num
  sorry


/- End of lemmas that are possibly useful in the proof of theorem in Cert.lean -/


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

theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
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

/- End of Original Cert lemmas -/




/-- The certified package (built from the concrete numerals in this file). -/
noncomputable def criterion : Criterion := by
  classical
  refine
    { sqrt_ge_X₀ := ?_
      eps_nonneg := ?_
      inv_cube_log_sqrt_le := ?_
      -- ...
    }
  · intro n hn; sorry
  · intro n hn; sorry
  · intro n hn; sorry

end Numerical

end Lcm
