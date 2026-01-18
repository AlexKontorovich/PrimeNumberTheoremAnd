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



-- What was refactored out of theorem exists_p_primes
-- lemma 1
lemma hx₀_pos : (0 : ℝ) < X₀ := by
    unfold X₀; norm_num
@[simp] lemma X₀_pos : (0 : ℝ) < (X₀ : ℝ) := by
  exact hx₀_pos

-- lemma 2
lemma hsqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) : √(n : ℝ) ≥ X₀ := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


-- lemma 3
lemma log_X₀_gt : Real.log X₀ > 11.4 := by
  dsimp [X₀]
  rw [gt_iff_lt, show (11.4 : ℝ) = 57 / (5 : ℕ) by norm_num, div_lt_iff₀ (by norm_num),
    mul_comm, ← Real.log_pow, Real.lt_log_iff_exp_lt (by norm_num), ← Real.exp_one_rpow]
  grw [Real.exp_one_lt_d9]
  norm_num

-- lemma 4
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

lemma X₀_sq_pos : (0 : ℝ) < ((X₀ ^ 2 : ℕ) : ℝ) := by
  have : (0 : ℝ) < (X₀ : ℝ) := X₀_pos
  -- `(X₀^2 : ℝ) = (X₀:ℝ)^2` by norm_cast; then positivity
  sorry


/- The following lemmas are used to prove exists_p_primes -/
/-This lemma is used in exists_q_primes-/
/-- (C1) `x := √n` is above the provider threshold. -/
lemma sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ √(n : ℝ) := by
  simpa using sqrt_le_sqrt (by exact_mod_cast hn : (n : ℝ) ≥ X₀ ^ 2)


/-- (C4) step-1 threshold propagation:
`x*(1+ε)` is still ≥ X₀ so we can apply the provider at that point. -/
lemma step1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) := by
  -- uses sqrt_ge_X₀ + eps_nonneg + le_mul_of_one_le_right etc
  sorry

/-- (C5) step-2 threshold propagation:
`x*(1+ε)^2` is still ≥ X₀. -/
lemma step2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (X₀ : ℝ) ≤ (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ 2 := by
  -- same pattern; uses `pow_two`/`sq_nonneg` etc
  sorry

/-- (C6) step-1 *upper bound* simplifier:
turn provider’s bound at `y = x*(1+ε)` into a bound by `x*(1+ε)^2`. -/
lemma step1_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε)) * (1 + gap.δ (x * (1 + ε))) ≤ x * (1 + ε) ^ 2 := by
  -- This is exactly where your old `upper` lemma + log monotonicity lives.
  -- For Dusart: δ decreases with x, so δ(x*(1+ε)) ≤ δ(x)=ε, then multiply out.
  sorry

/-- (C7) step-2 upper bound:
turn provider’s bound at `y = x*(1+ε)^2` into ≤ `x*(1+ε)^3`. -/
lemma step2_upper {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (x * (1 + ε) ^ 2) * (1 + gap.δ (x * (1 + ε) ^ 2)) ≤ x * (1 + ε) ^ 3 := by
  -- Same style as step1_upper.
  sorry


/- End of lemmas in exists_p_primes -/


/- The following lemmas are used in exists_q_primes-/
lemma y0_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 3 := by
    sorry
  -- this is your current `hy₀_ge` proof

lemma y1_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    sorry
  -- derived from y0_ge_X₀ and monotonicity of division by positive numbers

lemma y2_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    (X₀ : ℝ) ≤ (n : ℝ) / (1 + ε) := by
    sorry
  -- same

/-- Step 0: from y0’s Dusart upper bound to y1. -/
lemma y0_mul_one_add_delta_le_y1 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y0 : ℝ := (n : ℝ) / (1 + ε) ^ 3
    y0 * (1 + gap.δ y0) ≤ (n : ℝ) / (1 + ε) ^ 2 := by
    sorry
  -- uses:
  --   - y0 ≥ x  (proved below or inline)
  --   - δ(y0) ≤ ε  (Dusart monotonicity of 1/log^3)
  --   - algebra: y0*(1+ε)= n/(1+ε)^2

/-- Step 1: from y1’s upper bound to y2. -/
lemma y1_mul_one_add_delta_le_y2 {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y1 : ℝ := (n : ℝ) / (1 + ε) ^ 2
    y1 * (1 + gap.δ y1) ≤ (n : ℝ) / (1 + ε) := by
    sorry
  -- same pattern

/-- Final strict step: from y2’s upper bound to strictly below n. -/
lemma y2_mul_one_add_delta_lt_n {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    let x : ℝ := √(n : ℝ)
    let ε : ℝ := gap.δ x
    let y2 : ℝ := (n : ℝ) / (1 + ε)
    y2 * (1 + gap.δ y2) < (n : ℝ) := by
    sorry
  -- this is where you currently do the “strict log inequality” work
  -- i.e. prove δ(y2) < ε using y2 > x, then
  -- y2*(1+δ y2) < y2*(1+ε) = n

/- End of lemmas in exists_q_primes-/


/- The following lemmas are used in prod_q_ge-/
/--
`b(n)` is the “1 + δ(√n)” base that appears everywhere in q-side bounds.

We do *not* export `b` into theorem statements; it’s just a local convenience for Cert lemmas.
-/
noncomputable abbrev b (n : ℕ) : ℝ := 1 + gap.δ (√(n : ℝ))

/-- Positivity of `b(n) = 1 + δ(√n)` for `n ≥ X₀²`.

**Proof idea:** show `0 ≤ gap.δ (√n)` (Dusart: `δ(x)=1/(log x)^3` and `log √n > 0`), then `linarith`.
-/
lemma b_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : 0 < b n := by
  -- use your existing certified `log` bounds in the Dusart instance, or (better)
  -- a provider-specific lemma `δ_nonneg` exported from the provider/cert layer
  sorry

/--
Reindexing trick for `Fin 3`: convert exponents `i+1` to `3 - i`.

This is *structural*, but it’s noisy; keeping it in Cert keeps Main clean.

**Proof idea:** exactly your current proof:
`rw [Fin.prod_univ_three, Fin.prod_univ_three]` + the `conv` blocks + `ring`,
just replacing `1 + 1/(log √n)^3` by `b n`.
-/
lemma prod_q_rhs_reindex (n : ℕ) :
    (∏ i : Fin 3, (1 + (b n) ^ ((i : ℕ) + 1 : ℝ) / n))
      =
    (∏ i : Fin 3, (1 + (b n) ^ ((3 : ℝ) - (i : ℕ)) / n)) := by
  -- copy/paste your existing `Fin.prod_univ_three`/`conv` proof
  -- with `b n` in place of `(1 + 1/(log √n)^3)`
  sorry

/--
Core inequality used in `prod_q_ge`:

From a lower bound `n * b(n)^(-t) ≤ q` we get the reciprocal upper bound
`1/q ≤ b(n)^t / n`.

**Proof idea:** (this is exactly what your current Main proof does)
1. rewrite `b(n)^t / n = 1 / (n / b(n)^t)` (via `field_simp`, using `n>0`, `b(n)>0`)
2. apply `one_div_le_one_div_of_le` using positivity of `n / b(n)^t`
3. convert `hq` to `n / b(n)^t ≤ q` using `field_simp` + `Real.rpow_add` (or `Real.rpow_neg`).
-/
lemma inv_le_rpow_div_of_lower_bound {n : ℕ} (hn : n ≥ X₀ ^ 2)
    {t : ℝ} {q : ℕ}
    (hq : (n : ℝ) * (b n) ^ (-t) ≤ (q : ℝ)) :
    (1 : ℝ) / (q : ℝ) ≤ (b n) ^ t / n := by
  sorry

/- End of lemmas in prod_q_ge-/



/- The following lemmas are used in prod_p_ge -/
/--
Certification lemma: `1 + gap.δ(√n)` is positive once `n ≥ X₀²`.

Statement mentions only `gap.δ` (no `log`).

**Proof idea (Dusart provider):**
`gap.δ x = 1/(log x)^3` and for `n ≥ X₀²` we have `√n ≥ X₀`, hence `log √n ≥ log X₀ > 0`,
so `δ(√n) ≥ 0` and thus `1 + δ(√n) > 0`.
-/
lemma one_add_delta_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < (1 + gap.δ (√(n : ℝ))) := by
  sorry

/--
Key denominator bound for the `p`-product:

Given `p : Fin 3 → ℕ` satisfying the same hypotheses as `exists_p_primes` exports,
we bound `p_i(p_i+1)` above by the RHS denominator.

No `log` appears in the statement; only `gap.δ`.

**Proof sketch (copy/paste from your old `prod_p_ge` inner proof):**
1. From `hsqrt_lt_p0` and `hp_mono`, deduce `√n < p i` for all `i`.
2. From `hp_ub i`, square to get `(p i : ℝ)^2 ≤ (n : ℝ) * (1+δ(√n))^(2*i+2)`.
3. From `√n < p i`, show `(p i : ℝ) + 1 ≤ (p i : ℝ) * ((n+√n)/n)`
   via your existing `field_simp; linear_combination` trick.
4. Multiply and rearrange, then cast `p i * (p i + 1)` into `ℝ`.
-/
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
  sorry
/- End of lemmas in prod_p_ge-/



/- The following lemmas are used in pq_ratio -/
/-- Cast-positivity of `n` from the assumption `n ≥ X₀²`.

**Proof idea:** `X₀ ≥ 1` (or just `X₀^2 > 0`) so `n > 0` in `ℕ`, then cast to `ℝ`.
-/
lemma n_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) : (0 : ℝ) < (n : ℝ) := by
  sorry



/--
**RHS rewrite for `pq_ratio_ge`** (this is the key “plumbing lemma”).

It rewrites the analytic bound
`4 * (1 + δ(√n))^12 / n^(3/2)`
into a ratio of two *products* that match the pointwise bounds exported by
`exists_p_primes` and `exists_q_primes`.

**Proof idea:** let `b := 1 + gap.δ(√n)` (note `b>0`).
Compute explicitly over `Fin 3`:
- `∏ i, √n * b^((i:ℕ)+1) = n^(3/2) * b^6`
- `∏ i, (n:ℝ) / b^((3:ℕ)-(i:ℕ)) = n^3 * b^(-6)`
Then combine to get the ratio equals `b^12 / n^(3/2)` and multiply by `4`.
-/
lemma pq_ratio_rhs_as_fraction {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    4 * (1 + gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ)
      =
    ((4 : ℝ) * ∏ i : Fin 3,
        (√(n : ℝ)) * (1 + gap.δ (√(n : ℝ))) ^ ((i : ℕ) + 1 : ℝ))
      /
    (∏ i : Fin 3,
        (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ ((3 : ℕ) - (i : ℕ))) := by
  sorry
/- End of lemmas in pq_ratio -/

/- The following lemmas are used in the proof of the final criterion-/

/-
  This file is the “numerical/certified” layer:
  it is the ONLY place that knows how `gap.δ` behaves numerically (e.g. δ ≤ 0.000675),
  and the only place with “n is huge so 1/(n+√n) …” bounds.

  In Main.lean, we only *apply* these lemmas.
-/

/-- (Cert) For the concrete `gap := PrimeGaps.latest`, we have `X₀^2 ≥ 1`. -/
lemma one_le_X₀_sq : (1 : ℕ) ≤ X₀ ^ 2 := by
  /-
  Proof idea:
  - for the current `PrimeGaps.latest`, `X₀` is a concrete positive numeral (89693),
    so this is `decide`/`norm_num`.
  -/
  sorry

-- /-- (Cert) Positivity of the “b-parameter” `1 + δ(√n)` for large `n`. -/
-- lemma one_add_delta_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
--     0 < (1 + gap.δ (√(n : ℝ))) := by
--   /-
--   Proof idea:
--   - for Dusart-style providers δ(x) is defined as a positive expression (e.g. 1/log^3 x),
--     and √n is large hence in the domain; show δ(√n) ≥ 0 and conclude.
--   -/
--   sorry


/-- (Cert) Numerical bound on the prime-gap delta at √n: `δ(√n) ≤ 0.000675` for `n ≥ X₀^2`. -/
lemma delta_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    gap.δ (√(n : ℝ)) ≤ (0.000675 : ℝ) := by
  /-
  Proof idea (Dusart provider):
  - unfold `gap := PrimeGaps.latest` and the definition of δ;
  - use monotonicity of `x ↦ 1/(log x)^3` for x ≥ X₀ and the numerical estimate at X₀;
  - convert `hn : n ≥ X₀^2` into `√n ≥ X₀`, then finish by monotonicity + `norm_num`.
  -/
  sorry

/-- (Cert) The key “middle inequality” used in `h_ord_2`: upper bound for `p₂` is below lower bound for `q₀`. -/
lemma ord2_mid {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    √(n : ℝ) * (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ)
      <
    (n : ℝ) / (1 + gap.δ (√(n : ℝ))) ^ (3 : ℕ) := by
  /-
  Proof idea:
  - Let b := 1 + δ(√n). From `delta_sqrt_le` get b ≤ 1.000675.
  - Then b^6 ≤ (1.000675)^6 < 2 (checked by `norm_num`).
  - Also from `hn : n ≥ X₀^2` we know √n ≥ X₀, and for the concrete X₀ we have 2 ≤ √n.
  - So b^6 < √n, which is equivalent to √n*b^3 < n/b^3 (algebra, using n = (√n)^2).
  -/
  sorry

/-
  These already existed in your old file and are exactly the “1/n^{3/2}” and “1/(n+√n)”
  bounds you said should live in Cert.lean.  If you already have them elsewhere, you
  can delete these stubs and just `import` that file instead.
-/

/-- (Cert) Bound `1/n^(3/2)` by `(1/89693) * (1/n)` for `n ≥ X₀^2`. -/
lemma inv_n_pow_3_div_2_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (89693 : ℝ)) * (1 / n) := by
  /-
  Proof idea:
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

lemma inv_n_pow_3_div_2_le_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) ^ (3 / 2 : ℝ)) ≤ (1 / (X₀ : ℝ)) * (1 / n) := by
  /-
  Proof idea:
  - rewrite `n^(3/2) = n*√n`;
  - from `hn` get `√n ≥ 89693`;
  - conclude `1/(n*√n) ≤ (1/n)*(1/89693)`.
  -/
  sorry

/-- (Cert) Lower bound for `1/(n+√n)` in terms of `1/n`. -/
lemma inv_n_add_sqrt_ge {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / (n : ℝ) + √(n : ℝ)) ≥ (1 / (1 + 1 / (89693 : ℝ))) * (1 / n) := by
  /-
  Proof idea:
  - show `n + √n ≤ (1 + 1/89693)*n` using `√n ≤ n/89693` from `√n ≥ 89693`;
  - invert (monotone since positive) to obtain the displayed inequality.
  -/
  sorry

lemma inv_n_add_sqrt_ge_X₀ {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 / ((n : ℝ) + √(n : ℝ))) ≥ (1 / (1 + 1 / (X₀ : ℝ))) * (1 / (n : ℝ)) := by
  /-
  Proof idea:
  - from `√n ≥ X₀` deduce `√n ≤ (n:ℝ) / X₀` (since `n = (√n)^2`)
  - so `n + √n ≤ n + n/X₀ = (1+1/X₀)*n`
  - invert both sides (positive) to get the lower bound for `1/(n+√n)`
  -/
  sorry

lemma inv_n_le_inv_X₀_sq {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (X₀ ^ 2 : ℕ) := by
  /-
  Proof idea:
  - cast `hn` to reals: `(X₀^2 : ℝ) ≤ (n : ℝ)`
  - use `one_div_le_one_div_of_le` with positivity of `(X₀^2 : ℝ)`
  -/
  sorry


/- End of lemmas in the final criterion-/


/-- (C2) positivity of `x := √n`. -/
lemma sqrt_pos {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 < √(n : ℝ) := by
  -- can be `lt_of_lt_of_le (show (0:ℝ) < (X₀:ℝ) from ...) (sqrt_ge_X₀ hn)`
  -- or whatever you currently do
  sorry

/-- (C3) nonnegativity of `ε := δ(x)` at `x := √n`. -/
lemma eps_nonneg {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    0 ≤ gap.δ (√(n : ℝ)) := by
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
  Proof outline (exactly your write-up):
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
  /-
  Proof idea:
  1) `hn` ⇒ `0 < (n:ℝ)`; hence also `0 < (n:ℝ) + √(n:ℝ)`.
  2) `one_add_delta_pos hn` ⇒ `0 < 1 + δ(√n)` ⇒ `0 < (1+δ(√n))^(...)` by `Real.rpow_pos_of_pos`.
  3) Therefore the denominator in each factor is positive, so `1 / denom ≥ 0`,
     hence each factor `1 + ... ≥ 0`, so the product is ≥ 0.
  4) Also `1 + 3/(8*n) ≥ 0`. Multiply nonnegatives.
  -/
  sorry


lemma delta_ratio_term_nonneg {n : ℕ} (hn : n ≥ Lcm.X₀ ^ 2) :
    0 ≤ 1 - 4 * (1 + Lcm.gap.δ (√(n : ℝ))) ^ 12 / (n : ℝ) ^ (3 / 2 : ℝ) := by
  /-
  Proof idea (in Cert):
  - Use `delta_sqrt_le hn : gap.δ(√n) ≤ 0.000675` so `(1+δ)^12 ≤ (1.000675)^12`.
  - Use `inv_n_pow_3_div_2_le_X₀ hn : 1/n^(3/2) ≤ (1/X₀)*(1/n)`.
  - Combine to show `4*(1+δ)^12 / n^(3/2) ≤ 4*(1.000675)^12*(1/X₀)*(1/n)`.
  - Then use `hn` (so `1/n ≤ 1/X₀^2`) and `norm_num` (after `dsimp [X₀]`)
    to show the RHS ≤ 1.
  - Conclude `0 ≤ 1 - (...)` i.e. the subtracted term is ≤ 1.
  -/
  sorry



@[blueprint
  "lem:eps-bounds"
  (title := "Uniform bounds for large \\(n\\)")
  (statement := /--
  For all \(n \ge X_0^2\) we have
  \[
    \frac{1}{\log^3 \sqrt{n}}
    \le 0.000675,
    \qquad
    \frac{1}{n^{3/2}} \le \frac{1}{X_0}\cdot\frac{1}{n}.
  \]
  and
  \[ \frac{1}{n+\sqrt{n}} \ge \frac{1}{1 + 1/X_0}\cdot\frac{1}{n}. \]
  -/)
  (proof := /-- This is a straightforward calculus and monotonicity check: the left-hand sides are
  decreasing in \(n\) for \(n \ge X_0^2\), and equality (or the claimed upper bound) holds at
  \(n=X_0^2\).  One can verify numerically or symbolically. -/)
  (latexEnv := "lemma")]
-- theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
--     1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
--   dsimp [X₀] at *
--   calc
--     1 / Real.log √n ^ 3 ≤ 1 / Real.log X₀ ^ 3 := by
--       gcongr
--       exact Real.le_sqrt_of_sq_le (mod_cast hn)
--     _ ≤ eps_log := by
--       grw [← log_X₀_gt.le]
--       simpa [eps_log] using (show (1 / (11.4 : ℝ) ^ 3) ≤ (0.000675 : ℝ) by norm_num)



theorem inv_cube_log_sqrt_le {n : ℕ} (hn : n ≥ X₀ ^ 2) :
    1 / (log √(n : ℝ)) ^ 3 ≤ eps_log := by
    sorry




@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  \]
  and
  \[
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i}}\frac{1}{1 + 1/X_0}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{X_0}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_le {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    ∏ i : Fin 3, (1 + onePlusEps_log ^ ((i : ℕ) + 1 : ℝ) * ε) ≤
      1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 := by
  norm_cast; norm_num [Fin.prod_univ_three]; nlinarith

@[blueprint
  "lem:poly-ineq"
  (title := "Polynomial approximation of the inequality")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    \prod_{i=1}^3 (1 + 1.000675^i \varepsilon)
    \le
    \Bigl(1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3\Bigr),
  \]
  and
  \[
    \prod_{i=1}^3 \Bigl(1 + \frac{\varepsilon}{1.000675^{2i} (1 + \frac{1}{X_0})}\Bigr)
    \Bigl(1 + \frac{3}{8}\varepsilon\Bigr)
    \Bigl(1 - \frac{4 \times 1.000675^{12}}{X_0}\varepsilon\Bigr)
    \ge
    1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  Expand each finite product as a polynomial in \(\varepsilon\), estimate the coefficients using
  the bounds in Lemma~\ref{lem:eps-bounds}, and bound the tails by simple inequalities such as
  \[
    (1+C\varepsilon)^k \le 1 + k C\varepsilon + \dots
  \]
  for small \(\varepsilon\).
  All coefficients can be bounded numerically in a rigorous way; this step is a finite computation
  that can be checked mechanically.
  -/)
  (latexEnv := "lemma")]
theorem prod_epsilon_ge {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    (∏ i : Fin 3,
      (1 + ε / (onePlusEps_log ^ (2 * ((i : ℕ) + 1 : ℝ))) * (1 / (1 + 1/X₀)))) *
        (1 + (3 : ℝ) / 8 * ε) * (1 - 4 * onePlusEps_log ^ 12 / X₀ * ε) ≥
      1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
  norm_cast; norm_num [Fin.prod_univ_three]
  dsimp [X₀] at *
  nlinarith [pow_nonneg hε.left 3, pow_nonneg hε.left 4]


@[blueprint
  "lem:final-comparison"
  (title := "Final polynomial comparison")
  (statement := /--
  For \(0 \le \varepsilon \le 1/X_0^2\), we have
  \[
    1 + 3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 1 + 3.36683\varepsilon - 0.01\varepsilon^2.
  \]
  -/)
  (proof := /--
  This is equivalent to
  \[
    3.01\varepsilon + 3.01\varepsilon^2 + 1.01\varepsilon^3
    \le 3.36683\varepsilon - 0.01\varepsilon^2,
  \]
  or
  \[
    0 \le (3.36683 - 3.01)\varepsilon - (3.01+0.01)\varepsilon^2 - 1.01\varepsilon^3.
  \]
  Factor out \(\varepsilon\) and use that \(0<\varepsilon \le 1/X_0^2\) to check that the
  resulting quadratic in \(\varepsilon\) is nonnegative on this interval.  Again, this is a
  finite computation that can be verified mechanically.
  -/)
  (latexEnv := "lemma")]
theorem final_comparison {ε : ℝ} (hε : 0 ≤ ε ∧ ε ≤ 1 / (X₀ ^ 2 : ℝ)) :
    1 + 3.01 * ε + 3.01 * ε ^ 2 + 1.01 * ε ^ 3 ≤ 1 + 3.36683 * ε - 0.01 * ε ^ 2 := by
    dsimp [X₀] at *
    nlinarith


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
