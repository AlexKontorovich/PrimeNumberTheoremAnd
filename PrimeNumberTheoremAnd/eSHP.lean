import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.eSHP_tables

blueprint_comment /--
\section{Prime gap data from eSHP}

Numerical results on prime gaps from \cite{eSHP}.

-/

namespace eSHP

@[blueprint
  "table-8-prime-gap-test"
  (title := "Table 8 prime gap record - unit test")
  (statement := /--
  For every pair $(p_k,g_k)$ in Table 8 with $p_k < 30$, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$. -/)
  (proof := /-- Direct computation. -/)
  (latexEnv := "proposition")
  (discussion := 902)]
theorem table_8_prime_gap_test (p g : ℕ) (h : (p, g) ∈ table_8) (htest : p < 30) : prime_gap_record p g := by
  have hmem := h
  simp [table_8, Prod.mk.injEq] at hmem
  have hsmall : (p = 2 ∧ g = 1) ∨ (p = 3 ∧ g = 2) ∨ (p = 7 ∧ g = 4) ∨ (p = 23 ∧ g = 6) := by
    omega
  have nth_prime_eq_of_count {m i : ℕ} (hm : Nat.Prime m)
      (hcount : Nat.count Nat.Prime m = i) : nth_prime i = m := by
    simpa [nth_prime, hcount] using (Nat.nth_count (p := Nat.Prime) hm)
  rcases hsmall with h2 | h3 | h7 | h23
  · rcases h2 with ⟨rfl, rfl⟩
    refine ⟨0, by simp [nth_prime], by simp [nth_prime_gap, nth_prime], ?_⟩
    intro k hk
    have hk2 : 2 ≤ nth_prime k := by
      have hk2' : k + 2 ≤ nth_prime k := by
        simpa [nth_prime] using Nat.add_two_le_nth_prime k
      omega
    omega
  · rcases h3 with ⟨rfl, rfl⟩
    refine ⟨1, by simp [nth_prime], by simp [nth_prime_gap, nth_prime], ?_⟩
    intro k hk
    have hk' : k < 1 := by
      have hkn : Nat.nth Nat.Prime k < Nat.nth Nat.Prime 1 := by
        simpa [nth_prime] using hk
      exact (Nat.nth_lt_nth (p := Nat.Prime) Nat.infinite_setOf_prime).1 hkn
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk'
    subst hk0
    simp [nth_prime_gap, nth_prime]
  · rcases h7 with ⟨rfl, rfl⟩
    refine ⟨3, by simp [nth_prime], by simp [nth_prime_gap, nth_prime], ?_⟩
    intro k hk
    have hk' : k < 3 := by
      have hkn : Nat.nth Nat.Prime k < Nat.nth Nat.Prime 3 := by
        simpa [nth_prime] using hk
      exact (Nat.nth_lt_nth (p := Nat.Prime) Nat.infinite_setOf_prime).1 hkn
    interval_cases k <;> simp [nth_prime_gap, nth_prime]
  · rcases h23 with ⟨rfl, rfl⟩
    have h13 : nth_prime 5 = 13 := nth_prime_eq_of_count (by decide) (by decide)
    have h17 : nth_prime 6 = 17 := nth_prime_eq_of_count (by decide) (by decide)
    have h19 : nth_prime 7 = 19 := nth_prime_eq_of_count (by decide) (by decide)
    have h23' : nth_prime 8 = 23 := nth_prime_eq_of_count (by decide) (by decide)
    have h29 : nth_prime 9 = 29 := nth_prime_eq_of_count (by decide) (by decide)
    refine ⟨8, h23', by simp [nth_prime_gap, h23', h29], ?_⟩
    intro k hk
    have hk' : k < 8 := by
      have hkn : Nat.nth Nat.Prime k < Nat.nth Nat.Prime 8 := by
        simpa [nth_prime, h23'] using hk
      exact (Nat.nth_lt_nth (p := Nat.Prime) Nat.infinite_setOf_prime).1 hkn
    interval_cases k <;>
      simp [nth_prime_gap, nth_prime, h13, h17, h19, h23']
  /-
  PROOF PLAN FOR table_8_prime_gap_test:

  1) Goal shape:
     - Show `prime_gap_record p g`, i.e.
       `∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧ ∀ k, nth_prime k < p → nth_prime_gap k < g`.
     - Key definitions to unfold:
       - `prime_gap_record` (in `PrimeNumberTheoremAnd/Defs.lean`)
       - `nth_prime` (abbrev for `Nat.nth Nat.Prime`)
       - `nth_prime_gap` (abbrev for `nth_prime (n+1) - nth_prime n`)
       - `table_8` (in `PrimeNumberTheoremAnd/eSHP_tables.lean`)

  2) “Provable as stated?” check:
     - Yes. Under `p < 30`, the hypothesis `(p,g) ∈ table_8` forces `(p,g)` to be one of
       `(2,1)`, `(3,2)`, `(7,4)`, `(23,6)`. For each, the statement follows from explicit
       computations of the first few primes and their gaps, and a finite check that earlier gaps
       are smaller than `g`.
     - No extra hypotheses are needed because the `∀ k, ... → ...` part is vacuous for `p = 2`.

  3) If provable as stated: Lean tactic plan:
     A. Reduce to the four small rows of `table_8`.
        - Expand membership once:
          - Let `hmem : (p,g) = (2,1) ∨ (p,g) = (3,2) ∨ ...` be obtained by
            `have hmem : (p,g) = (2,1) ∨ (p,g) = (3,2) ∨ ... := by simpa [table_8] using h`.
          - Then `rcases hmem with h2 | h3 | h7 | h23 | h_rest`.
          - In the `h_rest` branches, `p` becomes a concrete numeral `≥ 30`; close via `htest`
            using `cases (by decide : ¬ (p < 30)) (by simpa [*] using htest)` (or `simp [*] at htest`).
        - If `simp [table_8]` creates too many branches, don’t guess lemma names: search for a
          “take/drop” or “prefix” lemma to avoid enumerating the tail:
          - `rg -n \"mem_take|mem_drop|takeWhile|dropWhile\" .lake/packages/mathlib/Mathlib/Data/List`
          - `rg -n \"table_8\" PrimeNumberTheoremAnd/eSHP_tables.lean`

     B. For each remaining case, build the witness `n` and verify the components.
        Common helper for computing `nth_prime i` from a prime `m` with known count:
        - Use the verified lemma (Mathlib) `Nat.nth_count`:
          - located at `.lake/packages/mathlib/Mathlib/Data/Nat/Nth.lean`:
            `@[simp] theorem Nat.nth_count {n} (hpn : p n) : Nat.nth p (Nat.count p n) = n`.
        - Define locally (inside the proof) a helper lemma:
          - `have nth_prime_eq_of_count {m i : ℕ} (hm : Nat.Prime m)
                (hcount : Nat.count Nat.Prime m = i) : nth_prime i = m := by
                simpa [nth_prime, hcount] using (Nat.nth_count (p := Nat.Prime) hm)`
        - Discharge `Nat.Prime m` and `Nat.count Nat.Prime m = i` for concrete numerals using
          `by decide`.

        Case (2,1):
        - Use `n := 0`.
        - `nth_prime 0 = 2` by `simp [nth_prime]` (uses `Nat.nth_prime_zero_eq_two`).
        - `nth_prime_gap 0 = 1` by `simp [nth_prime_gap, nth_prime]`.
        - For the `∀ k` part: given `hk : nth_prime k < 2`, rewrite as
          `nth_prime k < nth_prime 0` and use `Nat.nth_lt_nth Nat.infinite_setOf_prime` to get `k < 0`,
          contradiction; hence the implication is vacuous.

        Case (3,2):
        - Use `n := 1` and simp for `nth_prime 1 = 3`.
        - Compute `nth_prime_gap 1 = 2` by simp/norm_num using `nth_prime 2 = 5`.
        - For the `∀ k` part:
          - From `nth_prime k < 3 = nth_prime 1`, get `k < 1` via `Nat.nth_lt_nth Nat.infinite_setOf_prime`.
          - Then `k = 0` (use `Nat.lt_one_iff.mp`).
          - Compute `nth_prime_gap 0 = 1` and finish with `decide`/`simp`.

        Case (7,4):
        - Use `n := 3` and simp for `nth_prime 3 = 7`.
        - Compute `nth_prime_gap 3 = 4` using `nth_prime 4 = 11` (`Nat.nth_prime_four_eq_eleven`).
        - For the `∀ k` part:
          - From `nth_prime k < 7 = nth_prime 3`, get `k < 3`.
          - Do nested `cases k` to reduce to `k = 0 | 1 | 2` (no need for `interval_cases`).
          - For each, simp the gap (`1`, `2`, `2`) and close with `decide`/`simp`.

        Case (23,6):
        - Use `n := 8`. Obtain `nth_prime 8 = 23` via `Nat.nth_count` + `Nat.count` computation:
          - `have hcount23 : Nat.count Nat.Prime 23 = 8 := by decide`
          - `have h23 : nth_prime 8 = 23 := nth_prime_eq_of_count (by decide) hcount23`
        - Obtain `nth_prime 9 = 29` similarly:
          - `have hcount29 : Nat.count Nat.Prime 29 = 9 := by decide`
          - `have h29 : nth_prime 9 = 29 := nth_prime_eq_of_count (by decide) hcount29`
        - Then `nth_prime_gap 8 = 6` by `simp [nth_prime_gap, h23, h29]`.
        - For the `∀ k` part:
          - From `nth_prime k < 23 = nth_prime 8`, derive `k < 8` via `Nat.nth_lt_nth Nat.infinite_setOf_prime`.
          - Use nested `cases k` eight times to reduce to `k = 0,1,2,3,4,5,6,7`.
          - For each `k`, precompute `nth_prime` at indices `0..9`:
            - `0..4` by simp (`Nat.nth_prime_zero_eq_two` ... `Nat.nth_prime_four_eq_eleven`).
            - `5..9` via `nth_prime_eq_of_count` with `m = 13,17,19,23,29` and counts
              `Nat.count Nat.Prime 13 = 5`, `... 17 = 6`, `... 19 = 7`, `... 23 = 8`, `... 29 = 9`
              all by `decide`.
          - Then simp each `nth_prime_gap k` (they are `1,2,2,4,2,4,2,4`) and close with `decide`.

  4) If NOT provable as stated (possible typo):
     - Not applicable.

  5) Implementation checklist for Codex:
     - `simp [prime_gap_record, nth_prime_gap]` early to expose the existential/∀ structure.
     - Add the helper `nth_prime_eq_of_count` inside the proof (no new imports needed).
     - Use `Nat.nth_lt_nth Nat.infinite_setOf_prime` to convert `nth_prime k < nth_prime n` into `k < n`.
     - Use `by decide` for:
       - primality of concrete numerals (`Nat.Prime 13`, etc.)
       - count equalities (`Nat.count Nat.Prime 23 = 8`, etc.)
       - closing numeric inequalities after simp (`(1:ℕ) < 4`, etc.)
     - Watch coercions:
       - `nth_prime` is an abbrev; use `simp [nth_prime]` when lemma expects `Nat.nth`.
       - `nth_prime_gap` is Nat subtraction; ensure simp has rewritten primes so subtraction normalizes.

  END OF PLAN
  -/

@[blueprint
  "table-8-prime-gap"
  (title := "Table 8 prime gap records")
  (statement := /--
  For every pair $(p_k,g_k)$ in Table 8, $g_k$ is the prime gap $p_{k+1} - p_k$, and all prime gaps preceding this gap are less than $g_k$. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_8_prime_gap (p g : ℕ) (h : (p, g) ∈ table_8) : prime_gap_record p g := by
  sorry

@[blueprint
  "table-9-prime-gap-test"
  (title := "Table 9 prime gaps - unit test")
  (statement := /--
  For every pair $(g,P)$ in Table 9 with $P < 30$, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Direct computation. -/)
  (latexEnv := "proposition")
  (discussion := 903)]
theorem table_9_prime_gap_test (g P : ℕ) (h : (g, P) ∈ table_9) (htest : P < 30) : first_gap_record g P := by
  sorry

@[blueprint
  "table-9-prime-gap"
  (title := "Table 9 prime gaps")
  (statement := /--
  For every pair $(g,P)$ in Table 9, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_9_prime_gap (g P : ℕ) (h : (g, P) ∈ table_9) : first_gap_record g P := by
  sorry


end eSHP
