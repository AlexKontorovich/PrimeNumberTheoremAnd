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
