import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.eSHP_tables

open Nat

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
  "table-8-prime-gap-complete-test"
  (title := "Table 8 prime gap records - completeness unit test")
  (statement := /--
  Table 8 contains ALL the prime gap records $(p_k,g_k)$ with $p_k \leq 30$. -/)
  (proof := /-- Brute force verification. -/)
  (latexEnv := "proposition")
  (discussion := 948)]
theorem table_8_prime_gap_complete_test (p g : ℕ) (hp : p ≤ 30)
    (hrecord : prime_gap_record p g) : (p, g) ∈ table_8 := by
  rcases hrecord with ⟨n, hn₁, hn₂, hn₃⟩
  have nth_eq : ∀ {m i}, m.Prime → Nat.count Nat.Prime m = i → nth_prime i = m :=
    fun hm hc ↦ by simpa [nth_prime, hc] using nth_count hm
  have hpv : ∀ k < 11, nth_prime k =
      if k = 0 then 2 else if k = 1 then 3 else if k = 2 then 5 else if k = 3 then 7
      else if k = 4 then 11 else if k = 5 then 13 else if k = 6 then 17
      else if k = 7 then 19 else if k = 8 then 23 else if k = 9 then 29 else 31 := by
    intro k hk; interval_cases k <;> exact nth_eq (by decide) (by decide)
  by_cases hn : n < 11
  · interval_cases n <;> simp only [← hn₁, ← hn₂, nth_prime_gap] at *
    all_goals
      have := hn₃ 0; have := hn₃ 1; have := hn₃ 2; have := hn₃ 3; have := hn₃ 4
      have := hn₃ 5; have := hn₃ 6; have := hn₃ 7; have := hn₃ 8; have := hn₃ 9
      simp +decide [*] at *
  · have h10 := nth_eq (show Nat.Prime 31 by decide) (show count Nat.Prime 31 = 10 by decide)
    linarith [nth_monotone Nat.infinite_setOf_prime (show 10 ≤ n by omega), hn₁]

@[blueprint
  "table-8-prime-gap-complete"
  (title := "Table 8 prime gap records - completeness")
  (statement := /--
  Table 8 contains ALL the prime gap records $(p_k,g_k)$ with $p_k \leq 4 \times 10^{18}$. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_8_prime_gap_complete (p g : ℕ) (hp : p ≤ 4 * 10 ^ 18) (hrecord : prime_gap_record p g) : (p, g) ∈ table_8 := by sorry

lemma exists_prime_gap_record_le (n : ℕ) :
    ∃ m, nth_prime m ≤ nth_prime n ∧ nth_prime_gap n ≤ nth_prime_gap m ∧
      prime_gap_record (nth_prime m) (nth_prime_gap m) := by
  let g := nth_prime_gap n; let S := {k | k ≤ n ∧ g ≤ nth_prime_gap k}
  obtain ⟨m, hm_mem, hm_min⟩ : ∃ m ∈ S, ∀ k ∈ S, m ≤ k := ⟨Nat.find <|
    show S.Nonempty from ⟨n, le_rfl, le_rfl⟩, Nat.find_spec <|
      show S.Nonempty from ⟨n, le_rfl, le_rfl⟩, fun k hk ↦ Nat.find_min' _ hk⟩
  refine ⟨m, ?_, hm_mem.2, m, rfl, rfl, fun k hk ↦ ?_ ⟩
  · exact monotone_nat_of_le_succ (fun n ↦ nth_monotone (infinite_setOf_prime) n.le_succ) hm_mem.1
  · contrapose! hk
    exact monotone_nat_of_le_succ (fun n ↦ nth_monotone (infinite_setOf_prime) n.le_succ)
      (le_of_not_gt fun h ↦ not_lt_of_ge (hm_min _ ⟨by linarith [hm_mem.1], by linarith [hm_mem.2]⟩) h)

@[blueprint
  "max-prime-gap"
  (title := "Maximum prime gap")
  (statement := /--
  The maximum prime gap for primes less than or equal to $4 \times 10^{18}$ is $1476$. -/)
  (proof := /-- If not, then there would be an entry in Table 8 with $g > 1476$, which can be verified not to be the case. -/)
  (latexEnv := "proposition")
  (discussion := 949)]
theorem max_prime_gap (n : ℕ) (hp : nth_prime n ≤ 4 * 10 ^ 18) : nth_prime_gap n ≤ 1476 := by
  have h : ∀ x ∈ table_8, x.2 ≤ 1476 := by decide
  obtain ⟨m, hm₁, hm₂, hm₃⟩ := exists_prime_gap_record_le n
  exact hm₂.trans <| h _ <| table_8_prime_gap_complete _ _ (hm₁.trans hp) hm₃

@[blueprint
  "table-9-prime-gap-test"
  (title := "Table 9 prime gaps - unit test")
  (statement := /--
  For every pair $(g,P)$ in Table 9 with $P < 30$, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Direct computation. -/)
  (latexEnv := "proposition")
  (discussion := 903)]
theorem table_9_prime_gap_test (g P : ℕ) (h : (g, P) ∈ table_9) (htest : P < 30) : first_gap_record g P := by
  have hnp5 : nth_prime 5 = 13 := by
    have hp13 : Nat.Prime 13 := by decide
    have hcount13 : Nat.count Nat.Prime 13 = 5 := by decide
    simpa [nth_prime, hcount13] using (Nat.nth_count (p := Nat.Prime) (n := 13) hp13)
  have hnp6 : nth_prime 6 = 17 := by
    have hp17 : Nat.Prime 17 := by decide
    have hcount17 : Nat.count Nat.Prime 17 = 6 := by decide
    simpa [nth_prime, hcount17] using (Nat.nth_count (p := Nat.Prime) (n := 17) hp17)
  have hnp7 : nth_prime 7 = 19 := by
    have hp19 : Nat.Prime 19 := by decide
    have hcount19 : Nat.count Nat.Prime 19 = 7 := by decide
    simpa [nth_prime, hcount19] using (Nat.nth_count (p := Nat.Prime) (n := 19) hp19)
  have hnp8 : nth_prime 8 = 23 := by
    have hp23 : Nat.Prime 23 := by decide
    have hcount23 : Nat.count Nat.Prime 23 = 8 := by decide
    simpa [nth_prime, hcount23] using (Nat.nth_count (p := Nat.Prime) (n := 23) hp23)
  have hnp9 : nth_prime 9 = 29 := by
    have hp29 : Nat.Prime 29 := by decide
    have hcount29 : Nat.count Nat.Prime 29 = 9 := by decide
    simpa [nth_prime, hcount29] using (Nat.nth_count (p := Nat.Prime) (n := 29) hp29)

  have hfg1 : first_gap 1 = 2 := by
    have hex1 : ∃ n, nth_prime_gap n = 1 := ⟨0, by
      simp [nth_prime_gap, nth_prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    ⟩
    have hfind1 : Nat.find hex1 = 0 := by
      exact (Nat.find_eq_zero hex1).2 (by
        simp [nth_prime_gap, nth_prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three])
    simp [first_gap, hex1, hfind1, nth_prime, Nat.nth_prime_zero_eq_two]
  have hfg2 : first_gap 2 = 3 := by
    have hex2 : ∃ n, nth_prime_gap n = 2 := ⟨1, by
      simp [nth_prime_gap, nth_prime, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
    ⟩
    have hfind2 : Nat.find hex2 = 1 := by
      refine (Nat.find_eq_iff hex2).2 ?_
      refine ⟨by
        simp [nth_prime_gap, nth_prime, Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]
      , ?_⟩
      intro n hn
      have hn0 : n = 0 := by omega
      subst hn0
      simp [nth_prime_gap, nth_prime, Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]
    simp [first_gap, hex2, hfind2, nth_prime, Nat.nth_prime_one_eq_three]
  have hfg4 : first_gap 4 = 7 := by
    have hex4 : ∃ n, nth_prime_gap n = 4 := ⟨3, by
      simp [nth_prime_gap, nth_prime, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
    ⟩
    have hfind4 : Nat.find hex4 = 3 := by
      refine (Nat.find_eq_iff hex4).2 ?_
      refine ⟨by
        simp [nth_prime_gap, nth_prime, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
      , ?_⟩
      intro n hn
      interval_cases n <;>
        simp [nth_prime_gap, nth_prime,
          Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
          Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven]
    simp [first_gap, hex4, hfind4, nth_prime, Nat.nth_prime_three_eq_seven]
  have hfg6 : first_gap 6 = 23 := by
    have hex6 : ∃ n, nth_prime_gap n = 6 := ⟨8, by
      simp [nth_prime_gap, hnp8, hnp9]
    ⟩
    have hfind6 : Nat.find hex6 = 8 := by
      refine (Nat.find_eq_iff hex6).2 ?_
      refine ⟨by simp [nth_prime_gap, hnp8, hnp9], ?_⟩
      intro n hn
      interval_cases n <;>
        simp [nth_prime_gap, nth_prime,
          Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
          Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven,
          Nat.nth_prime_four_eq_eleven, hnp5, hnp6, hnp7, hnp8]
    simp [first_gap, hex6, hfind6, hnp8]

  have hrecord1 : first_gap_record 1 2 := by
    simp [first_gap_record, hfg1]
  have hrecord2 : first_gap_record 2 3 := by
    refine ⟨hfg2, ?_⟩
    intro g' hg' _
    have hg'1 : g' = 1 := by
      rcases Finset.mem_Ico.mp hg' with ⟨hg'1, hg'2⟩
      omega
    subst g'
    simp [Set.mem_Ico, hfg1]
  have hrecord4 : first_gap_record 4 7 := by
    refine ⟨hfg4, ?_⟩
    intro g' hg' hpar
    rcases Finset.mem_Ico.mp hg' with ⟨hg'1, hg'4⟩
    rcases hpar with hEven | hg'Eq1
    · rcases hEven with ⟨k, hk⟩
      have hk' : k = 1 := by
        omega
      subst hk
      subst hk'
      simp [Set.mem_Ico, hfg2]
    · subst hg'Eq1
      simp [Set.mem_Ico, hfg1]
  have hrecord6 : first_gap_record 6 23 := by
    refine ⟨hfg6, ?_⟩
    intro g' hg' hpar
    rcases Finset.mem_Ico.mp hg' with ⟨hg'1, hg'6⟩
    rcases hpar with hEven | hg'Eq1
    · rcases hEven with ⟨k, hk⟩
      have hk' : k = 1 ∨ k = 2 := by
        omega
      rcases hk' with hk' | hk'
      · subst hk
        subst hk'
        simp [Set.mem_Ico, hfg2]
      · subst hk
        subst hk'
        simp [Set.mem_Ico, hfg4]
    · subst hg'Eq1
      simp [Set.mem_Ico, hfg1]

  have hPmem : P ∈ table_9.map Prod.snd := by
    simpa using (List.mem_map_of_mem (f := Prod.snd) h)
  have htestb : decide (P < 30) = true := decide_eq_true htest
  have hPsmallmem : P ∈ (table_9.map Prod.snd).filter (fun n ↦ decide (n < 30)) :=
    List.mem_filter.mpr ⟨hPmem, htestb⟩
  have hPsmall : P = 2 ∨ P = 3 ∨ P = 7 ∨ P = 23 := by
    simpa [table_9] using hPsmallmem
  rcases hPsmall with rfl | rfl | rfl | rfl
  · have hg : g = 1 := by simpa [table_9] using h
    subst hg
    exact hrecord1
  · have hg : g = 2 := by simpa [table_9] using h
    subst hg
    exact hrecord2
  · have hg : g = 4 := by simpa [table_9] using h
    subst hg
    exact hrecord4
  · have hg : g = 6 := by simpa [table_9] using h
    subst hg
    exact hrecord6

@[blueprint
  "table-9-prime-gap"
  (title := "Table 9 prime gaps")
  (statement := /--
  For every pair $(g,P)$ in Table 9, $P$ is the first prime producing the prime gap $g$, and all smaller $g'$ (that are even or $1$) have a smaller first prime. -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_9_prime_gap (g P : ℕ) (h : (g, P) ∈ table_9) : first_gap_record g P := by
  sorry

@[blueprint
  "table-9-prime-gap-complete-test"
  (title := "Table 9 prime gaps - completeness test")
  (statement := /--
  Table 9 contains all first gap records $(g,P)$ with $g < 8$. -/)
  (proof := /-- Brute force verification. -/)
  (latexEnv := "proposition")
  (discussion := 950)]
theorem table_9_prime_gap_complete_test (g P : ℕ) (hg : g < 8) (hg' : 0 < g) (hrecord : first_gap_record g P) : (g, P) ∈ table_9 := by
  sorry

@[blueprint
  "table-9-prime-gap-complete"
  (title := "Table 9 prime gaps - completeness")
  (statement := /--
  Table 9 contains all first gap records $(g,P)$ with $g < 1346$ -/)
  (proof := /-- Verified by computer.  Unlikely to be formalizable in Lean with current technology, except for the small values of the table. -/)
  (latexEnv := "proposition")]
theorem table_9_prime_gap_complete (g P : ℕ) (hg : g < 1346) (hg' : 0 < g) (hrecord : first_gap_record g P) : (g, P) ∈ table_9 := by
  sorry

@[blueprint
  "exists-prime-gap"
  (title := "Existence of prime gap")
  (statement := /--
  Every gap $g < 1346$ that is even or one occurs as a prime gap with first prime at most $3278018069102480227$. -/)
  (proof := /-- If not, then there would be an entry in Table 8 with $P > 3278018069102480227$, which can be verified not to be the case. -/)
  (latexEnv := "proposition")
  (discussion := 951)]
theorem exists_prime_gap (g : ℕ) (hg : g ∈ Set.Ico 1 1476) (hg' : Even g ∨ g = 1) : first_gap g ≤ 3278018069102480227 := by
  sorry

end eSHP
