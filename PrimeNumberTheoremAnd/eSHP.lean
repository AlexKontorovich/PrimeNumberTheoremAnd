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
  sorry

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
  have hPsmallmem : P ∈ (table_9.map Prod.snd).filter (fun n => decide (n < 30)) :=
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


end eSHP
