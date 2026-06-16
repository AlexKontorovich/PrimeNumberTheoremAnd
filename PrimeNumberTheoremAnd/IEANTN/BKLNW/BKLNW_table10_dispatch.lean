import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows

/-! Generated proof of the Table 10 verification theorem from proved row/k margins. -/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace BKLNW

open Real

set_option maxHeartbeats 12000000 in
-- The generated proof enumerates all 287 table rows and five k-cases per row.
set_option maxRecDepth 100000 in
@[blueprint
  "bklnw-table-10-verification"
  (title := "BKLNW Table 10 verification")
  (statement := /--  Verification of the entries of Table 10, up to the safety margin
  $m = 1.002001$: each row $(b, B_1, \ldots, B_5)$ of the (unabridged) Table 10 satisfies
  $$B^{\mathrm{exact}}_k(b, \mathrm{next}(b)) \le B_k \cdot m \qquad (k = 1, \ldots, 5),$$
  where $m$ is the Table 8 margin $1.001$ composed with a further factor $1.001$,
  accounting for the final-digit rounding of the printed values. -/)
  (proof := /-- Enumerate the 287 rows of `table_10`, split into the five `k` cases,
  and discharge each case using the generated row margin and next-row certificates. -/)
  (latexEnv := "proposition")
  (discussion := 1255)]
theorem bklnw_table_10_verification (b : ℝ) (B : ℕ → ℝ) (h : (b, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_10) : ∀ k ∈ Finset.Icc 1 5, B_8_exact k b (table_10_next b) ≤ B k * table_10_margin := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk5 : k ≤ 5 := (Finset.mem_Icc.mp hk).2
  simp only [BKLNW.table_10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with h20 | h
  · simp only [Prod.mk.injEq] at h20
    rcases h20 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_20, hB1]
      convert table_10_row20_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20, hB2]
      convert table_10_row20_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20, hB3]
      convert table_10_row20_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20, hB4]
      convert table_10_row20_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20, hB5]
      convert table_10_row20_k5_margin using 1 <;> norm_num
  rcases h with h21 | h
  · simp only [Prod.mk.injEq] at h21
    rcases h21 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_21, hB1]
      convert table_10_row21_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21, hB2]
      convert table_10_row21_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21, hB3]
      convert table_10_row21_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21, hB4]
      convert table_10_row21_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21, hB5]
      convert table_10_row21_k5_margin using 1 <;> norm_num
  rcases h with h22 | h
  · simp only [Prod.mk.injEq] at h22
    rcases h22 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_22, hB1]
      convert table_10_row22_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22, hB2]
      convert table_10_row22_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22, hB3]
      convert table_10_row22_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22, hB4]
      convert table_10_row22_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22, hB5]
      convert table_10_row22_k5_margin using 1 <;> norm_num
  rcases h with h23 | h
  · simp only [Prod.mk.injEq] at h23
    rcases h23 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_23, hB1]
      convert table_10_row23_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23, hB2]
      convert table_10_row23_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23, hB3]
      convert table_10_row23_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23, hB4]
      convert table_10_row23_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23, hB5]
      convert table_10_row23_k5_margin using 1 <;> norm_num
  rcases h with h24 | h
  · simp only [Prod.mk.injEq] at h24
    rcases h24 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_24, hB1]
      convert table_10_row24_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_24, hB2]
      convert table_10_row24_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_24, hB3]
      convert table_10_row24_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_24, hB4]
      convert table_10_row24_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_24, hB5]
      convert table_10_row24_k5_margin using 1 <;> norm_num
  rcases h with h25 | h
  · simp only [Prod.mk.injEq] at h25
    rcases h25 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_25, hB1]
      convert table_10_row25_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_25, hB2]
      convert table_10_row25_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_25, hB3]
      convert table_10_row25_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_25, hB4]
      convert table_10_row25_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_25, hB5]
      convert table_10_row25_k5_margin using 1 <;> norm_num
  rcases h with h26 | h
  · simp only [Prod.mk.injEq] at h26
    rcases h26 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_26, hB1]
      convert table_10_row26_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_26, hB2]
      convert table_10_row26_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_26, hB3]
      convert table_10_row26_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_26, hB4]
      convert table_10_row26_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_26, hB5]
      convert table_10_row26_k5_margin using 1 <;> norm_num
  rcases h with h27 | h
  · simp only [Prod.mk.injEq] at h27
    rcases h27 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_27, hB1]
      convert table_10_row27_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_27, hB2]
      convert table_10_row27_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_27, hB3]
      convert table_10_row27_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_27, hB4]
      convert table_10_row27_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_27, hB5]
      convert table_10_row27_k5_margin using 1 <;> norm_num
  rcases h with h28 | h
  · simp only [Prod.mk.injEq] at h28
    rcases h28 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_28, hB1]
      convert table_10_row28_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_28, hB2]
      convert table_10_row28_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_28, hB3]
      convert table_10_row28_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_28, hB4]
      convert table_10_row28_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_28, hB5]
      convert table_10_row28_k5_margin using 1 <;> norm_num
  rcases h with h29 | h
  · simp only [Prod.mk.injEq] at h29
    rcases h29 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_29, hB1]
      convert table_10_row29_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_29, hB2]
      convert table_10_row29_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_29, hB3]
      convert table_10_row29_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_29, hB4]
      convert table_10_row29_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_29, hB5]
      convert table_10_row29_k5_margin using 1 <;> norm_num
  rcases h with h30 | h
  · simp only [Prod.mk.injEq] at h30
    rcases h30 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_30, hB1]
      convert table_10_row30_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_30, hB2]
      convert table_10_row30_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_30, hB3]
      convert table_10_row30_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_30, hB4]
      convert table_10_row30_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_30, hB5]
      convert table_10_row30_k5_margin using 1 <;> norm_num
  rcases h with h31 | h
  · simp only [Prod.mk.injEq] at h31
    rcases h31 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_31, hB1]
      convert table_10_row31_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_31, hB2]
      convert table_10_row31_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_31, hB3]
      convert table_10_row31_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_31, hB4]
      convert table_10_row31_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_31, hB5]
      convert table_10_row31_k5_margin using 1 <;> norm_num
  rcases h with h32 | h
  · simp only [Prod.mk.injEq] at h32
    rcases h32 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_32, hB1]
      convert table_10_row32_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_32, hB2]
      convert table_10_row32_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_32, hB3]
      convert table_10_row32_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_32, hB4]
      convert table_10_row32_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_32, hB5]
      convert table_10_row32_k5_margin using 1 <;> norm_num
  rcases h with h33 | h
  · simp only [Prod.mk.injEq] at h33
    rcases h33 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_33, hB1]
      convert table_10_row33_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_33, hB2]
      convert table_10_row33_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_33, hB3]
      convert table_10_row33_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_33, hB4]
      convert table_10_row33_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_33, hB5]
      convert table_10_row33_k5_margin using 1 <;> norm_num
  rcases h with h34 | h
  · simp only [Prod.mk.injEq] at h34
    rcases h34 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_34, hB1]
      convert table_10_row34_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_34, hB2]
      convert table_10_row34_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_34, hB3]
      convert table_10_row34_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_34, hB4]
      convert table_10_row34_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_34, hB5]
      convert table_10_row34_k5_margin using 1 <;> norm_num
  rcases h with h35 | h
  · simp only [Prod.mk.injEq] at h35
    rcases h35 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_35, hB1]
      convert table_10_row35_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_35, hB2]
      convert table_10_row35_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_35, hB3]
      convert table_10_row35_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_35, hB4]
      convert table_10_row35_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_35, hB5]
      convert table_10_row35_k5_margin using 1 <;> norm_num
  rcases h with h36 | h
  · simp only [Prod.mk.injEq] at h36
    rcases h36 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_36, hB1]
      convert table_10_row36_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_36, hB2]
      convert table_10_row36_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_36, hB3]
      convert table_10_row36_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_36, hB4]
      convert table_10_row36_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_36, hB5]
      convert table_10_row36_k5_margin using 1 <;> norm_num
  rcases h with h37 | h
  · simp only [Prod.mk.injEq] at h37
    rcases h37 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_37, hB1]
      convert table_10_row37_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_37, hB2]
      convert table_10_row37_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_37, hB3]
      convert table_10_row37_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_37, hB4]
      convert table_10_row37_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_37, hB5]
      convert table_10_row37_k5_margin using 1 <;> norm_num
  rcases h with h38 | h
  · simp only [Prod.mk.injEq] at h38
    rcases h38 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_38, hB1]
      convert table_10_row38_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_38, hB2]
      convert table_10_row38_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_38, hB3]
      convert table_10_row38_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_38, hB4]
      convert table_10_row38_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_38, hB5]
      convert table_10_row38_k5_margin using 1 <;> norm_num
  rcases h with h39 | h
  · simp only [Prod.mk.injEq] at h39
    rcases h39 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_39, hB1]
      convert table_10_row39_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_39, hB2]
      convert table_10_row39_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_39, hB3]
      convert table_10_row39_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_39, hB4]
      convert table_10_row39_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_39, hB5]
      convert table_10_row39_k5_margin using 1 <;> norm_num
  rcases h with h40 | h
  · simp only [Prod.mk.injEq] at h40
    rcases h40 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_40, hB1]
      convert table_10_row40_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_40, hB2]
      convert table_10_row40_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_40, hB3]
      convert table_10_row40_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_40, hB4]
      convert table_10_row40_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_40, hB5]
      convert table_10_row40_k5_margin using 1 <;> norm_num
  rcases h with h41 | h
  · simp only [Prod.mk.injEq] at h41
    rcases h41 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_41, hB1]
      convert table_10_row41_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_41, hB2]
      convert table_10_row41_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_41, hB3]
      convert table_10_row41_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_41, hB4]
      convert table_10_row41_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_41, hB5]
      convert table_10_row41_k5_margin using 1 <;> norm_num
  rcases h with h42 | h
  · simp only [Prod.mk.injEq] at h42
    rcases h42 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_42, hB1]
      convert table_10_row42_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_42, hB2]
      convert table_10_row42_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_42, hB3]
      convert table_10_row42_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_42, hB4]
      convert table_10_row42_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_42, hB5]
      convert table_10_row42_k5_margin using 1 <;> norm_num
  rcases h with h43 | h
  · simp only [Prod.mk.injEq] at h43
    rcases h43 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_43, hB1]
      convert table_10_row43_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_43, hB2]
      convert table_10_row43_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_43, hB3]
      convert table_10_row43_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_43, hB4]
      convert table_10_row43_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_43, hB5]
      convert table_10_row43_k5_margin using 1 <;> norm_num
  rcases h with h19log10 | h
  · simp only [Prod.mk.injEq] at h19log10
    rcases h19log10 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_19log10, hB1]
      convert table_10_row19log10_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19log10, hB2]
      convert table_10_row19log10_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19log10, hB3]
      convert table_10_row19log10_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19log10, hB4]
      convert table_10_row19log10_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19log10, hB5]
      convert table_10_row19log10_k5_margin using 1 <;> norm_num
  rcases h with h44 | h
  · simp only [Prod.mk.injEq] at h44
    rcases h44 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_44, hB1]
      convert table_10_row44_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_44, hB2]
      convert table_10_row44_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_44, hB3]
      convert table_10_row44_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_44, hB4]
      convert table_10_row44_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_44, hB5]
      convert table_10_row44_k5_margin using 1 <;> norm_num
  rcases h with h45 | h
  · simp only [Prod.mk.injEq] at h45
    rcases h45 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_45, hB1]
      convert table_10_row45_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_45, hB2]
      convert table_10_row45_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_45, hB3]
      convert table_10_row45_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_45, hB4]
      convert table_10_row45_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_45, hB5]
      convert table_10_row45_k5_margin using 1 <;> norm_num
  rcases h with h46 | h
  · simp only [Prod.mk.injEq] at h46
    rcases h46 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_46, hB1]
      convert table_10_row46_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_46, hB2]
      convert table_10_row46_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_46, hB3]
      convert table_10_row46_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_46, hB4]
      convert table_10_row46_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_46, hB5]
      convert table_10_row46_k5_margin using 1 <;> norm_num
  rcases h with h47 | h
  · simp only [Prod.mk.injEq] at h47
    rcases h47 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_47, hB1]
      convert table_10_row47_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_47, hB2]
      convert table_10_row47_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_47, hB3]
      convert table_10_row47_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_47, hB4]
      convert table_10_row47_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_47, hB5]
      convert table_10_row47_k5_margin using 1 <;> norm_num
  rcases h with h48 | h
  · simp only [Prod.mk.injEq] at h48
    rcases h48 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_48, hB1]
      convert table_10_row48_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_48, hB2]
      convert table_10_row48_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_48, hB3]
      convert table_10_row48_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_48, hB4]
      convert table_10_row48_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_48, hB5]
      convert table_10_row48_k5_margin using 1 <;> norm_num
  rcases h with h49 | h
  · simp only [Prod.mk.injEq] at h49
    rcases h49 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_49, hB1]
      convert table_10_row49_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_49, hB2]
      convert table_10_row49_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_49, hB3]
      convert table_10_row49_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_49, hB4]
      convert table_10_row49_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_49, hB5]
      convert table_10_row49_k5_margin using 1 <;> norm_num
  rcases h with h50 | h
  · simp only [Prod.mk.injEq] at h50
    rcases h50 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_50, hB1]
      convert table_10_row50_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_50, hB2]
      convert table_10_row50_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_50, hB3]
      convert table_10_row50_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_50, hB4]
      convert table_10_row50_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_50, hB5]
      convert table_10_row50_k5_margin using 1 <;> norm_num
  rcases h with h51 | h
  · simp only [Prod.mk.injEq] at h51
    rcases h51 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_51, hB1]
      convert table_10_row51_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_51, hB2]
      convert table_10_row51_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_51, hB3]
      convert table_10_row51_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_51, hB4]
      convert table_10_row51_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_51, hB5]
      convert table_10_row51_k5_margin using 1 <;> norm_num
  rcases h with h52 | h
  · simp only [Prod.mk.injEq] at h52
    rcases h52 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_52, hB1]
      convert table_10_row52_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_52, hB2]
      convert table_10_row52_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_52, hB3]
      convert table_10_row52_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_52, hB4]
      convert table_10_row52_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_52, hB5]
      convert table_10_row52_k5_margin using 1 <;> norm_num
  rcases h with h53 | h
  · simp only [Prod.mk.injEq] at h53
    rcases h53 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_53, hB1]
      convert table_10_row53_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_53, hB2]
      convert table_10_row53_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_53, hB3]
      convert table_10_row53_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_53, hB4]
      convert table_10_row53_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_53, hB5]
      convert table_10_row53_k5_margin using 1 <;> norm_num
  rcases h with h54 | h
  · simp only [Prod.mk.injEq] at h54
    rcases h54 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_54, hB1]
      convert table_10_row54_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_54, hB2]
      convert table_10_row54_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_54, hB3]
      convert table_10_row54_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_54, hB4]
      convert table_10_row54_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_54, hB5]
      convert table_10_row54_k5_margin using 1 <;> norm_num
  rcases h with h55 | h
  · simp only [Prod.mk.injEq] at h55
    rcases h55 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_55, hB1]
      convert table_10_row55_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_55, hB2]
      convert table_10_row55_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_55, hB3]
      convert table_10_row55_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_55, hB4]
      convert table_10_row55_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_55, hB5]
      convert table_10_row55_k5_margin using 1 <;> norm_num
  rcases h with h56 | h
  · simp only [Prod.mk.injEq] at h56
    rcases h56 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_56, hB1]
      convert table_10_row56_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_56, hB2]
      convert table_10_row56_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_56, hB3]
      convert table_10_row56_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_56, hB4]
      convert table_10_row56_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_56, hB5]
      convert table_10_row56_k5_margin using 1 <;> norm_num
  rcases h with h57 | h
  · simp only [Prod.mk.injEq] at h57
    rcases h57 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_57, hB1]
      convert table_10_row57_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_57, hB2]
      convert table_10_row57_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_57, hB3]
      convert table_10_row57_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_57, hB4]
      convert table_10_row57_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_57, hB5]
      convert table_10_row57_k5_margin using 1 <;> norm_num
  rcases h with h58 | h
  · simp only [Prod.mk.injEq] at h58
    rcases h58 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_58, hB1]
      convert table_10_row58_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_58, hB2]
      convert table_10_row58_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_58, hB3]
      convert table_10_row58_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_58, hB4]
      convert table_10_row58_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_58, hB5]
      convert table_10_row58_k5_margin using 1 <;> norm_num
  rcases h with h59 | h
  · simp only [Prod.mk.injEq] at h59
    rcases h59 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_59, hB1]
      convert table_10_row59_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_59, hB2]
      convert table_10_row59_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_59, hB3]
      convert table_10_row59_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_59, hB4]
      convert table_10_row59_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_59, hB5]
      convert table_10_row59_k5_margin using 1 <;> norm_num
  rcases h with h60 | h
  · simp only [Prod.mk.injEq] at h60
    rcases h60 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_60, hB1]
      convert table_10_row60_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_60, hB2]
      convert table_10_row60_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_60, hB3]
      convert table_10_row60_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_60, hB4]
      convert table_10_row60_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_60, hB5]
      convert table_10_row60_k5_margin using 1 <;> norm_num
  rcases h with h65 | h
  · simp only [Prod.mk.injEq] at h65
    rcases h65 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_65, hB1]
      convert table_10_row65_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_65, hB2]
      convert table_10_row65_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_65, hB3]
      convert table_10_row65_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_65, hB4]
      convert table_10_row65_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_65, hB5]
      convert table_10_row65_k5_margin using 1 <;> norm_num
  rcases h with h70 | h
  · simp only [Prod.mk.injEq] at h70
    rcases h70 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_70, hB1]
      convert table_10_row70_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_70, hB2]
      convert table_10_row70_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_70, hB3]
      convert table_10_row70_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_70, hB4]
      convert table_10_row70_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_70, hB5]
      convert table_10_row70_k5_margin using 1 <;> norm_num
  rcases h with h75 | h
  · simp only [Prod.mk.injEq] at h75
    rcases h75 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_75, hB1]
      convert table_10_row75_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_75, hB2]
      convert table_10_row75_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_75, hB3]
      convert table_10_row75_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_75, hB4]
      convert table_10_row75_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_75, hB5]
      convert table_10_row75_k5_margin using 1 <;> norm_num
  rcases h with h80 | h
  · simp only [Prod.mk.injEq] at h80
    rcases h80 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_80, hB1]
      convert table_10_row80_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_80, hB2]
      convert table_10_row80_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_80, hB3]
      convert table_10_row80_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_80, hB4]
      convert table_10_row80_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_80, hB5]
      convert table_10_row80_k5_margin using 1 <;> norm_num
  rcases h with h85 | h
  · simp only [Prod.mk.injEq] at h85
    rcases h85 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_85, hB1]
      convert table_10_row85_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_85, hB2]
      convert table_10_row85_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_85, hB3]
      convert table_10_row85_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_85, hB4]
      convert table_10_row85_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_85, hB5]
      convert table_10_row85_k5_margin using 1 <;> norm_num
  rcases h with h90 | h
  · simp only [Prod.mk.injEq] at h90
    rcases h90 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_90, hB1]
      convert table_10_row90_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_90, hB2]
      convert table_10_row90_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_90, hB3]
      convert table_10_row90_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_90, hB4]
      convert table_10_row90_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_90, hB5]
      convert table_10_row90_k5_margin using 1 <;> norm_num
  rcases h with h95 | h
  · simp only [Prod.mk.injEq] at h95
    rcases h95 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_95, hB1]
      convert table_10_row95_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_95, hB2]
      convert table_10_row95_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_95, hB3]
      convert table_10_row95_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_95, hB4]
      convert table_10_row95_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_95, hB5]
      convert table_10_row95_k5_margin using 1 <;> norm_num
  rcases h with h100 | h
  · simp only [Prod.mk.injEq] at h100
    rcases h100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_100, hB1]
      convert table_10_row100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_100, hB2]
      convert table_10_row100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_100, hB3]
      convert table_10_row100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_100, hB4]
      convert table_10_row100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_100, hB5]
      convert table_10_row100_k5_margin using 1 <;> norm_num
  rcases h with h200 | h
  · simp only [Prod.mk.injEq] at h200
    rcases h200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_200, hB1]
      convert table_10_row200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_200, hB2]
      convert table_10_row200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_200, hB3]
      convert table_10_row200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_200, hB4]
      convert table_10_row200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_200, hB5]
      convert table_10_row200_k5_margin using 1 <;> norm_num
  rcases h with h300 | h
  · simp only [Prod.mk.injEq] at h300
    rcases h300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_300, hB1]
      convert table_10_row300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_300, hB2]
      convert table_10_row300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_300, hB3]
      convert table_10_row300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_300, hB4]
      convert table_10_row300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_300, hB5]
      convert table_10_row300_k5_margin using 1 <;> norm_num
  rcases h with h400 | h
  · simp only [Prod.mk.injEq] at h400
    rcases h400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_400, hB1]
      convert table_10_row400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_400, hB2]
      convert table_10_row400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_400, hB3]
      convert table_10_row400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_400, hB4]
      convert table_10_row400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_400, hB5]
      convert table_10_row400_k5_margin using 1 <;> norm_num
  rcases h with h500 | h
  · simp only [Prod.mk.injEq] at h500
    rcases h500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_500, hB1]
      convert table_10_row500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_500, hB2]
      convert table_10_row500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_500, hB3]
      convert table_10_row500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_500, hB4]
      convert table_10_row500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_500, hB5]
      convert table_10_row500_k5_margin using 1 <;> norm_num
  rcases h with h600 | h
  · simp only [Prod.mk.injEq] at h600
    rcases h600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_600, hB1]
      convert table_10_row600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_600, hB2]
      convert table_10_row600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_600, hB3]
      convert table_10_row600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_600, hB4]
      convert table_10_row600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_600, hB5]
      convert table_10_row600_k5_margin using 1 <;> norm_num
  rcases h with h700 | h
  · simp only [Prod.mk.injEq] at h700
    rcases h700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_700, hB1]
      convert table_10_row700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_700, hB2]
      convert table_10_row700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_700, hB3]
      convert table_10_row700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_700, hB4]
      convert table_10_row700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_700, hB5]
      convert table_10_row700_k5_margin using 1 <;> norm_num
  rcases h with h800 | h
  · simp only [Prod.mk.injEq] at h800
    rcases h800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_800, hB1]
      convert table_10_row800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_800, hB2]
      convert table_10_row800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_800, hB3]
      convert table_10_row800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_800, hB4]
      convert table_10_row800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_800, hB5]
      convert table_10_row800_k5_margin using 1 <;> norm_num
  rcases h with h900 | h
  · simp only [Prod.mk.injEq] at h900
    rcases h900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_900, hB1]
      convert table_10_row900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_900, hB2]
      convert table_10_row900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_900, hB3]
      convert table_10_row900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_900, hB4]
      convert table_10_row900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_900, hB5]
      convert table_10_row900_k5_margin using 1 <;> norm_num
  rcases h with h1000 | h
  · simp only [Prod.mk.injEq] at h1000
    rcases h1000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1000, hB1]
      convert table_10_row1000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1000, hB2]
      convert table_10_row1000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1000, hB3]
      convert table_10_row1000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1000, hB4]
      convert table_10_row1000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1000, hB5]
      convert table_10_row1000_k5_margin using 1 <;> norm_num
  rcases h with h1500 | h
  · simp only [Prod.mk.injEq] at h1500
    rcases h1500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1500, hB1]
      convert table_10_row1500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1500, hB2]
      convert table_10_row1500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1500, hB3]
      convert table_10_row1500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1500, hB4]
      convert table_10_row1500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1500, hB5]
      convert table_10_row1500_k5_margin using 1 <;> norm_num
  rcases h with h1600 | h
  · simp only [Prod.mk.injEq] at h1600
    rcases h1600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1600, hB1]
      convert table_10_row1600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1600, hB2]
      convert table_10_row1600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1600, hB3]
      convert table_10_row1600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1600, hB4]
      convert table_10_row1600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1600, hB5]
      convert table_10_row1600_k5_margin using 1 <;> norm_num
  rcases h with h1700 | h
  · simp only [Prod.mk.injEq] at h1700
    rcases h1700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1700, hB1]
      convert table_10_row1700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1700, hB2]
      convert table_10_row1700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1700, hB3]
      convert table_10_row1700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1700, hB4]
      convert table_10_row1700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1700, hB5]
      convert table_10_row1700_k5_margin using 1 <;> norm_num
  rcases h with h1725 | h
  · simp only [Prod.mk.injEq] at h1725
    rcases h1725 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1725, hB1]
      convert table_10_row1725_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1725, hB2]
      convert table_10_row1725_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1725, hB3]
      convert table_10_row1725_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1725, hB4]
      convert table_10_row1725_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1725, hB5]
      convert table_10_row1725_k5_margin using 1 <;> norm_num
  rcases h with h1750 | h
  · simp only [Prod.mk.injEq] at h1750
    rcases h1750 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1750, hB1]
      convert table_10_row1750_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1750, hB2]
      convert table_10_row1750_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1750, hB3]
      convert table_10_row1750_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1750, hB4]
      convert table_10_row1750_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1750, hB5]
      convert table_10_row1750_k5_margin using 1 <;> norm_num
  rcases h with h1775 | h
  · simp only [Prod.mk.injEq] at h1775
    rcases h1775 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1775, hB1]
      convert table_10_row1775_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1775, hB2]
      convert table_10_row1775_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1775, hB3]
      convert table_10_row1775_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1775, hB4]
      convert table_10_row1775_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1775, hB5]
      convert table_10_row1775_k5_margin using 1 <;> norm_num
  rcases h with h1800 | h
  · simp only [Prod.mk.injEq] at h1800
    rcases h1800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1800, hB1]
      convert table_10_row1800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1800, hB2]
      convert table_10_row1800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1800, hB3]
      convert table_10_row1800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1800, hB4]
      convert table_10_row1800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1800, hB5]
      convert table_10_row1800_k5_margin using 1 <;> norm_num
  rcases h with h1825 | h
  · simp only [Prod.mk.injEq] at h1825
    rcases h1825 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1825, hB1]
      convert table_10_row1825_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1825, hB2]
      convert table_10_row1825_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1825, hB3]
      convert table_10_row1825_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1825, hB4]
      convert table_10_row1825_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1825, hB5]
      convert table_10_row1825_k5_margin using 1 <;> norm_num
  rcases h with h1850 | h
  · simp only [Prod.mk.injEq] at h1850
    rcases h1850 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1850, hB1]
      convert table_10_row1850_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1850, hB2]
      convert table_10_row1850_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1850, hB3]
      convert table_10_row1850_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1850, hB4]
      convert table_10_row1850_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1850, hB5]
      convert table_10_row1850_k5_margin using 1 <;> norm_num
  rcases h with h1875 | h
  · simp only [Prod.mk.injEq] at h1875
    rcases h1875 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1875, hB1]
      convert table_10_row1875_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1875, hB2]
      convert table_10_row1875_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1875, hB3]
      convert table_10_row1875_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1875, hB4]
      convert table_10_row1875_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1875, hB5]
      convert table_10_row1875_k5_margin using 1 <;> norm_num
  rcases h with h1900 | h
  · simp only [Prod.mk.injEq] at h1900
    rcases h1900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1900, hB1]
      convert table_10_row1900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1900, hB2]
      convert table_10_row1900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1900, hB3]
      convert table_10_row1900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1900, hB4]
      convert table_10_row1900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1900, hB5]
      convert table_10_row1900_k5_margin using 1 <;> norm_num
  rcases h with h1925 | h
  · simp only [Prod.mk.injEq] at h1925
    rcases h1925 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1925, hB1]
      convert table_10_row1925_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1925, hB2]
      convert table_10_row1925_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1925, hB3]
      convert table_10_row1925_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1925, hB4]
      convert table_10_row1925_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1925, hB5]
      convert table_10_row1925_k5_margin using 1 <;> norm_num
  rcases h with h1950 | h
  · simp only [Prod.mk.injEq] at h1950
    rcases h1950 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1950, hB1]
      convert table_10_row1950_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1950, hB2]
      convert table_10_row1950_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1950, hB3]
      convert table_10_row1950_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1950, hB4]
      convert table_10_row1950_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1950, hB5]
      convert table_10_row1950_k5_margin using 1 <;> norm_num
  rcases h with h1975 | h
  · simp only [Prod.mk.injEq] at h1975
    rcases h1975 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_1975, hB1]
      convert table_10_row1975_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1975, hB2]
      convert table_10_row1975_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1975, hB3]
      convert table_10_row1975_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1975, hB4]
      convert table_10_row1975_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_1975, hB5]
      convert table_10_row1975_k5_margin using 1 <;> norm_num
  rcases h with h2000 | h
  · simp only [Prod.mk.injEq] at h2000
    rcases h2000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2000, hB1]
      convert table_10_row2000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2000, hB2]
      convert table_10_row2000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2000, hB3]
      convert table_10_row2000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2000, hB4]
      convert table_10_row2000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2000, hB5]
      convert table_10_row2000_k5_margin using 1 <;> norm_num
  rcases h with h2025 | h
  · simp only [Prod.mk.injEq] at h2025
    rcases h2025 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2025, hB1]
      convert table_10_row2025_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2025, hB2]
      convert table_10_row2025_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2025, hB3]
      convert table_10_row2025_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2025, hB4]
      convert table_10_row2025_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2025, hB5]
      convert table_10_row2025_k5_margin using 1 <;> norm_num
  rcases h with h2050 | h
  · simp only [Prod.mk.injEq] at h2050
    rcases h2050 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2050, hB1]
      convert table_10_row2050_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2050, hB2]
      convert table_10_row2050_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2050, hB3]
      convert table_10_row2050_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2050, hB4]
      convert table_10_row2050_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2050, hB5]
      convert table_10_row2050_k5_margin using 1 <;> norm_num
  rcases h with h2075 | h
  · simp only [Prod.mk.injEq] at h2075
    rcases h2075 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2075, hB1]
      convert table_10_row2075_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2075, hB2]
      convert table_10_row2075_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2075, hB3]
      convert table_10_row2075_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2075, hB4]
      convert table_10_row2075_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2075, hB5]
      convert table_10_row2075_k5_margin using 1 <;> norm_num
  rcases h with h2100 | h
  · simp only [Prod.mk.injEq] at h2100
    rcases h2100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2100, hB1]
      convert table_10_row2100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2100, hB2]
      convert table_10_row2100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2100, hB3]
      convert table_10_row2100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2100, hB4]
      convert table_10_row2100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2100, hB5]
      convert table_10_row2100_k5_margin using 1 <;> norm_num
  rcases h with h2125 | h
  · simp only [Prod.mk.injEq] at h2125
    rcases h2125 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2125, hB1]
      convert table_10_row2125_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2125, hB2]
      convert table_10_row2125_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2125, hB3]
      convert table_10_row2125_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2125, hB4]
      convert table_10_row2125_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2125, hB5]
      convert table_10_row2125_k5_margin using 1 <;> norm_num
  rcases h with h2150 | h
  · simp only [Prod.mk.injEq] at h2150
    rcases h2150 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2150, hB1]
      convert table_10_row2150_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2150, hB2]
      convert table_10_row2150_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2150, hB3]
      convert table_10_row2150_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2150, hB4]
      convert table_10_row2150_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2150, hB5]
      convert table_10_row2150_k5_margin using 1 <;> norm_num
  rcases h with h2175 | h
  · simp only [Prod.mk.injEq] at h2175
    rcases h2175 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2175, hB1]
      convert table_10_row2175_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2175, hB2]
      convert table_10_row2175_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2175, hB3]
      convert table_10_row2175_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2175, hB4]
      convert table_10_row2175_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2175, hB5]
      convert table_10_row2175_k5_margin using 1 <;> norm_num
  rcases h with h2200 | h
  · simp only [Prod.mk.injEq] at h2200
    rcases h2200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2200, hB1]
      convert table_10_row2200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2200, hB2]
      convert table_10_row2200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2200, hB3]
      convert table_10_row2200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2200, hB4]
      convert table_10_row2200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2200, hB5]
      convert table_10_row2200_k5_margin using 1 <;> norm_num
  rcases h with h2225 | h
  · simp only [Prod.mk.injEq] at h2225
    rcases h2225 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2225, hB1]
      convert table_10_row2225_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2225, hB2]
      convert table_10_row2225_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2225, hB3]
      convert table_10_row2225_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2225, hB4]
      convert table_10_row2225_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2225, hB5]
      convert table_10_row2225_k5_margin using 1 <;> norm_num
  rcases h with h2250 | h
  · simp only [Prod.mk.injEq] at h2250
    rcases h2250 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2250, hB1]
      convert table_10_row2250_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2250, hB2]
      convert table_10_row2250_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2250, hB3]
      convert table_10_row2250_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2250, hB4]
      convert table_10_row2250_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2250, hB5]
      convert table_10_row2250_k5_margin using 1 <;> norm_num
  rcases h with h2275 | h
  · simp only [Prod.mk.injEq] at h2275
    rcases h2275 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2275, hB1]
      convert table_10_row2275_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2275, hB2]
      convert table_10_row2275_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2275, hB3]
      convert table_10_row2275_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2275, hB4]
      convert table_10_row2275_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2275, hB5]
      convert table_10_row2275_k5_margin using 1 <;> norm_num
  rcases h with h2300 | h
  · simp only [Prod.mk.injEq] at h2300
    rcases h2300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2300, hB1]
      convert table_10_row2300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2300, hB2]
      convert table_10_row2300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2300, hB3]
      convert table_10_row2300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2300, hB4]
      convert table_10_row2300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2300, hB5]
      convert table_10_row2300_k5_margin using 1 <;> norm_num
  rcases h with h2325 | h
  · simp only [Prod.mk.injEq] at h2325
    rcases h2325 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2325, hB1]
      convert table_10_row2325_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2325, hB2]
      convert table_10_row2325_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2325, hB3]
      convert table_10_row2325_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2325, hB4]
      convert table_10_row2325_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2325, hB5]
      convert table_10_row2325_k5_margin using 1 <;> norm_num
  rcases h with h2350 | h
  · simp only [Prod.mk.injEq] at h2350
    rcases h2350 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2350, hB1]
      convert table_10_row2350_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2350, hB2]
      convert table_10_row2350_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2350, hB3]
      convert table_10_row2350_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2350, hB4]
      convert table_10_row2350_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2350, hB5]
      convert table_10_row2350_k5_margin using 1 <;> norm_num
  rcases h with h2375 | h
  · simp only [Prod.mk.injEq] at h2375
    rcases h2375 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2375, hB1]
      convert table_10_row2375_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2375, hB2]
      convert table_10_row2375_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2375, hB3]
      convert table_10_row2375_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2375, hB4]
      convert table_10_row2375_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2375, hB5]
      convert table_10_row2375_k5_margin using 1 <;> norm_num
  rcases h with h2400 | h
  · simp only [Prod.mk.injEq] at h2400
    rcases h2400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2400, hB1]
      convert table_10_row2400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2400, hB2]
      convert table_10_row2400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2400, hB3]
      convert table_10_row2400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2400, hB4]
      convert table_10_row2400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2400, hB5]
      convert table_10_row2400_k5_margin using 1 <;> norm_num
  rcases h with h2425 | h
  · simp only [Prod.mk.injEq] at h2425
    rcases h2425 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2425, hB1]
      convert table_10_row2425_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2425, hB2]
      convert table_10_row2425_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2425, hB3]
      convert table_10_row2425_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2425, hB4]
      convert table_10_row2425_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2425, hB5]
      convert table_10_row2425_k5_margin using 1 <;> norm_num
  rcases h with h2450 | h
  · simp only [Prod.mk.injEq] at h2450
    rcases h2450 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2450, hB1]
      convert table_10_row2450_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2450, hB2]
      convert table_10_row2450_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2450, hB3]
      convert table_10_row2450_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2450, hB4]
      convert table_10_row2450_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2450, hB5]
      convert table_10_row2450_k5_margin using 1 <;> norm_num
  rcases h with h2475 | h
  · simp only [Prod.mk.injEq] at h2475
    rcases h2475 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2475, hB1]
      convert table_10_row2475_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2475, hB2]
      convert table_10_row2475_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2475, hB3]
      convert table_10_row2475_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2475, hB4]
      convert table_10_row2475_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2475, hB5]
      convert table_10_row2475_k5_margin using 1 <;> norm_num
  rcases h with h2500 | h
  · simp only [Prod.mk.injEq] at h2500
    rcases h2500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2500, hB1]
      convert table_10_row2500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2500, hB2]
      convert table_10_row2500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2500, hB3]
      convert table_10_row2500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2500, hB4]
      convert table_10_row2500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2500, hB5]
      convert table_10_row2500_k5_margin using 1 <;> norm_num
  rcases h with h2525 | h
  · simp only [Prod.mk.injEq] at h2525
    rcases h2525 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2525, hB1]
      convert table_10_row2525_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2525, hB2]
      convert table_10_row2525_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2525, hB3]
      convert table_10_row2525_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2525, hB4]
      convert table_10_row2525_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2525, hB5]
      convert table_10_row2525_k5_margin using 1 <;> norm_num
  rcases h with h2550 | h
  · simp only [Prod.mk.injEq] at h2550
    rcases h2550 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2550, hB1]
      convert table_10_row2550_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2550, hB2]
      convert table_10_row2550_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2550, hB3]
      convert table_10_row2550_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2550, hB4]
      convert table_10_row2550_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2550, hB5]
      convert table_10_row2550_k5_margin using 1 <;> norm_num
  rcases h with h2575 | h
  · simp only [Prod.mk.injEq] at h2575
    rcases h2575 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2575, hB1]
      convert table_10_row2575_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2575, hB2]
      convert table_10_row2575_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2575, hB3]
      convert table_10_row2575_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2575, hB4]
      convert table_10_row2575_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2575, hB5]
      convert table_10_row2575_k5_margin using 1 <;> norm_num
  rcases h with h2600 | h
  · simp only [Prod.mk.injEq] at h2600
    rcases h2600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2600, hB1]
      convert table_10_row2600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2600, hB2]
      convert table_10_row2600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2600, hB3]
      convert table_10_row2600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2600, hB4]
      convert table_10_row2600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2600, hB5]
      convert table_10_row2600_k5_margin using 1 <;> norm_num
  rcases h with h2625 | h
  · simp only [Prod.mk.injEq] at h2625
    rcases h2625 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2625, hB1]
      convert table_10_row2625_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2625, hB2]
      convert table_10_row2625_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2625, hB3]
      convert table_10_row2625_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2625, hB4]
      convert table_10_row2625_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2625, hB5]
      convert table_10_row2625_k5_margin using 1 <;> norm_num
  rcases h with h2650 | h
  · simp only [Prod.mk.injEq] at h2650
    rcases h2650 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2650, hB1]
      convert table_10_row2650_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2650, hB2]
      convert table_10_row2650_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2650, hB3]
      convert table_10_row2650_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2650, hB4]
      convert table_10_row2650_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2650, hB5]
      convert table_10_row2650_k5_margin using 1 <;> norm_num
  rcases h with h2675 | h
  · simp only [Prod.mk.injEq] at h2675
    rcases h2675 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2675, hB1]
      convert table_10_row2675_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2675, hB2]
      convert table_10_row2675_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2675, hB3]
      convert table_10_row2675_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2675, hB4]
      convert table_10_row2675_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2675, hB5]
      convert table_10_row2675_k5_margin using 1 <;> norm_num
  rcases h with h2700 | h
  · simp only [Prod.mk.injEq] at h2700
    rcases h2700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2700, hB1]
      convert table_10_row2700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2700, hB2]
      convert table_10_row2700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2700, hB3]
      convert table_10_row2700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2700, hB4]
      convert table_10_row2700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2700, hB5]
      convert table_10_row2700_k5_margin using 1 <;> norm_num
  rcases h with h2725 | h
  · simp only [Prod.mk.injEq] at h2725
    rcases h2725 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2725, hB1]
      convert table_10_row2725_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2725, hB2]
      convert table_10_row2725_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2725, hB3]
      convert table_10_row2725_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2725, hB4]
      convert table_10_row2725_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2725, hB5]
      convert table_10_row2725_k5_margin using 1 <;> norm_num
  rcases h with h2750 | h
  · simp only [Prod.mk.injEq] at h2750
    rcases h2750 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2750, hB1]
      convert table_10_row2750_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2750, hB2]
      convert table_10_row2750_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2750, hB3]
      convert table_10_row2750_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2750, hB4]
      convert table_10_row2750_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2750, hB5]
      convert table_10_row2750_k5_margin using 1 <;> norm_num
  rcases h with h2775 | h
  · simp only [Prod.mk.injEq] at h2775
    rcases h2775 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2775, hB1]
      convert table_10_row2775_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2775, hB2]
      convert table_10_row2775_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2775, hB3]
      convert table_10_row2775_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2775, hB4]
      convert table_10_row2775_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2775, hB5]
      convert table_10_row2775_k5_margin using 1 <;> norm_num
  rcases h with h2800 | h
  · simp only [Prod.mk.injEq] at h2800
    rcases h2800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2800, hB1]
      convert table_10_row2800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2800, hB2]
      convert table_10_row2800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2800, hB3]
      convert table_10_row2800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2800, hB4]
      convert table_10_row2800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2800, hB5]
      convert table_10_row2800_k5_margin using 1 <;> norm_num
  rcases h with h2825 | h
  · simp only [Prod.mk.injEq] at h2825
    rcases h2825 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2825, hB1]
      convert table_10_row2825_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2825, hB2]
      convert table_10_row2825_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2825, hB3]
      convert table_10_row2825_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2825, hB4]
      convert table_10_row2825_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2825, hB5]
      convert table_10_row2825_k5_margin using 1 <;> norm_num
  rcases h with h2850 | h
  · simp only [Prod.mk.injEq] at h2850
    rcases h2850 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2850, hB1]
      convert table_10_row2850_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2850, hB2]
      convert table_10_row2850_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2850, hB3]
      convert table_10_row2850_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2850, hB4]
      convert table_10_row2850_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2850, hB5]
      convert table_10_row2850_k5_margin using 1 <;> norm_num
  rcases h with h2875 | h
  · simp only [Prod.mk.injEq] at h2875
    rcases h2875 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2875, hB1]
      convert table_10_row2875_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2875, hB2]
      convert table_10_row2875_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2875, hB3]
      convert table_10_row2875_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2875, hB4]
      convert table_10_row2875_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2875, hB5]
      convert table_10_row2875_k5_margin using 1 <;> norm_num
  rcases h with h2900 | h
  · simp only [Prod.mk.injEq] at h2900
    rcases h2900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2900, hB1]
      convert table_10_row2900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2900, hB2]
      convert table_10_row2900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2900, hB3]
      convert table_10_row2900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2900, hB4]
      convert table_10_row2900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2900, hB5]
      convert table_10_row2900_k5_margin using 1 <;> norm_num
  rcases h with h2925 | h
  · simp only [Prod.mk.injEq] at h2925
    rcases h2925 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2925, hB1]
      convert table_10_row2925_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2925, hB2]
      convert table_10_row2925_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2925, hB3]
      convert table_10_row2925_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2925, hB4]
      convert table_10_row2925_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2925, hB5]
      convert table_10_row2925_k5_margin using 1 <;> norm_num
  rcases h with h2950 | h
  · simp only [Prod.mk.injEq] at h2950
    rcases h2950 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2950, hB1]
      convert table_10_row2950_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2950, hB2]
      convert table_10_row2950_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2950, hB3]
      convert table_10_row2950_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2950, hB4]
      convert table_10_row2950_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2950, hB5]
      convert table_10_row2950_k5_margin using 1 <;> norm_num
  rcases h with h2975 | h
  · simp only [Prod.mk.injEq] at h2975
    rcases h2975 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_2975, hB1]
      convert table_10_row2975_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2975, hB2]
      convert table_10_row2975_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2975, hB3]
      convert table_10_row2975_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2975, hB4]
      convert table_10_row2975_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_2975, hB5]
      convert table_10_row2975_k5_margin using 1 <;> norm_num
  rcases h with h3000 | h
  · simp only [Prod.mk.injEq] at h3000
    rcases h3000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3000, hB1]
      convert table_10_row3000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3000, hB2]
      convert table_10_row3000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3000, hB3]
      convert table_10_row3000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3000, hB4]
      convert table_10_row3000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3000, hB5]
      convert table_10_row3000_k5_margin using 1 <;> norm_num
  rcases h with h3025 | h
  · simp only [Prod.mk.injEq] at h3025
    rcases h3025 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3025, hB1]
      convert table_10_row3025_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3025, hB2]
      convert table_10_row3025_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3025, hB3]
      convert table_10_row3025_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3025, hB4]
      convert table_10_row3025_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3025, hB5]
      convert table_10_row3025_k5_margin using 1 <;> norm_num
  rcases h with h3050 | h
  · simp only [Prod.mk.injEq] at h3050
    rcases h3050 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3050, hB1]
      convert table_10_row3050_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3050, hB2]
      convert table_10_row3050_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3050, hB3]
      convert table_10_row3050_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3050, hB4]
      convert table_10_row3050_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3050, hB5]
      convert table_10_row3050_k5_margin using 1 <;> norm_num
  rcases h with h3075 | h
  · simp only [Prod.mk.injEq] at h3075
    rcases h3075 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3075, hB1]
      convert table_10_row3075_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3075, hB2]
      convert table_10_row3075_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3075, hB3]
      convert table_10_row3075_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3075, hB4]
      convert table_10_row3075_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3075, hB5]
      convert table_10_row3075_k5_margin using 1 <;> norm_num
  rcases h with h3100 | h
  · simp only [Prod.mk.injEq] at h3100
    rcases h3100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3100, hB1]
      convert table_10_row3100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3100, hB2]
      convert table_10_row3100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3100, hB3]
      convert table_10_row3100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3100, hB4]
      convert table_10_row3100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3100, hB5]
      convert table_10_row3100_k5_margin using 1 <;> norm_num
  rcases h with h3125 | h
  · simp only [Prod.mk.injEq] at h3125
    rcases h3125 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3125, hB1]
      convert table_10_row3125_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3125, hB2]
      convert table_10_row3125_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3125, hB3]
      convert table_10_row3125_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3125, hB4]
      convert table_10_row3125_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3125, hB5]
      convert table_10_row3125_k5_margin using 1 <;> norm_num
  rcases h with h3150 | h
  · simp only [Prod.mk.injEq] at h3150
    rcases h3150 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3150, hB1]
      convert table_10_row3150_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3150, hB2]
      convert table_10_row3150_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3150, hB3]
      convert table_10_row3150_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3150, hB4]
      convert table_10_row3150_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3150, hB5]
      convert table_10_row3150_k5_margin using 1 <;> norm_num
  rcases h with h3175 | h
  · simp only [Prod.mk.injEq] at h3175
    rcases h3175 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3175, hB1]
      convert table_10_row3175_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3175, hB2]
      convert table_10_row3175_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3175, hB3]
      convert table_10_row3175_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3175, hB4]
      convert table_10_row3175_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3175, hB5]
      convert table_10_row3175_k5_margin using 1 <;> norm_num
  rcases h with h3200 | h
  · simp only [Prod.mk.injEq] at h3200
    rcases h3200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3200, hB1]
      convert table_10_row3200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3200, hB2]
      convert table_10_row3200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3200, hB3]
      convert table_10_row3200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3200, hB4]
      convert table_10_row3200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3200, hB5]
      convert table_10_row3200_k5_margin using 1 <;> norm_num
  rcases h with h3225 | h
  · simp only [Prod.mk.injEq] at h3225
    rcases h3225 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3225, hB1]
      convert table_10_row3225_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3225, hB2]
      convert table_10_row3225_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3225, hB3]
      convert table_10_row3225_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3225, hB4]
      convert table_10_row3225_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3225, hB5]
      convert table_10_row3225_k5_margin using 1 <;> norm_num
  rcases h with h3250 | h
  · simp only [Prod.mk.injEq] at h3250
    rcases h3250 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3250, hB1]
      convert table_10_row3250_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3250, hB2]
      convert table_10_row3250_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3250, hB3]
      convert table_10_row3250_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3250, hB4]
      convert table_10_row3250_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3250, hB5]
      convert table_10_row3250_k5_margin using 1 <;> norm_num
  rcases h with h3275 | h
  · simp only [Prod.mk.injEq] at h3275
    rcases h3275 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3275, hB1]
      convert table_10_row3275_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3275, hB2]
      convert table_10_row3275_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3275, hB3]
      convert table_10_row3275_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3275, hB4]
      convert table_10_row3275_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3275, hB5]
      convert table_10_row3275_k5_margin using 1 <;> norm_num
  rcases h with h3300 | h
  · simp only [Prod.mk.injEq] at h3300
    rcases h3300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3300, hB1]
      convert table_10_row3300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3300, hB2]
      convert table_10_row3300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3300, hB3]
      convert table_10_row3300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3300, hB4]
      convert table_10_row3300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3300, hB5]
      convert table_10_row3300_k5_margin using 1 <;> norm_num
  rcases h with h3325 | h
  · simp only [Prod.mk.injEq] at h3325
    rcases h3325 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3325, hB1]
      convert table_10_row3325_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3325, hB2]
      convert table_10_row3325_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3325, hB3]
      convert table_10_row3325_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3325, hB4]
      convert table_10_row3325_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3325, hB5]
      convert table_10_row3325_k5_margin using 1 <;> norm_num
  rcases h with h3350 | h
  · simp only [Prod.mk.injEq] at h3350
    rcases h3350 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3350, hB1]
      convert table_10_row3350_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3350, hB2]
      convert table_10_row3350_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3350, hB3]
      convert table_10_row3350_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3350, hB4]
      convert table_10_row3350_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3350, hB5]
      convert table_10_row3350_k5_margin using 1 <;> norm_num
  rcases h with h3375 | h
  · simp only [Prod.mk.injEq] at h3375
    rcases h3375 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3375, hB1]
      convert table_10_row3375_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3375, hB2]
      convert table_10_row3375_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3375, hB3]
      convert table_10_row3375_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3375, hB4]
      convert table_10_row3375_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3375, hB5]
      convert table_10_row3375_k5_margin using 1 <;> norm_num
  rcases h with h3400 | h
  · simp only [Prod.mk.injEq] at h3400
    rcases h3400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3400, hB1]
      convert table_10_row3400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3400, hB2]
      convert table_10_row3400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3400, hB3]
      convert table_10_row3400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3400, hB4]
      convert table_10_row3400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3400, hB5]
      convert table_10_row3400_k5_margin using 1 <;> norm_num
  rcases h with h3425 | h
  · simp only [Prod.mk.injEq] at h3425
    rcases h3425 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3425, hB1]
      convert table_10_row3425_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3425, hB2]
      convert table_10_row3425_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3425, hB3]
      convert table_10_row3425_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3425, hB4]
      convert table_10_row3425_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3425, hB5]
      convert table_10_row3425_k5_margin using 1 <;> norm_num
  rcases h with h3450 | h
  · simp only [Prod.mk.injEq] at h3450
    rcases h3450 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3450, hB1]
      convert table_10_row3450_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3450, hB2]
      convert table_10_row3450_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3450, hB3]
      convert table_10_row3450_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3450, hB4]
      convert table_10_row3450_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3450, hB5]
      convert table_10_row3450_k5_margin using 1 <;> norm_num
  rcases h with h3475 | h
  · simp only [Prod.mk.injEq] at h3475
    rcases h3475 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3475, hB1]
      convert table_10_row3475_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3475, hB2]
      convert table_10_row3475_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3475, hB3]
      convert table_10_row3475_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3475, hB4]
      convert table_10_row3475_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3475, hB5]
      convert table_10_row3475_k5_margin using 1 <;> norm_num
  rcases h with h3500 | h
  · simp only [Prod.mk.injEq] at h3500
    rcases h3500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3500, hB1]
      convert table_10_row3500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3500, hB2]
      convert table_10_row3500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3500, hB3]
      convert table_10_row3500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3500, hB4]
      convert table_10_row3500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3500, hB5]
      convert table_10_row3500_k5_margin using 1 <;> norm_num
  rcases h with h3525 | h
  · simp only [Prod.mk.injEq] at h3525
    rcases h3525 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3525, hB1]
      convert table_10_row3525_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3525, hB2]
      convert table_10_row3525_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3525, hB3]
      convert table_10_row3525_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3525, hB4]
      convert table_10_row3525_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3525, hB5]
      convert table_10_row3525_k5_margin using 1 <;> norm_num
  rcases h with h3550 | h
  · simp only [Prod.mk.injEq] at h3550
    rcases h3550 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3550, hB1]
      convert table_10_row3550_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3550, hB2]
      convert table_10_row3550_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3550, hB3]
      convert table_10_row3550_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3550, hB4]
      convert table_10_row3550_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3550, hB5]
      convert table_10_row3550_k5_margin using 1 <;> norm_num
  rcases h with h3575 | h
  · simp only [Prod.mk.injEq] at h3575
    rcases h3575 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3575, hB1]
      convert table_10_row3575_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3575, hB2]
      convert table_10_row3575_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3575, hB3]
      convert table_10_row3575_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3575, hB4]
      convert table_10_row3575_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3575, hB5]
      convert table_10_row3575_k5_margin using 1 <;> norm_num
  rcases h with h3600 | h
  · simp only [Prod.mk.injEq] at h3600
    rcases h3600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3600, hB1]
      convert table_10_row3600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3600, hB2]
      convert table_10_row3600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3600, hB3]
      convert table_10_row3600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3600, hB4]
      convert table_10_row3600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3600, hB5]
      convert table_10_row3600_k5_margin using 1 <;> norm_num
  rcases h with h3625 | h
  · simp only [Prod.mk.injEq] at h3625
    rcases h3625 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3625, hB1]
      convert table_10_row3625_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3625, hB2]
      convert table_10_row3625_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3625, hB3]
      convert table_10_row3625_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3625, hB4]
      convert table_10_row3625_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3625, hB5]
      convert table_10_row3625_k5_margin using 1 <;> norm_num
  rcases h with h3650 | h
  · simp only [Prod.mk.injEq] at h3650
    rcases h3650 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3650, hB1]
      convert table_10_row3650_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3650, hB2]
      convert table_10_row3650_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3650, hB3]
      convert table_10_row3650_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3650, hB4]
      convert table_10_row3650_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3650, hB5]
      convert table_10_row3650_k5_margin using 1 <;> norm_num
  rcases h with h3675 | h
  · simp only [Prod.mk.injEq] at h3675
    rcases h3675 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3675, hB1]
      convert table_10_row3675_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3675, hB2]
      convert table_10_row3675_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3675, hB3]
      convert table_10_row3675_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3675, hB4]
      convert table_10_row3675_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3675, hB5]
      convert table_10_row3675_k5_margin using 1 <;> norm_num
  rcases h with h3700 | h
  · simp only [Prod.mk.injEq] at h3700
    rcases h3700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3700, hB1]
      convert table_10_row3700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3700, hB2]
      convert table_10_row3700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3700, hB3]
      convert table_10_row3700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3700, hB4]
      convert table_10_row3700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3700, hB5]
      convert table_10_row3700_k5_margin using 1 <;> norm_num
  rcases h with h3725 | h
  · simp only [Prod.mk.injEq] at h3725
    rcases h3725 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3725, hB1]
      convert table_10_row3725_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3725, hB2]
      convert table_10_row3725_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3725, hB3]
      convert table_10_row3725_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3725, hB4]
      convert table_10_row3725_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3725, hB5]
      convert table_10_row3725_k5_margin using 1 <;> norm_num
  rcases h with h3750 | h
  · simp only [Prod.mk.injEq] at h3750
    rcases h3750 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3750, hB1]
      convert table_10_row3750_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3750, hB2]
      convert table_10_row3750_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3750, hB3]
      convert table_10_row3750_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3750, hB4]
      convert table_10_row3750_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3750, hB5]
      convert table_10_row3750_k5_margin using 1 <;> norm_num
  rcases h with h3775 | h
  · simp only [Prod.mk.injEq] at h3775
    rcases h3775 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3775, hB1]
      convert table_10_row3775_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3775, hB2]
      convert table_10_row3775_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3775, hB3]
      convert table_10_row3775_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3775, hB4]
      convert table_10_row3775_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3775, hB5]
      convert table_10_row3775_k5_margin using 1 <;> norm_num
  rcases h with h3800 | h
  · simp only [Prod.mk.injEq] at h3800
    rcases h3800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3800, hB1]
      convert table_10_row3800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3800, hB2]
      convert table_10_row3800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3800, hB3]
      convert table_10_row3800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3800, hB4]
      convert table_10_row3800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3800, hB5]
      convert table_10_row3800_k5_margin using 1 <;> norm_num
  rcases h with h3825 | h
  · simp only [Prod.mk.injEq] at h3825
    rcases h3825 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3825, hB1]
      convert table_10_row3825_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3825, hB2]
      convert table_10_row3825_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3825, hB3]
      convert table_10_row3825_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3825, hB4]
      convert table_10_row3825_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3825, hB5]
      convert table_10_row3825_k5_margin using 1 <;> norm_num
  rcases h with h3850 | h
  · simp only [Prod.mk.injEq] at h3850
    rcases h3850 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3850, hB1]
      convert table_10_row3850_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3850, hB2]
      convert table_10_row3850_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3850, hB3]
      convert table_10_row3850_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3850, hB4]
      convert table_10_row3850_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3850, hB5]
      convert table_10_row3850_k5_margin using 1 <;> norm_num
  rcases h with h3875 | h
  · simp only [Prod.mk.injEq] at h3875
    rcases h3875 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3875, hB1]
      convert table_10_row3875_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3875, hB2]
      convert table_10_row3875_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3875, hB3]
      convert table_10_row3875_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3875, hB4]
      convert table_10_row3875_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3875, hB5]
      convert table_10_row3875_k5_margin using 1 <;> norm_num
  rcases h with h3900 | h
  · simp only [Prod.mk.injEq] at h3900
    rcases h3900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3900, hB1]
      convert table_10_row3900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3900, hB2]
      convert table_10_row3900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3900, hB3]
      convert table_10_row3900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3900, hB4]
      convert table_10_row3900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3900, hB5]
      convert table_10_row3900_k5_margin using 1 <;> norm_num
  rcases h with h3925 | h
  · simp only [Prod.mk.injEq] at h3925
    rcases h3925 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3925, hB1]
      convert table_10_row3925_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3925, hB2]
      convert table_10_row3925_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3925, hB3]
      convert table_10_row3925_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3925, hB4]
      convert table_10_row3925_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3925, hB5]
      convert table_10_row3925_k5_margin using 1 <;> norm_num
  rcases h with h3950 | h
  · simp only [Prod.mk.injEq] at h3950
    rcases h3950 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3950, hB1]
      convert table_10_row3950_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3950, hB2]
      convert table_10_row3950_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3950, hB3]
      convert table_10_row3950_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3950, hB4]
      convert table_10_row3950_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3950, hB5]
      convert table_10_row3950_k5_margin using 1 <;> norm_num
  rcases h with h3975 | h
  · simp only [Prod.mk.injEq] at h3975
    rcases h3975 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_3975, hB1]
      convert table_10_row3975_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3975, hB2]
      convert table_10_row3975_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3975, hB3]
      convert table_10_row3975_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3975, hB4]
      convert table_10_row3975_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_3975, hB5]
      convert table_10_row3975_k5_margin using 1 <;> norm_num
  rcases h with h4000 | h
  · simp only [Prod.mk.injEq] at h4000
    rcases h4000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4000, hB1]
      convert table_10_row4000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4000, hB2]
      convert table_10_row4000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4000, hB3]
      convert table_10_row4000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4000, hB4]
      convert table_10_row4000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4000, hB5]
      convert table_10_row4000_k5_margin using 1 <;> norm_num
  rcases h with h4025 | h
  · simp only [Prod.mk.injEq] at h4025
    rcases h4025 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4025, hB1]
      convert table_10_row4025_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4025, hB2]
      convert table_10_row4025_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4025, hB3]
      convert table_10_row4025_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4025, hB4]
      convert table_10_row4025_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4025, hB5]
      convert table_10_row4025_k5_margin using 1 <;> norm_num
  rcases h with h4050 | h
  · simp only [Prod.mk.injEq] at h4050
    rcases h4050 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4050, hB1]
      convert table_10_row4050_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4050, hB2]
      convert table_10_row4050_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4050, hB3]
      convert table_10_row4050_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4050, hB4]
      convert table_10_row4050_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4050, hB5]
      convert table_10_row4050_k5_margin using 1 <;> norm_num
  rcases h with h4075 | h
  · simp only [Prod.mk.injEq] at h4075
    rcases h4075 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4075, hB1]
      convert table_10_row4075_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4075, hB2]
      convert table_10_row4075_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4075, hB3]
      convert table_10_row4075_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4075, hB4]
      convert table_10_row4075_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4075, hB5]
      convert table_10_row4075_k5_margin using 1 <;> norm_num
  rcases h with h4100 | h
  · simp only [Prod.mk.injEq] at h4100
    rcases h4100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4100, hB1]
      convert table_10_row4100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4100, hB2]
      convert table_10_row4100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4100, hB3]
      convert table_10_row4100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4100, hB4]
      convert table_10_row4100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4100, hB5]
      convert table_10_row4100_k5_margin using 1 <;> norm_num
  rcases h with h4125 | h
  · simp only [Prod.mk.injEq] at h4125
    rcases h4125 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4125, hB1]
      convert table_10_row4125_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4125, hB2]
      convert table_10_row4125_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4125, hB3]
      convert table_10_row4125_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4125, hB4]
      convert table_10_row4125_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4125, hB5]
      convert table_10_row4125_k5_margin using 1 <;> norm_num
  rcases h with h4150 | h
  · simp only [Prod.mk.injEq] at h4150
    rcases h4150 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4150, hB1]
      convert table_10_row4150_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4150, hB2]
      convert table_10_row4150_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4150, hB3]
      convert table_10_row4150_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4150, hB4]
      convert table_10_row4150_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4150, hB5]
      convert table_10_row4150_k5_margin using 1 <;> norm_num
  rcases h with h4175 | h
  · simp only [Prod.mk.injEq] at h4175
    rcases h4175 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4175, hB1]
      convert table_10_row4175_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4175, hB2]
      convert table_10_row4175_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4175, hB3]
      convert table_10_row4175_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4175, hB4]
      convert table_10_row4175_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4175, hB5]
      convert table_10_row4175_k5_margin using 1 <;> norm_num
  rcases h with h4200 | h
  · simp only [Prod.mk.injEq] at h4200
    rcases h4200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4200, hB1]
      convert table_10_row4200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4200, hB2]
      convert table_10_row4200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4200, hB3]
      convert table_10_row4200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4200, hB4]
      convert table_10_row4200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4200, hB5]
      convert table_10_row4200_k5_margin using 1 <;> norm_num
  rcases h with h4225 | h
  · simp only [Prod.mk.injEq] at h4225
    rcases h4225 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4225, hB1]
      convert table_10_row4225_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4225, hB2]
      convert table_10_row4225_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4225, hB3]
      convert table_10_row4225_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4225, hB4]
      convert table_10_row4225_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4225, hB5]
      convert table_10_row4225_k5_margin using 1 <;> norm_num
  rcases h with h4250 | h
  · simp only [Prod.mk.injEq] at h4250
    rcases h4250 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4250, hB1]
      convert table_10_row4250_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4250, hB2]
      convert table_10_row4250_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4250, hB3]
      convert table_10_row4250_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4250, hB4]
      convert table_10_row4250_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4250, hB5]
      convert table_10_row4250_k5_margin using 1 <;> norm_num
  rcases h with h4275 | h
  · simp only [Prod.mk.injEq] at h4275
    rcases h4275 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4275, hB1]
      convert table_10_row4275_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4275, hB2]
      convert table_10_row4275_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4275, hB3]
      convert table_10_row4275_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4275, hB4]
      convert table_10_row4275_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4275, hB5]
      convert table_10_row4275_k5_margin using 1 <;> norm_num
  rcases h with h4300 | h
  · simp only [Prod.mk.injEq] at h4300
    rcases h4300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4300, hB1]
      convert table_10_row4300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4300, hB2]
      convert table_10_row4300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4300, hB3]
      convert table_10_row4300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4300, hB4]
      convert table_10_row4300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4300, hB5]
      convert table_10_row4300_k5_margin using 1 <;> norm_num
  rcases h with h4325 | h
  · simp only [Prod.mk.injEq] at h4325
    rcases h4325 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4325, hB1]
      convert table_10_row4325_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4325, hB2]
      convert table_10_row4325_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4325, hB3]
      convert table_10_row4325_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4325, hB4]
      convert table_10_row4325_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4325, hB5]
      convert table_10_row4325_k5_margin using 1 <;> norm_num
  rcases h with h4350 | h
  · simp only [Prod.mk.injEq] at h4350
    rcases h4350 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4350, hB1]
      convert table_10_row4350_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4350, hB2]
      convert table_10_row4350_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4350, hB3]
      convert table_10_row4350_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4350, hB4]
      convert table_10_row4350_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4350, hB5]
      convert table_10_row4350_k5_margin using 1 <;> norm_num
  rcases h with h4375 | h
  · simp only [Prod.mk.injEq] at h4375
    rcases h4375 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4375, hB1]
      convert table_10_row4375_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4375, hB2]
      convert table_10_row4375_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4375, hB3]
      convert table_10_row4375_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4375, hB4]
      convert table_10_row4375_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4375, hB5]
      convert table_10_row4375_k5_margin using 1 <;> norm_num
  rcases h with h4400 | h
  · simp only [Prod.mk.injEq] at h4400
    rcases h4400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4400, hB1]
      convert table_10_row4400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4400, hB2]
      convert table_10_row4400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4400, hB3]
      convert table_10_row4400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4400, hB4]
      convert table_10_row4400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4400, hB5]
      convert table_10_row4400_k5_margin using 1 <;> norm_num
  rcases h with h4425 | h
  · simp only [Prod.mk.injEq] at h4425
    rcases h4425 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4425, hB1]
      convert table_10_row4425_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4425, hB2]
      convert table_10_row4425_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4425, hB3]
      convert table_10_row4425_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4425, hB4]
      convert table_10_row4425_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4425, hB5]
      convert table_10_row4425_k5_margin using 1 <;> norm_num
  rcases h with h4450 | h
  · simp only [Prod.mk.injEq] at h4450
    rcases h4450 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4450, hB1]
      convert table_10_row4450_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4450, hB2]
      convert table_10_row4450_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4450, hB3]
      convert table_10_row4450_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4450, hB4]
      convert table_10_row4450_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4450, hB5]
      convert table_10_row4450_k5_margin using 1 <;> norm_num
  rcases h with h4475 | h
  · simp only [Prod.mk.injEq] at h4475
    rcases h4475 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4475, hB1]
      convert table_10_row4475_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4475, hB2]
      convert table_10_row4475_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4475, hB3]
      convert table_10_row4475_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4475, hB4]
      convert table_10_row4475_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4475, hB5]
      convert table_10_row4475_k5_margin using 1 <;> norm_num
  rcases h with h4500 | h
  · simp only [Prod.mk.injEq] at h4500
    rcases h4500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4500, hB1]
      convert table_10_row4500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4500, hB2]
      convert table_10_row4500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4500, hB3]
      convert table_10_row4500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4500, hB4]
      convert table_10_row4500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4500, hB5]
      convert table_10_row4500_k5_margin using 1 <;> norm_num
  rcases h with h4525 | h
  · simp only [Prod.mk.injEq] at h4525
    rcases h4525 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4525, hB1]
      convert table_10_row4525_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4525, hB2]
      convert table_10_row4525_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4525, hB3]
      convert table_10_row4525_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4525, hB4]
      convert table_10_row4525_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4525, hB5]
      convert table_10_row4525_k5_margin using 1 <;> norm_num
  rcases h with h4550 | h
  · simp only [Prod.mk.injEq] at h4550
    rcases h4550 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4550, hB1]
      convert table_10_row4550_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4550, hB2]
      convert table_10_row4550_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4550, hB3]
      convert table_10_row4550_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4550, hB4]
      convert table_10_row4550_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4550, hB5]
      convert table_10_row4550_k5_margin using 1 <;> norm_num
  rcases h with h4575 | h
  · simp only [Prod.mk.injEq] at h4575
    rcases h4575 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4575, hB1]
      convert table_10_row4575_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4575, hB2]
      convert table_10_row4575_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4575, hB3]
      convert table_10_row4575_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4575, hB4]
      convert table_10_row4575_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4575, hB5]
      convert table_10_row4575_k5_margin using 1 <;> norm_num
  rcases h with h4600 | h
  · simp only [Prod.mk.injEq] at h4600
    rcases h4600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4600, hB1]
      convert table_10_row4600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4600, hB2]
      convert table_10_row4600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4600, hB3]
      convert table_10_row4600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4600, hB4]
      convert table_10_row4600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4600, hB5]
      convert table_10_row4600_k5_margin using 1 <;> norm_num
  rcases h with h4625 | h
  · simp only [Prod.mk.injEq] at h4625
    rcases h4625 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4625, hB1]
      convert table_10_row4625_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4625, hB2]
      convert table_10_row4625_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4625, hB3]
      convert table_10_row4625_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4625, hB4]
      convert table_10_row4625_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4625, hB5]
      convert table_10_row4625_k5_margin using 1 <;> norm_num
  rcases h with h4650 | h
  · simp only [Prod.mk.injEq] at h4650
    rcases h4650 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4650, hB1]
      convert table_10_row4650_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4650, hB2]
      convert table_10_row4650_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4650, hB3]
      convert table_10_row4650_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4650, hB4]
      convert table_10_row4650_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4650, hB5]
      convert table_10_row4650_k5_margin using 1 <;> norm_num
  rcases h with h4675 | h
  · simp only [Prod.mk.injEq] at h4675
    rcases h4675 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4675, hB1]
      convert table_10_row4675_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4675, hB2]
      convert table_10_row4675_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4675, hB3]
      convert table_10_row4675_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4675, hB4]
      convert table_10_row4675_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4675, hB5]
      convert table_10_row4675_k5_margin using 1 <;> norm_num
  rcases h with h4700 | h
  · simp only [Prod.mk.injEq] at h4700
    rcases h4700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4700, hB1]
      convert table_10_row4700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4700, hB2]
      convert table_10_row4700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4700, hB3]
      convert table_10_row4700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4700, hB4]
      convert table_10_row4700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4700, hB5]
      convert table_10_row4700_k5_margin using 1 <;> norm_num
  rcases h with h4725 | h
  · simp only [Prod.mk.injEq] at h4725
    rcases h4725 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4725, hB1]
      convert table_10_row4725_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4725, hB2]
      convert table_10_row4725_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4725, hB3]
      convert table_10_row4725_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4725, hB4]
      convert table_10_row4725_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4725, hB5]
      convert table_10_row4725_k5_margin using 1 <;> norm_num
  rcases h with h4750 | h
  · simp only [Prod.mk.injEq] at h4750
    rcases h4750 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4750, hB1]
      convert table_10_row4750_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4750, hB2]
      convert table_10_row4750_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4750, hB3]
      convert table_10_row4750_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4750, hB4]
      convert table_10_row4750_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4750, hB5]
      convert table_10_row4750_k5_margin using 1 <;> norm_num
  rcases h with h4775 | h
  · simp only [Prod.mk.injEq] at h4775
    rcases h4775 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4775, hB1]
      convert table_10_row4775_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4775, hB2]
      convert table_10_row4775_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4775, hB3]
      convert table_10_row4775_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4775, hB4]
      convert table_10_row4775_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4775, hB5]
      convert table_10_row4775_k5_margin using 1 <;> norm_num
  rcases h with h4800 | h
  · simp only [Prod.mk.injEq] at h4800
    rcases h4800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4800, hB1]
      convert table_10_row4800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4800, hB2]
      convert table_10_row4800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4800, hB3]
      convert table_10_row4800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4800, hB4]
      convert table_10_row4800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4800, hB5]
      convert table_10_row4800_k5_margin using 1 <;> norm_num
  rcases h with h4825 | h
  · simp only [Prod.mk.injEq] at h4825
    rcases h4825 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4825, hB1]
      convert table_10_row4825_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4825, hB2]
      convert table_10_row4825_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4825, hB3]
      convert table_10_row4825_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4825, hB4]
      convert table_10_row4825_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4825, hB5]
      convert table_10_row4825_k5_margin using 1 <;> norm_num
  rcases h with h4850 | h
  · simp only [Prod.mk.injEq] at h4850
    rcases h4850 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4850, hB1]
      convert table_10_row4850_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4850, hB2]
      convert table_10_row4850_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4850, hB3]
      convert table_10_row4850_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4850, hB4]
      convert table_10_row4850_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4850, hB5]
      convert table_10_row4850_k5_margin using 1 <;> norm_num
  rcases h with h4875 | h
  · simp only [Prod.mk.injEq] at h4875
    rcases h4875 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4875, hB1]
      convert table_10_row4875_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4875, hB2]
      convert table_10_row4875_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4875, hB3]
      convert table_10_row4875_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4875, hB4]
      convert table_10_row4875_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4875, hB5]
      convert table_10_row4875_k5_margin using 1 <;> norm_num
  rcases h with h4900 | h
  · simp only [Prod.mk.injEq] at h4900
    rcases h4900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4900, hB1]
      convert table_10_row4900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4900, hB2]
      convert table_10_row4900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4900, hB3]
      convert table_10_row4900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4900, hB4]
      convert table_10_row4900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4900, hB5]
      convert table_10_row4900_k5_margin using 1 <;> norm_num
  rcases h with h4925 | h
  · simp only [Prod.mk.injEq] at h4925
    rcases h4925 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4925, hB1]
      convert table_10_row4925_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4925, hB2]
      convert table_10_row4925_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4925, hB3]
      convert table_10_row4925_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4925, hB4]
      convert table_10_row4925_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4925, hB5]
      convert table_10_row4925_k5_margin using 1 <;> norm_num
  rcases h with h4950 | h
  · simp only [Prod.mk.injEq] at h4950
    rcases h4950 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4950, hB1]
      convert table_10_row4950_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4950, hB2]
      convert table_10_row4950_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4950, hB3]
      convert table_10_row4950_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4950, hB4]
      convert table_10_row4950_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4950, hB5]
      convert table_10_row4950_k5_margin using 1 <;> norm_num
  rcases h with h4975 | h
  · simp only [Prod.mk.injEq] at h4975
    rcases h4975 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_4975, hB1]
      convert table_10_row4975_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4975, hB2]
      convert table_10_row4975_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4975, hB3]
      convert table_10_row4975_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4975, hB4]
      convert table_10_row4975_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_4975, hB5]
      convert table_10_row4975_k5_margin using 1 <;> norm_num
  rcases h with h5000 | h
  · simp only [Prod.mk.injEq] at h5000
    rcases h5000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5000, hB1]
      convert table_10_row5000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5000, hB2]
      convert table_10_row5000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5000, hB3]
      convert table_10_row5000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5000, hB4]
      convert table_10_row5000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5000, hB5]
      convert table_10_row5000_k5_margin using 1 <;> norm_num
  rcases h with h5100 | h
  · simp only [Prod.mk.injEq] at h5100
    rcases h5100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5100, hB1]
      convert table_10_row5100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5100, hB2]
      convert table_10_row5100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5100, hB3]
      convert table_10_row5100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5100, hB4]
      convert table_10_row5100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5100, hB5]
      convert table_10_row5100_k5_margin using 1 <;> norm_num
  rcases h with h5200 | h
  · simp only [Prod.mk.injEq] at h5200
    rcases h5200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5200, hB1]
      convert table_10_row5200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5200, hB2]
      convert table_10_row5200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5200, hB3]
      convert table_10_row5200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5200, hB4]
      convert table_10_row5200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5200, hB5]
      convert table_10_row5200_k5_margin using 1 <;> norm_num
  rcases h with h5300 | h
  · simp only [Prod.mk.injEq] at h5300
    rcases h5300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5300, hB1]
      convert table_10_row5300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5300, hB2]
      convert table_10_row5300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5300, hB3]
      convert table_10_row5300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5300, hB4]
      convert table_10_row5300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5300, hB5]
      convert table_10_row5300_k5_margin using 1 <;> norm_num
  rcases h with h5400 | h
  · simp only [Prod.mk.injEq] at h5400
    rcases h5400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5400, hB1]
      convert table_10_row5400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5400, hB2]
      convert table_10_row5400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5400, hB3]
      convert table_10_row5400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5400, hB4]
      convert table_10_row5400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5400, hB5]
      convert table_10_row5400_k5_margin using 1 <;> norm_num
  rcases h with h5500 | h
  · simp only [Prod.mk.injEq] at h5500
    rcases h5500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5500, hB1]
      convert table_10_row5500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5500, hB2]
      convert table_10_row5500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5500, hB3]
      convert table_10_row5500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5500, hB4]
      convert table_10_row5500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5500, hB5]
      convert table_10_row5500_k5_margin using 1 <;> norm_num
  rcases h with h5600 | h
  · simp only [Prod.mk.injEq] at h5600
    rcases h5600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5600, hB1]
      convert table_10_row5600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5600, hB2]
      convert table_10_row5600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5600, hB3]
      convert table_10_row5600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5600, hB4]
      convert table_10_row5600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5600, hB5]
      convert table_10_row5600_k5_margin using 1 <;> norm_num
  rcases h with h5700 | h
  · simp only [Prod.mk.injEq] at h5700
    rcases h5700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5700, hB1]
      convert table_10_row5700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5700, hB2]
      convert table_10_row5700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5700, hB3]
      convert table_10_row5700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5700, hB4]
      convert table_10_row5700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5700, hB5]
      convert table_10_row5700_k5_margin using 1 <;> norm_num
  rcases h with h5800 | h
  · simp only [Prod.mk.injEq] at h5800
    rcases h5800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5800, hB1]
      convert table_10_row5800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5800, hB2]
      convert table_10_row5800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5800, hB3]
      convert table_10_row5800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5800, hB4]
      convert table_10_row5800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5800, hB5]
      convert table_10_row5800_k5_margin using 1 <;> norm_num
  rcases h with h5900 | h
  · simp only [Prod.mk.injEq] at h5900
    rcases h5900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_5900, hB1]
      convert table_10_row5900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5900, hB2]
      convert table_10_row5900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5900, hB3]
      convert table_10_row5900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5900, hB4]
      convert table_10_row5900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_5900, hB5]
      convert table_10_row5900_k5_margin using 1 <;> norm_num
  rcases h with h6000 | h
  · simp only [Prod.mk.injEq] at h6000
    rcases h6000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6000, hB1]
      convert table_10_row6000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6000, hB2]
      convert table_10_row6000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6000, hB3]
      convert table_10_row6000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6000, hB4]
      convert table_10_row6000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6000, hB5]
      convert table_10_row6000_k5_margin using 1 <;> norm_num
  rcases h with h6100 | h
  · simp only [Prod.mk.injEq] at h6100
    rcases h6100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6100, hB1]
      convert table_10_row6100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6100, hB2]
      convert table_10_row6100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6100, hB3]
      convert table_10_row6100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6100, hB4]
      convert table_10_row6100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6100, hB5]
      convert table_10_row6100_k5_margin using 1 <;> norm_num
  rcases h with h6200 | h
  · simp only [Prod.mk.injEq] at h6200
    rcases h6200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6200, hB1]
      convert table_10_row6200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6200, hB2]
      convert table_10_row6200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6200, hB3]
      convert table_10_row6200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6200, hB4]
      convert table_10_row6200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6200, hB5]
      convert table_10_row6200_k5_margin using 1 <;> norm_num
  rcases h with h6300 | h
  · simp only [Prod.mk.injEq] at h6300
    rcases h6300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6300, hB1]
      convert table_10_row6300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6300, hB2]
      convert table_10_row6300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6300, hB3]
      convert table_10_row6300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6300, hB4]
      convert table_10_row6300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6300, hB5]
      convert table_10_row6300_k5_margin using 1 <;> norm_num
  rcases h with h6400 | h
  · simp only [Prod.mk.injEq] at h6400
    rcases h6400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6400, hB1]
      convert table_10_row6400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6400, hB2]
      convert table_10_row6400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6400, hB3]
      convert table_10_row6400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6400, hB4]
      convert table_10_row6400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6400, hB5]
      convert table_10_row6400_k5_margin using 1 <;> norm_num
  rcases h with h6500 | h
  · simp only [Prod.mk.injEq] at h6500
    rcases h6500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6500, hB1]
      convert table_10_row6500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6500, hB2]
      convert table_10_row6500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6500, hB3]
      convert table_10_row6500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6500, hB4]
      convert table_10_row6500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6500, hB5]
      convert table_10_row6500_k5_margin using 1 <;> norm_num
  rcases h with h6600 | h
  · simp only [Prod.mk.injEq] at h6600
    rcases h6600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6600, hB1]
      convert table_10_row6600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6600, hB2]
      convert table_10_row6600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6600, hB3]
      convert table_10_row6600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6600, hB4]
      convert table_10_row6600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6600, hB5]
      convert table_10_row6600_k5_margin using 1 <;> norm_num
  rcases h with h6700 | h
  · simp only [Prod.mk.injEq] at h6700
    rcases h6700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6700, hB1]
      convert table_10_row6700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6700, hB2]
      convert table_10_row6700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6700, hB3]
      convert table_10_row6700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6700, hB4]
      convert table_10_row6700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6700, hB5]
      convert table_10_row6700_k5_margin using 1 <;> norm_num
  rcases h with h6800 | h
  · simp only [Prod.mk.injEq] at h6800
    rcases h6800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6800, hB1]
      convert table_10_row6800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6800, hB2]
      convert table_10_row6800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6800, hB3]
      convert table_10_row6800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6800, hB4]
      convert table_10_row6800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6800, hB5]
      convert table_10_row6800_k5_margin using 1 <;> norm_num
  rcases h with h6900 | h
  · simp only [Prod.mk.injEq] at h6900
    rcases h6900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_6900, hB1]
      convert table_10_row6900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6900, hB2]
      convert table_10_row6900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6900, hB3]
      convert table_10_row6900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6900, hB4]
      convert table_10_row6900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_6900, hB5]
      convert table_10_row6900_k5_margin using 1 <;> norm_num
  rcases h with h7000 | h
  · simp only [Prod.mk.injEq] at h7000
    rcases h7000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7000, hB1]
      convert table_10_row7000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7000, hB2]
      convert table_10_row7000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7000, hB3]
      convert table_10_row7000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7000, hB4]
      convert table_10_row7000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7000, hB5]
      convert table_10_row7000_k5_margin using 1 <;> norm_num
  rcases h with h7100 | h
  · simp only [Prod.mk.injEq] at h7100
    rcases h7100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7100, hB1]
      convert table_10_row7100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7100, hB2]
      convert table_10_row7100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7100, hB3]
      convert table_10_row7100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7100, hB4]
      convert table_10_row7100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7100, hB5]
      convert table_10_row7100_k5_margin using 1 <;> norm_num
  rcases h with h7200 | h
  · simp only [Prod.mk.injEq] at h7200
    rcases h7200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7200, hB1]
      convert table_10_row7200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7200, hB2]
      convert table_10_row7200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7200, hB3]
      convert table_10_row7200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7200, hB4]
      convert table_10_row7200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7200, hB5]
      convert table_10_row7200_k5_margin using 1 <;> norm_num
  rcases h with h7300 | h
  · simp only [Prod.mk.injEq] at h7300
    rcases h7300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7300, hB1]
      convert table_10_row7300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7300, hB2]
      convert table_10_row7300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7300, hB3]
      convert table_10_row7300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7300, hB4]
      convert table_10_row7300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7300, hB5]
      convert table_10_row7300_k5_margin using 1 <;> norm_num
  rcases h with h7400 | h
  · simp only [Prod.mk.injEq] at h7400
    rcases h7400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7400, hB1]
      convert table_10_row7400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7400, hB2]
      convert table_10_row7400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7400, hB3]
      convert table_10_row7400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7400, hB4]
      convert table_10_row7400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7400, hB5]
      convert table_10_row7400_k5_margin using 1 <;> norm_num
  rcases h with h7500 | h
  · simp only [Prod.mk.injEq] at h7500
    rcases h7500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7500, hB1]
      convert table_10_row7500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7500, hB2]
      convert table_10_row7500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7500, hB3]
      convert table_10_row7500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7500, hB4]
      convert table_10_row7500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7500, hB5]
      convert table_10_row7500_k5_margin using 1 <;> norm_num
  rcases h with h7600 | h
  · simp only [Prod.mk.injEq] at h7600
    rcases h7600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7600, hB1]
      convert table_10_row7600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7600, hB2]
      convert table_10_row7600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7600, hB3]
      convert table_10_row7600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7600, hB4]
      convert table_10_row7600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7600, hB5]
      convert table_10_row7600_k5_margin using 1 <;> norm_num
  rcases h with h7700 | h
  · simp only [Prod.mk.injEq] at h7700
    rcases h7700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7700, hB1]
      convert table_10_row7700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7700, hB2]
      convert table_10_row7700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7700, hB3]
      convert table_10_row7700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7700, hB4]
      convert table_10_row7700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7700, hB5]
      convert table_10_row7700_k5_margin using 1 <;> norm_num
  rcases h with h7800 | h
  · simp only [Prod.mk.injEq] at h7800
    rcases h7800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7800, hB1]
      convert table_10_row7800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7800, hB2]
      convert table_10_row7800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7800, hB3]
      convert table_10_row7800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7800, hB4]
      convert table_10_row7800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7800, hB5]
      convert table_10_row7800_k5_margin using 1 <;> norm_num
  rcases h with h7900 | h
  · simp only [Prod.mk.injEq] at h7900
    rcases h7900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_7900, hB1]
      convert table_10_row7900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7900, hB2]
      convert table_10_row7900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7900, hB3]
      convert table_10_row7900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7900, hB4]
      convert table_10_row7900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_7900, hB5]
      convert table_10_row7900_k5_margin using 1 <;> norm_num
  rcases h with h8000 | h
  · simp only [Prod.mk.injEq] at h8000
    rcases h8000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8000, hB1]
      convert table_10_row8000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8000, hB2]
      convert table_10_row8000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8000, hB3]
      convert table_10_row8000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8000, hB4]
      convert table_10_row8000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8000, hB5]
      convert table_10_row8000_k5_margin using 1 <;> norm_num
  rcases h with h8100 | h
  · simp only [Prod.mk.injEq] at h8100
    rcases h8100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8100, hB1]
      convert table_10_row8100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8100, hB2]
      convert table_10_row8100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8100, hB3]
      convert table_10_row8100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8100, hB4]
      convert table_10_row8100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8100, hB5]
      convert table_10_row8100_k5_margin using 1 <;> norm_num
  rcases h with h8200 | h
  · simp only [Prod.mk.injEq] at h8200
    rcases h8200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8200, hB1]
      convert table_10_row8200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8200, hB2]
      convert table_10_row8200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8200, hB3]
      convert table_10_row8200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8200, hB4]
      convert table_10_row8200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8200, hB5]
      convert table_10_row8200_k5_margin using 1 <;> norm_num
  rcases h with h8300 | h
  · simp only [Prod.mk.injEq] at h8300
    rcases h8300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8300, hB1]
      convert table_10_row8300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8300, hB2]
      convert table_10_row8300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8300, hB3]
      convert table_10_row8300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8300, hB4]
      convert table_10_row8300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8300, hB5]
      convert table_10_row8300_k5_margin using 1 <;> norm_num
  rcases h with h8400 | h
  · simp only [Prod.mk.injEq] at h8400
    rcases h8400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8400, hB1]
      convert table_10_row8400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8400, hB2]
      convert table_10_row8400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8400, hB3]
      convert table_10_row8400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8400, hB4]
      convert table_10_row8400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8400, hB5]
      convert table_10_row8400_k5_margin using 1 <;> norm_num
  rcases h with h8500 | h
  · simp only [Prod.mk.injEq] at h8500
    rcases h8500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8500, hB1]
      convert table_10_row8500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8500, hB2]
      convert table_10_row8500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8500, hB3]
      convert table_10_row8500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8500, hB4]
      convert table_10_row8500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8500, hB5]
      convert table_10_row8500_k5_margin using 1 <;> norm_num
  rcases h with h8600 | h
  · simp only [Prod.mk.injEq] at h8600
    rcases h8600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8600, hB1]
      convert table_10_row8600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8600, hB2]
      convert table_10_row8600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8600, hB3]
      convert table_10_row8600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8600, hB4]
      convert table_10_row8600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8600, hB5]
      convert table_10_row8600_k5_margin using 1 <;> norm_num
  rcases h with h8700 | h
  · simp only [Prod.mk.injEq] at h8700
    rcases h8700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8700, hB1]
      convert table_10_row8700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8700, hB2]
      convert table_10_row8700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8700, hB3]
      convert table_10_row8700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8700, hB4]
      convert table_10_row8700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8700, hB5]
      convert table_10_row8700_k5_margin using 1 <;> norm_num
  rcases h with h8800 | h
  · simp only [Prod.mk.injEq] at h8800
    rcases h8800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8800, hB1]
      convert table_10_row8800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8800, hB2]
      convert table_10_row8800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8800, hB3]
      convert table_10_row8800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8800, hB4]
      convert table_10_row8800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8800, hB5]
      convert table_10_row8800_k5_margin using 1 <;> norm_num
  rcases h with h8900 | h
  · simp only [Prod.mk.injEq] at h8900
    rcases h8900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_8900, hB1]
      convert table_10_row8900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8900, hB2]
      convert table_10_row8900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8900, hB3]
      convert table_10_row8900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8900, hB4]
      convert table_10_row8900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_8900, hB5]
      convert table_10_row8900_k5_margin using 1 <;> norm_num
  rcases h with h9000 | h
  · simp only [Prod.mk.injEq] at h9000
    rcases h9000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9000, hB1]
      convert table_10_row9000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9000, hB2]
      convert table_10_row9000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9000, hB3]
      convert table_10_row9000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9000, hB4]
      convert table_10_row9000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9000, hB5]
      convert table_10_row9000_k5_margin using 1 <;> norm_num
  rcases h with h9100 | h
  · simp only [Prod.mk.injEq] at h9100
    rcases h9100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9100, hB1]
      convert table_10_row9100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9100, hB2]
      convert table_10_row9100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9100, hB3]
      convert table_10_row9100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9100, hB4]
      convert table_10_row9100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9100, hB5]
      convert table_10_row9100_k5_margin using 1 <;> norm_num
  rcases h with h9200 | h
  · simp only [Prod.mk.injEq] at h9200
    rcases h9200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9200, hB1]
      convert table_10_row9200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9200, hB2]
      convert table_10_row9200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9200, hB3]
      convert table_10_row9200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9200, hB4]
      convert table_10_row9200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9200, hB5]
      convert table_10_row9200_k5_margin using 1 <;> norm_num
  rcases h with h9300 | h
  · simp only [Prod.mk.injEq] at h9300
    rcases h9300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9300, hB1]
      convert table_10_row9300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9300, hB2]
      convert table_10_row9300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9300, hB3]
      convert table_10_row9300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9300, hB4]
      convert table_10_row9300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9300, hB5]
      convert table_10_row9300_k5_margin using 1 <;> norm_num
  rcases h with h9400 | h
  · simp only [Prod.mk.injEq] at h9400
    rcases h9400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9400, hB1]
      convert table_10_row9400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9400, hB2]
      convert table_10_row9400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9400, hB3]
      convert table_10_row9400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9400, hB4]
      convert table_10_row9400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9400, hB5]
      convert table_10_row9400_k5_margin using 1 <;> norm_num
  rcases h with h9500 | h
  · simp only [Prod.mk.injEq] at h9500
    rcases h9500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9500, hB1]
      convert table_10_row9500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9500, hB2]
      convert table_10_row9500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9500, hB3]
      convert table_10_row9500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9500, hB4]
      convert table_10_row9500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9500, hB5]
      convert table_10_row9500_k5_margin using 1 <;> norm_num
  rcases h with h9600 | h
  · simp only [Prod.mk.injEq] at h9600
    rcases h9600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9600, hB1]
      convert table_10_row9600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9600, hB2]
      convert table_10_row9600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9600, hB3]
      convert table_10_row9600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9600, hB4]
      convert table_10_row9600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9600, hB5]
      convert table_10_row9600_k5_margin using 1 <;> norm_num
  rcases h with h9700 | h
  · simp only [Prod.mk.injEq] at h9700
    rcases h9700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9700, hB1]
      convert table_10_row9700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9700, hB2]
      convert table_10_row9700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9700, hB3]
      convert table_10_row9700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9700, hB4]
      convert table_10_row9700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9700, hB5]
      convert table_10_row9700_k5_margin using 1 <;> norm_num
  rcases h with h9800 | h
  · simp only [Prod.mk.injEq] at h9800
    rcases h9800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9800, hB1]
      convert table_10_row9800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9800, hB2]
      convert table_10_row9800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9800, hB3]
      convert table_10_row9800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9800, hB4]
      convert table_10_row9800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9800, hB5]
      convert table_10_row9800_k5_margin using 1 <;> norm_num
  rcases h with h9900 | h
  · simp only [Prod.mk.injEq] at h9900
    rcases h9900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_9900, hB1]
      convert table_10_row9900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9900, hB2]
      convert table_10_row9900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9900, hB3]
      convert table_10_row9900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9900, hB4]
      convert table_10_row9900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_9900, hB5]
      convert table_10_row9900_k5_margin using 1 <;> norm_num
  rcases h with h10000 | h
  · simp only [Prod.mk.injEq] at h10000
    rcases h10000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10000, hB1]
      convert table_10_row10000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10000, hB2]
      convert table_10_row10000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10000, hB3]
      convert table_10_row10000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10000, hB4]
      convert table_10_row10000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10000, hB5]
      convert table_10_row10000_k5_margin using 1 <;> norm_num
  rcases h with h10100 | h
  · simp only [Prod.mk.injEq] at h10100
    rcases h10100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10100, hB1]
      convert table_10_row10100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10100, hB2]
      convert table_10_row10100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10100, hB3]
      convert table_10_row10100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10100, hB4]
      convert table_10_row10100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10100, hB5]
      convert table_10_row10100_k5_margin using 1 <;> norm_num
  rcases h with h10200 | h
  · simp only [Prod.mk.injEq] at h10200
    rcases h10200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10200, hB1]
      convert table_10_row10200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10200, hB2]
      convert table_10_row10200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10200, hB3]
      convert table_10_row10200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10200, hB4]
      convert table_10_row10200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10200, hB5]
      convert table_10_row10200_k5_margin using 1 <;> norm_num
  rcases h with h10300 | h
  · simp only [Prod.mk.injEq] at h10300
    rcases h10300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10300, hB1]
      convert table_10_row10300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10300, hB2]
      convert table_10_row10300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10300, hB3]
      convert table_10_row10300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10300, hB4]
      convert table_10_row10300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10300, hB5]
      convert table_10_row10300_k5_margin using 1 <;> norm_num
  rcases h with h10400 | h
  · simp only [Prod.mk.injEq] at h10400
    rcases h10400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10400, hB1]
      convert table_10_row10400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10400, hB2]
      convert table_10_row10400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10400, hB3]
      convert table_10_row10400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10400, hB4]
      convert table_10_row10400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10400, hB5]
      convert table_10_row10400_k5_margin using 1 <;> norm_num
  rcases h with h10500 | h
  · simp only [Prod.mk.injEq] at h10500
    rcases h10500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10500, hB1]
      convert table_10_row10500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10500, hB2]
      convert table_10_row10500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10500, hB3]
      convert table_10_row10500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10500, hB4]
      convert table_10_row10500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10500, hB5]
      convert table_10_row10500_k5_margin using 1 <;> norm_num
  rcases h with h10600 | h
  · simp only [Prod.mk.injEq] at h10600
    rcases h10600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10600, hB1]
      convert table_10_row10600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10600, hB2]
      convert table_10_row10600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10600, hB3]
      convert table_10_row10600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10600, hB4]
      convert table_10_row10600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10600, hB5]
      convert table_10_row10600_k5_margin using 1 <;> norm_num
  rcases h with h10700 | h
  · simp only [Prod.mk.injEq] at h10700
    rcases h10700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10700, hB1]
      convert table_10_row10700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10700, hB2]
      convert table_10_row10700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10700, hB3]
      convert table_10_row10700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10700, hB4]
      convert table_10_row10700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10700, hB5]
      convert table_10_row10700_k5_margin using 1 <;> norm_num
  rcases h with h10800 | h
  · simp only [Prod.mk.injEq] at h10800
    rcases h10800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10800, hB1]
      convert table_10_row10800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10800, hB2]
      convert table_10_row10800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10800, hB3]
      convert table_10_row10800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10800, hB4]
      convert table_10_row10800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10800, hB5]
      convert table_10_row10800_k5_margin using 1 <;> norm_num
  rcases h with h10900 | h
  · simp only [Prod.mk.injEq] at h10900
    rcases h10900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_10900, hB1]
      convert table_10_row10900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10900, hB2]
      convert table_10_row10900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10900, hB3]
      convert table_10_row10900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10900, hB4]
      convert table_10_row10900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_10900, hB5]
      convert table_10_row10900_k5_margin using 1 <;> norm_num
  rcases h with h11000 | h
  · simp only [Prod.mk.injEq] at h11000
    rcases h11000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11000, hB1]
      convert table_10_row11000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11000, hB2]
      convert table_10_row11000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11000, hB3]
      convert table_10_row11000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11000, hB4]
      convert table_10_row11000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11000, hB5]
      convert table_10_row11000_k5_margin using 1 <;> norm_num
  rcases h with h11100 | h
  · simp only [Prod.mk.injEq] at h11100
    rcases h11100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11100, hB1]
      convert table_10_row11100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11100, hB2]
      convert table_10_row11100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11100, hB3]
      convert table_10_row11100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11100, hB4]
      convert table_10_row11100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11100, hB5]
      convert table_10_row11100_k5_margin using 1 <;> norm_num
  rcases h with h11200 | h
  · simp only [Prod.mk.injEq] at h11200
    rcases h11200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11200, hB1]
      convert table_10_row11200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11200, hB2]
      convert table_10_row11200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11200, hB3]
      convert table_10_row11200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11200, hB4]
      convert table_10_row11200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11200, hB5]
      convert table_10_row11200_k5_margin using 1 <;> norm_num
  rcases h with h11300 | h
  · simp only [Prod.mk.injEq] at h11300
    rcases h11300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11300, hB1]
      convert table_10_row11300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11300, hB2]
      convert table_10_row11300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11300, hB3]
      convert table_10_row11300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11300, hB4]
      convert table_10_row11300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11300, hB5]
      convert table_10_row11300_k5_margin using 1 <;> norm_num
  rcases h with h11400 | h
  · simp only [Prod.mk.injEq] at h11400
    rcases h11400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11400, hB1]
      convert table_10_row11400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11400, hB2]
      convert table_10_row11400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11400, hB3]
      convert table_10_row11400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11400, hB4]
      convert table_10_row11400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11400, hB5]
      convert table_10_row11400_k5_margin using 1 <;> norm_num
  rcases h with h11500 | h
  · simp only [Prod.mk.injEq] at h11500
    rcases h11500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11500, hB1]
      convert table_10_row11500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11500, hB2]
      convert table_10_row11500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11500, hB3]
      convert table_10_row11500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11500, hB4]
      convert table_10_row11500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11500, hB5]
      convert table_10_row11500_k5_margin using 1 <;> norm_num
  rcases h with h11600 | h
  · simp only [Prod.mk.injEq] at h11600
    rcases h11600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11600, hB1]
      convert table_10_row11600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11600, hB2]
      convert table_10_row11600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11600, hB3]
      convert table_10_row11600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11600, hB4]
      convert table_10_row11600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11600, hB5]
      convert table_10_row11600_k5_margin using 1 <;> norm_num
  rcases h with h11700 | h
  · simp only [Prod.mk.injEq] at h11700
    rcases h11700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11700, hB1]
      convert table_10_row11700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11700, hB2]
      convert table_10_row11700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11700, hB3]
      convert table_10_row11700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11700, hB4]
      convert table_10_row11700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11700, hB5]
      convert table_10_row11700_k5_margin using 1 <;> norm_num
  rcases h with h11800 | h
  · simp only [Prod.mk.injEq] at h11800
    rcases h11800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11800, hB1]
      convert table_10_row11800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11800, hB2]
      convert table_10_row11800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11800, hB3]
      convert table_10_row11800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11800, hB4]
      convert table_10_row11800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11800, hB5]
      convert table_10_row11800_k5_margin using 1 <;> norm_num
  rcases h with h11900 | h
  · simp only [Prod.mk.injEq] at h11900
    rcases h11900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_11900, hB1]
      convert table_10_row11900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11900, hB2]
      convert table_10_row11900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11900, hB3]
      convert table_10_row11900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11900, hB4]
      convert table_10_row11900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_11900, hB5]
      convert table_10_row11900_k5_margin using 1 <;> norm_num
  rcases h with h12000 | h
  · simp only [Prod.mk.injEq] at h12000
    rcases h12000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12000, hB1]
      convert table_10_row12000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12000, hB2]
      convert table_10_row12000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12000, hB3]
      convert table_10_row12000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12000, hB4]
      convert table_10_row12000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12000, hB5]
      convert table_10_row12000_k5_margin using 1 <;> norm_num
  rcases h with h12100 | h
  · simp only [Prod.mk.injEq] at h12100
    rcases h12100 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12100, hB1]
      convert table_10_row12100_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12100, hB2]
      convert table_10_row12100_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12100, hB3]
      convert table_10_row12100_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12100, hB4]
      convert table_10_row12100_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12100, hB5]
      convert table_10_row12100_k5_margin using 1 <;> norm_num
  rcases h with h12200 | h
  · simp only [Prod.mk.injEq] at h12200
    rcases h12200 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12200, hB1]
      convert table_10_row12200_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12200, hB2]
      convert table_10_row12200_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12200, hB3]
      convert table_10_row12200_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12200, hB4]
      convert table_10_row12200_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12200, hB5]
      convert table_10_row12200_k5_margin using 1 <;> norm_num
  rcases h with h12300 | h
  · simp only [Prod.mk.injEq] at h12300
    rcases h12300 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12300, hB1]
      convert table_10_row12300_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12300, hB2]
      convert table_10_row12300_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12300, hB3]
      convert table_10_row12300_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12300, hB4]
      convert table_10_row12300_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12300, hB5]
      convert table_10_row12300_k5_margin using 1 <;> norm_num
  rcases h with h12400 | h
  · simp only [Prod.mk.injEq] at h12400
    rcases h12400 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12400, hB1]
      convert table_10_row12400_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12400, hB2]
      convert table_10_row12400_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12400, hB3]
      convert table_10_row12400_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12400, hB4]
      convert table_10_row12400_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12400, hB5]
      convert table_10_row12400_k5_margin using 1 <;> norm_num
  rcases h with h12500 | h
  · simp only [Prod.mk.injEq] at h12500
    rcases h12500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12500, hB1]
      convert table_10_row12500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12500, hB2]
      convert table_10_row12500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12500, hB3]
      convert table_10_row12500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12500, hB4]
      convert table_10_row12500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12500, hB5]
      convert table_10_row12500_k5_margin using 1 <;> norm_num
  rcases h with h12600 | h
  · simp only [Prod.mk.injEq] at h12600
    rcases h12600 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12600, hB1]
      convert table_10_row12600_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12600, hB2]
      convert table_10_row12600_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12600, hB3]
      convert table_10_row12600_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12600, hB4]
      convert table_10_row12600_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12600, hB5]
      convert table_10_row12600_k5_margin using 1 <;> norm_num
  rcases h with h12700 | h
  · simp only [Prod.mk.injEq] at h12700
    rcases h12700 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12700, hB1]
      convert table_10_row12700_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12700, hB2]
      convert table_10_row12700_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12700, hB3]
      convert table_10_row12700_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12700, hB4]
      convert table_10_row12700_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12700, hB5]
      convert table_10_row12700_k5_margin using 1 <;> norm_num
  rcases h with h12800 | h
  · simp only [Prod.mk.injEq] at h12800
    rcases h12800 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12800, hB1]
      convert table_10_row12800_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12800, hB2]
      convert table_10_row12800_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12800, hB3]
      convert table_10_row12800_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12800, hB4]
      convert table_10_row12800_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12800, hB5]
      convert table_10_row12800_k5_margin using 1 <;> norm_num
  rcases h with h12900 | h
  · simp only [Prod.mk.injEq] at h12900
    rcases h12900 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_12900, hB1]
      convert table_10_row12900_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12900, hB2]
      convert table_10_row12900_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12900, hB3]
      convert table_10_row12900_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12900, hB4]
      convert table_10_row12900_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_12900, hB5]
      convert table_10_row12900_k5_margin using 1 <;> norm_num
  rcases h with h13000 | h
  · simp only [Prod.mk.injEq] at h13000
    rcases h13000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_13000, hB1]
      convert table_10_row13000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13000, hB2]
      convert table_10_row13000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13000, hB3]
      convert table_10_row13000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13000, hB4]
      convert table_10_row13000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13000, hB5]
      convert table_10_row13000_k5_margin using 1 <;> norm_num
  rcases h with h13500 | h
  · simp only [Prod.mk.injEq] at h13500
    rcases h13500 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_13500, hB1]
      convert table_10_row13500_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13500, hB2]
      convert table_10_row13500_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13500, hB3]
      convert table_10_row13500_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13500, hB4]
      convert table_10_row13500_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13500, hB5]
      convert table_10_row13500_k5_margin using 1 <;> norm_num
  rcases h with h13800_7464 | h
  · simp only [Prod.mk.injEq] at h13800_7464
    rcases h13800_7464 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_13800_7464, hB1]
      convert table_10_row13800_7464_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13800_7464, hB2]
      convert table_10_row13800_7464_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13800_7464, hB3]
      convert table_10_row13800_7464_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13800_7464, hB4]
      convert table_10_row13800_7464_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_13800_7464, hB5]
      convert table_10_row13800_7464_k5_margin using 1 <;> norm_num
  rcases h with h14000 | h
  · simp only [Prod.mk.injEq] at h14000
    rcases h14000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_14000, hB1]
      convert table_10_row14000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_14000, hB2]
      convert table_10_row14000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_14000, hB3]
      convert table_10_row14000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_14000, hB4]
      convert table_10_row14000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_14000, hB5]
      convert table_10_row14000_k5_margin using 1 <;> norm_num
  rcases h with h15000 | h
  · simp only [Prod.mk.injEq] at h15000
    rcases h15000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_15000, hB1]
      convert table_10_row15000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_15000, hB2]
      convert table_10_row15000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_15000, hB3]
      convert table_10_row15000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_15000, hB4]
      convert table_10_row15000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_15000, hB5]
      convert table_10_row15000_k5_margin using 1 <;> norm_num
  rcases h with h16000 | h
  · simp only [Prod.mk.injEq] at h16000
    rcases h16000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_16000, hB1]
      convert table_10_row16000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_16000, hB2]
      convert table_10_row16000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_16000, hB3]
      convert table_10_row16000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_16000, hB4]
      convert table_10_row16000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_16000, hB5]
      convert table_10_row16000_k5_margin using 1 <;> norm_num
  rcases h with h17000 | h
  · simp only [Prod.mk.injEq] at h17000
    rcases h17000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_17000, hB1]
      convert table_10_row17000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_17000, hB2]
      convert table_10_row17000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_17000, hB3]
      convert table_10_row17000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_17000, hB4]
      convert table_10_row17000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_17000, hB5]
      convert table_10_row17000_k5_margin using 1 <;> norm_num
  rcases h with h18000 | h
  · simp only [Prod.mk.injEq] at h18000
    rcases h18000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_18000, hB1]
      convert table_10_row18000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_18000, hB2]
      convert table_10_row18000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_18000, hB3]
      convert table_10_row18000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_18000, hB4]
      convert table_10_row18000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_18000, hB5]
      convert table_10_row18000_k5_margin using 1 <;> norm_num
  rcases h with h19000 | h
  · simp only [Prod.mk.injEq] at h19000
    rcases h19000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_19000, hB1]
      convert table_10_row19000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19000, hB2]
      convert table_10_row19000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19000, hB3]
      convert table_10_row19000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19000, hB4]
      convert table_10_row19000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_19000, hB5]
      convert table_10_row19000_k5_margin using 1 <;> norm_num
  rcases h with h20000 | h
  · simp only [Prod.mk.injEq] at h20000
    rcases h20000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_20000, hB1]
      convert table_10_row20000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20000, hB2]
      convert table_10_row20000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20000, hB3]
      convert table_10_row20000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20000, hB4]
      convert table_10_row20000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_20000, hB5]
      convert table_10_row20000_k5_margin using 1 <;> norm_num
  rcases h with h21000 | h
  · simp only [Prod.mk.injEq] at h21000
    rcases h21000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_21000, hB1]
      convert table_10_row21000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21000, hB2]
      convert table_10_row21000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21000, hB3]
      convert table_10_row21000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21000, hB4]
      convert table_10_row21000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_21000, hB5]
      convert table_10_row21000_k5_margin using 1 <;> norm_num
  rcases h with h22000 | h
  · simp only [Prod.mk.injEq] at h22000
    rcases h22000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_22000, hB1]
      convert table_10_row22000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22000, hB2]
      convert table_10_row22000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22000, hB3]
      convert table_10_row22000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22000, hB4]
      convert table_10_row22000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_22000, hB5]
      convert table_10_row22000_k5_margin using 1 <;> norm_num
  rcases h with h23000 | h
  · simp only [Prod.mk.injEq] at h23000
    rcases h23000 with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
    subst b
    interval_cases k
    · rw [table_10_next_cert_23000, hB1]
      convert table_10_row23000_k1_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23000, hB2]
      convert table_10_row23000_k2_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23000, hB3]
      convert table_10_row23000_k3_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23000, hB4]
      convert table_10_row23000_k4_margin using 1 <;> norm_num
    · rw [table_10_next_cert_23000, hB5]
      convert table_10_row23000_k5_margin using 1 <;> norm_num
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨hb, hB1, hB2, hB3, hB4, hB5⟩
  subst b
  interval_cases k
  · rw [table_10_next_cert_24000, hB1]
    convert table_10_row24000_k1_margin using 1 <;> norm_num
  · rw [table_10_next_cert_24000, hB2]
    convert table_10_row24000_k2_margin using 1 <;> norm_num
  · rw [table_10_next_cert_24000, hB3]
    convert table_10_row24000_k3_margin using 1 <;> norm_num
  · rw [table_10_next_cert_24000, hB4]
    convert table_10_row24000_k4_margin using 1 <;> norm_num
  · rw [table_10_next_cert_24000, hB5]
    convert table_10_row24000_k5_margin using 1 <;> norm_num

end BKLNW
