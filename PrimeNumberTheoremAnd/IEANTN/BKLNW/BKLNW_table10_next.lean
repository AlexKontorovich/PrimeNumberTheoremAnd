import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Table 10 next-value certificates from the checked b-column. -/

namespace BKLNW

open Real

theorem table_10_next_cert_20 : table_10_next (20) = (21) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 0
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨0, by rw [table_10_bcol_length]; norm_num⟩ = (20) := rfl
  have h1 : table_10_bcol.get ⟨1, by rw [table_10_bcol_length]; norm_num⟩ = (21) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_21 : table_10_next (21) = (22) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 1
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨1, by rw [table_10_bcol_length]; norm_num⟩ = (21) := rfl
  have h1 : table_10_bcol.get ⟨2, by rw [table_10_bcol_length]; norm_num⟩ = (22) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_22 : table_10_next (22) = (23) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 2
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨2, by rw [table_10_bcol_length]; norm_num⟩ = (22) := rfl
  have h1 : table_10_bcol.get ⟨3, by rw [table_10_bcol_length]; norm_num⟩ = (23) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_23 : table_10_next (23) = (24) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 3
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨3, by rw [table_10_bcol_length]; norm_num⟩ = (23) := rfl
  have h1 : table_10_bcol.get ⟨4, by rw [table_10_bcol_length]; norm_num⟩ = (24) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_24 : table_10_next (24) = (25) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 4
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨4, by rw [table_10_bcol_length]; norm_num⟩ = (24) := rfl
  have h1 : table_10_bcol.get ⟨5, by rw [table_10_bcol_length]; norm_num⟩ = (25) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_25 : table_10_next (25) = (26) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 5
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨5, by rw [table_10_bcol_length]; norm_num⟩ = (25) := rfl
  have h1 : table_10_bcol.get ⟨6, by rw [table_10_bcol_length]; norm_num⟩ = (26) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_26 : table_10_next (26) = (27) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 6
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨6, by rw [table_10_bcol_length]; norm_num⟩ = (26) := rfl
  have h1 : table_10_bcol.get ⟨7, by rw [table_10_bcol_length]; norm_num⟩ = (27) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_27 : table_10_next (27) = (28) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 7
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨7, by rw [table_10_bcol_length]; norm_num⟩ = (27) := rfl
  have h1 : table_10_bcol.get ⟨8, by rw [table_10_bcol_length]; norm_num⟩ = (28) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_28 : table_10_next (28) = (29) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 8
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨8, by rw [table_10_bcol_length]; norm_num⟩ = (28) := rfl
  have h1 : table_10_bcol.get ⟨9, by rw [table_10_bcol_length]; norm_num⟩ = (29) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_29 : table_10_next (29) = (30) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 9
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨9, by rw [table_10_bcol_length]; norm_num⟩ = (29) := rfl
  have h1 : table_10_bcol.get ⟨10, by rw [table_10_bcol_length]; norm_num⟩ = (30) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_30 : table_10_next (30) = (31) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 10
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨10, by rw [table_10_bcol_length]; norm_num⟩ = (30) := rfl
  have h1 : table_10_bcol.get ⟨11, by rw [table_10_bcol_length]; norm_num⟩ = (31) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_31 : table_10_next (31) = (32) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 11
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨11, by rw [table_10_bcol_length]; norm_num⟩ = (31) := rfl
  have h1 : table_10_bcol.get ⟨12, by rw [table_10_bcol_length]; norm_num⟩ = (32) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_32 : table_10_next (32) = (33) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 12
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨12, by rw [table_10_bcol_length]; norm_num⟩ = (32) := rfl
  have h1 : table_10_bcol.get ⟨13, by rw [table_10_bcol_length]; norm_num⟩ = (33) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_33 : table_10_next (33) = (34) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 13
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨13, by rw [table_10_bcol_length]; norm_num⟩ = (33) := rfl
  have h1 : table_10_bcol.get ⟨14, by rw [table_10_bcol_length]; norm_num⟩ = (34) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_34 : table_10_next (34) = (35) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 14
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨14, by rw [table_10_bcol_length]; norm_num⟩ = (34) := rfl
  have h1 : table_10_bcol.get ⟨15, by rw [table_10_bcol_length]; norm_num⟩ = (35) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_35 : table_10_next (35) = (36) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 15
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨15, by rw [table_10_bcol_length]; norm_num⟩ = (35) := rfl
  have h1 : table_10_bcol.get ⟨16, by rw [table_10_bcol_length]; norm_num⟩ = (36) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_36 : table_10_next (36) = (37) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 16
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨16, by rw [table_10_bcol_length]; norm_num⟩ = (36) := rfl
  have h1 : table_10_bcol.get ⟨17, by rw [table_10_bcol_length]; norm_num⟩ = (37) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_37 : table_10_next (37) = (38) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 17
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨17, by rw [table_10_bcol_length]; norm_num⟩ = (37) := rfl
  have h1 : table_10_bcol.get ⟨18, by rw [table_10_bcol_length]; norm_num⟩ = (38) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_38 : table_10_next (38) = (39) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 18
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨18, by rw [table_10_bcol_length]; norm_num⟩ = (38) := rfl
  have h1 : table_10_bcol.get ⟨19, by rw [table_10_bcol_length]; norm_num⟩ = (39) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_39 : table_10_next (39) = (40) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 19
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨19, by rw [table_10_bcol_length]; norm_num⟩ = (39) := rfl
  have h1 : table_10_bcol.get ⟨20, by rw [table_10_bcol_length]; norm_num⟩ = (40) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_40 : table_10_next (40) = (41) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 20
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨20, by rw [table_10_bcol_length]; norm_num⟩ = (40) := rfl
  have h1 : table_10_bcol.get ⟨21, by rw [table_10_bcol_length]; norm_num⟩ = (41) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_41 : table_10_next (41) = (42) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 21
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨21, by rw [table_10_bcol_length]; norm_num⟩ = (41) := rfl
  have h1 : table_10_bcol.get ⟨22, by rw [table_10_bcol_length]; norm_num⟩ = (42) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_42 : table_10_next (42) = (43) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 22
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨22, by rw [table_10_bcol_length]; norm_num⟩ = (42) := rfl
  have h1 : table_10_bcol.get ⟨23, by rw [table_10_bcol_length]; norm_num⟩ = (43) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_43 : table_10_next (43) = (19 * log 10) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 23
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨23, by rw [table_10_bcol_length]; norm_num⟩ = (43) := rfl
  have h1 : table_10_bcol.get ⟨24, by rw [table_10_bcol_length]; norm_num⟩ = (19 * log 10) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_19log10 : table_10_next (19 * log 10) = (44) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 24
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨24, by rw [table_10_bcol_length]; norm_num⟩ = (19 * log 10) := rfl
  have h1 : table_10_bcol.get ⟨25, by rw [table_10_bcol_length]; norm_num⟩ = (44) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_44 : table_10_next (44) = (45) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 25
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨25, by rw [table_10_bcol_length]; norm_num⟩ = (44) := rfl
  have h1 : table_10_bcol.get ⟨26, by rw [table_10_bcol_length]; norm_num⟩ = (45) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_45 : table_10_next (45) = (46) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 26
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨26, by rw [table_10_bcol_length]; norm_num⟩ = (45) := rfl
  have h1 : table_10_bcol.get ⟨27, by rw [table_10_bcol_length]; norm_num⟩ = (46) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_46 : table_10_next (46) = (47) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 27
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨27, by rw [table_10_bcol_length]; norm_num⟩ = (46) := rfl
  have h1 : table_10_bcol.get ⟨28, by rw [table_10_bcol_length]; norm_num⟩ = (47) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_47 : table_10_next (47) = (48) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 28
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨28, by rw [table_10_bcol_length]; norm_num⟩ = (47) := rfl
  have h1 : table_10_bcol.get ⟨29, by rw [table_10_bcol_length]; norm_num⟩ = (48) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_48 : table_10_next (48) = (49) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 29
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨29, by rw [table_10_bcol_length]; norm_num⟩ = (48) := rfl
  have h1 : table_10_bcol.get ⟨30, by rw [table_10_bcol_length]; norm_num⟩ = (49) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_49 : table_10_next (49) = (50) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 30
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨30, by rw [table_10_bcol_length]; norm_num⟩ = (49) := rfl
  have h1 : table_10_bcol.get ⟨31, by rw [table_10_bcol_length]; norm_num⟩ = (50) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_50 : table_10_next (50) = (51) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 31
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨31, by rw [table_10_bcol_length]; norm_num⟩ = (50) := rfl
  have h1 : table_10_bcol.get ⟨32, by rw [table_10_bcol_length]; norm_num⟩ = (51) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_51 : table_10_next (51) = (52) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 32
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨32, by rw [table_10_bcol_length]; norm_num⟩ = (51) := rfl
  have h1 : table_10_bcol.get ⟨33, by rw [table_10_bcol_length]; norm_num⟩ = (52) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_52 : table_10_next (52) = (53) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 33
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨33, by rw [table_10_bcol_length]; norm_num⟩ = (52) := rfl
  have h1 : table_10_bcol.get ⟨34, by rw [table_10_bcol_length]; norm_num⟩ = (53) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_53 : table_10_next (53) = (54) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 34
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨34, by rw [table_10_bcol_length]; norm_num⟩ = (53) := rfl
  have h1 : table_10_bcol.get ⟨35, by rw [table_10_bcol_length]; norm_num⟩ = (54) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_54 : table_10_next (54) = (55) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 35
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨35, by rw [table_10_bcol_length]; norm_num⟩ = (54) := rfl
  have h1 : table_10_bcol.get ⟨36, by rw [table_10_bcol_length]; norm_num⟩ = (55) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_55 : table_10_next (55) = (56) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 36
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨36, by rw [table_10_bcol_length]; norm_num⟩ = (55) := rfl
  have h1 : table_10_bcol.get ⟨37, by rw [table_10_bcol_length]; norm_num⟩ = (56) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_56 : table_10_next (56) = (57) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 37
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨37, by rw [table_10_bcol_length]; norm_num⟩ = (56) := rfl
  have h1 : table_10_bcol.get ⟨38, by rw [table_10_bcol_length]; norm_num⟩ = (57) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_57 : table_10_next (57) = (58) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 38
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨38, by rw [table_10_bcol_length]; norm_num⟩ = (57) := rfl
  have h1 : table_10_bcol.get ⟨39, by rw [table_10_bcol_length]; norm_num⟩ = (58) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_58 : table_10_next (58) = (59) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 39
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨39, by rw [table_10_bcol_length]; norm_num⟩ = (58) := rfl
  have h1 : table_10_bcol.get ⟨40, by rw [table_10_bcol_length]; norm_num⟩ = (59) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_59 : table_10_next (59) = (60) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 40
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨40, by rw [table_10_bcol_length]; norm_num⟩ = (59) := rfl
  have h1 : table_10_bcol.get ⟨41, by rw [table_10_bcol_length]; norm_num⟩ = (60) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_60 : table_10_next (60) = (65) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 41
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨41, by rw [table_10_bcol_length]; norm_num⟩ = (60) := rfl
  have h1 : table_10_bcol.get ⟨42, by rw [table_10_bcol_length]; norm_num⟩ = (65) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_65 : table_10_next (65) = (70) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 42
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨42, by rw [table_10_bcol_length]; norm_num⟩ = (65) := rfl
  have h1 : table_10_bcol.get ⟨43, by rw [table_10_bcol_length]; norm_num⟩ = (70) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_70 : table_10_next (70) = (75) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 43
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨43, by rw [table_10_bcol_length]; norm_num⟩ = (70) := rfl
  have h1 : table_10_bcol.get ⟨44, by rw [table_10_bcol_length]; norm_num⟩ = (75) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_75 : table_10_next (75) = (80) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 44
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨44, by rw [table_10_bcol_length]; norm_num⟩ = (75) := rfl
  have h1 : table_10_bcol.get ⟨45, by rw [table_10_bcol_length]; norm_num⟩ = (80) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_80 : table_10_next (80) = (85) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 45
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨45, by rw [table_10_bcol_length]; norm_num⟩ = (80) := rfl
  have h1 : table_10_bcol.get ⟨46, by rw [table_10_bcol_length]; norm_num⟩ = (85) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_85 : table_10_next (85) = (90) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 46
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨46, by rw [table_10_bcol_length]; norm_num⟩ = (85) := rfl
  have h1 : table_10_bcol.get ⟨47, by rw [table_10_bcol_length]; norm_num⟩ = (90) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_90 : table_10_next (90) = (95) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 47
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨47, by rw [table_10_bcol_length]; norm_num⟩ = (90) := rfl
  have h1 : table_10_bcol.get ⟨48, by rw [table_10_bcol_length]; norm_num⟩ = (95) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_95 : table_10_next (95) = (100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 48
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨48, by rw [table_10_bcol_length]; norm_num⟩ = (95) := rfl
  have h1 : table_10_bcol.get ⟨49, by rw [table_10_bcol_length]; norm_num⟩ = (100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_100 : table_10_next (100) = (200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 49
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨49, by rw [table_10_bcol_length]; norm_num⟩ = (100) := rfl
  have h1 : table_10_bcol.get ⟨50, by rw [table_10_bcol_length]; norm_num⟩ = (200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_200 : table_10_next (200) = (300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 50
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨50, by rw [table_10_bcol_length]; norm_num⟩ = (200) := rfl
  have h1 : table_10_bcol.get ⟨51, by rw [table_10_bcol_length]; norm_num⟩ = (300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_300 : table_10_next (300) = (400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 51
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨51, by rw [table_10_bcol_length]; norm_num⟩ = (300) := rfl
  have h1 : table_10_bcol.get ⟨52, by rw [table_10_bcol_length]; norm_num⟩ = (400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_400 : table_10_next (400) = (500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 52
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨52, by rw [table_10_bcol_length]; norm_num⟩ = (400) := rfl
  have h1 : table_10_bcol.get ⟨53, by rw [table_10_bcol_length]; norm_num⟩ = (500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_500 : table_10_next (500) = (600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 53
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨53, by rw [table_10_bcol_length]; norm_num⟩ = (500) := rfl
  have h1 : table_10_bcol.get ⟨54, by rw [table_10_bcol_length]; norm_num⟩ = (600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_600 : table_10_next (600) = (700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 54
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨54, by rw [table_10_bcol_length]; norm_num⟩ = (600) := rfl
  have h1 : table_10_bcol.get ⟨55, by rw [table_10_bcol_length]; norm_num⟩ = (700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_700 : table_10_next (700) = (800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 55
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨55, by rw [table_10_bcol_length]; norm_num⟩ = (700) := rfl
  have h1 : table_10_bcol.get ⟨56, by rw [table_10_bcol_length]; norm_num⟩ = (800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_800 : table_10_next (800) = (900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 56
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨56, by rw [table_10_bcol_length]; norm_num⟩ = (800) := rfl
  have h1 : table_10_bcol.get ⟨57, by rw [table_10_bcol_length]; norm_num⟩ = (900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_900 : table_10_next (900) = (1000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 57
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨57, by rw [table_10_bcol_length]; norm_num⟩ = (900) := rfl
  have h1 : table_10_bcol.get ⟨58, by rw [table_10_bcol_length]; norm_num⟩ = (1000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1000 : table_10_next (1000) = (1500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 58
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨58, by rw [table_10_bcol_length]; norm_num⟩ = (1000) := rfl
  have h1 : table_10_bcol.get ⟨59, by rw [table_10_bcol_length]; norm_num⟩ = (1500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1500 : table_10_next (1500) = (1600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 59
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨59, by rw [table_10_bcol_length]; norm_num⟩ = (1500) := rfl
  have h1 : table_10_bcol.get ⟨60, by rw [table_10_bcol_length]; norm_num⟩ = (1600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1600 : table_10_next (1600) = (1700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 60
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨60, by rw [table_10_bcol_length]; norm_num⟩ = (1600) := rfl
  have h1 : table_10_bcol.get ⟨61, by rw [table_10_bcol_length]; norm_num⟩ = (1700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1700 : table_10_next (1700) = (1725) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 61
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨61, by rw [table_10_bcol_length]; norm_num⟩ = (1700) := rfl
  have h1 : table_10_bcol.get ⟨62, by rw [table_10_bcol_length]; norm_num⟩ = (1725) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1725 : table_10_next (1725) = (1750) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 62
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨62, by rw [table_10_bcol_length]; norm_num⟩ = (1725) := rfl
  have h1 : table_10_bcol.get ⟨63, by rw [table_10_bcol_length]; norm_num⟩ = (1750) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1750 : table_10_next (1750) = (1775) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 63
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨63, by rw [table_10_bcol_length]; norm_num⟩ = (1750) := rfl
  have h1 : table_10_bcol.get ⟨64, by rw [table_10_bcol_length]; norm_num⟩ = (1775) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1775 : table_10_next (1775) = (1800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 64
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨64, by rw [table_10_bcol_length]; norm_num⟩ = (1775) := rfl
  have h1 : table_10_bcol.get ⟨65, by rw [table_10_bcol_length]; norm_num⟩ = (1800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1800 : table_10_next (1800) = (1825) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 65
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨65, by rw [table_10_bcol_length]; norm_num⟩ = (1800) := rfl
  have h1 : table_10_bcol.get ⟨66, by rw [table_10_bcol_length]; norm_num⟩ = (1825) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1825 : table_10_next (1825) = (1850) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 66
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨66, by rw [table_10_bcol_length]; norm_num⟩ = (1825) := rfl
  have h1 : table_10_bcol.get ⟨67, by rw [table_10_bcol_length]; norm_num⟩ = (1850) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1850 : table_10_next (1850) = (1875) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 67
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨67, by rw [table_10_bcol_length]; norm_num⟩ = (1850) := rfl
  have h1 : table_10_bcol.get ⟨68, by rw [table_10_bcol_length]; norm_num⟩ = (1875) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1875 : table_10_next (1875) = (1900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 68
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨68, by rw [table_10_bcol_length]; norm_num⟩ = (1875) := rfl
  have h1 : table_10_bcol.get ⟨69, by rw [table_10_bcol_length]; norm_num⟩ = (1900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1900 : table_10_next (1900) = (1925) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 69
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨69, by rw [table_10_bcol_length]; norm_num⟩ = (1900) := rfl
  have h1 : table_10_bcol.get ⟨70, by rw [table_10_bcol_length]; norm_num⟩ = (1925) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1925 : table_10_next (1925) = (1950) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 70
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨70, by rw [table_10_bcol_length]; norm_num⟩ = (1925) := rfl
  have h1 : table_10_bcol.get ⟨71, by rw [table_10_bcol_length]; norm_num⟩ = (1950) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1950 : table_10_next (1950) = (1975) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 71
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨71, by rw [table_10_bcol_length]; norm_num⟩ = (1950) := rfl
  have h1 : table_10_bcol.get ⟨72, by rw [table_10_bcol_length]; norm_num⟩ = (1975) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_1975 : table_10_next (1975) = (2000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 72
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨72, by rw [table_10_bcol_length]; norm_num⟩ = (1975) := rfl
  have h1 : table_10_bcol.get ⟨73, by rw [table_10_bcol_length]; norm_num⟩ = (2000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2000 : table_10_next (2000) = (2025) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 73
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨73, by rw [table_10_bcol_length]; norm_num⟩ = (2000) := rfl
  have h1 : table_10_bcol.get ⟨74, by rw [table_10_bcol_length]; norm_num⟩ = (2025) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2025 : table_10_next (2025) = (2050) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 74
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨74, by rw [table_10_bcol_length]; norm_num⟩ = (2025) := rfl
  have h1 : table_10_bcol.get ⟨75, by rw [table_10_bcol_length]; norm_num⟩ = (2050) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2050 : table_10_next (2050) = (2075) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 75
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨75, by rw [table_10_bcol_length]; norm_num⟩ = (2050) := rfl
  have h1 : table_10_bcol.get ⟨76, by rw [table_10_bcol_length]; norm_num⟩ = (2075) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2075 : table_10_next (2075) = (2100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 76
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨76, by rw [table_10_bcol_length]; norm_num⟩ = (2075) := rfl
  have h1 : table_10_bcol.get ⟨77, by rw [table_10_bcol_length]; norm_num⟩ = (2100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2100 : table_10_next (2100) = (2125) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 77
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨77, by rw [table_10_bcol_length]; norm_num⟩ = (2100) := rfl
  have h1 : table_10_bcol.get ⟨78, by rw [table_10_bcol_length]; norm_num⟩ = (2125) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2125 : table_10_next (2125) = (2150) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 78
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨78, by rw [table_10_bcol_length]; norm_num⟩ = (2125) := rfl
  have h1 : table_10_bcol.get ⟨79, by rw [table_10_bcol_length]; norm_num⟩ = (2150) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2150 : table_10_next (2150) = (2175) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 79
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨79, by rw [table_10_bcol_length]; norm_num⟩ = (2150) := rfl
  have h1 : table_10_bcol.get ⟨80, by rw [table_10_bcol_length]; norm_num⟩ = (2175) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2175 : table_10_next (2175) = (2200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 80
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨80, by rw [table_10_bcol_length]; norm_num⟩ = (2175) := rfl
  have h1 : table_10_bcol.get ⟨81, by rw [table_10_bcol_length]; norm_num⟩ = (2200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2200 : table_10_next (2200) = (2225) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 81
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨81, by rw [table_10_bcol_length]; norm_num⟩ = (2200) := rfl
  have h1 : table_10_bcol.get ⟨82, by rw [table_10_bcol_length]; norm_num⟩ = (2225) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2225 : table_10_next (2225) = (2250) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 82
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨82, by rw [table_10_bcol_length]; norm_num⟩ = (2225) := rfl
  have h1 : table_10_bcol.get ⟨83, by rw [table_10_bcol_length]; norm_num⟩ = (2250) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2250 : table_10_next (2250) = (2275) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 83
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨83, by rw [table_10_bcol_length]; norm_num⟩ = (2250) := rfl
  have h1 : table_10_bcol.get ⟨84, by rw [table_10_bcol_length]; norm_num⟩ = (2275) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2275 : table_10_next (2275) = (2300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 84
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨84, by rw [table_10_bcol_length]; norm_num⟩ = (2275) := rfl
  have h1 : table_10_bcol.get ⟨85, by rw [table_10_bcol_length]; norm_num⟩ = (2300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2300 : table_10_next (2300) = (2325) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 85
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨85, by rw [table_10_bcol_length]; norm_num⟩ = (2300) := rfl
  have h1 : table_10_bcol.get ⟨86, by rw [table_10_bcol_length]; norm_num⟩ = (2325) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2325 : table_10_next (2325) = (2350) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 86
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨86, by rw [table_10_bcol_length]; norm_num⟩ = (2325) := rfl
  have h1 : table_10_bcol.get ⟨87, by rw [table_10_bcol_length]; norm_num⟩ = (2350) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2350 : table_10_next (2350) = (2375) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 87
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨87, by rw [table_10_bcol_length]; norm_num⟩ = (2350) := rfl
  have h1 : table_10_bcol.get ⟨88, by rw [table_10_bcol_length]; norm_num⟩ = (2375) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2375 : table_10_next (2375) = (2400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 88
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨88, by rw [table_10_bcol_length]; norm_num⟩ = (2375) := rfl
  have h1 : table_10_bcol.get ⟨89, by rw [table_10_bcol_length]; norm_num⟩ = (2400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2400 : table_10_next (2400) = (2425) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 89
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨89, by rw [table_10_bcol_length]; norm_num⟩ = (2400) := rfl
  have h1 : table_10_bcol.get ⟨90, by rw [table_10_bcol_length]; norm_num⟩ = (2425) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2425 : table_10_next (2425) = (2450) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 90
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨90, by rw [table_10_bcol_length]; norm_num⟩ = (2425) := rfl
  have h1 : table_10_bcol.get ⟨91, by rw [table_10_bcol_length]; norm_num⟩ = (2450) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2450 : table_10_next (2450) = (2475) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 91
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨91, by rw [table_10_bcol_length]; norm_num⟩ = (2450) := rfl
  have h1 : table_10_bcol.get ⟨92, by rw [table_10_bcol_length]; norm_num⟩ = (2475) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2475 : table_10_next (2475) = (2500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 92
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨92, by rw [table_10_bcol_length]; norm_num⟩ = (2475) := rfl
  have h1 : table_10_bcol.get ⟨93, by rw [table_10_bcol_length]; norm_num⟩ = (2500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2500 : table_10_next (2500) = (2525) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 93
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨93, by rw [table_10_bcol_length]; norm_num⟩ = (2500) := rfl
  have h1 : table_10_bcol.get ⟨94, by rw [table_10_bcol_length]; norm_num⟩ = (2525) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2525 : table_10_next (2525) = (2550) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 94
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨94, by rw [table_10_bcol_length]; norm_num⟩ = (2525) := rfl
  have h1 : table_10_bcol.get ⟨95, by rw [table_10_bcol_length]; norm_num⟩ = (2550) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2550 : table_10_next (2550) = (2575) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 95
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨95, by rw [table_10_bcol_length]; norm_num⟩ = (2550) := rfl
  have h1 : table_10_bcol.get ⟨96, by rw [table_10_bcol_length]; norm_num⟩ = (2575) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2575 : table_10_next (2575) = (2600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 96
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨96, by rw [table_10_bcol_length]; norm_num⟩ = (2575) := rfl
  have h1 : table_10_bcol.get ⟨97, by rw [table_10_bcol_length]; norm_num⟩ = (2600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2600 : table_10_next (2600) = (2625) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 97
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨97, by rw [table_10_bcol_length]; norm_num⟩ = (2600) := rfl
  have h1 : table_10_bcol.get ⟨98, by rw [table_10_bcol_length]; norm_num⟩ = (2625) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2625 : table_10_next (2625) = (2650) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 98
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨98, by rw [table_10_bcol_length]; norm_num⟩ = (2625) := rfl
  have h1 : table_10_bcol.get ⟨99, by rw [table_10_bcol_length]; norm_num⟩ = (2650) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2650 : table_10_next (2650) = (2675) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 99
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨99, by rw [table_10_bcol_length]; norm_num⟩ = (2650) := rfl
  have h1 : table_10_bcol.get ⟨100, by rw [table_10_bcol_length]; norm_num⟩ = (2675) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2675 : table_10_next (2675) = (2700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 100
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨100, by rw [table_10_bcol_length]; norm_num⟩ = (2675) := rfl
  have h1 : table_10_bcol.get ⟨101, by rw [table_10_bcol_length]; norm_num⟩ = (2700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2700 : table_10_next (2700) = (2725) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 101
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨101, by rw [table_10_bcol_length]; norm_num⟩ = (2700) := rfl
  have h1 : table_10_bcol.get ⟨102, by rw [table_10_bcol_length]; norm_num⟩ = (2725) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2725 : table_10_next (2725) = (2750) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 102
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨102, by rw [table_10_bcol_length]; norm_num⟩ = (2725) := rfl
  have h1 : table_10_bcol.get ⟨103, by rw [table_10_bcol_length]; norm_num⟩ = (2750) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2750 : table_10_next (2750) = (2775) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 103
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨103, by rw [table_10_bcol_length]; norm_num⟩ = (2750) := rfl
  have h1 : table_10_bcol.get ⟨104, by rw [table_10_bcol_length]; norm_num⟩ = (2775) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2775 : table_10_next (2775) = (2800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 104
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨104, by rw [table_10_bcol_length]; norm_num⟩ = (2775) := rfl
  have h1 : table_10_bcol.get ⟨105, by rw [table_10_bcol_length]; norm_num⟩ = (2800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2800 : table_10_next (2800) = (2825) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 105
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨105, by rw [table_10_bcol_length]; norm_num⟩ = (2800) := rfl
  have h1 : table_10_bcol.get ⟨106, by rw [table_10_bcol_length]; norm_num⟩ = (2825) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2825 : table_10_next (2825) = (2850) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 106
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨106, by rw [table_10_bcol_length]; norm_num⟩ = (2825) := rfl
  have h1 : table_10_bcol.get ⟨107, by rw [table_10_bcol_length]; norm_num⟩ = (2850) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2850 : table_10_next (2850) = (2875) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 107
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨107, by rw [table_10_bcol_length]; norm_num⟩ = (2850) := rfl
  have h1 : table_10_bcol.get ⟨108, by rw [table_10_bcol_length]; norm_num⟩ = (2875) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2875 : table_10_next (2875) = (2900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 108
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨108, by rw [table_10_bcol_length]; norm_num⟩ = (2875) := rfl
  have h1 : table_10_bcol.get ⟨109, by rw [table_10_bcol_length]; norm_num⟩ = (2900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2900 : table_10_next (2900) = (2925) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 109
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨109, by rw [table_10_bcol_length]; norm_num⟩ = (2900) := rfl
  have h1 : table_10_bcol.get ⟨110, by rw [table_10_bcol_length]; norm_num⟩ = (2925) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2925 : table_10_next (2925) = (2950) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 110
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨110, by rw [table_10_bcol_length]; norm_num⟩ = (2925) := rfl
  have h1 : table_10_bcol.get ⟨111, by rw [table_10_bcol_length]; norm_num⟩ = (2950) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2950 : table_10_next (2950) = (2975) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 111
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨111, by rw [table_10_bcol_length]; norm_num⟩ = (2950) := rfl
  have h1 : table_10_bcol.get ⟨112, by rw [table_10_bcol_length]; norm_num⟩ = (2975) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_2975 : table_10_next (2975) = (3000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 112
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨112, by rw [table_10_bcol_length]; norm_num⟩ = (2975) := rfl
  have h1 : table_10_bcol.get ⟨113, by rw [table_10_bcol_length]; norm_num⟩ = (3000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3000 : table_10_next (3000) = (3025) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 113
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨113, by rw [table_10_bcol_length]; norm_num⟩ = (3000) := rfl
  have h1 : table_10_bcol.get ⟨114, by rw [table_10_bcol_length]; norm_num⟩ = (3025) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3025 : table_10_next (3025) = (3050) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 114
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨114, by rw [table_10_bcol_length]; norm_num⟩ = (3025) := rfl
  have h1 : table_10_bcol.get ⟨115, by rw [table_10_bcol_length]; norm_num⟩ = (3050) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3050 : table_10_next (3050) = (3075) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 115
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨115, by rw [table_10_bcol_length]; norm_num⟩ = (3050) := rfl
  have h1 : table_10_bcol.get ⟨116, by rw [table_10_bcol_length]; norm_num⟩ = (3075) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3075 : table_10_next (3075) = (3100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 116
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨116, by rw [table_10_bcol_length]; norm_num⟩ = (3075) := rfl
  have h1 : table_10_bcol.get ⟨117, by rw [table_10_bcol_length]; norm_num⟩ = (3100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3100 : table_10_next (3100) = (3125) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 117
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨117, by rw [table_10_bcol_length]; norm_num⟩ = (3100) := rfl
  have h1 : table_10_bcol.get ⟨118, by rw [table_10_bcol_length]; norm_num⟩ = (3125) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3125 : table_10_next (3125) = (3150) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 118
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨118, by rw [table_10_bcol_length]; norm_num⟩ = (3125) := rfl
  have h1 : table_10_bcol.get ⟨119, by rw [table_10_bcol_length]; norm_num⟩ = (3150) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3150 : table_10_next (3150) = (3175) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 119
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨119, by rw [table_10_bcol_length]; norm_num⟩ = (3150) := rfl
  have h1 : table_10_bcol.get ⟨120, by rw [table_10_bcol_length]; norm_num⟩ = (3175) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3175 : table_10_next (3175) = (3200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 120
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨120, by rw [table_10_bcol_length]; norm_num⟩ = (3175) := rfl
  have h1 : table_10_bcol.get ⟨121, by rw [table_10_bcol_length]; norm_num⟩ = (3200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3200 : table_10_next (3200) = (3225) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 121
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨121, by rw [table_10_bcol_length]; norm_num⟩ = (3200) := rfl
  have h1 : table_10_bcol.get ⟨122, by rw [table_10_bcol_length]; norm_num⟩ = (3225) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3225 : table_10_next (3225) = (3250) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 122
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨122, by rw [table_10_bcol_length]; norm_num⟩ = (3225) := rfl
  have h1 : table_10_bcol.get ⟨123, by rw [table_10_bcol_length]; norm_num⟩ = (3250) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3250 : table_10_next (3250) = (3275) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 123
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨123, by rw [table_10_bcol_length]; norm_num⟩ = (3250) := rfl
  have h1 : table_10_bcol.get ⟨124, by rw [table_10_bcol_length]; norm_num⟩ = (3275) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3275 : table_10_next (3275) = (3300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 124
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨124, by rw [table_10_bcol_length]; norm_num⟩ = (3275) := rfl
  have h1 : table_10_bcol.get ⟨125, by rw [table_10_bcol_length]; norm_num⟩ = (3300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3300 : table_10_next (3300) = (3325) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 125
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨125, by rw [table_10_bcol_length]; norm_num⟩ = (3300) := rfl
  have h1 : table_10_bcol.get ⟨126, by rw [table_10_bcol_length]; norm_num⟩ = (3325) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3325 : table_10_next (3325) = (3350) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 126
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨126, by rw [table_10_bcol_length]; norm_num⟩ = (3325) := rfl
  have h1 : table_10_bcol.get ⟨127, by rw [table_10_bcol_length]; norm_num⟩ = (3350) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3350 : table_10_next (3350) = (3375) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 127
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨127, by rw [table_10_bcol_length]; norm_num⟩ = (3350) := rfl
  have h1 : table_10_bcol.get ⟨128, by rw [table_10_bcol_length]; norm_num⟩ = (3375) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3375 : table_10_next (3375) = (3400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 128
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨128, by rw [table_10_bcol_length]; norm_num⟩ = (3375) := rfl
  have h1 : table_10_bcol.get ⟨129, by rw [table_10_bcol_length]; norm_num⟩ = (3400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3400 : table_10_next (3400) = (3425) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 129
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨129, by rw [table_10_bcol_length]; norm_num⟩ = (3400) := rfl
  have h1 : table_10_bcol.get ⟨130, by rw [table_10_bcol_length]; norm_num⟩ = (3425) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3425 : table_10_next (3425) = (3450) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 130
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨130, by rw [table_10_bcol_length]; norm_num⟩ = (3425) := rfl
  have h1 : table_10_bcol.get ⟨131, by rw [table_10_bcol_length]; norm_num⟩ = (3450) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3450 : table_10_next (3450) = (3475) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 131
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨131, by rw [table_10_bcol_length]; norm_num⟩ = (3450) := rfl
  have h1 : table_10_bcol.get ⟨132, by rw [table_10_bcol_length]; norm_num⟩ = (3475) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3475 : table_10_next (3475) = (3500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 132
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨132, by rw [table_10_bcol_length]; norm_num⟩ = (3475) := rfl
  have h1 : table_10_bcol.get ⟨133, by rw [table_10_bcol_length]; norm_num⟩ = (3500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3500 : table_10_next (3500) = (3525) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 133
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨133, by rw [table_10_bcol_length]; norm_num⟩ = (3500) := rfl
  have h1 : table_10_bcol.get ⟨134, by rw [table_10_bcol_length]; norm_num⟩ = (3525) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3525 : table_10_next (3525) = (3550) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 134
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨134, by rw [table_10_bcol_length]; norm_num⟩ = (3525) := rfl
  have h1 : table_10_bcol.get ⟨135, by rw [table_10_bcol_length]; norm_num⟩ = (3550) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3550 : table_10_next (3550) = (3575) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 135
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨135, by rw [table_10_bcol_length]; norm_num⟩ = (3550) := rfl
  have h1 : table_10_bcol.get ⟨136, by rw [table_10_bcol_length]; norm_num⟩ = (3575) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3575 : table_10_next (3575) = (3600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 136
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨136, by rw [table_10_bcol_length]; norm_num⟩ = (3575) := rfl
  have h1 : table_10_bcol.get ⟨137, by rw [table_10_bcol_length]; norm_num⟩ = (3600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3600 : table_10_next (3600) = (3625) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 137
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨137, by rw [table_10_bcol_length]; norm_num⟩ = (3600) := rfl
  have h1 : table_10_bcol.get ⟨138, by rw [table_10_bcol_length]; norm_num⟩ = (3625) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3625 : table_10_next (3625) = (3650) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 138
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨138, by rw [table_10_bcol_length]; norm_num⟩ = (3625) := rfl
  have h1 : table_10_bcol.get ⟨139, by rw [table_10_bcol_length]; norm_num⟩ = (3650) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3650 : table_10_next (3650) = (3675) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 139
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨139, by rw [table_10_bcol_length]; norm_num⟩ = (3650) := rfl
  have h1 : table_10_bcol.get ⟨140, by rw [table_10_bcol_length]; norm_num⟩ = (3675) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3675 : table_10_next (3675) = (3700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 140
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨140, by rw [table_10_bcol_length]; norm_num⟩ = (3675) := rfl
  have h1 : table_10_bcol.get ⟨141, by rw [table_10_bcol_length]; norm_num⟩ = (3700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3700 : table_10_next (3700) = (3725) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 141
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨141, by rw [table_10_bcol_length]; norm_num⟩ = (3700) := rfl
  have h1 : table_10_bcol.get ⟨142, by rw [table_10_bcol_length]; norm_num⟩ = (3725) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3725 : table_10_next (3725) = (3750) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 142
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨142, by rw [table_10_bcol_length]; norm_num⟩ = (3725) := rfl
  have h1 : table_10_bcol.get ⟨143, by rw [table_10_bcol_length]; norm_num⟩ = (3750) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3750 : table_10_next (3750) = (3775) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 143
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨143, by rw [table_10_bcol_length]; norm_num⟩ = (3750) := rfl
  have h1 : table_10_bcol.get ⟨144, by rw [table_10_bcol_length]; norm_num⟩ = (3775) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3775 : table_10_next (3775) = (3800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 144
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨144, by rw [table_10_bcol_length]; norm_num⟩ = (3775) := rfl
  have h1 : table_10_bcol.get ⟨145, by rw [table_10_bcol_length]; norm_num⟩ = (3800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3800 : table_10_next (3800) = (3825) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 145
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨145, by rw [table_10_bcol_length]; norm_num⟩ = (3800) := rfl
  have h1 : table_10_bcol.get ⟨146, by rw [table_10_bcol_length]; norm_num⟩ = (3825) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3825 : table_10_next (3825) = (3850) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 146
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨146, by rw [table_10_bcol_length]; norm_num⟩ = (3825) := rfl
  have h1 : table_10_bcol.get ⟨147, by rw [table_10_bcol_length]; norm_num⟩ = (3850) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3850 : table_10_next (3850) = (3875) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 147
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨147, by rw [table_10_bcol_length]; norm_num⟩ = (3850) := rfl
  have h1 : table_10_bcol.get ⟨148, by rw [table_10_bcol_length]; norm_num⟩ = (3875) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3875 : table_10_next (3875) = (3900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 148
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨148, by rw [table_10_bcol_length]; norm_num⟩ = (3875) := rfl
  have h1 : table_10_bcol.get ⟨149, by rw [table_10_bcol_length]; norm_num⟩ = (3900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3900 : table_10_next (3900) = (3925) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 149
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨149, by rw [table_10_bcol_length]; norm_num⟩ = (3900) := rfl
  have h1 : table_10_bcol.get ⟨150, by rw [table_10_bcol_length]; norm_num⟩ = (3925) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3925 : table_10_next (3925) = (3950) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 150
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨150, by rw [table_10_bcol_length]; norm_num⟩ = (3925) := rfl
  have h1 : table_10_bcol.get ⟨151, by rw [table_10_bcol_length]; norm_num⟩ = (3950) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3950 : table_10_next (3950) = (3975) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 151
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨151, by rw [table_10_bcol_length]; norm_num⟩ = (3950) := rfl
  have h1 : table_10_bcol.get ⟨152, by rw [table_10_bcol_length]; norm_num⟩ = (3975) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_3975 : table_10_next (3975) = (4000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 152
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨152, by rw [table_10_bcol_length]; norm_num⟩ = (3975) := rfl
  have h1 : table_10_bcol.get ⟨153, by rw [table_10_bcol_length]; norm_num⟩ = (4000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4000 : table_10_next (4000) = (4025) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 153
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨153, by rw [table_10_bcol_length]; norm_num⟩ = (4000) := rfl
  have h1 : table_10_bcol.get ⟨154, by rw [table_10_bcol_length]; norm_num⟩ = (4025) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4025 : table_10_next (4025) = (4050) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 154
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨154, by rw [table_10_bcol_length]; norm_num⟩ = (4025) := rfl
  have h1 : table_10_bcol.get ⟨155, by rw [table_10_bcol_length]; norm_num⟩ = (4050) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4050 : table_10_next (4050) = (4075) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 155
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨155, by rw [table_10_bcol_length]; norm_num⟩ = (4050) := rfl
  have h1 : table_10_bcol.get ⟨156, by rw [table_10_bcol_length]; norm_num⟩ = (4075) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4075 : table_10_next (4075) = (4100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 156
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨156, by rw [table_10_bcol_length]; norm_num⟩ = (4075) := rfl
  have h1 : table_10_bcol.get ⟨157, by rw [table_10_bcol_length]; norm_num⟩ = (4100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4100 : table_10_next (4100) = (4125) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 157
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨157, by rw [table_10_bcol_length]; norm_num⟩ = (4100) := rfl
  have h1 : table_10_bcol.get ⟨158, by rw [table_10_bcol_length]; norm_num⟩ = (4125) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4125 : table_10_next (4125) = (4150) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 158
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨158, by rw [table_10_bcol_length]; norm_num⟩ = (4125) := rfl
  have h1 : table_10_bcol.get ⟨159, by rw [table_10_bcol_length]; norm_num⟩ = (4150) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4150 : table_10_next (4150) = (4175) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 159
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨159, by rw [table_10_bcol_length]; norm_num⟩ = (4150) := rfl
  have h1 : table_10_bcol.get ⟨160, by rw [table_10_bcol_length]; norm_num⟩ = (4175) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4175 : table_10_next (4175) = (4200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 160
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨160, by rw [table_10_bcol_length]; norm_num⟩ = (4175) := rfl
  have h1 : table_10_bcol.get ⟨161, by rw [table_10_bcol_length]; norm_num⟩ = (4200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4200 : table_10_next (4200) = (4225) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 161
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨161, by rw [table_10_bcol_length]; norm_num⟩ = (4200) := rfl
  have h1 : table_10_bcol.get ⟨162, by rw [table_10_bcol_length]; norm_num⟩ = (4225) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4225 : table_10_next (4225) = (4250) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 162
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨162, by rw [table_10_bcol_length]; norm_num⟩ = (4225) := rfl
  have h1 : table_10_bcol.get ⟨163, by rw [table_10_bcol_length]; norm_num⟩ = (4250) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4250 : table_10_next (4250) = (4275) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 163
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨163, by rw [table_10_bcol_length]; norm_num⟩ = (4250) := rfl
  have h1 : table_10_bcol.get ⟨164, by rw [table_10_bcol_length]; norm_num⟩ = (4275) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4275 : table_10_next (4275) = (4300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 164
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨164, by rw [table_10_bcol_length]; norm_num⟩ = (4275) := rfl
  have h1 : table_10_bcol.get ⟨165, by rw [table_10_bcol_length]; norm_num⟩ = (4300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4300 : table_10_next (4300) = (4325) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 165
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨165, by rw [table_10_bcol_length]; norm_num⟩ = (4300) := rfl
  have h1 : table_10_bcol.get ⟨166, by rw [table_10_bcol_length]; norm_num⟩ = (4325) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4325 : table_10_next (4325) = (4350) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 166
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨166, by rw [table_10_bcol_length]; norm_num⟩ = (4325) := rfl
  have h1 : table_10_bcol.get ⟨167, by rw [table_10_bcol_length]; norm_num⟩ = (4350) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4350 : table_10_next (4350) = (4375) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 167
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨167, by rw [table_10_bcol_length]; norm_num⟩ = (4350) := rfl
  have h1 : table_10_bcol.get ⟨168, by rw [table_10_bcol_length]; norm_num⟩ = (4375) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4375 : table_10_next (4375) = (4400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 168
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨168, by rw [table_10_bcol_length]; norm_num⟩ = (4375) := rfl
  have h1 : table_10_bcol.get ⟨169, by rw [table_10_bcol_length]; norm_num⟩ = (4400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4400 : table_10_next (4400) = (4425) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 169
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨169, by rw [table_10_bcol_length]; norm_num⟩ = (4400) := rfl
  have h1 : table_10_bcol.get ⟨170, by rw [table_10_bcol_length]; norm_num⟩ = (4425) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4425 : table_10_next (4425) = (4450) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 170
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨170, by rw [table_10_bcol_length]; norm_num⟩ = (4425) := rfl
  have h1 : table_10_bcol.get ⟨171, by rw [table_10_bcol_length]; norm_num⟩ = (4450) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4450 : table_10_next (4450) = (4475) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 171
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨171, by rw [table_10_bcol_length]; norm_num⟩ = (4450) := rfl
  have h1 : table_10_bcol.get ⟨172, by rw [table_10_bcol_length]; norm_num⟩ = (4475) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4475 : table_10_next (4475) = (4500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 172
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨172, by rw [table_10_bcol_length]; norm_num⟩ = (4475) := rfl
  have h1 : table_10_bcol.get ⟨173, by rw [table_10_bcol_length]; norm_num⟩ = (4500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4500 : table_10_next (4500) = (4525) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 173
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨173, by rw [table_10_bcol_length]; norm_num⟩ = (4500) := rfl
  have h1 : table_10_bcol.get ⟨174, by rw [table_10_bcol_length]; norm_num⟩ = (4525) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4525 : table_10_next (4525) = (4550) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 174
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨174, by rw [table_10_bcol_length]; norm_num⟩ = (4525) := rfl
  have h1 : table_10_bcol.get ⟨175, by rw [table_10_bcol_length]; norm_num⟩ = (4550) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4550 : table_10_next (4550) = (4575) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 175
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨175, by rw [table_10_bcol_length]; norm_num⟩ = (4550) := rfl
  have h1 : table_10_bcol.get ⟨176, by rw [table_10_bcol_length]; norm_num⟩ = (4575) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4575 : table_10_next (4575) = (4600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 176
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨176, by rw [table_10_bcol_length]; norm_num⟩ = (4575) := rfl
  have h1 : table_10_bcol.get ⟨177, by rw [table_10_bcol_length]; norm_num⟩ = (4600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4600 : table_10_next (4600) = (4625) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 177
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨177, by rw [table_10_bcol_length]; norm_num⟩ = (4600) := rfl
  have h1 : table_10_bcol.get ⟨178, by rw [table_10_bcol_length]; norm_num⟩ = (4625) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4625 : table_10_next (4625) = (4650) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 178
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨178, by rw [table_10_bcol_length]; norm_num⟩ = (4625) := rfl
  have h1 : table_10_bcol.get ⟨179, by rw [table_10_bcol_length]; norm_num⟩ = (4650) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4650 : table_10_next (4650) = (4675) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 179
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨179, by rw [table_10_bcol_length]; norm_num⟩ = (4650) := rfl
  have h1 : table_10_bcol.get ⟨180, by rw [table_10_bcol_length]; norm_num⟩ = (4675) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4675 : table_10_next (4675) = (4700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 180
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨180, by rw [table_10_bcol_length]; norm_num⟩ = (4675) := rfl
  have h1 : table_10_bcol.get ⟨181, by rw [table_10_bcol_length]; norm_num⟩ = (4700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4700 : table_10_next (4700) = (4725) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 181
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨181, by rw [table_10_bcol_length]; norm_num⟩ = (4700) := rfl
  have h1 : table_10_bcol.get ⟨182, by rw [table_10_bcol_length]; norm_num⟩ = (4725) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4725 : table_10_next (4725) = (4750) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 182
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨182, by rw [table_10_bcol_length]; norm_num⟩ = (4725) := rfl
  have h1 : table_10_bcol.get ⟨183, by rw [table_10_bcol_length]; norm_num⟩ = (4750) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4750 : table_10_next (4750) = (4775) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 183
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨183, by rw [table_10_bcol_length]; norm_num⟩ = (4750) := rfl
  have h1 : table_10_bcol.get ⟨184, by rw [table_10_bcol_length]; norm_num⟩ = (4775) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4775 : table_10_next (4775) = (4800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 184
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨184, by rw [table_10_bcol_length]; norm_num⟩ = (4775) := rfl
  have h1 : table_10_bcol.get ⟨185, by rw [table_10_bcol_length]; norm_num⟩ = (4800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4800 : table_10_next (4800) = (4825) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 185
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨185, by rw [table_10_bcol_length]; norm_num⟩ = (4800) := rfl
  have h1 : table_10_bcol.get ⟨186, by rw [table_10_bcol_length]; norm_num⟩ = (4825) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4825 : table_10_next (4825) = (4850) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 186
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨186, by rw [table_10_bcol_length]; norm_num⟩ = (4825) := rfl
  have h1 : table_10_bcol.get ⟨187, by rw [table_10_bcol_length]; norm_num⟩ = (4850) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4850 : table_10_next (4850) = (4875) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 187
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨187, by rw [table_10_bcol_length]; norm_num⟩ = (4850) := rfl
  have h1 : table_10_bcol.get ⟨188, by rw [table_10_bcol_length]; norm_num⟩ = (4875) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4875 : table_10_next (4875) = (4900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 188
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨188, by rw [table_10_bcol_length]; norm_num⟩ = (4875) := rfl
  have h1 : table_10_bcol.get ⟨189, by rw [table_10_bcol_length]; norm_num⟩ = (4900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4900 : table_10_next (4900) = (4925) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 189
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨189, by rw [table_10_bcol_length]; norm_num⟩ = (4900) := rfl
  have h1 : table_10_bcol.get ⟨190, by rw [table_10_bcol_length]; norm_num⟩ = (4925) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4925 : table_10_next (4925) = (4950) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 190
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨190, by rw [table_10_bcol_length]; norm_num⟩ = (4925) := rfl
  have h1 : table_10_bcol.get ⟨191, by rw [table_10_bcol_length]; norm_num⟩ = (4950) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4950 : table_10_next (4950) = (4975) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 191
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨191, by rw [table_10_bcol_length]; norm_num⟩ = (4950) := rfl
  have h1 : table_10_bcol.get ⟨192, by rw [table_10_bcol_length]; norm_num⟩ = (4975) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_4975 : table_10_next (4975) = (5000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 192
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨192, by rw [table_10_bcol_length]; norm_num⟩ = (4975) := rfl
  have h1 : table_10_bcol.get ⟨193, by rw [table_10_bcol_length]; norm_num⟩ = (5000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5000 : table_10_next (5000) = (5100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 193
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨193, by rw [table_10_bcol_length]; norm_num⟩ = (5000) := rfl
  have h1 : table_10_bcol.get ⟨194, by rw [table_10_bcol_length]; norm_num⟩ = (5100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5100 : table_10_next (5100) = (5200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 194
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨194, by rw [table_10_bcol_length]; norm_num⟩ = (5100) := rfl
  have h1 : table_10_bcol.get ⟨195, by rw [table_10_bcol_length]; norm_num⟩ = (5200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5200 : table_10_next (5200) = (5300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 195
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨195, by rw [table_10_bcol_length]; norm_num⟩ = (5200) := rfl
  have h1 : table_10_bcol.get ⟨196, by rw [table_10_bcol_length]; norm_num⟩ = (5300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5300 : table_10_next (5300) = (5400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 196
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨196, by rw [table_10_bcol_length]; norm_num⟩ = (5300) := rfl
  have h1 : table_10_bcol.get ⟨197, by rw [table_10_bcol_length]; norm_num⟩ = (5400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5400 : table_10_next (5400) = (5500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 197
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨197, by rw [table_10_bcol_length]; norm_num⟩ = (5400) := rfl
  have h1 : table_10_bcol.get ⟨198, by rw [table_10_bcol_length]; norm_num⟩ = (5500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5500 : table_10_next (5500) = (5600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 198
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨198, by rw [table_10_bcol_length]; norm_num⟩ = (5500) := rfl
  have h1 : table_10_bcol.get ⟨199, by rw [table_10_bcol_length]; norm_num⟩ = (5600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5600 : table_10_next (5600) = (5700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 199
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨199, by rw [table_10_bcol_length]; norm_num⟩ = (5600) := rfl
  have h1 : table_10_bcol.get ⟨200, by rw [table_10_bcol_length]; norm_num⟩ = (5700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5700 : table_10_next (5700) = (5800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 200
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨200, by rw [table_10_bcol_length]; norm_num⟩ = (5700) := rfl
  have h1 : table_10_bcol.get ⟨201, by rw [table_10_bcol_length]; norm_num⟩ = (5800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5800 : table_10_next (5800) = (5900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 201
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨201, by rw [table_10_bcol_length]; norm_num⟩ = (5800) := rfl
  have h1 : table_10_bcol.get ⟨202, by rw [table_10_bcol_length]; norm_num⟩ = (5900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_5900 : table_10_next (5900) = (6000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 202
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨202, by rw [table_10_bcol_length]; norm_num⟩ = (5900) := rfl
  have h1 : table_10_bcol.get ⟨203, by rw [table_10_bcol_length]; norm_num⟩ = (6000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6000 : table_10_next (6000) = (6100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 203
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨203, by rw [table_10_bcol_length]; norm_num⟩ = (6000) := rfl
  have h1 : table_10_bcol.get ⟨204, by rw [table_10_bcol_length]; norm_num⟩ = (6100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6100 : table_10_next (6100) = (6200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 204
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨204, by rw [table_10_bcol_length]; norm_num⟩ = (6100) := rfl
  have h1 : table_10_bcol.get ⟨205, by rw [table_10_bcol_length]; norm_num⟩ = (6200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6200 : table_10_next (6200) = (6300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 205
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨205, by rw [table_10_bcol_length]; norm_num⟩ = (6200) := rfl
  have h1 : table_10_bcol.get ⟨206, by rw [table_10_bcol_length]; norm_num⟩ = (6300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6300 : table_10_next (6300) = (6400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 206
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨206, by rw [table_10_bcol_length]; norm_num⟩ = (6300) := rfl
  have h1 : table_10_bcol.get ⟨207, by rw [table_10_bcol_length]; norm_num⟩ = (6400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6400 : table_10_next (6400) = (6500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 207
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨207, by rw [table_10_bcol_length]; norm_num⟩ = (6400) := rfl
  have h1 : table_10_bcol.get ⟨208, by rw [table_10_bcol_length]; norm_num⟩ = (6500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6500 : table_10_next (6500) = (6600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 208
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨208, by rw [table_10_bcol_length]; norm_num⟩ = (6500) := rfl
  have h1 : table_10_bcol.get ⟨209, by rw [table_10_bcol_length]; norm_num⟩ = (6600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6600 : table_10_next (6600) = (6700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 209
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨209, by rw [table_10_bcol_length]; norm_num⟩ = (6600) := rfl
  have h1 : table_10_bcol.get ⟨210, by rw [table_10_bcol_length]; norm_num⟩ = (6700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6700 : table_10_next (6700) = (6800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 210
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨210, by rw [table_10_bcol_length]; norm_num⟩ = (6700) := rfl
  have h1 : table_10_bcol.get ⟨211, by rw [table_10_bcol_length]; norm_num⟩ = (6800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6800 : table_10_next (6800) = (6900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 211
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨211, by rw [table_10_bcol_length]; norm_num⟩ = (6800) := rfl
  have h1 : table_10_bcol.get ⟨212, by rw [table_10_bcol_length]; norm_num⟩ = (6900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_6900 : table_10_next (6900) = (7000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 212
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨212, by rw [table_10_bcol_length]; norm_num⟩ = (6900) := rfl
  have h1 : table_10_bcol.get ⟨213, by rw [table_10_bcol_length]; norm_num⟩ = (7000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7000 : table_10_next (7000) = (7100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 213
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨213, by rw [table_10_bcol_length]; norm_num⟩ = (7000) := rfl
  have h1 : table_10_bcol.get ⟨214, by rw [table_10_bcol_length]; norm_num⟩ = (7100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7100 : table_10_next (7100) = (7200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 214
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨214, by rw [table_10_bcol_length]; norm_num⟩ = (7100) := rfl
  have h1 : table_10_bcol.get ⟨215, by rw [table_10_bcol_length]; norm_num⟩ = (7200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7200 : table_10_next (7200) = (7300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 215
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨215, by rw [table_10_bcol_length]; norm_num⟩ = (7200) := rfl
  have h1 : table_10_bcol.get ⟨216, by rw [table_10_bcol_length]; norm_num⟩ = (7300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7300 : table_10_next (7300) = (7400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 216
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨216, by rw [table_10_bcol_length]; norm_num⟩ = (7300) := rfl
  have h1 : table_10_bcol.get ⟨217, by rw [table_10_bcol_length]; norm_num⟩ = (7400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7400 : table_10_next (7400) = (7500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 217
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨217, by rw [table_10_bcol_length]; norm_num⟩ = (7400) := rfl
  have h1 : table_10_bcol.get ⟨218, by rw [table_10_bcol_length]; norm_num⟩ = (7500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7500 : table_10_next (7500) = (7600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 218
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨218, by rw [table_10_bcol_length]; norm_num⟩ = (7500) := rfl
  have h1 : table_10_bcol.get ⟨219, by rw [table_10_bcol_length]; norm_num⟩ = (7600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7600 : table_10_next (7600) = (7700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 219
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨219, by rw [table_10_bcol_length]; norm_num⟩ = (7600) := rfl
  have h1 : table_10_bcol.get ⟨220, by rw [table_10_bcol_length]; norm_num⟩ = (7700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7700 : table_10_next (7700) = (7800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 220
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨220, by rw [table_10_bcol_length]; norm_num⟩ = (7700) := rfl
  have h1 : table_10_bcol.get ⟨221, by rw [table_10_bcol_length]; norm_num⟩ = (7800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7800 : table_10_next (7800) = (7900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 221
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨221, by rw [table_10_bcol_length]; norm_num⟩ = (7800) := rfl
  have h1 : table_10_bcol.get ⟨222, by rw [table_10_bcol_length]; norm_num⟩ = (7900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_7900 : table_10_next (7900) = (8000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 222
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨222, by rw [table_10_bcol_length]; norm_num⟩ = (7900) := rfl
  have h1 : table_10_bcol.get ⟨223, by rw [table_10_bcol_length]; norm_num⟩ = (8000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8000 : table_10_next (8000) = (8100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 223
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨223, by rw [table_10_bcol_length]; norm_num⟩ = (8000) := rfl
  have h1 : table_10_bcol.get ⟨224, by rw [table_10_bcol_length]; norm_num⟩ = (8100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8100 : table_10_next (8100) = (8200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 224
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨224, by rw [table_10_bcol_length]; norm_num⟩ = (8100) := rfl
  have h1 : table_10_bcol.get ⟨225, by rw [table_10_bcol_length]; norm_num⟩ = (8200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8200 : table_10_next (8200) = (8300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 225
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨225, by rw [table_10_bcol_length]; norm_num⟩ = (8200) := rfl
  have h1 : table_10_bcol.get ⟨226, by rw [table_10_bcol_length]; norm_num⟩ = (8300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8300 : table_10_next (8300) = (8400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 226
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨226, by rw [table_10_bcol_length]; norm_num⟩ = (8300) := rfl
  have h1 : table_10_bcol.get ⟨227, by rw [table_10_bcol_length]; norm_num⟩ = (8400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8400 : table_10_next (8400) = (8500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 227
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨227, by rw [table_10_bcol_length]; norm_num⟩ = (8400) := rfl
  have h1 : table_10_bcol.get ⟨228, by rw [table_10_bcol_length]; norm_num⟩ = (8500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8500 : table_10_next (8500) = (8600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 228
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨228, by rw [table_10_bcol_length]; norm_num⟩ = (8500) := rfl
  have h1 : table_10_bcol.get ⟨229, by rw [table_10_bcol_length]; norm_num⟩ = (8600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8600 : table_10_next (8600) = (8700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 229
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨229, by rw [table_10_bcol_length]; norm_num⟩ = (8600) := rfl
  have h1 : table_10_bcol.get ⟨230, by rw [table_10_bcol_length]; norm_num⟩ = (8700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8700 : table_10_next (8700) = (8800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 230
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨230, by rw [table_10_bcol_length]; norm_num⟩ = (8700) := rfl
  have h1 : table_10_bcol.get ⟨231, by rw [table_10_bcol_length]; norm_num⟩ = (8800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8800 : table_10_next (8800) = (8900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 231
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨231, by rw [table_10_bcol_length]; norm_num⟩ = (8800) := rfl
  have h1 : table_10_bcol.get ⟨232, by rw [table_10_bcol_length]; norm_num⟩ = (8900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_8900 : table_10_next (8900) = (9000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 232
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨232, by rw [table_10_bcol_length]; norm_num⟩ = (8900) := rfl
  have h1 : table_10_bcol.get ⟨233, by rw [table_10_bcol_length]; norm_num⟩ = (9000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9000 : table_10_next (9000) = (9100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 233
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨233, by rw [table_10_bcol_length]; norm_num⟩ = (9000) := rfl
  have h1 : table_10_bcol.get ⟨234, by rw [table_10_bcol_length]; norm_num⟩ = (9100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9100 : table_10_next (9100) = (9200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 234
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨234, by rw [table_10_bcol_length]; norm_num⟩ = (9100) := rfl
  have h1 : table_10_bcol.get ⟨235, by rw [table_10_bcol_length]; norm_num⟩ = (9200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9200 : table_10_next (9200) = (9300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 235
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨235, by rw [table_10_bcol_length]; norm_num⟩ = (9200) := rfl
  have h1 : table_10_bcol.get ⟨236, by rw [table_10_bcol_length]; norm_num⟩ = (9300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9300 : table_10_next (9300) = (9400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 236
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨236, by rw [table_10_bcol_length]; norm_num⟩ = (9300) := rfl
  have h1 : table_10_bcol.get ⟨237, by rw [table_10_bcol_length]; norm_num⟩ = (9400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9400 : table_10_next (9400) = (9500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 237
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨237, by rw [table_10_bcol_length]; norm_num⟩ = (9400) := rfl
  have h1 : table_10_bcol.get ⟨238, by rw [table_10_bcol_length]; norm_num⟩ = (9500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9500 : table_10_next (9500) = (9600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 238
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨238, by rw [table_10_bcol_length]; norm_num⟩ = (9500) := rfl
  have h1 : table_10_bcol.get ⟨239, by rw [table_10_bcol_length]; norm_num⟩ = (9600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9600 : table_10_next (9600) = (9700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 239
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨239, by rw [table_10_bcol_length]; norm_num⟩ = (9600) := rfl
  have h1 : table_10_bcol.get ⟨240, by rw [table_10_bcol_length]; norm_num⟩ = (9700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9700 : table_10_next (9700) = (9800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 240
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨240, by rw [table_10_bcol_length]; norm_num⟩ = (9700) := rfl
  have h1 : table_10_bcol.get ⟨241, by rw [table_10_bcol_length]; norm_num⟩ = (9800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9800 : table_10_next (9800) = (9900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 241
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨241, by rw [table_10_bcol_length]; norm_num⟩ = (9800) := rfl
  have h1 : table_10_bcol.get ⟨242, by rw [table_10_bcol_length]; norm_num⟩ = (9900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_9900 : table_10_next (9900) = (10000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 242
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨242, by rw [table_10_bcol_length]; norm_num⟩ = (9900) := rfl
  have h1 : table_10_bcol.get ⟨243, by rw [table_10_bcol_length]; norm_num⟩ = (10000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10000 : table_10_next (10000) = (10100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 243
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨243, by rw [table_10_bcol_length]; norm_num⟩ = (10000) := rfl
  have h1 : table_10_bcol.get ⟨244, by rw [table_10_bcol_length]; norm_num⟩ = (10100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10100 : table_10_next (10100) = (10200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 244
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨244, by rw [table_10_bcol_length]; norm_num⟩ = (10100) := rfl
  have h1 : table_10_bcol.get ⟨245, by rw [table_10_bcol_length]; norm_num⟩ = (10200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10200 : table_10_next (10200) = (10300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 245
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨245, by rw [table_10_bcol_length]; norm_num⟩ = (10200) := rfl
  have h1 : table_10_bcol.get ⟨246, by rw [table_10_bcol_length]; norm_num⟩ = (10300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10300 : table_10_next (10300) = (10400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 246
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨246, by rw [table_10_bcol_length]; norm_num⟩ = (10300) := rfl
  have h1 : table_10_bcol.get ⟨247, by rw [table_10_bcol_length]; norm_num⟩ = (10400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10400 : table_10_next (10400) = (10500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 247
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨247, by rw [table_10_bcol_length]; norm_num⟩ = (10400) := rfl
  have h1 : table_10_bcol.get ⟨248, by rw [table_10_bcol_length]; norm_num⟩ = (10500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10500 : table_10_next (10500) = (10600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 248
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨248, by rw [table_10_bcol_length]; norm_num⟩ = (10500) := rfl
  have h1 : table_10_bcol.get ⟨249, by rw [table_10_bcol_length]; norm_num⟩ = (10600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10600 : table_10_next (10600) = (10700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 249
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨249, by rw [table_10_bcol_length]; norm_num⟩ = (10600) := rfl
  have h1 : table_10_bcol.get ⟨250, by rw [table_10_bcol_length]; norm_num⟩ = (10700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10700 : table_10_next (10700) = (10800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 250
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨250, by rw [table_10_bcol_length]; norm_num⟩ = (10700) := rfl
  have h1 : table_10_bcol.get ⟨251, by rw [table_10_bcol_length]; norm_num⟩ = (10800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10800 : table_10_next (10800) = (10900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 251
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨251, by rw [table_10_bcol_length]; norm_num⟩ = (10800) := rfl
  have h1 : table_10_bcol.get ⟨252, by rw [table_10_bcol_length]; norm_num⟩ = (10900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_10900 : table_10_next (10900) = (11000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 252
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨252, by rw [table_10_bcol_length]; norm_num⟩ = (10900) := rfl
  have h1 : table_10_bcol.get ⟨253, by rw [table_10_bcol_length]; norm_num⟩ = (11000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11000 : table_10_next (11000) = (11100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 253
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨253, by rw [table_10_bcol_length]; norm_num⟩ = (11000) := rfl
  have h1 : table_10_bcol.get ⟨254, by rw [table_10_bcol_length]; norm_num⟩ = (11100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11100 : table_10_next (11100) = (11200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 254
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨254, by rw [table_10_bcol_length]; norm_num⟩ = (11100) := rfl
  have h1 : table_10_bcol.get ⟨255, by rw [table_10_bcol_length]; norm_num⟩ = (11200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11200 : table_10_next (11200) = (11300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 255
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨255, by rw [table_10_bcol_length]; norm_num⟩ = (11200) := rfl
  have h1 : table_10_bcol.get ⟨256, by rw [table_10_bcol_length]; norm_num⟩ = (11300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11300 : table_10_next (11300) = (11400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 256
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨256, by rw [table_10_bcol_length]; norm_num⟩ = (11300) := rfl
  have h1 : table_10_bcol.get ⟨257, by rw [table_10_bcol_length]; norm_num⟩ = (11400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11400 : table_10_next (11400) = (11500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 257
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨257, by rw [table_10_bcol_length]; norm_num⟩ = (11400) := rfl
  have h1 : table_10_bcol.get ⟨258, by rw [table_10_bcol_length]; norm_num⟩ = (11500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11500 : table_10_next (11500) = (11600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 258
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨258, by rw [table_10_bcol_length]; norm_num⟩ = (11500) := rfl
  have h1 : table_10_bcol.get ⟨259, by rw [table_10_bcol_length]; norm_num⟩ = (11600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11600 : table_10_next (11600) = (11700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 259
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨259, by rw [table_10_bcol_length]; norm_num⟩ = (11600) := rfl
  have h1 : table_10_bcol.get ⟨260, by rw [table_10_bcol_length]; norm_num⟩ = (11700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11700 : table_10_next (11700) = (11800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 260
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨260, by rw [table_10_bcol_length]; norm_num⟩ = (11700) := rfl
  have h1 : table_10_bcol.get ⟨261, by rw [table_10_bcol_length]; norm_num⟩ = (11800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11800 : table_10_next (11800) = (11900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 261
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨261, by rw [table_10_bcol_length]; norm_num⟩ = (11800) := rfl
  have h1 : table_10_bcol.get ⟨262, by rw [table_10_bcol_length]; norm_num⟩ = (11900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_11900 : table_10_next (11900) = (12000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 262
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨262, by rw [table_10_bcol_length]; norm_num⟩ = (11900) := rfl
  have h1 : table_10_bcol.get ⟨263, by rw [table_10_bcol_length]; norm_num⟩ = (12000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12000 : table_10_next (12000) = (12100) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 263
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨263, by rw [table_10_bcol_length]; norm_num⟩ = (12000) := rfl
  have h1 : table_10_bcol.get ⟨264, by rw [table_10_bcol_length]; norm_num⟩ = (12100) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12100 : table_10_next (12100) = (12200) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 264
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨264, by rw [table_10_bcol_length]; norm_num⟩ = (12100) := rfl
  have h1 : table_10_bcol.get ⟨265, by rw [table_10_bcol_length]; norm_num⟩ = (12200) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12200 : table_10_next (12200) = (12300) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 265
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨265, by rw [table_10_bcol_length]; norm_num⟩ = (12200) := rfl
  have h1 : table_10_bcol.get ⟨266, by rw [table_10_bcol_length]; norm_num⟩ = (12300) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12300 : table_10_next (12300) = (12400) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 266
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨266, by rw [table_10_bcol_length]; norm_num⟩ = (12300) := rfl
  have h1 : table_10_bcol.get ⟨267, by rw [table_10_bcol_length]; norm_num⟩ = (12400) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12400 : table_10_next (12400) = (12500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 267
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨267, by rw [table_10_bcol_length]; norm_num⟩ = (12400) := rfl
  have h1 : table_10_bcol.get ⟨268, by rw [table_10_bcol_length]; norm_num⟩ = (12500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12500 : table_10_next (12500) = (12600) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 268
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨268, by rw [table_10_bcol_length]; norm_num⟩ = (12500) := rfl
  have h1 : table_10_bcol.get ⟨269, by rw [table_10_bcol_length]; norm_num⟩ = (12600) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12600 : table_10_next (12600) = (12700) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 269
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨269, by rw [table_10_bcol_length]; norm_num⟩ = (12600) := rfl
  have h1 : table_10_bcol.get ⟨270, by rw [table_10_bcol_length]; norm_num⟩ = (12700) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12700 : table_10_next (12700) = (12800) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 270
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨270, by rw [table_10_bcol_length]; norm_num⟩ = (12700) := rfl
  have h1 : table_10_bcol.get ⟨271, by rw [table_10_bcol_length]; norm_num⟩ = (12800) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12800 : table_10_next (12800) = (12900) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 271
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨271, by rw [table_10_bcol_length]; norm_num⟩ = (12800) := rfl
  have h1 : table_10_bcol.get ⟨272, by rw [table_10_bcol_length]; norm_num⟩ = (12900) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_12900 : table_10_next (12900) = (13000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 272
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨272, by rw [table_10_bcol_length]; norm_num⟩ = (12900) := rfl
  have h1 : table_10_bcol.get ⟨273, by rw [table_10_bcol_length]; norm_num⟩ = (13000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_13000 : table_10_next (13000) = (13500) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 273
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨273, by rw [table_10_bcol_length]; norm_num⟩ = (13000) := rfl
  have h1 : table_10_bcol.get ⟨274, by rw [table_10_bcol_length]; norm_num⟩ = (13500) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_13500 : table_10_next (13500) = (13800.7464) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 274
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨274, by rw [table_10_bcol_length]; norm_num⟩ = (13500) := rfl
  have h1 : table_10_bcol.get ⟨275, by rw [table_10_bcol_length]; norm_num⟩ = (13800.7464) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_13800_7464 : table_10_next (13800.7464) = (14000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 275
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨275, by rw [table_10_bcol_length]; norm_num⟩ = (13800.7464) := rfl
  have h1 : table_10_bcol.get ⟨276, by rw [table_10_bcol_length]; norm_num⟩ = (14000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_14000 : table_10_next (14000) = (15000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 276
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨276, by rw [table_10_bcol_length]; norm_num⟩ = (14000) := rfl
  have h1 : table_10_bcol.get ⟨277, by rw [table_10_bcol_length]; norm_num⟩ = (15000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_15000 : table_10_next (15000) = (16000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 277
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨277, by rw [table_10_bcol_length]; norm_num⟩ = (15000) := rfl
  have h1 : table_10_bcol.get ⟨278, by rw [table_10_bcol_length]; norm_num⟩ = (16000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_16000 : table_10_next (16000) = (17000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 278
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨278, by rw [table_10_bcol_length]; norm_num⟩ = (16000) := rfl
  have h1 : table_10_bcol.get ⟨279, by rw [table_10_bcol_length]; norm_num⟩ = (17000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_17000 : table_10_next (17000) = (18000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 279
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨279, by rw [table_10_bcol_length]; norm_num⟩ = (17000) := rfl
  have h1 : table_10_bcol.get ⟨280, by rw [table_10_bcol_length]; norm_num⟩ = (18000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_18000 : table_10_next (18000) = (19000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 280
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨280, by rw [table_10_bcol_length]; norm_num⟩ = (18000) := rfl
  have h1 : table_10_bcol.get ⟨281, by rw [table_10_bcol_length]; norm_num⟩ = (19000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_19000 : table_10_next (19000) = (20000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 281
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨281, by rw [table_10_bcol_length]; norm_num⟩ = (19000) := rfl
  have h1 : table_10_bcol.get ⟨282, by rw [table_10_bcol_length]; norm_num⟩ = (20000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_20000 : table_10_next (20000) = (21000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 282
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨282, by rw [table_10_bcol_length]; norm_num⟩ = (20000) := rfl
  have h1 : table_10_bcol.get ⟨283, by rw [table_10_bcol_length]; norm_num⟩ = (21000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_21000 : table_10_next (21000) = (22000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 283
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨283, by rw [table_10_bcol_length]; norm_num⟩ = (21000) := rfl
  have h1 : table_10_bcol.get ⟨284, by rw [table_10_bcol_length]; norm_num⟩ = (22000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_22000 : table_10_next (22000) = (23000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 284
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨284, by rw [table_10_bcol_length]; norm_num⟩ = (22000) := rfl
  have h1 : table_10_bcol.get ⟨285, by rw [table_10_bcol_length]; norm_num⟩ = (23000) := rfl
  rw [h0, h1] at h
  exact h

theorem table_10_next_cert_23000 : table_10_next (23000) = (24000) := by
  have h := table_10_next_get table_10_bcol_sortedLT table_10_bcol_le_K 285
    (by rw [table_10_bcol_length]; norm_num)
  have h0 : table_10_bcol.get ⟨285, by rw [table_10_bcol_length]; norm_num⟩ = (23000) := rfl
  have h1 : table_10_bcol.get ⟨286, by rw [table_10_bcol_length]; norm_num⟩ = (24000) := rfl
  rw [h0, h1] at h
  exact h

set_option maxRecDepth 100000 in
theorem table_10_next_cert_24000 : table_10_next (24000) = (25000) := by
  apply table_10_next_eq_of_adjacent
  · norm_num
  · exact table_10_bs_mem_iff.mpr (Or.inr (by norm_num [K]))
  · intro z hz hgt
    rcases table_10_bs_mem_iff.mp hz with hzL | hzK
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hzL
      have hlast_idx : (j : Fin table_10_bcol.length) ≤
          (⟨286, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) := by
        simp only [Fin.le_def]
        have hjlt : (j : ℕ) < 287 := by
          simpa [table_10_bcol_length] using j.2
        omega
      have hle_last : table_10_bcol.get j ≤
          table_10_bcol.get ⟨286, by rw [table_10_bcol_length]; norm_num⟩ :=
        table_10_bcol_sortedLT.strictMono_get.monotone hlast_idx
      have hlast : table_10_bcol.get ⟨286, by rw [table_10_bcol_length]; norm_num⟩ = (24000) := rfl
      rw [hj, hlast] at hle_last
      exact False.elim ((not_lt_of_ge hle_last) hgt)
    · rw [hzK]
      norm_num [K]

end BKLNW
