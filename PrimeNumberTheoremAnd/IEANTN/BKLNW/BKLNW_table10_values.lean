import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Table 10 printed-value certificates from the checked b-column. -/

namespace BKLNW

open Real

set_option maxRecDepth 100000 in
theorem table_10_row20_values_of_mem (B : ℕ → ℝ)
    (h : ((20), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8077e-3 ∧ B 2 = 3.6154e-2 ∧ B 3 = 7.2309e-1 ∧
      B 4 = 1.4462e1 ∧ B 5 = 2.9160e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨0, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨0, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 0 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨0, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨0, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((20 : ℝ), 1.8077e-3, 3.6154e-2, 7.2309e-1, 1.4462e1, 2.9160e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row21_values_of_mem (B : ℕ → ℝ)
    (h : ((21), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1458e-3 ∧ B 2 = 2.4062e-2 ∧ B 3 = 5.0530e-1 ∧
      B 4 = 1.0611e1 ∧ B 5 = 2.2284e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨1, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨1, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 1 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨1, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨1, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((21 : ℝ), 1.1458e-3, 2.4062e-2, 5.0530e-1, 1.0611e1, 2.2284e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row22_values_of_mem (B : ℕ → ℝ)
    (h : ((22), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.2527e-4 ∧ B 2 = 1.5956e-2 ∧ B 3 = 3.5103e-1 ∧
      B 4 = 7.7226e0 ∧ B 5 = 1.6990e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨2, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨2, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 2 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨2, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨2, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((22 : ℝ), 7.2527e-4, 1.5956e-2, 3.5103e-1, 7.7226e0, 1.6990e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row23_values_of_mem (B : ℕ → ℝ)
    (h : ((23), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5848e-4 ∧ B 2 = 1.0545e-2 ∧ B 3 = 2.4254e-1 ∧
      B 4 = 5.5783e0 ∧ B 5 = 1.2830e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨3, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨3, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 3 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨3, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨3, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((23 : ℝ), 4.5848e-4, 1.0545e-2, 2.4254e-1, 5.5783e0, 1.2830e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row24_values_of_mem (B : ℕ → ℝ)
    (h : ((24), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8945e-4 ∧ B 2 = 6.9468e-3 ∧ B 3 = 1.6672e-1 ∧
      B 4 = 4.0013e0 ∧ B 5 = 9.6032e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨4, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨4, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 4 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨4, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨4, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((24 : ℝ), 2.8945e-4, 6.9468e-3, 1.6672e-1, 4.0013e0, 9.6032e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row25_values_of_mem (B : ℕ → ℝ)
    (h : ((25), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8251e-4 ∧ B 2 = 4.5626e-3 ∧ B 3 = 1.1407e-1 ∧
      B 4 = 2.8516e0 ∧ B 5 = 7.1291e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨5, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨5, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 5 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨5, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨5, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((25 : ℝ), 1.8251e-4, 4.5626e-3, 1.1407e-1, 2.8516e0, 7.1291e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row26_values_of_mem (B : ℕ → ℝ)
    (h : ((26), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1493e-4 ∧ B 2 = 2.9882e-3 ∧ B 3 = 7.7694e-2 ∧
      B 4 = 2.0200e0 ∧ B 5 = 5.2521e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨6, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨6, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 6 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨6, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨6, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((26 : ℝ), 1.1493e-4, 2.9882e-3, 7.7694e-2, 2.0200e0, 5.2521e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row27_values_of_mem (B : ℕ → ℝ)
    (h : ((27), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.2293e-5 ∧ B 2 = 1.9519e-3 ∧ B 3 = 5.2702e-2 ∧
      B 4 = 1.4229e0 ∧ B 5 = 3.8419e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨7, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨7, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 7 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨7, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨7, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((27 : ℝ), 7.2293e-5, 1.9519e-3, 5.2702e-2, 1.4229e0, 3.8419e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row28_values_of_mem (B : ℕ → ℝ)
    (h : ((28), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5421e-5 ∧ B 2 = 1.2718e-3 ∧ B 3 = 3.5610e-2 ∧
      B 4 = 9.9708e-1 ∧ B 5 = 2.7918e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨8, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨8, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 8 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨8, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨8, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((28 : ℝ), 4.5421e-5, 1.2718e-3, 3.5610e-2, 9.9708e-1, 2.7918e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row29_values_of_mem (B : ℕ → ℝ)
    (h : ((29), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8507e-5 ∧ B 2 = 8.2670e-4 ∧ B 3 = 2.3974e-2 ∧
      B 4 = 6.9525e-1 ∧ B 5 = 2.0162e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨9, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨9, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 9 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨9, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨9, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((29 : ℝ), 2.8507e-5, 8.2670e-4, 2.3974e-2, 6.9525e-1, 2.0162e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row30_values_of_mem (B : ℕ → ℝ)
    (h : ((30), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7873e-5 ∧ B 2 = 5.3619e-4 ∧ B 3 = 1.6086e-2 ∧
      B 4 = 4.8257e-1 ∧ B 5 = 1.4477e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨10, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨10, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 10 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨10, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨10, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((30 : ℝ), 1.7873e-5, 5.3619e-4, 1.6086e-2, 4.8257e-1, 1.4477e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row31_values_of_mem (B : ℕ → ℝ)
    (h : ((31), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1195e-5 ∧ B 2 = 3.4704e-4 ∧ B 3 = 1.0758e-2 ∧
      B 4 = 3.3350e-1 ∧ B 5 = 1.0339e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨11, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨11, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 11 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨11, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨11, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((31 : ℝ), 1.1195e-5, 3.4704e-4, 1.0758e-2, 3.3350e-1, 1.0339e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row32_values_of_mem (B : ℕ → ℝ)
    (h : ((32), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.0053e-6 ∧ B 2 = 2.2417e-4 ∧ B 3 = 7.1734e-3 ∧
      B 4 = 2.2955e-1 ∧ B 5 = 7.3456e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨12, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨12, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 12 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨12, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨12, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((32 : ℝ), 7.0053e-6, 2.2417e-4, 7.1734e-3, 2.2955e-1, 7.3456e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row33_values_of_mem (B : ℕ → ℝ)
    (h : ((33), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3798e-6 ∧ B 2 = 1.4453e-4 ∧ B 3 = 4.7696e-3 ∧
      B 4 = 1.5740e-1 ∧ B 5 = 5.1941e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨13, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨13, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 13 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨13, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨13, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((33 : ℝ), 4.3798e-6, 1.4453e-4, 4.7696e-3, 1.5740e-1, 5.1941e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row34_values_of_mem (B : ℕ → ℝ)
    (h : ((34), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7360e-6 ∧ B 2 = 9.3023e-5 ∧ B 3 = 3.1628e-3 ∧
      B 4 = 1.0754e-1 ∧ B 5 = 3.6562e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨14, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨14, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 14 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨14, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨14, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((34 : ℝ), 2.7360e-6, 9.3023e-5, 3.1628e-3, 1.0754e-1, 3.6562e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row35_values_of_mem (B : ℕ → ℝ)
    (h : ((35), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7077e-6 ∧ B 2 = 5.9770e-5 ∧ B 3 = 2.0920e-3 ∧
      B 4 = 7.3219e-2 ∧ B 5 = 2.5627e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨15, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨15, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 15 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨15, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨15, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((35 : ℝ), 1.7077e-6, 5.9770e-5, 2.0920e-3, 7.3219e-2, 2.5627e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row36_values_of_mem (B : ℕ → ℝ)
    (h : ((36), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2459e-6 ∧ B 2 = 4.4852e-5 ∧ B 3 = 1.6147e-3 ∧
      B 4 = 5.8128e-2 ∧ B 5 = 2.0926e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨16, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨16, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 16 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨16, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨16, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((36 : ℝ), 1.2459e-6, 4.4852e-5, 1.6147e-3, 5.8128e-2, 2.0926e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row37_values_of_mem (B : ℕ → ℝ)
    (h : ((37), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0581e-6 ∧ B 2 = 3.9148e-5 ∧ B 3 = 1.4485e-3 ∧
      B 4 = 5.3593e-2 ∧ B 5 = 1.9830e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨17, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨17, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 17 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨17, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨17, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((37 : ℝ), 1.0581e-6, 3.9148e-5, 1.4485e-3, 5.3593e-2, 1.9830e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row38_values_of_mem (B : ℕ → ℝ)
    (h : ((38), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.4814e-7 ∧ B 2 = 3.6029e-5 ∧ B 3 = 1.3691e-3 ∧
      B 4 = 5.2611e-2 ∧ B 5 = 2.0518e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨18, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨18, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 18 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨18, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨18, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((38 : ℝ), 9.4814e-7, 3.6029e-5, 1.3691e-3, 5.2611e-2, 2.0518e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row39_values_of_mem (B : ℕ → ℝ)
    (h : ((39), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.8692e-7 ∧ B 2 = 3.4590e-5 ∧ B 3 = 1.3697e-3 ∧
      B 4 = 5.4788e-2 ∧ B 5 = 2.1915e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨19, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨19, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 19 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨19, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨19, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((39 : ℝ), 8.8692e-7, 3.4590e-5, 1.3697e-3, 5.4788e-2, 2.1915e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row40_values_of_mem (B : ℕ → ℝ)
    (h : ((40), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5607e-7 ∧ B 2 = 3.4611e-5 ∧ B 3 = 1.4190e-3 ∧
      B 4 = 5.8181e-2 ∧ B 5 = 2.3854e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨20, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨20, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 20 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨20, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨20, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((40 : ℝ), 8.5607e-7, 3.4611e-5, 1.4190e-3, 5.8181e-2, 2.3854e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row41_values_of_mem (B : ℕ → ℝ)
    (h : ((41), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.4416e-7 ∧ B 2 = 3.5451e-5 ∧ B 3 = 1.4889e-3 ∧
      B 4 = 6.2535e-2 ∧ B 5 = 2.6265e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨21, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨21, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 21 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨21, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨21, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((41 : ℝ), 8.4416e-7, 3.5451e-5, 1.4889e-3, 6.2535e-2, 2.6265e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row42_values_of_mem (B : ℕ → ℝ)
    (h : ((42), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5132e-7 ∧ B 2 = 3.6607e-5 ∧ B 3 = 1.5741e-3 ∧
      B 4 = 6.7686e-2 ∧ B 5 = 2.9105e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨22, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨22, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 22 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨22, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨22, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((42 : ℝ), 8.5132e-7, 3.6607e-5, 1.5741e-3, 6.7686e-2, 2.9105e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row43_values_of_mem (B : ℕ → ℝ)
    (h : ((43), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5986e-7 ∧ B 2 = 3.7618e-5 ∧ B 3 = 1.6458e-3 ∧
      B 4 = 7.2000e-2 ∧ B 5 = 3.1500e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨23, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨23, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 23 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨23, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨23, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((43 : ℝ), 8.5986e-7, 3.7618e-5, 1.6458e-3, 7.2000e-2, 3.1500e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row19log10_values_of_mem (B : ℕ → ℝ)
    (h : ((19 * Real.log 10), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.6315e-7 ∧ B 2 = 3.7978e-5 ∧ B 3 = 1.6711e-3 ∧
      B 4 = 7.3526e-2 ∧ B 5 = 3.2352e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨24, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨24, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 24 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨24, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨24, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((19 * Real.log 10 : ℝ), 8.6315e-7, 3.7978e-5, 1.6711e-3, 7.3526e-2, 3.2352e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row44_values_of_mem (B : ℕ → ℝ)
    (h : ((44), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.8162e-7 ∧ B 2 = 3.5173e-5 ∧ B 3 = 1.5828e-3 ∧
      B 4 = 7.1225e-2 ∧ B 5 = 3.2052e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨25, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨25, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 25 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨25, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨25, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((44 : ℝ), 7.8162e-7, 3.5173e-5, 1.5828e-3, 7.1225e-2, 3.2052e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row45_values_of_mem (B : ℕ → ℝ)
    (h : ((45), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0646e-7 ∧ B 2 = 2.3297e-5 ∧ B 3 = 1.0717e-3 ∧
      B 4 = 4.9297e-2 ∧ B 5 = 2.2677e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨26, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨26, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 26 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨26, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨26, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((45 : ℝ), 5.0646e-7, 2.3297e-5, 1.0717e-3, 4.9297e-2, 2.2677e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row46_values_of_mem (B : ℕ → ℝ)
    (h : ((46), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2935e-7 ∧ B 2 = 1.5479e-5 ∧ B 3 = 7.2752e-4 ∧
      B 4 = 3.4194e-2 ∧ B 5 = 1.6071e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨27, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨27, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 27 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨27, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨27, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((46 : ℝ), 3.2935e-7, 1.5479e-5, 7.2752e-4, 3.4194e-2, 1.6071e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row47_values_of_mem (B : ℕ → ℝ)
    (h : ((47), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1307e-7 ∧ B 2 = 1.0228e-5 ∧ B 3 = 4.9092e-4 ∧
      B 4 = 2.3564e-2 ∧ B 5 = 1.1311e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨28, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨28, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 28 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨28, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨28, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((47 : ℝ), 2.1307e-7, 1.0228e-5, 4.9092e-4, 2.3564e-2, 1.1311e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row48_values_of_mem (B : ℕ → ℝ)
    (h : ((48), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3790e-7 ∧ B 2 = 6.7572e-6 ∧ B 3 = 3.3110e-4 ∧
      B 4 = 1.6224e-2 ∧ B 5 = 7.9498e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨29, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨29, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 29 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨29, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨29, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((48 : ℝ), 1.3790e-7, 6.7572e-6, 3.3110e-4, 1.6224e-2, 7.9498e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row49_values_of_mem (B : ℕ → ℝ)
    (h : ((49), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.9139e-8 ∧ B 2 = 4.4570e-6 ∧ B 3 = 2.2285e-4 ∧
      B 4 = 1.1142e-2 ∧ B 5 = 5.5712e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨30, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨30, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 30 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨30, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨30, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((49 : ℝ), 8.9139e-8, 4.4570e-6, 2.2285e-4, 1.1142e-2, 5.5712e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row50_values_of_mem (B : ℕ → ℝ)
    (h : ((50), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7545e-8 ∧ B 2 = 2.9348e-6 ∧ B 3 = 1.4967e-4 ∧
      B 4 = 7.6334e-3 ∧ B 5 = 3.8930e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨31, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨31, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 31 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨31, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨31, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((50 : ℝ), 5.7545e-8, 2.9348e-6, 1.4967e-4, 7.6334e-3, 3.8930e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row51_values_of_mem (B : ℕ → ℝ)
    (h : ((51), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7146e-8 ∧ B 2 = 1.9316e-6 ∧ B 3 = 1.0044e-4 ∧
      B 4 = 5.2231e-3 ∧ B 5 = 2.7160e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨32, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨32, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 32 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨32, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨32, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((51 : ℝ), 3.7146e-8, 1.9316e-6, 1.0044e-4, 5.2231e-3, 2.7160e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row52_values_of_mem (B : ℕ → ℝ)
    (h : ((52), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3898e-8 ∧ B 2 = 1.2666e-6 ∧ B 3 = 6.7130e-5 ∧
      B 4 = 3.5579e-3 ∧ B 5 = 1.8857e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨33, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨33, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 33 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨33, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨33, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((52 : ℝ), 2.3898e-8, 1.2666e-6, 6.7130e-5, 3.5579e-3, 1.8857e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row53_values_of_mem (B : ℕ → ℝ)
    (h : ((53), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5373e-8 ∧ B 2 = 8.3012e-7 ∧ B 3 = 4.4826e-5 ∧
      B 4 = 2.4206e-3 ∧ B 5 = 1.3071e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨34, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨34, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 34 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨34, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨34, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((53 : ℝ), 1.5373e-8, 8.3012e-7, 4.4826e-5, 2.4206e-3, 1.3071e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row54_values_of_mem (B : ℕ → ℝ)
    (h : ((54), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8777e-9 ∧ B 2 = 5.4328e-7 ∧ B 3 = 2.9880e-5 ∧
      B 4 = 1.6434e-3 ∧ B 5 = 9.0388e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨35, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨35, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 35 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨35, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨35, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((54 : ℝ), 9.8777e-9, 5.4328e-7, 2.9880e-5, 1.6434e-3, 9.0388e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row55_values_of_mem (B : ℕ → ℝ)
    (h : ((55), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.3417e-9 ∧ B 2 = 3.5514e-7 ∧ B 3 = 1.9888e-5 ∧
      B 4 = 1.1137e-3 ∧ B 5 = 6.2367e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨36, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨36, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 36 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨36, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨36, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((55 : ℝ), 6.3417e-9, 3.5514e-7, 1.9888e-5, 1.1137e-3, 6.2367e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row56_values_of_mem (B : ℕ → ℝ)
    (h : ((56), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0668e-9 ∧ B 2 = 2.3181e-7 ∧ B 3 = 1.3213e-5 ∧
      B 4 = 7.5315e-4 ∧ B 5 = 4.2929e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨37, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨37, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 37 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨37, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨37, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((56 : ℝ), 4.0668e-9, 2.3181e-7, 1.3213e-5, 7.5315e-4, 4.2929e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row57_values_of_mem (B : ℕ → ℝ)
    (h : ((57), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6047e-9 ∧ B 2 = 1.5107e-7 ∧ B 3 = 8.7623e-6 ∧
      B 4 = 5.0821e-4 ∧ B 5 = 2.9476e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨38, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨38, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 38 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨38, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨38, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((57 : ℝ), 2.6047e-9, 1.5107e-7, 8.7623e-6, 5.0821e-4, 2.9476e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row58_values_of_mem (B : ℕ → ℝ)
    (h : ((58), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6805e-9 ∧ B 2 = 9.9147e-8 ∧ B 3 = 5.8497e-6 ∧
      B 4 = 3.4513e-4 ∧ B 5 = 2.0363e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨39, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨39, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 39 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨39, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨39, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((58 : ℝ), 1.6805e-9, 9.9147e-8, 5.8497e-6, 3.4513e-4, 2.0363e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row59_values_of_mem (B : ℕ → ℝ)
    (h : ((59), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1120e-9 ∧ B 2 = 6.6721e-8 ∧ B 3 = 4.0033e-6 ∧
      B 4 = 2.4020e-4 ∧ B 5 = 1.4412e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨40, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨40, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 40 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨40, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨40, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((59 : ℝ), 1.1120e-9, 6.6721e-8, 4.0033e-6, 2.4020e-4, 1.4412e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row60_values_of_mem (B : ℕ → ℝ)
    (h : ((60), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9446e-10 ∧ B 2 = 5.1640e-8 ∧ B 3 = 3.3566e-6 ∧
      B 4 = 2.1818e-4 ∧ B 5 = 1.4182e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨41, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨41, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 41 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨41, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨41, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((60 : ℝ), 7.9446e-10, 5.1640e-8, 3.3566e-6, 2.1818e-4, 1.4182e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row65_values_of_mem (B : ℕ → ℝ)
    (h : ((65), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5003e-10 ∧ B 2 = 1.7502e-8 ∧ B 3 = 1.2252e-6 ∧
      B 4 = 8.5761e-5 ∧ B 5 = 6.0033e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨42, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨42, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 42 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨42, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨42, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((65 : ℝ), 2.5003e-10, 1.7502e-8, 1.2252e-6, 8.5761e-5, 6.0033e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row70_values_of_mem (B : ℕ → ℝ)
    (h : ((70), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0943e-10 ∧ B 2 = 1.5707e-8 ∧ B 3 = 1.1780e-6 ∧
      B 4 = 8.8353e-5 ∧ B 5 = 6.6265e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨43, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨43, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 43 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨43, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨43, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((70 : ℝ), 2.0943e-10, 1.5707e-8, 1.1780e-6, 8.8353e-5, 6.6265e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row75_values_of_mem (B : ℕ → ℝ)
    (h : ((75), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1629e-10 ∧ B 2 = 1.7303e-8 ∧ B 3 = 1.3842e-6 ∧
      B 4 = 1.1074e-4 ∧ B 5 = 8.8591e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨44, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨44, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 44 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨44, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨44, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((75 : ℝ), 2.1629e-10, 1.7303e-8, 1.3842e-6, 1.1074e-4, 8.8591e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row80_values_of_mem (B : ℕ → ℝ)
    (h : ((80), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2192e-10 ∧ B 2 = 1.8863e-8 ∧ B 3 = 1.6034e-6 ∧
      B 4 = 1.3629e-4 ∧ B 5 = 1.1584e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨45, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨45, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 45 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨45, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨45, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((80 : ℝ), 2.2192e-10, 1.8863e-8, 1.6034e-6, 1.3629e-4, 1.1584e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row85_values_of_mem (B : ℕ → ℝ)
    (h : ((85), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3123e-10 ∧ B 2 = 2.0811e-8 ∧ B 3 = 1.8730e-6 ∧
      B 4 = 1.6857e-4 ∧ B 5 = 1.5171e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨46, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨46, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 46 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨46, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨46, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((85 : ℝ), 2.3123e-10, 2.0811e-8, 1.8730e-6, 1.6857e-4, 1.5171e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row90_values_of_mem (B : ℕ → ℝ)
    (h : ((90), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3952e-10 ∧ B 2 = 2.2755e-8 ∧ B 3 = 2.1617e-6 ∧
      B 4 = 2.0536e-4 ∧ B 5 = 1.9509e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨47, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨47, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 47 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨47, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨47, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((90 : ℝ), 2.3952e-10, 2.2755e-8, 2.1617e-6, 2.0536e-4, 1.9509e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row95_values_of_mem (B : ℕ → ℝ)
    (h : ((95), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4919e-10 ∧ B 2 = 2.4919e-8 ∧ B 3 = 2.4919e-6 ∧
      B 4 = 2.4919e-4 ∧ B 5 = 2.4919e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨48, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨48, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 48 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨48, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨48, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((95 : ℝ), 2.4919e-10, 2.4919e-8, 2.4919e-6, 2.4919e-4, 2.4919e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row100_values_of_mem (B : ℕ → ℝ)
    (h : ((100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.9060e-10 ∧ B 2 = 9.8120e-8 ∧ B 3 = 1.9624e-5 ∧
      B 4 = 3.9248e-3 ∧ B 5 = 7.8496e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨49, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨49, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 49 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨49, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨49, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((100 : ℝ), 4.9060e-10, 9.8120e-8, 1.9624e-5, 3.9248e-3, 7.8496e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row200_values_of_mem (B : ℕ → ℝ)
    (h : ((200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5446e-10 ∧ B 2 = 1.9634e-7 ∧ B 3 = 5.8902e-5 ∧
      B 4 = 1.7671e-2 ∧ B 5 = 5.3012e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨50, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨50, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 50 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨50, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨50, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((200 : ℝ), 6.5446e-10, 1.9634e-7, 5.8902e-5, 1.7671e-2, 5.3012e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row300_values_of_mem (B : ℕ → ℝ)
    (h : ((300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.3609e-10 ∧ B 2 = 3.3444e-7 ∧ B 3 = 1.3378e-4 ∧
      B 4 = 5.3510e-2 ∧ B 5 = 2.1404e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨51, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨51, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 51 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨51, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨51, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((300 : ℝ), 8.3609e-10, 3.3444e-7, 1.3378e-4, 5.3510e-2, 2.1404e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row400_values_of_mem (B : ℕ → ℝ)
    (h : ((400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0199e-9 ∧ B 2 = 5.0995e-7 ∧ B 3 = 2.5498e-4 ∧
      B 4 = 1.2749e-1 ∧ B 5 = 6.3744e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨52, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨52, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 52 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨52, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨52, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((400 : ℝ), 1.0199e-9, 5.0995e-7, 2.5498e-4, 1.2749e-1, 6.3744e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row500_values_of_mem (B : ℕ → ℝ)
    (h : ((500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1999e-9 ∧ B 2 = 7.1995e-7 ∧ B 3 = 4.3197e-4 ∧
      B 4 = 2.5918e-1 ∧ B 5 = 1.5551e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨53, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨53, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 53 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨53, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨53, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((500 : ℝ), 1.1999e-9, 7.1995e-7, 4.3197e-4, 2.5918e-1, 1.5551e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row600_values_of_mem (B : ℕ → ℝ)
    (h : ((600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3923e-9 ∧ B 2 = 9.7458e-7 ∧ B 3 = 6.8221e-4 ∧
      B 4 = 4.7755e-1 ∧ B 5 = 3.3428e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨54, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨54, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 54 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨54, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨54, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((600 : ℝ), 1.3923e-9, 9.7458e-7, 6.8221e-4, 4.7755e-1, 3.3428e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row700_values_of_mem (B : ℕ → ℝ)
    (h : ((700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5812e-9 ∧ B 2 = 1.2649e-6 ∧ B 3 = 1.0119e-3 ∧
      B 4 = 8.0955e-1 ∧ B 5 = 6.4764e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨55, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨55, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 55 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨55, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨55, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((700 : ℝ), 1.5812e-9, 1.2649e-6, 1.0119e-3, 8.0955e-1, 6.4764e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row800_values_of_mem (B : ℕ → ℝ)
    (h : ((800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7704e-9 ∧ B 2 = 1.5934e-6 ∧ B 3 = 1.4340e-3 ∧
      B 4 = 1.2906e0 ∧ B 5 = 1.1616e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨56, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨56, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 56 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨56, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨56, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((800 : ℝ), 1.7704e-9, 1.5934e-6, 1.4340e-3, 1.2906e0, 1.1616e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row900_values_of_mem (B : ℕ → ℝ)
    (h : ((900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9599e-9 ∧ B 2 = 1.9599e-6 ∧ B 3 = 1.9599e-3 ∧
      B 4 = 1.9599e0 ∧ B 5 = 1.9599e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨57, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨57, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 57 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨57, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨57, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((900 : ℝ), 1.9599e-9, 1.9599e-6, 1.9599e-3, 1.9599e0, 1.9599e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1000_values_of_mem (B : ℕ → ℝ)
    (h : ((1000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9213e-9 ∧ B 2 = 4.3819e-6 ∧ B 3 = 6.5729e-3 ∧
      B 4 = 9.8593e0 ∧ B 5 = 1.4789e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨58, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨58, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 58 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨58, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨58, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1000 : ℝ), 2.9213e-9, 4.3819e-6, 6.5729e-3, 9.8593e0, 1.4789e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1500_values_of_mem (B : ℕ → ℝ)
    (h : ((1500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0988e-9 ∧ B 2 = 4.9581e-6 ∧ B 3 = 7.9330e-3 ∧
      B 4 = 1.2693e1 ∧ B 5 = 2.0309e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨59, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨59, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 59 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨59, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨59, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1500 : ℝ), 3.0988e-9, 4.9581e-6, 7.9330e-3, 1.2693e1, 2.0309e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1600_values_of_mem (B : ℕ → ℝ)
    (h : ((1600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2797e-9 ∧ B 2 = 5.5755e-6 ∧ B 3 = 9.4783e-3 ∧
      B 4 = 1.6113e1 ∧ B 5 = 2.7392e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨60, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨60, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 60 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨60, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨60, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1600 : ℝ), 3.2797e-9, 5.5755e-6, 9.4783e-3, 1.6113e1, 2.7392e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1700_values_of_mem (B : ℕ → ℝ)
    (h : ((1700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3247e-9 ∧ B 2 = 5.7350e-6 ∧ B 3 = 9.8929e-3 ∧
      B 4 = 1.7065e1 ∧ B 5 = 2.9438e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨61, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨61, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 61 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨61, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨61, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1700 : ℝ), 3.3247e-9, 5.7350e-6, 9.8929e-3, 1.7065e1, 2.9438e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1725_values_of_mem (B : ℕ → ℝ)
    (h : ((1725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3721e-9 ∧ B 2 = 5.9011e-6 ∧ B 3 = 1.0327e-2 ∧
      B 4 = 1.8072e1 ∧ B 5 = 3.1626e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨62, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨62, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 62 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨62, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨62, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1725 : ℝ), 3.3721e-9, 5.9011e-6, 1.0327e-2, 1.8072e1, 3.1626e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1750_values_of_mem (B : ℕ → ℝ)
    (h : ((1750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4195e-9 ∧ B 2 = 6.0696e-6 ∧ B 3 = 1.0774e-2 ∧
      B 4 = 1.9123e1 ∧ B 5 = 3.3943e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨63, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨63, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 63 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨63, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨63, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1750 : ℝ), 3.4195e-9, 6.0696e-6, 1.0774e-2, 1.9123e1, 3.3943e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1775_values_of_mem (B : ℕ → ℝ)
    (h : ((1775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4669e-9 ∧ B 2 = 6.2404e-6 ∧ B 3 = 1.1233e-2 ∧
      B 4 = 2.0219e1 ∧ B 5 = 3.6394e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨64, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨64, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 64 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨64, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨64, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1775 : ℝ), 3.4669e-9, 6.2404e-6, 1.1233e-2, 2.0219e1, 3.6394e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1800_values_of_mem (B : ℕ → ℝ)
    (h : ((1800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5143e-9 ∧ B 2 = 6.4136e-6 ∧ B 3 = 1.1705e-2 ∧
      B 4 = 2.1361e1 ∧ B 5 = 3.8984e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨65, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨65, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 65 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨65, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨65, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1800 : ℝ), 3.5143e-9, 6.4136e-6, 1.1705e-2, 2.1361e1, 3.8984e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1825_values_of_mem (B : ℕ → ℝ)
    (h : ((1825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5617e-9 ∧ B 2 = 6.5892e-6 ∧ B 3 = 1.2190e-2 ∧
      B 4 = 2.2552e1 ∧ B 5 = 4.1720e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨66, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨66, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 66 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨66, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨66, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1825 : ℝ), 3.5617e-9, 6.5892e-6, 1.2190e-2, 2.2552e1, 4.1720e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1850_values_of_mem (B : ℕ → ℝ)
    (h : ((1850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6091e-9 ∧ B 2 = 6.7671e-6 ∧ B 3 = 1.2688e-2 ∧
      B 4 = 2.3791e1 ∧ B 5 = 4.4608e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨67, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨67, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 67 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨67, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨67, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1850 : ℝ), 3.6091e-9, 6.7671e-6, 1.2688e-2, 2.3791e1, 4.4608e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1875_values_of_mem (B : ℕ → ℝ)
    (h : ((1875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6566e-9 ∧ B 2 = 6.9475e-6 ∧ B 3 = 1.3200e-2 ∧
      B 4 = 2.5080e1 ∧ B 5 = 4.7653e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨68, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨68, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 68 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨68, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨68, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1875 : ℝ), 3.6566e-9, 6.9475e-6, 1.3200e-2, 2.5080e1, 4.7653e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1900_values_of_mem (B : ℕ → ℝ)
    (h : ((1900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7040e-9 ∧ B 2 = 7.1302e-6 ∧ B 3 = 1.3726e-2 ∧
      B 4 = 2.6422e1 ∧ B 5 = 5.0862e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨69, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨69, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 69 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨69, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨69, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1900 : ℝ), 3.7040e-9, 7.1302e-6, 1.3726e-2, 2.6422e1, 5.0862e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1925_values_of_mem (B : ℕ → ℝ)
    (h : ((1925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7514e-9 ∧ B 2 = 7.3152e-6 ∧ B 3 = 1.4265e-2 ∧
      B 4 = 2.7816e1 ∧ B 5 = 5.4241e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨70, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨70, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 70 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨70, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨70, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1925 : ℝ), 3.7514e-9, 7.3152e-6, 1.4265e-2, 2.7816e1, 5.4241e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1950_values_of_mem (B : ℕ → ℝ)
    (h : ((1950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7988e-9 ∧ B 2 = 7.5026e-6 ∧ B 3 = 1.4818e-2 ∧
      B 4 = 2.9265e1 ∧ B 5 = 5.7798e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨71, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨71, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 71 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨71, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨71, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1950 : ℝ), 3.7988e-9, 7.5026e-6, 1.4818e-2, 2.9265e1, 5.7798e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row1975_values_of_mem (B : ℕ → ℝ)
    (h : ((1975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8462e-9 ∧ B 2 = 7.6924e-6 ∧ B 3 = 1.5385e-2 ∧
      B 4 = 3.0770e1 ∧ B 5 = 6.1540e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨72, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨72, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 72 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨72, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨72, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((1975 : ℝ), 3.8462e-9, 7.6924e-6, 1.5385e-2, 3.0770e1, 6.1540e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2000_values_of_mem (B : ℕ → ℝ)
    (h : ((2000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8937e-9 ∧ B 2 = 7.8847e-6 ∧ B 3 = 1.5966e-2 ∧
      B 4 = 3.2332e1 ∧ B 5 = 6.5472e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨73, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨73, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 73 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨73, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨73, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2000 : ℝ), 3.8937e-9, 7.8847e-6, 1.5966e-2, 3.2332e1, 6.5472e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2025_values_of_mem (B : ℕ → ℝ)
    (h : ((2025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9411e-9 ∧ B 2 = 8.0792e-6 ∧ B 3 = 1.6562e-2 ∧
      B 4 = 3.3953e1 ∧ B 5 = 6.9603e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨74, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨74, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 74 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨74, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨74, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2025 : ℝ), 3.9411e-9, 8.0792e-6, 1.6562e-2, 3.3953e1, 6.9603e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2050_values_of_mem (B : ℕ → ℝ)
    (h : ((2050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9885e-9 ∧ B 2 = 8.2761e-6 ∧ B 3 = 1.7173e-2 ∧
      B 4 = 3.5634e1 ∧ B 5 = 7.3940e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨75, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨75, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 75 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨75, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨75, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2050 : ℝ), 3.9885e-9, 8.2761e-6, 1.7173e-2, 3.5634e1, 7.3940e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2075_values_of_mem (B : ℕ → ℝ)
    (h : ((2075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0359e-9 ∧ B 2 = 8.4754e-6 ∧ B 3 = 1.7798e-2 ∧
      B 4 = 3.7377e1 ∧ B 5 = 7.8491e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨76, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨76, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 76 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨76, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨76, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2075 : ℝ), 4.0359e-9, 8.4754e-6, 1.7798e-2, 3.7377e1, 7.8491e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2100_values_of_mem (B : ℕ → ℝ)
    (h : ((2100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0833e-9 ∧ B 2 = 8.6771e-6 ∧ B 3 = 1.8439e-2 ∧
      B 4 = 3.9182e1 ∧ B 5 = 8.3262e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨77, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨77, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 77 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨77, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨77, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2100 : ℝ), 4.0833e-9, 8.6771e-6, 1.8439e-2, 3.9182e1, 8.3262e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2125_values_of_mem (B : ℕ → ℝ)
    (h : ((2125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1308e-9 ∧ B 2 = 8.8811e-6 ∧ B 3 = 1.9095e-2 ∧
      B 4 = 4.1053e1 ∧ B 5 = 8.8264e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨78, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨78, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 78 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨78, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨78, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2125 : ℝ), 4.1308e-9, 8.8811e-6, 1.9095e-2, 4.1053e1, 8.8264e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2150_values_of_mem (B : ℕ → ℝ)
    (h : ((2150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1782e-9 ∧ B 2 = 9.0875e-6 ∧ B 3 = 1.9765e-2 ∧
      B 4 = 4.2990e1 ∧ B 5 = 9.3503e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨79, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨79, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 79 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨79, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨79, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2150 : ℝ), 4.1782e-9, 9.0875e-6, 1.9765e-2, 4.2990e1, 9.3503e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2175_values_of_mem (B : ℕ → ℝ)
    (h : ((2175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2256e-9 ∧ B 2 = 9.2963e-6 ∧ B 3 = 2.0452e-2 ∧
      B 4 = 4.4994e1 ∧ B 5 = 9.8987e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨80, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨80, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 80 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨80, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨80, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2175 : ℝ), 4.2256e-9, 9.2963e-6, 2.0452e-2, 4.4994e1, 9.8987e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2200_values_of_mem (B : ℕ → ℝ)
    (h : ((2200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2730e-9 ∧ B 2 = 9.5075e-6 ∧ B 3 = 2.1154e-2 ∧
      B 4 = 4.7068e1 ∧ B 5 = 1.0473e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨81, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨81, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 81 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨81, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨81, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2200 : ℝ), 4.2730e-9, 9.5075e-6, 2.1154e-2, 4.7068e1, 1.0473e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2225_values_of_mem (B : ℕ → ℝ)
    (h : ((2225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3204e-9 ∧ B 2 = 9.7210e-6 ∧ B 3 = 2.1872e-2 ∧
      B 4 = 4.9212e1 ∧ B 5 = 1.1073e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨82, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨82, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 82 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨82, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨82, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2225 : ℝ), 4.3204e-9, 9.7210e-6, 2.1872e-2, 4.9212e1, 1.1073e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2250_values_of_mem (B : ℕ → ℝ)
    (h : ((2250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3679e-9 ∧ B 2 = 9.9369e-6 ∧ B 3 = 2.2607e-2 ∧
      B 4 = 5.1430e1 ∧ B 5 = 1.1700e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨83, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨83, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 83 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨83, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨83, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2250 : ℝ), 4.3679e-9, 9.9369e-6, 2.2607e-2, 5.1430e1, 1.1700e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2275_values_of_mem (B : ℕ → ℝ)
    (h : ((2275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4153e-9 ∧ B 2 = 1.0155e-5 ∧ B 3 = 2.3357e-2 ∧
      B 4 = 5.3721e1 ∧ B 5 = 1.2356e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨84, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨84, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 84 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨84, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨84, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2275 : ℝ), 4.4153e-9, 1.0155e-5, 2.3357e-2, 5.3721e1, 1.2356e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2300_values_of_mem (B : ℕ → ℝ)
    (h : ((2300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4627e-9 ∧ B 2 = 1.0376e-5 ∧ B 3 = 2.4124e-2 ∧
      B 4 = 5.6088e1 ∧ B 5 = 1.3040e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨85, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨85, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 85 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨85, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨85, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2300 : ℝ), 4.4627e-9, 1.0376e-5, 2.4124e-2, 5.6088e1, 1.3040e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2325_values_of_mem (B : ℕ → ℝ)
    (h : ((2325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4062e-9 ∧ B 2 = 1.0355e-5 ∧ B 3 = 2.4333e-2 ∧
      B 4 = 5.7184e1 ∧ B 5 = 1.3438e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨86, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨86, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 86 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨86, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨86, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2325 : ℝ), 4.4062e-9, 1.0355e-5, 2.4333e-2, 5.7184e1, 1.3438e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2350_values_of_mem (B : ℕ → ℝ)
    (h : ((2350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2245e-9 ∧ B 2 = 1.0033e-5 ∧ B 3 = 2.3829e-2 ∧
      B 4 = 5.6593e1 ∧ B 5 = 1.3441e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨87, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨87, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 87 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨87, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨87, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2350 : ℝ), 4.2245e-9, 1.0033e-5, 2.3829e-2, 5.6593e1, 1.3441e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2375_values_of_mem (B : ℕ → ℝ)
    (h : ((2375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0498e-9 ∧ B 2 = 9.7196e-6 ∧ B 3 = 2.3327e-2 ∧
      B 4 = 5.5985e1 ∧ B 5 = 1.3436e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨88, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨88, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 88 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨88, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨88, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2375 : ℝ), 4.0498e-9, 9.7196e-6, 2.3327e-2, 5.5985e1, 1.3436e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2400_values_of_mem (B : ℕ → ℝ)
    (h : ((2400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8820e-9 ∧ B 2 = 9.4139e-6 ∧ B 3 = 2.2829e-2 ∧
      B 4 = 5.5360e1 ∧ B 5 = 1.3425e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨89, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨89, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 89 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨89, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨89, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2400 : ℝ), 3.8820e-9, 9.4139e-6, 2.2829e-2, 5.5360e1, 1.3425e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2425_values_of_mem (B : ℕ → ℝ)
    (h : ((2425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4832e-9 ∧ B 2 = 8.5339e-6 ∧ B 3 = 2.0908e-2 ∧
      B 4 = 5.1225e1 ∧ B 5 = 1.2550e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨90, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨90, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 90 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨90, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨90, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2425 : ℝ), 3.4832e-9, 8.5339e-6, 2.0908e-2, 5.1225e1, 1.2550e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2450_values_of_mem (B : ℕ → ℝ)
    (h : ((2450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0228e-9 ∧ B 2 = 7.4814e-6 ∧ B 3 = 1.8517e-2 ∧
      B 4 = 4.5828e1 ∧ B 5 = 1.1343e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨91, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨91, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 91 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨91, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨91, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2450 : ℝ), 3.0228e-9, 7.4814e-6, 1.8517e-2, 4.5828e1, 1.1343e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2475_values_of_mem (B : ℕ → ℝ)
    (h : ((2475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6278e-9 ∧ B 2 = 6.5696e-6 ∧ B 3 = 1.6424e-2 ∧
      B 4 = 4.1060e1 ∧ B 5 = 1.0265e5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨92, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨92, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 92 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨92, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨92, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2475 : ℝ), 2.6278e-9, 6.5696e-6, 1.6424e-2, 4.1060e1, 1.0265e5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2500_values_of_mem (B : ℕ → ℝ)
    (h : ((2500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2884e-9 ∧ B 2 = 5.7783e-6 ∧ B 3 = 1.4590e-2 ∧
      B 4 = 3.6840e1 ∧ B 5 = 9.3021e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨93, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨93, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 93 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨93, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨93, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2500 : ℝ), 2.2884e-9, 5.7783e-6, 1.4590e-2, 3.6840e1, 9.3021e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2525_values_of_mem (B : ℕ → ℝ)
    (h : ((2525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9873e-9 ∧ B 2 = 5.0676e-6 ∧ B 3 = 1.2922e-2 ∧
      B 4 = 3.2952e1 ∧ B 5 = 8.4027e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨94, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨94, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 94 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨94, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨94, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2525 : ℝ), 1.9873e-9, 5.0676e-6, 1.2922e-2, 3.2952e1, 8.4027e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2550_values_of_mem (B : ℕ → ℝ)
    (h : ((2550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7270e-9 ∧ B 2 = 4.4470e-6 ∧ B 3 = 1.1451e-2 ∧
      B 4 = 2.9487e1 ∧ B 5 = 7.5928e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨95, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨95, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 95 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨95, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨95, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2550 : ℝ), 1.7270e-9, 4.4470e-6, 1.1451e-2, 2.9487e1, 7.5928e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2575_values_of_mem (B : ℕ → ℝ)
    (h : ((2575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4992e-9 ∧ B 2 = 3.8979e-6 ∧ B 3 = 1.0135e-2 ∧
      B 4 = 2.6350e1 ∧ B 5 = 6.8509e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨96, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨96, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 96 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨96, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨96, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2575 : ℝ), 1.4992e-9, 3.8979e-6, 1.0135e-2, 2.6350e1, 6.8509e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2600_values_of_mem (B : ℕ → ℝ)
    (h : ((2600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3022e-9 ∧ B 2 = 3.4184e-6 ∧ B 3 = 8.9732e-3 ∧
      B 4 = 2.3555e1 ∧ B 5 = 6.1831e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨97, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨97, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 97 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨97, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨97, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2600 : ℝ), 1.3022e-9, 3.4184e-6, 8.9732e-3, 2.3555e1, 6.1831e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2625_values_of_mem (B : ℕ → ℝ)
    (h : ((2625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1314e-9 ∧ B 2 = 2.9981e-6 ∧ B 3 = 7.9449e-3 ∧
      B 4 = 2.1054e1 ∧ B 5 = 5.5793e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨98, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨98, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 98 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨98, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨98, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2625 : ℝ), 1.1314e-9, 2.9981e-6, 7.9449e-3, 2.1054e1, 5.5793e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2650_values_of_mem (B : ℕ → ℝ)
    (h : ((2650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8296e-10 ∧ B 2 = 2.6294e-6 ∧ B 3 = 7.0337e-3 ∧
      B 4 = 1.8815e1 ∧ B 5 = 5.0330e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨99, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨99, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 99 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨99, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨99, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2650 : ℝ), 9.8296e-10, 2.6294e-6, 7.0337e-3, 1.8815e1, 5.0330e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2675_values_of_mem (B : ℕ → ℝ)
    (h : ((2675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5431e-10 ∧ B 2 = 2.3067e-6 ∧ B 3 = 6.2279e-3 ∧
      B 4 = 1.6816e1 ∧ B 5 = 4.5402e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨100, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨100, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 100 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨100, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨100, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2675 : ℝ), 8.5431e-10, 2.3067e-6, 6.2279e-3, 1.6816e1, 4.5402e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2700_values_of_mem (B : ℕ → ℝ)
    (h : ((2700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.4234e-10 ∧ B 2 = 2.0229e-6 ∧ B 3 = 5.5123e-3 ∧
      B 4 = 1.5021e1 ∧ B 5 = 4.0932e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨101, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨101, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 101 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨101, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨101, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2700 : ℝ), 7.4234e-10, 2.0229e-6, 5.5123e-3, 1.5021e1, 4.0932e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2725_values_of_mem (B : ℕ → ℝ)
    (h : ((2725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.4498e-10 ∧ B 2 = 1.7737e-6 ∧ B 3 = 4.8777e-3 ∧
      B 4 = 1.3414e1 ∧ B 5 = 3.6887e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨102, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨102, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 102 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨102, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨102, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2725 : ℝ), 6.4498e-10, 1.7737e-6, 4.8777e-3, 1.3414e1, 3.6887e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2750_values_of_mem (B : ℕ → ℝ)
    (h : ((2750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.6071e-10 ∧ B 2 = 1.5560e-6 ∧ B 3 = 4.3178e-3 ∧
      B 4 = 1.1982e1 ∧ B 5 = 3.3250e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨103, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨103, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 103 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨103, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨103, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2750 : ℝ), 5.6071e-10, 1.5560e-6, 4.3178e-3, 1.1982e1, 3.3250e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2775_values_of_mem (B : ℕ → ℝ)
    (h : ((2775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.8730e-10 ∧ B 2 = 1.3644e-6 ∧ B 3 = 3.8204e-3 ∧
      B 4 = 1.0697e1 ∧ B 5 = 2.9952e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨104, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨104, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 104 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨104, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨104, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2775 : ℝ), 4.8730e-10, 1.3644e-6, 3.8204e-3, 1.0697e1, 2.9952e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2800_values_of_mem (B : ℕ → ℝ)
    (h : ((2800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2388e-10 ∧ B 2 = 1.1975e-6 ∧ B 3 = 3.3829e-3 ∧
      B 4 = 9.5565e0 ∧ B 5 = 2.6997e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨105, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨105, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 105 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨105, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨105, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2800 : ℝ), 4.2388e-10, 1.1975e-6, 3.3829e-3, 9.5565e0, 2.6997e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2825_values_of_mem (B : ℕ → ℝ)
    (h : ((2825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6911e-10 ∧ B 2 = 1.0520e-6 ∧ B 3 = 2.9981e-3 ∧
      B 4 = 8.5446e0 ∧ B 5 = 2.4352e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨106, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨106, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 106 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨106, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨106, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2825 : ℝ), 3.6911e-10, 1.0520e-6, 2.9981e-3, 8.5446e0, 2.4352e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2850_values_of_mem (B : ℕ → ℝ)
    (h : ((2850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2167e-10 ∧ B 2 = 9.2481e-7 ∧ B 3 = 2.6588e-3 ∧
      B 4 = 7.6442e0 ∧ B 5 = 2.1977e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨107, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨107, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 107 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨107, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨107, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2850 : ℝ), 3.2167e-10, 9.2481e-7, 2.6588e-3, 7.6442e0, 2.1977e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2875_values_of_mem (B : ℕ → ℝ)
    (h : ((2875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7953e-10 ∧ B 2 = 8.1062e-7 ∧ B 3 = 2.3508e-3 ∧
      B 4 = 6.8173e0 ∧ B 5 = 1.9770e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨108, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨108, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 108 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨108, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨108, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2875 : ℝ), 2.7953e-10, 8.1062e-7, 2.3508e-3, 6.8173e0, 1.9770e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2900_values_of_mem (B : ℕ → ℝ)
    (h : ((2900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4326e-10 ∧ B 2 = 7.1154e-7 ∧ B 3 = 2.0813e-3 ∧
      B 4 = 6.0877e0 ∧ B 5 = 1.7806e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨109, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨109, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 109 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨109, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨109, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2900 : ℝ), 2.4326e-10, 7.1154e-7, 2.0813e-3, 6.0877e0, 1.7806e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2925_values_of_mem (B : ℕ → ℝ)
    (h : ((2925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1140e-10 ∧ B 2 = 6.2363e-7 ∧ B 3 = 1.8397e-3 ∧
      B 4 = 5.4272e0 ∧ B 5 = 1.6010e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨110, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨110, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 110 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨110, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨110, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2925 : ℝ), 2.1140e-10, 6.2363e-7, 1.8397e-3, 5.4272e0, 1.6010e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2950_values_of_mem (B : ℕ → ℝ)
    (h : ((2950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8391e-10 ∧ B 2 = 5.4712e-7 ∧ B 3 = 1.6277e-3 ∧
      B 4 = 4.8423e0 ∧ B 5 = 1.4406e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨111, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨111, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 111 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨111, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨111, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2950 : ℝ), 1.8391e-10, 5.4712e-7, 1.6277e-3, 4.8423e0, 1.4406e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row2975_values_of_mem (B : ℕ → ℝ)
    (h : ((2975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6015e-10 ∧ B 2 = 4.8044e-7 ∧ B 3 = 1.4413e-3 ∧
      B 4 = 4.3240e0 ∧ B 5 = 1.2972e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨112, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨112, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 112 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨112, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨112, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((2975 : ℝ), 1.6015e-10, 4.8044e-7, 1.4413e-3, 4.3240e0, 1.2972e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3000_values_of_mem (B : ℕ → ℝ)
    (h : ((3000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3914e-10 ∧ B 2 = 4.2090e-7 ∧ B 3 = 1.2732e-3 ∧
      B 4 = 3.8515e0 ∧ B 5 = 1.1651e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨113, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨113, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 113 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨113, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨113, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3000 : ℝ), 1.3914e-10, 4.2090e-7, 1.2732e-3, 3.8515e0, 1.1651e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3025_values_of_mem (B : ℕ → ℝ)
    (h : ((3025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2115e-10 ∧ B 2 = 3.6949e-7 ∧ B 3 = 1.1270e-3 ∧
      B 4 = 3.4372e0 ∧ B 5 = 1.0484e4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨114, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨114, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 114 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨114, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨114, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3025 : ℝ), 1.2115e-10, 3.6949e-7, 1.1270e-3, 3.4372e0, 1.0484e4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3050_values_of_mem (B : ℕ → ℝ)
    (h : ((3050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0531e-10 ∧ B 2 = 3.2382e-7 ∧ B 3 = 9.9573e-4 ∧
      B 4 = 3.0619e0 ∧ B 5 = 9.4152e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨115, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨115, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 115 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨115, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨115, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3050 : ℝ), 1.0531e-10, 3.2382e-7, 9.9573e-4, 3.0619e0, 9.4152e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3075_values_of_mem (B : ℕ → ℝ)
    (h : ((3075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.1684e-11 ∧ B 2 = 2.8422e-7 ∧ B 3 = 8.8108e-4 ∧
      B 4 = 2.7314e0 ∧ B 5 = 8.4672e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨116, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨116, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 116 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨116, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨116, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3075 : ℝ), 9.1684e-11, 2.8422e-7, 8.8108e-4, 2.7314e0, 8.4672e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3100_values_of_mem (B : ℕ → ℝ)
    (h : ((3100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9793e-11 ∧ B 2 = 2.4935e-7 ∧ B 3 = 7.7922e-4 ∧
      B 4 = 2.4351e0 ∧ B 5 = 7.6096e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨117, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨117, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 117 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨117, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨117, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3100 : ℝ), 7.9793e-11, 2.4935e-7, 7.7922e-4, 2.4351e0, 7.6096e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3125_values_of_mem (B : ℕ → ℝ)
    (h : ((3125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.9396e-11 ∧ B 2 = 2.1860e-7 ∧ B 3 = 6.8858e-4 ∧
      B 4 = 2.1690e0 ∧ B 5 = 6.8325e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨118, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨118, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 118 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨118, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨118, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3125 : ℝ), 6.9396e-11, 2.1860e-7, 6.8858e-4, 2.1690e0, 6.8325e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3150_values_of_mem (B : ℕ → ℝ)
    (h : ((3150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0410e-11 ∧ B 2 = 1.9180e-7 ∧ B 3 = 6.0897e-4 ∧
      B 4 = 1.9335e0 ∧ B 5 = 6.1388e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨119, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨119, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 119 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨119, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨119, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3150 : ℝ), 6.0410e-11, 1.9180e-7, 6.0897e-4, 1.9335e0, 6.1388e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3175_values_of_mem (B : ℕ → ℝ)
    (h : ((3175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.2572e-11 ∧ B 2 = 1.6823e-7 ∧ B 3 = 5.3834e-4 ∧
      B 4 = 1.7227e0 ∧ B 5 = 5.5126e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨120, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨120, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 120 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨120, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨120, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3175 : ℝ), 5.2572e-11, 1.6823e-7, 5.3834e-4, 1.7227e0, 5.5126e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3200_values_of_mem (B : ℕ → ℝ)
    (h : ((3200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5782e-11 ∧ B 2 = 1.4765e-7 ∧ B 3 = 4.7616e-4 ∧
      B 4 = 1.5356e0 ∧ B 5 = 4.9524e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨121, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨121, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 121 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨121, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨121, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3200 : ℝ), 4.5782e-11, 1.4765e-7, 4.7616e-4, 1.5356e0, 4.9524e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3225_values_of_mem (B : ℕ → ℝ)
    (h : ((3225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9901e-11 ∧ B 2 = 1.2968e-7 ∧ B 3 = 4.2146e-4 ∧
      B 4 = 1.3697e0 ∧ B 5 = 4.4516e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨122, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨122, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 122 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨122, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨122, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3225 : ℝ), 3.9901e-11, 1.2968e-7, 4.2146e-4, 1.3697e0, 4.4516e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3250_values_of_mem (B : ℕ → ℝ)
    (h : ((3250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4800e-11 ∧ B 2 = 1.1397e-7 ∧ B 3 = 3.7326e-4 ∧
      B 4 = 1.2224e0 ∧ B 5 = 4.0034e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨123, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨123, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 123 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨123, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨123, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3250 : ℝ), 3.4800e-11, 1.1397e-7, 3.7326e-4, 1.2224e0, 4.0034e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3275_values_of_mem (B : ℕ → ℝ)
    (h : ((3275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0332e-11 ∧ B 2 = 1.0009e-7 ∧ B 3 = 3.3031e-4 ∧
      B 4 = 1.0900e0 ∧ B 5 = 3.5971e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨124, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨124, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 124 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨124, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨124, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3275 : ℝ), 3.0332e-11, 1.0009e-7, 3.3031e-4, 1.0900e0, 3.5971e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3300_values_of_mem (B : ℕ → ℝ)
    (h : ((3300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6412e-11 ∧ B 2 = 8.7820e-8 ∧ B 3 = 2.9200e-4 ∧
      B 4 = 9.7090e-1 ∧ B 5 = 3.2283e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨125, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨125, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 125 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨125, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨125, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3300 : ℝ), 2.6412e-11, 8.7820e-8, 2.9200e-4, 9.7090e-1, 3.2283e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3325_values_of_mem (B : ℕ → ℝ)
    (h : ((3325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3015e-11 ∧ B 2 = 7.7100e-8 ∧ B 3 = 2.5829e-4 ∧
      B 4 = 8.6525e-1 ∧ B 5 = 2.8986e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨126, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨126, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 126 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨126, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨126, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3325 : ℝ), 2.3015e-11, 7.7100e-8, 2.5829e-4, 8.6525e-1, 2.8986e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3350_values_of_mem (B : ℕ → ℝ)
    (h : ((3350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0043e-11 ∧ B 2 = 6.7644e-8 ∧ B 3 = 2.2830e-4 ∧
      B 4 = 7.7051e-1 ∧ B 5 = 2.6005e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨127, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨127, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 127 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨127, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨127, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3350 : ℝ), 2.0043e-11, 6.7644e-8, 2.2830e-4, 7.7051e-1, 2.6005e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3375_values_of_mem (B : ℕ → ℝ)
    (h : ((3375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7453e-11 ∧ B 2 = 5.9340e-8 ∧ B 3 = 2.0176e-4 ∧
      B 4 = 6.8597e-1 ∧ B 5 = 2.3323e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨128, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨128, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 128 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨128, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨128, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3375 : ℝ), 1.7453e-11, 5.9340e-8, 2.0176e-4, 6.8597e-1, 2.3323e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3400_values_of_mem (B : ℕ → ℝ)
    (h : ((3400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5212e-11 ∧ B 2 = 5.2099e-8 ∧ B 3 = 1.7844e-4 ∧
      B 4 = 6.1116e-1 ∧ B 5 = 2.0932e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨129, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨129, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 129 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨129, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨129, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3400 : ℝ), 1.5212e-11, 5.2099e-8, 1.7844e-4, 6.1116e-1, 2.0932e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3425_values_of_mem (B : ℕ → ℝ)
    (h : ((3425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3266e-11 ∧ B 2 = 4.5768e-8 ∧ B 3 = 1.5790e-4 ∧
      B 4 = 5.4476e-1 ∧ B 5 = 1.8794e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨130, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨130, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 130 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨130, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨130, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3425 : ℝ), 1.3266e-11, 4.5768e-8, 1.5790e-4, 5.4476e-1, 1.8794e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3450_values_of_mem (B : ℕ → ℝ)
    (h : ((3450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1554e-11 ∧ B 2 = 4.0151e-8 ∧ B 3 = 1.3953e-4 ∧
      B 4 = 4.8485e-1 ∧ B 5 = 1.6849e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨131, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨131, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 131 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨131, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨131, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3450 : ℝ), 1.1554e-11, 4.0151e-8, 1.3953e-4, 4.8485e-1, 1.6849e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3475_values_of_mem (B : ℕ → ℝ)
    (h : ((3475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0059e-11 ∧ B 2 = 3.5206e-8 ∧ B 3 = 1.2322e-4 ∧
      B 4 = 4.3127e-1 ∧ B 5 = 1.5095e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨132, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨132, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 132 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨132, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨132, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3475 : ℝ), 1.0059e-11, 3.5206e-8, 1.2322e-4, 4.3127e-1, 1.5095e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3500_values_of_mem (B : ℕ → ℝ)
    (h : ((3500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.7646e-12 ∧ B 2 = 3.0895e-8 ∧ B 3 = 1.0891e-4 ∧
      B 4 = 3.8389e-1 ∧ B 5 = 1.3532e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨133, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨133, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 133 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨133, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨133, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3500 : ℝ), 8.7646e-12, 3.0895e-8, 1.0891e-4, 3.8389e-1, 1.3532e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3525_values_of_mem (B : ℕ → ℝ)
    (h : ((3525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6403e-12 ∧ B 2 = 2.7123e-8 ∧ B 3 = 9.6287e-5 ∧
      B 4 = 3.4182e-1 ∧ B 5 = 1.2135e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨134, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨134, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 134 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨134, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨134, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3525 : ℝ), 7.6403e-12, 2.7123e-8, 9.6287e-5, 3.4182e-1, 1.2135e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3550_values_of_mem (B : ℕ → ℝ)
    (h : ((3550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6608e-12 ∧ B 2 = 2.3812e-8 ∧ B 3 = 8.5129e-5 ∧
      B 4 = 3.0434e-1 ∧ B 5 = 1.0880e3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨135, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨135, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 135 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨135, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨135, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3550 : ℝ), 6.6608e-12, 2.3812e-8, 8.5129e-5, 3.0434e-1, 1.0880e3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3575_values_of_mem (B : ℕ → ℝ)
    (h : ((3575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8042e-12 ∧ B 2 = 2.0895e-8 ∧ B 3 = 7.5222e-5 ∧
      B 4 = 2.7080e-1 ∧ B 5 = 9.7488e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨136, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨136, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 136 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨136, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨136, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3575 : ℝ), 5.8042e-12, 2.0895e-8, 7.5222e-5, 2.7080e-1, 9.7488e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3600_values_of_mem (B : ℕ → ℝ)
    (h : ((3600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0621e-12 ∧ B 2 = 1.8350e-8 ∧ B 3 = 6.6520e-5 ∧
      B 4 = 2.4113e-1 ∧ B 5 = 8.7411e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨137, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨137, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 137 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨137, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨137, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3600 : ℝ), 5.0621e-12, 1.8350e-8, 6.6520e-5, 2.4113e-1, 8.7411e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3625_values_of_mem (B : ℕ → ℝ)
    (h : ((3625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4165e-12 ∧ B 2 = 1.6120e-8 ∧ B 3 = 5.8839e-5 ∧
      B 4 = 2.1476e-1 ∧ B 5 = 7.8388e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨138, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨138, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 138 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨138, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨138, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3625 : ℝ), 4.4165e-12, 1.6120e-8, 5.8839e-5, 2.1476e-1, 7.8388e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3650_values_of_mem (B : ℕ → ℝ)
    (h : ((3650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8475e-12 ∧ B 2 = 1.4140e-8 ∧ B 3 = 5.1963e-5 ∧
      B 4 = 1.9096e-1 ∧ B 5 = 7.0179e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨139, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨139, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 139 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨139, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨139, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3650 : ℝ), 3.8475e-12, 1.4140e-8, 5.1963e-5, 1.9096e-1, 7.0179e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3675_values_of_mem (B : ℕ → ℝ)
    (h : ((3675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3560e-12 ∧ B 2 = 1.2417e-8 ∧ B 3 = 4.5944e-5 ∧
      B 4 = 1.6999e-1 ∧ B 5 = 6.2897e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨140, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨140, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 140 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨140, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨140, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3675 : ℝ), 3.3560e-12, 1.2417e-8, 4.5944e-5, 1.6999e-1, 6.2897e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3700_values_of_mem (B : ℕ → ℝ)
    (h : ((3700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9296e-12 ∧ B 2 = 1.0913e-8 ∧ B 3 = 4.0649e-5 ∧
      B 4 = 1.5142e-1 ∧ B 5 = 5.6404e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨141, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨141, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 141 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨141, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨141, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3700 : ℝ), 2.9296e-12, 1.0913e-8, 4.0649e-5, 1.5142e-1, 5.6404e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3725_values_of_mem (B : ℕ → ℝ)
    (h : ((3725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5580e-12 ∧ B 2 = 9.5924e-9 ∧ B 3 = 3.5971e-5 ∧
      B 4 = 1.3489e-1 ∧ B 5 = 5.0585e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨142, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨142, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 142 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨142, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨142, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3725 : ℝ), 2.5580e-12, 9.5924e-9, 3.5971e-5, 1.3489e-1, 5.0585e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3750_values_of_mem (B : ℕ → ℝ)
    (h : ((3750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2346e-12 ∧ B 2 = 8.4357e-9 ∧ B 3 = 3.1845e-5 ∧
      B 4 = 1.2022e-1 ∧ B 5 = 4.5381e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨143, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨143, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 143 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨143, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨143, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3750 : ℝ), 2.2346e-12, 8.4357e-9, 3.1845e-5, 1.2022e-1, 4.5381e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3775_values_of_mem (B : ℕ → ℝ)
    (h : ((3775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9513e-12 ∧ B 2 = 7.4151e-9 ∧ B 3 = 2.8177e-5 ∧
      B 4 = 1.0707e-1 ∧ B 5 = 4.0688e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨144, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨144, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 144 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨144, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨144, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3775 : ℝ), 1.9513e-12, 7.4151e-9, 2.8177e-5, 1.0707e-1, 4.0688e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3800_values_of_mem (B : ℕ → ℝ)
    (h : ((3800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7020e-12 ∧ B 2 = 6.5099e-9 ∧ B 3 = 2.4901e-5 ∧
      B 4 = 9.5244e-2 ∧ B 5 = 3.6431e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨145, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨145, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 145 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨145, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨145, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3800 : ℝ), 1.7020e-12, 6.5099e-9, 2.4901e-5, 9.5244e-2, 3.6431e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3825_values_of_mem (B : ℕ → ℝ)
    (h : ((3825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4854e-12 ∧ B 2 = 5.7189e-9 ∧ B 3 = 2.2018e-5 ∧
      B 4 = 8.4768e-2 ∧ B 5 = 3.2636e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨146, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨146, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 146 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨146, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨146, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3825 : ℝ), 1.4854e-12, 5.7189e-9, 2.2018e-5, 8.4768e-2, 3.2636e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3850_values_of_mem (B : ℕ → ℝ)
    (h : ((3850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2972e-12 ∧ B 2 = 5.0267e-9 ∧ B 3 = 1.9478e-5 ∧
      B 4 = 7.5479e-2 ∧ B 5 = 2.9248e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨147, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨147, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 147 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨147, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨147, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3850 : ℝ), 1.2972e-12, 5.0267e-9, 1.9478e-5, 7.5479e-2, 2.9248e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3875_values_of_mem (B : ℕ → ℝ)
    (h : ((3875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1314e-12 ∧ B 2 = 4.4124e-9 ∧ B 3 = 1.7208e-5 ∧
      B 4 = 6.7112e-2 ∧ B 5 = 2.6174e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨148, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨148, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 148 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨148, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨148, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3875 : ℝ), 1.1314e-12, 4.4124e-9, 1.7208e-5, 6.7112e-2, 2.6174e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3900_values_of_mem (B : ℕ → ℝ)
    (h : ((3900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8800e-13 ∧ B 2 = 3.8779e-9 ∧ B 3 = 1.5221e-5 ∧
      B 4 = 5.9741e-2 ∧ B 5 = 2.3449e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨149, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨149, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 149 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨149, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨149, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3900 : ℝ), 9.8800e-13, 3.8779e-9, 1.5221e-5, 5.9741e-2, 2.3449e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3925_values_of_mem (B : ℕ → ℝ)
    (h : ((3925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.6323e-13 ∧ B 2 = 3.4098e-9 ∧ B 3 = 1.3469e-5 ∧
      B 4 = 5.3201e-2 ∧ B 5 = 2.1014e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨150, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨150, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 150 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨150, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨150, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3925 : ℝ), 8.6323e-13, 3.4098e-9, 1.3469e-5, 5.3201e-2, 2.1014e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3950_values_of_mem (B : ℕ → ℝ)
    (h : ((3950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.5449e-13 ∧ B 2 = 2.9991e-9 ∧ B 3 = 1.1922e-5 ∧
      B 4 = 4.7388e-2 ∧ B 5 = 1.8837e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨151, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨151, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 151 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨151, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨151, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3950 : ℝ), 7.5449e-13, 2.9991e-9, 1.1922e-5, 4.7388e-2, 1.8837e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row3975_values_of_mem (B : ℕ → ℝ)
    (h : ((3975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5788e-13 ∧ B 2 = 2.6315e-9 ∧ B 3 = 1.0526e-5 ∧
      B 4 = 4.2104e-2 ∧ B 5 = 1.6842e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨152, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨152, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 152 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨152, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨152, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((3975 : ℝ), 6.5788e-13, 2.6315e-9, 1.0526e-5, 4.2104e-2, 1.6842e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4000_values_of_mem (B : ℕ → ℝ)
    (h : ((4000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7409e-13 ∧ B 2 = 2.3107e-9 ∧ B 3 = 9.3007e-6 ∧
      B 4 = 3.7435e-2 ∧ B 5 = 1.5068e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨153, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨153, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 153 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨153, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨153, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4000 : ℝ), 5.7409e-13, 2.3107e-9, 9.3007e-6, 3.7435e-2, 1.5068e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4025_values_of_mem (B : ℕ → ℝ)
    (h : ((4025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0264e-13 ∧ B 2 = 2.0357e-9 ∧ B 3 = 8.2446e-6 ∧
      B 4 = 3.3391e-2 ∧ B 5 = 1.3523e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨154, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨154, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 154 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨154, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨154, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4025 : ℝ), 5.0264e-13, 2.0357e-9, 8.2446e-6, 3.3391e-2, 1.3523e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4050_values_of_mem (B : ℕ → ℝ)
    (h : ((4050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3803e-13 ∧ B 2 = 1.7850e-9 ∧ B 3 = 7.2737e-6 ∧
      B 4 = 2.9640e-2 ∧ B 5 = 1.2078e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨155, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨155, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 155 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨155, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨155, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4050 : ℝ), 4.3803e-13, 1.7850e-9, 7.2737e-6, 2.9640e-2, 1.2078e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4075_values_of_mem (B : ℕ → ℝ)
    (h : ((4075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8285e-13 ∧ B 2 = 1.5697e-9 ∧ B 3 = 6.4356e-6 ∧
      B 4 = 2.6386e-2 ∧ B 5 = 1.0818e2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨156, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨156, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 156 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨156, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨156, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4075 : ℝ), 3.8285e-13, 1.5697e-9, 6.4356e-6, 2.6386e-2, 1.0818e2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4100_values_of_mem (B : ℕ → ℝ)
    (h : ((4100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3428e-13 ∧ B 2 = 1.3789e-9 ∧ B 3 = 5.6879e-6 ∧
      B 4 = 2.3463e-2 ∧ B 5 = 9.6783e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨157, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨157, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 157 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨157, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨157, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4100 : ℝ), 3.3428e-13, 1.3789e-9, 5.6879e-6, 2.3463e-2, 9.6783e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4125_values_of_mem (B : ℕ → ℝ)
    (h : ((4125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9206e-13 ∧ B 2 = 1.2120e-9 ∧ B 3 = 5.0299e-6 ∧
      B 4 = 2.0874e-2 ∧ B 5 = 8.6628e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨158, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨158, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 158 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨158, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨158, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4125 : ℝ), 2.9206e-13, 1.2120e-9, 5.0299e-6, 2.0874e-2, 8.6628e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4150_values_of_mem (B : ℕ → ℝ)
    (h : ((4150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5566e-13 ∧ B 2 = 1.0674e-9 ∧ B 3 = 4.4563e-6 ∧
      B 4 = 1.8605e-2 ∧ B 5 = 7.7676e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨159, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨159, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 159 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨159, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨159, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4150 : ℝ), 2.5566e-13, 1.0674e-9, 4.4563e-6, 1.8605e-2, 7.7676e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4175_values_of_mem (B : ℕ → ℝ)
    (h : ((4175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2309e-13 ∧ B 2 = 9.3698e-10 ∧ B 3 = 3.9353e-6 ∧
      B 4 = 1.6528e-2 ∧ B 5 = 6.9419e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨160, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨160, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 160 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨160, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨160, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4175 : ℝ), 2.2309e-13, 9.3698e-10, 3.9353e-6, 1.6528e-2, 6.9419e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4200_values_of_mem (B : ℕ → ℝ)
    (h : ((4200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9496e-13 ∧ B 2 = 8.2370e-10 ∧ B 3 = 3.4801e-6 ∧
      B 4 = 1.4704e-2 ∧ B 5 = 6.2122e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨161, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨161, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 161 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨161, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨161, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4200 : ℝ), 1.9496e-13, 8.2370e-10, 3.4801e-6, 1.4704e-2, 6.2122e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4225_values_of_mem (B : ℕ → ℝ)
    (h : ((4225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7047e-13 ∧ B 2 = 7.2449e-10 ∧ B 3 = 3.0791e-6 ∧
      B 4 = 1.3086e-2 ∧ B 5 = 5.5616e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨162, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨162, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 162 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨162, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨162, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4225 : ℝ), 1.7047e-13, 7.2449e-10, 3.0791e-6, 1.3086e-2, 5.5616e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4250_values_of_mem (B : ℕ → ℝ)
    (h : ((4250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4913e-13 ∧ B 2 = 6.3751e-10 ∧ B 3 = 2.7254e-6 ∧
      B 4 = 1.1651e-2 ∧ B 5 = 4.9808e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨163, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨163, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 163 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨163, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨163, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4250 : ℝ), 1.4913e-13, 6.3751e-10, 2.7254e-6, 1.1651e-2, 4.9808e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4275_values_of_mem (B : ℕ → ℝ)
    (h : ((4275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3036e-13 ∧ B 2 = 5.6056e-10 ∧ B 3 = 2.4104e-6 ∧
      B 4 = 1.0365e-2 ∧ B 5 = 4.4568e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨164, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨164, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 164 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨164, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨164, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4275 : ℝ), 1.3036e-13, 5.6056e-10, 2.4104e-6, 1.0365e-2, 4.4568e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4300_values_of_mem (B : ℕ → ℝ)
    (h : ((4300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1396e-13 ∧ B 2 = 4.9288e-10 ∧ B 3 = 2.1317e-6 ∧
      B 4 = 9.2195e-3 ∧ B 5 = 3.9875e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨165, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨165, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 165 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨165, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨165, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4300 : ℝ), 1.1396e-13, 4.9288e-10, 2.1317e-6, 9.2195e-3, 3.9875e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4325_values_of_mem (B : ℕ → ℝ)
    (h : ((4325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.9670e-14 ∧ B 2 = 4.3356e-10 ∧ B 3 = 1.8860e-6 ∧
      B 4 = 8.2041e-3 ∧ B 5 = 3.5688e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨166, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨166, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 166 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨166, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨166, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4325 : ℝ), 9.9670e-14, 4.3356e-10, 1.8860e-6, 8.2041e-3, 3.5688e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4350_values_of_mem (B : ℕ → ℝ)
    (h : ((4350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.7210e-14 ∧ B 2 = 3.8154e-10 ∧ B 3 = 1.6693e-6 ∧
      B 4 = 7.3030e-3 ∧ B 5 = 3.1951e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨167, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨167, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 167 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨167, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨167, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4350 : ℝ), 8.7210e-14, 3.8154e-10, 1.6693e-6, 7.3030e-3, 3.1951e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4375_values_of_mem (B : ℕ → ℝ)
    (h : ((4375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6274e-14 ∧ B 2 = 3.3561e-10 ∧ B 3 = 1.4767e-6 ∧
      B 4 = 6.4973e-3 ∧ B 5 = 2.8588e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨168, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨168, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 168 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨168, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨168, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4375 : ℝ), 7.6274e-14, 3.3561e-10, 1.4767e-6, 6.4973e-3, 2.8588e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4400_values_of_mem (B : ℕ → ℝ)
    (h : ((4400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6744e-14 ∧ B 2 = 2.9534e-10 ∧ B 3 = 1.3069e-6 ∧
      B 4 = 5.7829e-3 ∧ B 5 = 2.5590e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨169, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨169, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 169 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨169, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨169, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4400 : ℝ), 6.6744e-14, 2.9534e-10, 1.3069e-6, 5.7829e-3, 2.5590e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4425_values_of_mem (B : ℕ → ℝ)
    (h : ((4425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8436e-14 ∧ B 2 = 2.6004e-10 ∧ B 3 = 1.1572e-6 ∧
      B 4 = 5.1495e-3 ∧ B 5 = 2.2915e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨170, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨170, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 170 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨170, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨170, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4425 : ℝ), 5.8436e-14, 2.6004e-10, 1.1572e-6, 5.1495e-3, 2.2915e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4450_values_of_mem (B : ℕ → ℝ)
    (h : ((4450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.1174e-14 ∧ B 2 = 2.2901e-10 ∧ B 3 = 1.0248e-6 ∧
      B 4 = 4.5860e-3 ∧ B 5 = 2.0522e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨171, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨171, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 171 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨171, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨171, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4450 : ℝ), 5.1174e-14, 2.2901e-10, 1.0248e-6, 4.5860e-3, 2.0522e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4475_values_of_mem (B : ℕ → ℝ)
    (h : ((4475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4832e-14 ∧ B 2 = 2.0174e-10 ∧ B 3 = 9.0785e-7 ∧
      B 4 = 4.0853e-3 ∧ B 5 = 1.8384e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨172, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨172, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 172 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨172, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨172, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4475 : ℝ), 4.4832e-14, 2.0174e-10, 9.0785e-7, 4.0853e-3, 1.8384e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4500_values_of_mem (B : ℕ → ℝ)
    (h : ((4500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9290e-14 ∧ B 2 = 1.7779e-10 ∧ B 3 = 8.0450e-7 ∧
      B 4 = 3.6403e-3 ∧ B 5 = 1.6473e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨173, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨173, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 173 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨173, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨173, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4500 : ℝ), 3.9290e-14, 1.7779e-10, 8.0450e-7, 3.6403e-3, 1.6473e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4525_values_of_mem (B : ℕ → ℝ)
    (h : ((4525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4446e-14 ∧ B 2 = 1.5673e-10 ∧ B 3 = 7.1312e-7 ∧
      B 4 = 3.2447e-3 ∧ B 5 = 1.4763e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨174, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨174, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 174 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨174, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨174, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4525 : ℝ), 3.4446e-14, 1.5673e-10, 7.1312e-7, 3.2447e-3, 1.4763e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4550_values_of_mem (B : ℕ → ℝ)
    (h : ((4550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0155e-14 ∧ B 2 = 1.3796e-10 ∧ B 3 = 6.3117e-7 ∧
      B 4 = 2.8876e-3 ∧ B 5 = 1.3211e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨175, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨175, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 175 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨175, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨175, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4550 : ℝ), 3.0155e-14, 1.3796e-10, 6.3117e-7, 2.8876e-3, 1.3211e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4575_values_of_mem (B : ℕ → ℝ)
    (h : ((4575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6404e-14 ∧ B 2 = 1.2146e-10 ∧ B 3 = 5.5870e-7 ∧
      B 4 = 2.5700e-3 ∧ B 5 = 1.1822e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨176, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨176, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 176 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨176, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨176, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4575 : ℝ), 2.6404e-14, 1.2146e-10, 5.5870e-7, 2.5700e-3, 1.1822e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4600_values_of_mem (B : ℕ → ℝ)
    (h : ((4600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3157e-14 ∧ B 2 = 1.0710e-10 ∧ B 3 = 4.9535e-7 ∧
      B 4 = 2.2910e-3 ∧ B 5 = 1.0596e1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨177, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨177, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 177 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨177, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨177, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4600 : ℝ), 2.3157e-14, 1.0710e-10, 4.9535e-7, 2.2910e-3, 1.0596e1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4625_values_of_mem (B : ℕ → ℝ)
    (h : ((4625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0259e-14 ∧ B 2 = 9.4206e-11 ∧ B 3 = 4.3806e-7 ∧
      B 4 = 2.0370e-3 ∧ B 5 = 9.4719e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨178, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨178, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 178 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨178, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨178, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4625 : ℝ), 2.0259e-14, 9.4206e-11, 4.3806e-7, 2.0370e-3, 9.4719e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4650_values_of_mem (B : ℕ → ℝ)
    (h : ((4650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7753e-14 ∧ B 2 = 8.2997e-11 ∧ B 3 = 3.8801e-7 ∧
      B 4 = 1.8140e-3 ∧ B 5 = 8.4802e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨179, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨179, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 179 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨179, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨179, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4650 : ℝ), 1.7753e-14, 8.2997e-11, 3.8801e-7, 1.8140e-3, 8.4802e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4675_values_of_mem (B : ℕ → ℝ)
    (h : ((4675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5563e-14 ∧ B 2 = 7.3144e-11 ∧ B 3 = 3.4378e-7 ∧
      B 4 = 1.6158e-3 ∧ B 5 = 7.5941e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨180, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨180, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 180 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨180, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨180, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4675 : ℝ), 1.5563e-14, 7.3144e-11, 3.4378e-7, 1.6158e-3, 7.5941e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4700_values_of_mem (B : ℕ → ℝ)
    (h : ((4700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3648e-14 ∧ B 2 = 6.4486e-11 ∧ B 3 = 3.0470e-7 ∧
      B 4 = 1.4397e-3 ∧ B 5 = 6.8026e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨181, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨181, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 181 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨181, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨181, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4700 : ℝ), 1.3648e-14, 6.4486e-11, 3.0470e-7, 1.4397e-3, 6.8026e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4725_values_of_mem (B : ℕ → ℝ)
    (h : ((4725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1976e-14 ∧ B 2 = 5.6887e-11 ∧ B 3 = 2.7021e-7 ∧
      B 4 = 1.2835e-3 ∧ B 5 = 6.0967e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨182, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨182, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 182 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨182, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨182, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4725 : ℝ), 1.1976e-14, 5.6887e-11, 2.7021e-7, 1.2835e-3, 6.0967e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4750_values_of_mem (B : ℕ → ℝ)
    (h : ((4750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0491e-14 ∧ B 2 = 5.0095e-11 ∧ B 3 = 2.3920e-7 ∧
      B 4 = 1.1422e-3 ∧ B 5 = 5.4540e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨183, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨183, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 183 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨183, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨183, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4750 : ℝ), 1.0491e-14, 5.0095e-11, 2.3920e-7, 1.1422e-3, 5.4540e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4775_values_of_mem (B : ℕ → ℝ)
    (h : ((4775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.1894e-15 ∧ B 2 = 4.4109e-11 ∧ B 3 = 2.1172e-7 ∧
      B 4 = 1.0163e-3 ∧ B 5 = 4.8781e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨184, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨184, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 184 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨184, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨184, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4775 : ℝ), 9.1894e-15, 4.4109e-11, 2.1172e-7, 1.0163e-3, 4.8781e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4800_values_of_mem (B : ℕ → ℝ)
    (h : ((4800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.0537e-15 ∧ B 2 = 3.8859e-11 ∧ B 3 = 1.8750e-7 ∧
      B 4 = 9.0466e-4 ∧ B 5 = 4.3650e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨185, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨185, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 185 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨185, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨185, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4800 : ℝ), 8.0537e-15, 3.8859e-11, 1.8750e-7, 9.0466e-4, 4.3650e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4825_values_of_mem (B : ℕ → ℝ)
    (h : ((4825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.0614e-15 ∧ B 2 = 3.4248e-11 ∧ B 3 = 1.6610e-7 ∧
      B 4 = 8.0560e-4 ∧ B 5 = 3.9072e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨186, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨186, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 186 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨186, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨186, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4825 : ℝ), 7.0614e-15, 3.4248e-11, 1.6610e-7, 8.0560e-4, 3.9072e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4850_values_of_mem (B : ℕ → ℝ)
    (h : ((4850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.1951e-15 ∧ B 2 = 3.0201e-11 ∧ B 3 = 1.4723e-7 ∧
      B 4 = 7.1775e-4 ∧ B 5 = 3.4990e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨187, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨187, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 187 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨187, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨187, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4850 : ℝ), 6.1951e-15, 3.0201e-11, 1.4723e-7, 7.1775e-4, 3.4990e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4875_values_of_mem (B : ℕ → ℝ)
    (h : ((4875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4361e-15 ∧ B 2 = 2.6637e-11 ∧ B 3 = 1.3052e-7 ∧
      B 4 = 6.3955e-4 ∧ B 5 = 3.1338e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨188, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨188, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 188 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨188, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨188, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4875 : ℝ), 5.4361e-15, 2.6637e-11, 1.3052e-7, 6.3955e-4, 3.1338e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4900_values_of_mem (B : ℕ → ℝ)
    (h : ((4900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.7720e-15 ∧ B 2 = 2.3502e-11 ∧ B 3 = 1.1575e-7 ∧
      B 4 = 5.7006e-4 ∧ B 5 = 2.8076e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨189, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨189, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 189 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨189, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨189, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4900 : ℝ), 4.7720e-15, 2.3502e-11, 1.1575e-7, 5.7006e-4, 2.8076e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4925_values_of_mem (B : ℕ → ℝ)
    (h : ((4925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1878e-15 ∧ B 2 = 2.0729e-11 ∧ B 3 = 1.0261e-7 ∧
      B 4 = 5.0792e-4 ∧ B 5 = 2.5142e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨190, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨190, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 190 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨190, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨190, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4925 : ℝ), 4.1878e-15, 2.0729e-11, 1.0261e-7, 5.0792e-4, 2.5142e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4950_values_of_mem (B : ℕ → ℝ)
    (h : ((4950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6731e-15 ∧ B 2 = 1.8274e-11 ∧ B 3 = 9.0911e-8 ∧
      B 4 = 4.5228e-4 ∧ B 5 = 2.2501e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨191, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨191, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 191 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨191, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨191, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4950 : ℝ), 3.6731e-15, 1.8274e-11, 9.0911e-8, 4.5228e-4, 2.2501e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row4975_values_of_mem (B : ℕ → ℝ)
    (h : ((4975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2229e-15 ∧ B 2 = 1.6114e-11 ∧ B 3 = 8.0571e-8 ∧
      B 4 = 4.0286e-4 ∧ B 5 = 2.0143e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨192, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨192, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 192 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨192, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨192, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((4975 : ℝ), 3.2229e-15, 1.6114e-11, 8.0571e-8, 4.0286e-4, 2.0143e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5000_values_of_mem (B : ℕ → ℝ)
    (h : ((5000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8715e-15 ∧ B 2 = 1.4645e-11 ∧ B 3 = 7.4687e-8 ∧
      B 4 = 3.8090e-4 ∧ B 5 = 1.9426e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨193, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨193, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 193 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨193, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨193, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5000 : ℝ), 2.8715e-15, 1.4645e-11, 7.4687e-8, 3.8090e-4, 1.9426e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5100_values_of_mem (B : ℕ → ℝ)
    (h : ((5100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7087e-15 ∧ B 2 = 8.8850e-12 ∧ B 3 = 4.6202e-8 ∧
      B 4 = 2.4025e-4 ∧ B 5 = 1.2493e0 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨194, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨194, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 194 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨194, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨194, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5100 : ℝ), 1.7087e-15, 8.8850e-12, 4.6202e-8, 2.4025e-4, 1.2493e0) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5200_values_of_mem (B : ℕ → ℝ)
    (h : ((5200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0185e-15 ∧ B 2 = 5.3980e-12 ∧ B 3 = 2.8610e-8 ∧
      B 4 = 1.5163e-4 ∧ B 5 = 8.0364e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨195, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨195, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 195 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨195, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨195, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5200 : ℝ), 1.0185e-15, 5.3980e-12, 2.8610e-8, 1.5163e-4, 8.0364e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5300_values_of_mem (B : ℕ → ℝ)
    (h : ((5300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0977e-16 ∧ B 2 = 3.2927e-12 ∧ B 3 = 1.7781e-8 ∧
      B 4 = 9.6016e-5 ∧ B 5 = 5.1849e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨196, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨196, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 196 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨196, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨196, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5300 : ℝ), 6.0977e-16, 3.2927e-12, 1.7781e-8, 9.6016e-5, 5.1849e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5400_values_of_mem (B : ℕ → ℝ)
    (h : ((5400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6472e-16 ∧ B 2 = 2.0059e-12 ∧ B 3 = 1.1033e-8 ∧
      B 4 = 6.0679e-5 ∧ B 5 = 3.3374e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨197, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨197, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 197 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨197, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨197, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5400 : ℝ), 3.6472e-16, 2.0059e-12, 1.1033e-8, 6.0679e-5, 3.3374e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5500_values_of_mem (B : ℕ → ℝ)
    (h : ((5500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1916e-16 ∧ B 2 = 1.2273e-12 ∧ B 3 = 6.8727e-9 ∧
      B 4 = 3.8487e-5 ∧ B 5 = 2.1553e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨198, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨198, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 198 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨198, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨198, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5500 : ℝ), 2.1916e-16, 1.2273e-12, 6.8727e-9, 3.8487e-5, 2.1553e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5600_values_of_mem (B : ℕ → ℝ)
    (h : ((5600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3217e-16 ∧ B 2 = 7.5337e-13 ∧ B 3 = 4.2942e-9 ∧
      B 4 = 2.4477e-5 ∧ B 5 = 1.3952e-1 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨199, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨199, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 199 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨199, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨199, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5600 : ℝ), 1.3217e-16, 7.5337e-13, 4.2942e-9, 2.4477e-5, 1.3952e-1) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5700_values_of_mem (B : ℕ → ℝ)
    (h : ((5700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.0079e-17 ∧ B 2 = 4.6446e-13 ∧ B 3 = 2.6938e-9 ∧
      B 4 = 1.5624e-5 ∧ B 5 = 9.0621e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨200, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨200, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 200 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨200, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨200, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5700 : ℝ), 8.0079e-17, 4.6446e-13, 2.6938e-9, 1.5624e-5, 9.0621e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5800_values_of_mem (B : ℕ → ℝ)
    (h : ((5800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.8518e-17 ∧ B 2 = 2.8626e-13 ∧ B 3 = 1.6889e-9 ∧
      B 4 = 9.9646e-6 ∧ B 5 = 5.8791e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨201, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨201, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 201 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨201, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨201, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5800 : ℝ), 4.8518e-17, 2.8626e-13, 1.6889e-9, 9.9646e-6, 5.8791e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row5900_values_of_mem (B : ℕ → ℝ)
    (h : ((5900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9482e-17 ∧ B 2 = 1.7689e-13 ∧ B 3 = 1.0614e-9 ∧
      B 4 = 6.3682e-6 ∧ B 5 = 3.8209e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨202, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨202, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 202 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨202, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨202, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((5900 : ℝ), 2.9482e-17, 1.7689e-13, 1.0614e-9, 6.3682e-6, 3.8209e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6000_values_of_mem (B : ℕ → ℝ)
    (h : ((6000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7952e-17 ∧ B 2 = 1.0951e-13 ∧ B 3 = 6.6798e-10 ∧
      B 4 = 4.0747e-6 ∧ B 5 = 2.4855e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨203, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨203, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 203 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨203, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨203, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6000 : ℝ), 1.7952e-17, 1.0951e-13, 6.6798e-10, 4.0747e-6, 2.4855e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6100_values_of_mem (B : ℕ → ℝ)
    (h : ((6100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0987e-17 ∧ B 2 = 6.8120e-14 ∧ B 3 = 4.2234e-10 ∧
      B 4 = 2.6185e-6 ∧ B 5 = 1.6235e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨204, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨204, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 204 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨204, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨204, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6100 : ℝ), 1.0987e-17, 6.8120e-14, 4.2234e-10, 2.6185e-6, 1.6235e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6200_values_of_mem (B : ℕ → ℝ)
    (h : ((6200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.7178e-18 ∧ B 2 = 4.2322e-14 ∧ B 3 = 2.6663e-10 ∧
      B 4 = 1.6798e-6 ∧ B 5 = 1.0583e-2 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨205, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨205, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 205 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨205, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨205, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6200 : ℝ), 6.7178e-18, 4.2322e-14, 2.6663e-10, 1.6798e-6, 1.0583e-2) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6300_values_of_mem (B : ℕ → ℝ)
    (h : ((6300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1267e-18 ∧ B 2 = 2.6411e-14 ∧ B 3 = 1.6903e-10 ∧
      B 4 = 1.0818e-6 ∧ B 5 = 6.9235e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨206, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨206, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 206 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨206, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨206, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6300 : ℝ), 4.1267e-18, 2.6411e-14, 1.6903e-10, 1.0818e-6, 6.9235e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6400_values_of_mem (B : ℕ → ℝ)
    (h : ((6400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5481e-18 ∧ B 2 = 1.6563e-14 ∧ B 3 = 1.0766e-10 ∧
      B 4 = 6.9977e-7 ∧ B 5 = 4.5485e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨207, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨207, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 207 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨207, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨207, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6400 : ℝ), 2.5481e-18, 1.6563e-14, 1.0766e-10, 6.9977e-7, 4.5485e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6500_values_of_mem (B : ℕ → ℝ)
    (h : ((6500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5741e-18 ∧ B 2 = 1.0389e-14 ∧ B 3 = 6.8566e-11 ∧
      B 4 = 4.5253e-7 ∧ B 5 = 2.9867e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨208, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨208, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 208 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨208, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨208, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6500 : ℝ), 1.5741e-18, 1.0389e-14, 6.8566e-11, 4.5253e-7, 2.9867e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6600_values_of_mem (B : ℕ → ℝ)
    (h : ((6600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.7287e-19 ∧ B 2 = 6.5182e-15 ∧ B 3 = 4.3672e-11 ∧
      B 4 = 2.9260e-7 ∧ B 5 = 1.9604e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨209, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨209, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 209 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨209, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨209, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6600 : ℝ), 9.7287e-19, 6.5182e-15, 4.3672e-11, 2.9260e-7, 1.9604e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6700_values_of_mem (B : ℕ → ℝ)
    (h : ((6700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0447e-19 ∧ B 2 = 4.1104e-15 ∧ B 3 = 2.7951e-11 ∧
      B 4 = 1.9007e-7 ∧ B 5 = 1.2924e-3 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨210, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨210, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 210 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨210, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨210, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6700 : ℝ), 6.0447e-19, 4.1104e-15, 2.7951e-11, 1.9007e-7, 1.2924e-3) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6800_values_of_mem (B : ℕ → ℝ)
    (h : ((6800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7651e-19 ∧ B 2 = 2.5979e-15 ∧ B 3 = 1.7926e-11 ∧
      B 4 = 1.2369e-7 ∧ B 5 = 8.5344e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨211, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨211, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 211 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨211, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨211, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6800 : ℝ), 3.7651e-19, 2.5979e-15, 1.7926e-11, 1.2369e-7, 8.5344e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row6900_values_of_mem (B : ℕ → ℝ)
    (h : ((6900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3554e-19 ∧ B 2 = 1.6488e-15 ∧ B 3 = 1.1542e-11 ∧
      B 4 = 8.0791e-8 ∧ B 5 = 5.6554e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨212, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨212, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 212 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨212, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨212, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((6900 : ℝ), 2.3554e-19, 1.6488e-15, 1.1542e-11, 8.0791e-8, 5.6554e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7000_values_of_mem (B : ℕ → ℝ)
    (h : ((7000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4744e-19 ∧ B 2 = 1.0468e-15 ∧ B 3 = 7.4322e-12 ∧
      B 4 = 5.2769e-8 ∧ B 5 = 3.7466e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨213, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨213, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 213 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨213, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨213, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7000 : ℝ), 1.4744e-19, 1.0468e-15, 7.4322e-12, 5.2769e-8, 3.7466e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7100_values_of_mem (B : ℕ → ℝ)
    (h : ((7100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.2826e-20 ∧ B 2 = 6.6834e-16 ∧ B 3 = 4.8121e-12 ∧
      B 4 = 3.4647e-8 ∧ B 5 = 2.4946e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨214, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨214, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 214 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨214, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨214, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7100 : ℝ), 9.2826e-20, 6.6834e-16, 4.8121e-12, 3.4647e-8, 2.4946e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7200_values_of_mem (B : ℕ → ℝ)
    (h : ((7200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8601e-20 ∧ B 2 = 4.2779e-16 ∧ B 3 = 3.1229e-12 ∧
      B 4 = 2.2797e-8 ∧ B 5 = 1.6642e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨215, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨215, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 215 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨215, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨215, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7200 : ℝ), 5.8601e-20, 4.2779e-16, 3.1229e-12, 2.2797e-8, 1.6642e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7300_values_of_mem (B : ℕ → ℝ)
    (h : ((7300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7014e-20 ∧ B 2 = 2.7390e-16 ∧ B 3 = 2.0269e-12 ∧
      B 4 = 1.4999e-8 ∧ B 5 = 1.1099e-4 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨216, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨216, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 216 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨216, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨216, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7300 : ℝ), 3.7014e-20, 2.7390e-16, 2.0269e-12, 1.4999e-8, 1.1099e-4) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7400_values_of_mem (B : ℕ → ℝ)
    (h : ((7400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3488e-20 ∧ B 2 = 1.7616e-16 ∧ B 3 = 1.3212e-12 ∧
      B 4 = 9.9091e-9 ∧ B 5 = 7.4318e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨217, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨217, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 217 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨217, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨217, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7400 : ℝ), 2.3488e-20, 1.7616e-16, 1.3212e-12, 9.9091e-9, 7.4318e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7500_values_of_mem (B : ℕ → ℝ)
    (h : ((7500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4907e-20 ∧ B 2 = 1.1330e-16 ∧ B 3 = 8.6105e-13 ∧
      B 4 = 6.5440e-9 ∧ B 5 = 4.9734e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨218, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨218, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 218 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨218, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨218, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7500 : ℝ), 1.4907e-20, 1.1330e-16, 8.6105e-13, 6.5440e-9, 4.9734e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7600_values_of_mem (B : ℕ → ℝ)
    (h : ((7600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.4822e-21 ∧ B 2 = 7.3013e-17 ∧ B 3 = 5.6220e-13 ∧
      B 4 = 4.3289e-9 ∧ B 5 = 3.3333e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨219, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨219, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 219 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨219, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨219, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7600 : ℝ), 9.4822e-21, 7.3013e-17, 5.6220e-13, 4.3289e-9, 3.3333e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7700_values_of_mem (B : ℕ → ℝ)
    (h : ((7700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0569e-21 ∧ B 2 = 4.7244e-17 ∧ B 3 = 3.6850e-13 ∧
      B 4 = 2.8743e-9 ∧ B 5 = 2.2420e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨220, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨220, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 220 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨220, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨220, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7700 : ℝ), 6.0569e-21, 4.7244e-17, 3.6850e-13, 2.8743e-9, 2.2420e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7800_values_of_mem (B : ℕ → ℝ)
    (h : ((7800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8811e-21 ∧ B 2 = 3.0661e-17 ∧ B 3 = 2.4222e-13 ∧
      B 4 = 1.9136e-9 ∧ B 5 = 1.5117e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨221, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨221, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 221 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨221, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨221, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7800 : ℝ), 3.8811e-21, 3.0661e-17, 2.4222e-13, 1.9136e-9, 1.5117e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row7900_values_of_mem (B : ℕ → ℝ)
    (h : ((7900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4928e-21 ∧ B 2 = 1.9942e-17 ∧ B 3 = 1.5954e-13 ∧
      B 4 = 1.2763e-9 ∧ B 5 = 1.0211e-5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨222, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨222, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 222 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨222, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨222, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((7900 : ℝ), 2.4928e-21, 1.9942e-17, 1.5954e-13, 1.2763e-9, 1.0211e-5) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8000_values_of_mem (B : ℕ → ℝ)
    (h : ((8000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6007e-21 ∧ B 2 = 1.2965e-17 ∧ B 3 = 1.0502e-13 ∧
      B 4 = 8.5065e-10 ∧ B 5 = 6.8903e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨223, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨223, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 223 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨223, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨223, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8000 : ℝ), 1.6007e-21, 1.2965e-17, 1.0502e-13, 8.5065e-10, 6.8903e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8100_values_of_mem (B : ℕ → ℝ)
    (h : ((8100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0326e-21 ∧ B 2 = 8.4674e-18 ∧ B 3 = 6.9433e-14 ∧
      B 4 = 5.6935e-10 ∧ B 5 = 4.6687e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨224, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨224, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 224 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨224, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨224, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8100 : ℝ), 1.0326e-21, 8.4674e-18, 6.9433e-14, 5.6935e-10, 4.6687e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8200_values_of_mem (B : ℕ → ℝ)
    (h : ((8200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6828e-22 ∧ B 2 = 5.5467e-18 ∧ B 3 = 4.6038e-14 ∧
      B 4 = 3.8212e-10 ∧ B 5 = 3.1716e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨225, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨225, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 225 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨225, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨225, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8200 : ℝ), 6.6828e-22, 5.5467e-18, 4.6038e-14, 3.8212e-10, 3.1716e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8300_values_of_mem (B : ℕ → ℝ)
    (h : ((8300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3257e-22 ∧ B 2 = 3.6336e-18 ∧ B 3 = 3.0522e-14 ∧
      B 4 = 2.5639e-10 ∧ B 5 = 2.1536e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨226, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨226, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 226 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨226, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨226, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8300 : ℝ), 4.3257e-22, 3.6336e-18, 3.0522e-14, 2.5639e-10, 2.1536e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8400_values_of_mem (B : ℕ → ℝ)
    (h : ((8400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8105e-22 ∧ B 2 = 2.3889e-18 ∧ B 3 = 2.0306e-14 ∧
      B 4 = 1.7260e-10 ∧ B 5 = 1.4671e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨227, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨227, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 227 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨227, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨227, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8400 : ℝ), 2.8105e-22, 2.3889e-18, 2.0306e-14, 1.7260e-10, 1.4671e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8500_values_of_mem (B : ℕ → ℝ)
    (h : ((8500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8315e-22 ∧ B 2 = 1.5751e-18 ∧ B 3 = 1.3546e-14 ∧
      B 4 = 1.1650e-10 ∧ B 5 = 1.0019e-6 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨228, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨228, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 228 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨228, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨228, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8500 : ℝ), 1.8315e-22, 1.5751e-18, 1.3546e-14, 1.1650e-10, 1.0019e-6) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8600_values_of_mem (B : ℕ → ℝ)
    (h : ((8600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1981e-22 ∧ B 2 = 1.0423e-18 ∧ B 3 = 9.0682e-15 ∧
      B 4 = 7.8893e-11 ∧ B 5 = 6.8637e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨229, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨229, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 229 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨229, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨229, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8600 : ℝ), 1.1981e-22, 1.0423e-18, 9.0682e-15, 7.8893e-11, 6.8637e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8700_values_of_mem (B : ℕ → ℝ)
    (h : ((8700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.8220e-23 ∧ B 2 = 6.8834e-19 ∧ B 3 = 6.0574e-15 ∧
      B 4 = 5.3305e-11 ∧ B 5 = 4.6908e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨230, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨230, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 230 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨230, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨230, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8700 : ℝ), 7.8220e-23, 6.8834e-19, 6.0574e-15, 5.3305e-11, 4.6908e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8800_values_of_mem (B : ℕ → ℝ)
    (h : ((8800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.1585e-23 ∧ B 2 = 4.5910e-19 ∧ B 3 = 4.0860e-15 ∧
      B 4 = 3.6366e-11 ∧ B 5 = 3.2365e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨231, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨231, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 231 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨231, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨231, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8800 : ℝ), 5.1585e-23, 4.5910e-19, 4.0860e-15, 3.6366e-11, 3.2365e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row8900_values_of_mem (B : ℕ → ℝ)
    (h : ((8900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3882e-23 ∧ B 2 = 3.0494e-19 ∧ B 3 = 2.7445e-15 ∧
      B 4 = 2.4700e-11 ∧ B 5 = 2.2230e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨232, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨232, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 232 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨232, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨232, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((8900 : ℝ), 3.3882e-23, 3.0494e-19, 2.7445e-15, 2.4700e-11, 2.2230e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9000_values_of_mem (B : ℕ → ℝ)
    (h : ((9000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2252e-23 ∧ B 2 = 2.0250e-19 ∧ B 3 = 1.8427e-15 ∧
      B 4 = 1.6769e-11 ∧ B 5 = 1.5260e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨233, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨233, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 233 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨233, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨233, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9000 : ℝ), 2.2252e-23, 2.0250e-19, 1.8427e-15, 1.6769e-11, 1.5260e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9100_values_of_mem (B : ℕ → ℝ)
    (h : ((9100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4641e-23 ∧ B 2 = 1.3470e-19 ∧ B 3 = 1.2392e-15 ∧
      B 4 = 1.1401e-11 ∧ B 5 = 1.0489e-7 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨234, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨234, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 234 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨234, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨234, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9100 : ℝ), 1.4641e-23, 1.3470e-19, 1.2392e-15, 1.1401e-11, 1.0489e-7) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9200_values_of_mem (B : ℕ → ℝ)
    (h : ((9200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.6777e-24 ∧ B 2 = 9.0003e-20 ∧ B 3 = 8.3703e-16 ∧
      B 4 = 7.7844e-12 ∧ B 5 = 7.2395e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨235, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨235, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 235 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨235, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨235, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9200 : ℝ), 9.6777e-24, 9.0003e-20, 8.3703e-16, 7.7844e-12, 7.2395e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9300_values_of_mem (B : ℕ → ℝ)
    (h : ((9300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.4195e-24 ∧ B 2 = 6.0343e-20 ∧ B 3 = 5.6723e-16 ∧
      B 4 = 5.3319e-12 ∧ B 5 = 5.0120e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨236, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨236, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 236 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨236, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨236, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9300 : ℝ), 6.4195e-24, 6.0343e-20, 5.6723e-16, 5.3319e-12, 5.0120e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9400_values_of_mem (B : ℕ → ℝ)
    (h : ((9400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2972e-24 ∧ B 2 = 4.0823e-20 ∧ B 3 = 3.8782e-16 ∧
      B 4 = 3.6843e-12 ∧ B 5 = 3.5001e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨237, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨237, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 237 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨237, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨237, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9400 : ℝ), 4.2972e-24, 4.0823e-20, 3.8782e-16, 3.6843e-12, 3.5001e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9500_values_of_mem (B : ℕ → ℝ)
    (h : ((9500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8512e-24 ∧ B 2 = 2.7372e-20 ∧ B 3 = 2.6277e-16 ∧
      B 4 = 2.5226e-12 ∧ B 5 = 2.4217e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨238, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨238, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 238 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨238, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨238, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9500 : ℝ), 2.8512e-24, 2.7372e-20, 2.6277e-16, 2.5226e-12, 2.4217e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9600_values_of_mem (B : ℕ → ℝ)
    (h : ((9600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9059e-24 ∧ B 2 = 1.8487e-20 ∧ B 3 = 1.7932e-16 ∧
      B 4 = 1.7395e-12 ∧ B 5 = 1.6873e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨239, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨239, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 239 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨239, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨239, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9600 : ℝ), 1.9059e-24, 1.8487e-20, 1.7932e-16, 1.7395e-12, 1.6873e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9700_values_of_mem (B : ℕ → ℝ)
    (h : ((9700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2689e-24 ∧ B 2 = 1.2435e-20 ∧ B 3 = 1.2187e-16 ∧
      B 4 = 1.1943e-12 ∧ B 5 = 1.1704e-8 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨240, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨240, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 240 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨240, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨240, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9700 : ℝ), 1.2689e-24, 1.2435e-20, 1.2187e-16, 1.1943e-12, 1.1704e-8) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9800_values_of_mem (B : ℕ → ℝ)
    (h : ((9800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.4841e-25 ∧ B 2 = 8.3992e-21 ∧ B 3 = 8.3152e-17 ∧
      B 4 = 8.2321e-13 ∧ B 5 = 8.1497e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨241, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨241, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 241 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨241, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨241, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9800 : ℝ), 8.4841e-25, 8.3992e-21, 8.3152e-17, 8.2321e-13, 8.1497e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row9900_values_of_mem (B : ℕ → ℝ)
    (h : ((9900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7395e-25 ∧ B 2 = 5.7395e-21 ∧ B 3 = 5.7395e-17 ∧
      B 4 = 5.7395e-13 ∧ B 5 = 5.7395e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨242, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨242, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 242 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨242, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨242, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((9900 : ℝ), 5.7395e-25, 5.7395e-21, 5.7395e-17, 5.7395e-13, 5.7395e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10000_values_of_mem (B : ℕ → ℝ)
    (h : ((10000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8228e-25 ∧ B 2 = 3.8610e-21 ∧ B 3 = 3.8996e-17 ∧
      B 4 = 3.9386e-13 ∧ B 5 = 3.9780e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨243, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨243, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 243 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨243, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨243, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10000 : ℝ), 3.8228e-25, 3.8610e-21, 3.8996e-17, 3.9386e-13, 3.9780e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10100_values_of_mem (B : ℕ → ℝ)
    (h : ((10100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5745e-25 ∧ B 2 = 2.6260e-21 ∧ B 3 = 2.6785e-17 ∧
      B 4 = 2.7321e-13 ∧ B 5 = 2.7867e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨244, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨244, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 244 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨244, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨244, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10100 : ℝ), 2.5745e-25, 2.6260e-21, 2.6785e-17, 2.7321e-13, 2.7867e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10200_values_of_mem (B : ℕ → ℝ)
    (h : ((10200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7389e-25 ∧ B 2 = 1.7911e-21 ∧ B 3 = 1.8448e-17 ∧
      B 4 = 1.9001e-13 ∧ B 5 = 1.9571e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨245, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨245, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 245 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨245, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨245, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10200 : ℝ), 1.7389e-25, 1.7911e-21, 1.8448e-17, 1.9001e-13, 1.9571e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10300_values_of_mem (B : ℕ → ℝ)
    (h : ((10300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1734e-25 ∧ B 2 = 1.2203e-21 ∧ B 3 = 1.2691e-17 ∧
      B 4 = 1.3199e-13 ∧ B 5 = 1.3727e-9 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨246, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨246, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 246 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨246, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨246, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10300 : ℝ), 1.1734e-25, 1.2203e-21, 1.2691e-17, 1.3199e-13, 1.3727e-9) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10400_values_of_mem (B : ℕ → ℝ)
    (h : ((10400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9556e-26 ∧ B 2 = 8.3534e-22 ∧ B 3 = 8.7710e-18 ∧
      B 4 = 9.2096e-14 ∧ B 5 = 9.6701e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨247, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨247, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 247 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨247, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨247, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10400 : ℝ), 7.9556e-26, 8.3534e-22, 8.7710e-18, 9.2096e-14, 9.6701e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10500_values_of_mem (B : ℕ → ℝ)
    (h : ((10500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4076e-26 ∧ B 2 = 5.7321e-22 ∧ B 3 = 6.0760e-18 ∧
      B 4 = 6.4406e-14 ∧ B 5 = 6.8270e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨248, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨248, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 248 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨248, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨248, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10500 : ℝ), 5.4076e-26, 5.7321e-22, 6.0760e-18, 6.4406e-14, 6.8270e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10600_values_of_mem (B : ℕ → ℝ)
    (h : ((10600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6845e-26 ∧ B 2 = 3.9424e-22 ∧ B 3 = 4.2184e-18 ∧
      B 4 = 4.5136e-14 ∧ B 5 = 4.8296e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨249, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨249, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 249 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨249, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨249, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10600 : ℝ), 3.6845e-26, 3.9424e-22, 4.2184e-18, 4.5136e-14, 4.8296e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10700_values_of_mem (B : ℕ → ℝ)
    (h : ((10700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5150e-26 ∧ B 2 = 2.7162e-22 ∧ B 3 = 2.9335e-18 ∧
      B 4 = 3.1682e-14 ∧ B 5 = 3.4216e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨250, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨250, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 250 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨250, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨250, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10700 : ℝ), 2.5150e-26, 2.7162e-22, 2.9335e-18, 3.1682e-14, 3.4216e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10800_values_of_mem (B : ℕ → ℝ)
    (h : ((10800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7201e-26 ∧ B 2 = 1.8749e-22 ∧ B 3 = 2.0436e-18 ∧
      B 4 = 2.2276e-14 ∧ B 5 = 2.4280e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨251, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨251, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 251 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨251, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨251, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10800 : ℝ), 1.7201e-26, 1.8749e-22, 2.0436e-18, 2.2276e-14, 2.4280e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row10900_values_of_mem (B : ℕ → ℝ)
    (h : ((10900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1639e-26 ∧ B 2 = 1.2803e-22 ∧ B 3 = 1.4083e-18 ∧
      B 4 = 1.5492e-14 ∧ B 5 = 1.7041e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨252, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨252, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 252 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨252, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨252, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((10900 : ℝ), 1.1639e-26, 1.2803e-22, 1.4083e-18, 1.5492e-14, 1.7041e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11000_values_of_mem (B : ℕ → ℝ)
    (h : ((11000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9283e-27 ∧ B 2 = 8.8005e-23 ∧ B 3 = 9.7685e-19 ∧
      B 4 = 1.0843e-14 ∧ B 5 = 1.2036e-10 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨253, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨253, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 253 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨253, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨253, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11000 : ℝ), 7.9283e-27, 8.8005e-23, 9.7685e-19, 1.0843e-14, 1.2036e-10) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11100_values_of_mem (B : ℕ → ℝ)
    (h : ((11100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4156e-27 ∧ B 2 = 6.0654e-23 ∧ B 3 = 6.7933e-19 ∧
      B 4 = 7.6085e-15 ∧ B 5 = 8.5215e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨254, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨254, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 254 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨254, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨254, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11100 : ℝ), 5.4156e-27, 6.0654e-23, 6.7933e-19, 7.6085e-15, 8.5215e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11200_values_of_mem (B : ℕ → ℝ)
    (h : ((11200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7120e-27 ∧ B 2 = 4.1945e-23 ∧ B 3 = 4.7398e-19 ∧
      B 4 = 5.3560e-15 ∧ B 5 = 6.0522e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨255, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨255, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 255 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨255, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨255, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11200 : ℝ), 3.7120e-27, 4.1945e-23, 4.7398e-19, 5.3560e-15, 6.0522e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11300_values_of_mem (B : ℕ → ℝ)
    (h : ((11300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5509e-27 ∧ B 2 = 2.9080e-23 ∧ B 3 = 3.3151e-19 ∧
      B 4 = 3.7792e-15 ∧ B 5 = 4.3083e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨256, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨256, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 256 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨256, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨256, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11300 : ℝ), 2.5509e-27, 2.9080e-23, 3.3151e-19, 3.7792e-15, 4.3083e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11400_values_of_mem (B : ℕ → ℝ)
    (h : ((11400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7569e-27 ∧ B 2 = 2.0205e-23 ∧ B 3 = 2.3235e-19 ∧
      B 4 = 2.6721e-15 ∧ B 5 = 3.0729e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨257, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨257, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 257 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨257, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨257, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11400 : ℝ), 1.7569e-27, 2.0205e-23, 2.3235e-19, 2.6721e-15, 3.0729e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11500_values_of_mem (B : ℕ → ℝ)
    (h : ((11500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2102e-27 ∧ B 2 = 1.4039e-23 ∧ B 3 = 1.6285e-19 ∧
      B 4 = 1.8890e-15 ∧ B 5 = 2.1913e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨258, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨258, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 258 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨258, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨258, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11500 : ℝ), 1.2102e-27, 1.4039e-23, 1.6285e-19, 1.8890e-15, 2.1913e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11600_values_of_mem (B : ℕ → ℝ)
    (h : ((11600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.3444e-28 ∧ B 2 = 9.7630e-24 ∧ B 3 = 1.1423e-19 ∧
      B 4 = 1.3365e-15 ∧ B 5 = 1.5637e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨259, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨259, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 259 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨259, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨259, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11600 : ℝ), 8.3444e-28, 9.7630e-24, 1.1423e-19, 1.3365e-15, 1.5637e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11700_values_of_mem (B : ℕ → ℝ)
    (h : ((11700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7692e-28 ∧ B 2 = 6.8076e-24 ∧ B 3 = 8.0330e-20 ∧
      B 4 = 9.4789e-16 ∧ B 5 = 1.1185e-11 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨260, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨260, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 260 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨260, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨260, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11700 : ℝ), 5.7692e-28, 6.8076e-24, 8.0330e-20, 9.4789e-16, 1.1185e-11) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11800_values_of_mem (B : ℕ → ℝ)
    (h : ((11800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9987e-28 ∧ B 2 = 4.7584e-24 ∧ B 3 = 5.6625e-20 ∧
      B 4 = 6.7384e-16 ∧ B 5 = 8.0187e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨261, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨261, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 261 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨261, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨261, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11800 : ℝ), 3.9987e-28, 4.7584e-24, 5.6625e-20, 6.7384e-16, 8.0187e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row11900_values_of_mem (B : ℕ → ℝ)
    (h : ((11900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7776e-28 ∧ B 2 = 3.3331e-24 ∧ B 3 = 3.9997e-20 ∧
      B 4 = 4.7996e-16 ∧ B 5 = 5.7595e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨262, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨262, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 262 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨262, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨262, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((11900 : ℝ), 2.7776e-28, 3.3331e-24, 3.9997e-20, 4.7996e-16, 5.7595e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12000_values_of_mem (B : ℕ → ℝ)
    (h : ((12000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9330e-28 ∧ B 2 = 2.3390e-24 ∧ B 3 = 2.8302e-20 ∧
      B 4 = 3.4245e-16 ∧ B 5 = 4.1436e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨263, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨263, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 263 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨263, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨263, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12000 : ℝ), 1.9330e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1436e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12100_values_of_mem (B : ℕ → ℝ)
    (h : ((12100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3477e-28 ∧ B 2 = 1.6442e-24 ∧ B 3 = 2.0060e-20 ∧
      B 4 = 2.4473e-16 ∧ B 5 = 2.9857e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨264, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨264, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 264 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨264, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨264, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12100 : ℝ), 1.3477e-28, 1.6442e-24, 2.0060e-20, 2.4473e-16, 2.9857e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12200_values_of_mem (B : ℕ → ℝ)
    (h : ((12200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.3146e-29 ∧ B 2 = 1.1457e-24 ∧ B 3 = 1.4092e-20 ∧
      B 4 = 1.7333e-16 ∧ B 5 = 2.1320e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨265, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨265, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 265 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨265, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨265, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12200 : ℝ), 9.3146e-29, 1.1457e-24, 1.4092e-20, 1.7333e-16, 2.1320e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12300_values_of_mem (B : ℕ → ℝ)
    (h : ((12300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5069e-29 ∧ B 2 = 8.0685e-25 ∧ B 3 = 1.0005e-20 ∧
      B 4 = 1.2406e-16 ∧ B 5 = 1.5384e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨266, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨266, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 266 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨266, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨266, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12300 : ℝ), 6.5069e-29, 8.0685e-25, 1.0005e-20, 1.2406e-16, 1.5384e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12400_values_of_mem (B : ℕ → ℝ)
    (h : ((12400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5539e-29 ∧ B 2 = 5.6924e-25 ∧ B 3 = 7.1155e-21 ∧
      B 4 = 8.8944e-17 ∧ B 5 = 1.1118e-12 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨267, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨267, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 267 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨267, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨267, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12400 : ℝ), 4.5539e-29, 5.6924e-25, 7.1155e-21, 8.8944e-17, 1.1118e-12) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12500_values_of_mem (B : ℕ → ℝ)
    (h : ((12500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.1924e-29 ∧ B 2 = 4.0224e-25 ∧ B 3 = 5.0682e-21 ∧
      B 4 = 6.3859e-17 ∧ B 5 = 8.0462e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨268, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨268, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 268 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨268, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨268, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12500 : ℝ), 3.1924e-29, 4.0224e-25, 5.0682e-21, 6.3859e-17, 8.0462e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12600_values_of_mem (B : ℕ → ℝ)
    (h : ((12600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2307e-29 ∧ B 2 = 2.8330e-25 ∧ B 3 = 3.5979e-21 ∧
      B 4 = 4.5693e-17 ∧ B 5 = 5.8030e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨269, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨269, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 269 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨269, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨269, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12600 : ℝ), 2.2307e-29, 2.8330e-25, 3.5979e-21, 4.5693e-17, 5.8030e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12700_values_of_mem (B : ℕ → ℝ)
    (h : ((12700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5599e-29 ∧ B 2 = 1.9967e-25 ∧ B 3 = 2.5558e-21 ∧
      B 4 = 3.2714e-17 ∧ B 5 = 4.1873e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨270, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨270, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 270 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨270, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨270, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12700 : ℝ), 1.5599e-29, 1.9967e-25, 2.5558e-21, 3.2714e-17, 4.1873e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12800_values_of_mem (B : ℕ → ℝ)
    (h : ((12800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0940e-29 ∧ B 2 = 1.4112e-25 ∧ B 3 = 1.8205e-21 ∧
      B 4 = 2.3484e-17 ∧ B 5 = 3.0294e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨271, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨271, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 271 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨271, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨271, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12800 : ℝ), 1.0940e-29, 1.4112e-25, 1.8205e-21, 2.3484e-17, 3.0294e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row12900_values_of_mem (B : ℕ → ℝ)
    (h : ((12900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6899e-30 ∧ B 2 = 9.9969e-26 ∧ B 3 = 1.2996e-21 ∧
      B 4 = 1.6895e-17 ∧ B 5 = 2.1963e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨272, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨272, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 272 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨272, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨272, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((12900 : ℝ), 7.6899e-30, 9.9969e-26, 1.2996e-21, 1.6895e-17, 2.1963e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row13000_values_of_mem (B : ℕ → ℝ)
    (h : ((13000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.5830e-30 ∧ B 2 = 7.5370e-26 ∧ B 3 = 1.0175e-21 ∧
      B 4 = 1.3736e-17 ∧ B 5 = 1.8544e-13 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨273, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨273, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 273 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨273, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨273, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((13000 : ℝ), 5.5830e-30, 7.5370e-26, 1.0175e-21, 1.3736e-17, 1.8544e-13) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row13500_values_of_mem (B : ℕ → ℝ)
    (h : ((13500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.9578e-31 ∧ B 2 = 1.3743e-26 ∧ B 3 = 1.8966e-22 ∧
      B 4 = 2.6174e-18 ∧ B 5 = 3.6122e-14 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨274, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨274, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 274 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨274, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨274, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((13500 : ℝ), 9.9578e-31, 1.3743e-26, 1.8966e-22, 2.6174e-18, 3.6122e-14) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row13800_7464_values_of_mem (B : ℕ → ℝ)
    (h : ((13800.7464), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5592e-31 ∧ B 2 = 4.9829e-27 ∧ B 3 = 6.9761e-23 ∧
      B 4 = 9.7665e-19 ∧ B 5 = 1.3673e-14 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨275, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨275, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 275 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨275, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨275, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((13800.7464 : ℝ), 3.5592e-31, 4.9829e-27, 6.9761e-23, 9.7665e-19, 1.3673e-14) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row14000_values_of_mem (B : ℕ → ℝ)
    (h : ((14000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8398e-31 ∧ B 2 = 2.7597e-27 ∧ B 3 = 4.1396e-23 ∧
      B 4 = 6.2094e-19 ∧ B 5 = 9.3141e-15 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨276, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨276, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 276 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨276, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨276, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((14000 : ℝ), 1.8398e-31, 2.7597e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row15000_values_of_mem (B : ℕ → ℝ)
    (h : ((15000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5711e-33 ∧ B 2 = 1.0514e-28 ∧ B 3 = 1.6822e-24 ∧
      B 4 = 2.6915e-20 ∧ B 5 = 4.3065e-16 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨277, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨277, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 277 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨277, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨277, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((15000 : ℝ), 6.5711e-33, 1.0514e-28, 1.6822e-24, 2.6915e-20, 4.3065e-16) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row16000_values_of_mem (B : ℕ → ℝ)
    (h : ((16000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5738e-34 ∧ B 2 = 4.3755e-30 ∧ B 3 = 7.4384e-26 ∧
      B 4 = 1.2645e-21 ∧ B 5 = 2.1497e-17 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨278, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨278, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 278 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨278, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨278, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((16000 : ℝ), 2.5738e-34, 4.3755e-30, 7.4384e-26, 1.2645e-21, 2.1497e-17) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row17000_values_of_mem (B : ℕ → ℝ)
    (h : ((17000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1167e-35 ∧ B 2 = 2.0101e-31 ∧ B 3 = 3.6182e-27 ∧
      B 4 = 6.5127e-23 ∧ B 5 = 1.1723e-18 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨279, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨279, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 279 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨279, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨279, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((17000 : ℝ), 1.1167e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row18000_values_of_mem (B : ℕ → ℝ)
    (h : ((18000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.3738e-37 ∧ B 2 = 1.0210e-32 ∧ B 3 = 1.9400e-28 ∧
      B 4 = 3.6859e-24 ∧ B 5 = 7.0032e-20 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨280, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨280, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 280 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨280, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨280, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((18000 : ℝ), 5.3738e-37, 1.0210e-32, 1.9400e-28, 3.6859e-24, 7.0032e-20) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row19000_values_of_mem (B : ℕ → ℝ)
    (h : ((19000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7357e-38 ∧ B 2 = 5.4714e-34 ∧ B 3 = 1.0943e-29 ∧
      B 4 = 2.1886e-25 ∧ B 5 = 4.3771e-21 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨281, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨281, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 281 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨281, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨281, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((19000 : ℝ), 2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3771e-21) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row20000_values_of_mem (B : ℕ → ℝ)
    (h : ((20000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5040e-39 ∧ B 2 = 3.1585e-35 ∧ B 3 = 6.6328e-31 ∧
      B 4 = 1.3929e-26 ∧ B 5 = 2.9251e-22 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨282, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨282, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 282 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨282, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨282, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((20000 : ℝ), 1.5040e-39, 3.1585e-35, 6.6328e-31, 1.3929e-26, 2.9251e-22) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row21000_values_of_mem (B : ℕ → ℝ)
    (h : ((21000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.0605e-41 ∧ B 2 = 1.9933e-36 ∧ B 3 = 4.3853e-32 ∧
      B 4 = 9.6476e-28 ∧ B 5 = 2.1225e-23 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨283, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨283, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 283 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨283, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨283, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((21000 : ℝ), 9.0605e-41, 1.9933e-36, 4.3853e-32, 9.6476e-28, 2.1225e-23) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row22000_values_of_mem (B : ℕ → ℝ)
    (h : ((22000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.6101e-42 ∧ B 2 = 1.2903e-37 ∧ B 3 = 2.9677e-33 ∧
      B 4 = 6.8258e-29 ∧ B 5 = 1.5699e-24 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨284, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨284, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 284 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨284, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨284, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((22000 : ℝ), 5.6101e-42, 1.2903e-37, 2.9677e-33, 6.8258e-29, 1.5699e-24) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row23000_values_of_mem (B : ℕ → ℝ)
    (h : ((23000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7554e-43 ∧ B 2 = 9.0129e-39 ∧ B 3 = 2.1631e-34 ∧
      B 4 = 5.1914e-30 ∧ B 5 = 1.2460e-25 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨285, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨285, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 285 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨285, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨285, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((23000 : ℝ), 3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1914e-30, 1.2460e-25) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

set_option maxRecDepth 100000 in
theorem table_10_row24000_values_of_mem (B : ℕ → ℝ)
    (h : ((24000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6755e-44 ∧ B 2 = 6.6888e-40 ∧ B 3 = 1.6722e-35 ∧
      B 4 = 4.1805e-31 ∧ B 5 = 1.0451e-26 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hfst : (table_10_bcol.get ⟨286, by rw [table_10_bcol_length]; norm_num⟩) =
      (table_10.get j).1 := by
    rw [hj]
    rfl
  have hji : (⟨286, by rw [table_10_bcol_length]; norm_num⟩ : Fin table_10_bcol.length) =
      table_10_bidx j := table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = 286 := by
    have h := congrArg Fin.val hji
    simpa [table_10_bidx] using h.symm
  have hj_eq : j = ⟨286, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ := by
    exact Fin.ext hval
  subst j
  have hrow : table_10.get ⟨286, by
      have hlen : table_10.length = 287 := by
        simpa [table_10_bcol] using table_10_bcol_length
      rw [hlen]
      norm_num⟩ = ((24000 : ℝ), 2.6755e-44, 6.6888e-40, 1.6722e-35, 4.1805e-31, 1.0451e-26) := rfl
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

end BKLNW
