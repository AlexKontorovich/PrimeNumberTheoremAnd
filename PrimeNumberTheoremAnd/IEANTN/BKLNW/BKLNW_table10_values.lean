import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Table 10 printed-value certificates from the checked b-column. -/

namespace BKLNW

open Real

/-- Cached length of `table_10` (computed once, reused by every row's value certificate). -/
lemma table_10_length_eq : table_10.length = 287 := by
  simpa [table_10_bcol] using table_10_bcol_length

set_option maxRecDepth 1000 in
/-- Per-row value-extraction helper. Given an index `N` together with the row's literal
contents (witnessed by `rfl` at the call site), conclude the five `B i = value` equalities
from membership of `(rid, B 1, ..., B 5)` in `table_10`. Factors out the bidx / sorted
injectivity / `subst` boilerplate from every per-row theorem. -/
lemma table_10_values_of_mem_aux
    (N : ℕ) (hN : N < table_10.length)
    {rid b1 b2 b3 b4 b5 : ℝ}
    (hrow : table_10.get ⟨N, hN⟩ = (rid, b1, b2, b3, b4, b5))
    {B : ℕ → ℝ}
    (h : (rid, B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = b1 ∧ B 2 = b2 ∧ B 3 = b3 ∧ B 4 = b4 ∧ B 5 = b5 := by
  obtain ⟨j, hj⟩ := List.mem_iff_get.mp h
  have hN_bcol : N < table_10_bcol.length := by
    rw [table_10_bcol_length, ← table_10_length_eq]; exact hN
  have hbcol_N : table_10_bcol.get ⟨N, hN_bcol⟩ = (table_10.get ⟨N, hN⟩).1 := by
    have key := table_10_bcol_get_bidx ⟨N, hN⟩
    have hbidx : table_10_bidx ⟨N, hN⟩ = (⟨N, hN_bcol⟩ : Fin table_10_bcol.length) :=
      Fin.ext rfl
    rw [hbidx] at key
    exact key
  have hfst : table_10_bcol.get ⟨N, hN_bcol⟩ = (table_10.get j).1 := by
    rw [hbcol_N, hrow, hj]
  have hij : (⟨N, hN_bcol⟩ : Fin table_10_bcol.length) = table_10_bidx j :=
    table_10_bidx_eq_of_get_eq hfst
  have hval : j.1 = N := by
    have h' := congrArg Fin.val hij
    simpa [table_10_bidx] using h'.symm
  have hj_eq : j = ⟨N, hN⟩ := Fin.ext hval
  subst j
  rw [hrow] at hj
  simp only [Prod.mk.injEq] at hj
  exact ⟨hj.2.1.symm, hj.2.2.1.symm, hj.2.2.2.1.symm, hj.2.2.2.2.1.symm,
    hj.2.2.2.2.2.symm⟩

theorem table_10_row20_values_of_mem (B : ℕ → ℝ)
    (h : ((20), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8077e-3 ∧ B 2 = 3.6154e-2 ∧ B 3 = 7.2309e-1 ∧
      B 4 = 1.4462e1 ∧ B 5 = 2.9160e2 :=
  table_10_values_of_mem_aux 0 (table_10_length_eq ▸ (by norm_num : 0 < 287)) rfl h

theorem table_10_row21_values_of_mem (B : ℕ → ℝ)
    (h : ((21), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1458e-3 ∧ B 2 = 2.4062e-2 ∧ B 3 = 5.0530e-1 ∧
      B 4 = 1.0611e1 ∧ B 5 = 2.2284e2 :=
  table_10_values_of_mem_aux 1 (table_10_length_eq ▸ (by norm_num : 1 < 287)) rfl h

theorem table_10_row22_values_of_mem (B : ℕ → ℝ)
    (h : ((22), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.2527e-4 ∧ B 2 = 1.5956e-2 ∧ B 3 = 3.5103e-1 ∧
      B 4 = 7.7226e0 ∧ B 5 = 1.6990e2 :=
  table_10_values_of_mem_aux 2 (table_10_length_eq ▸ (by norm_num : 2 < 287)) rfl h

theorem table_10_row23_values_of_mem (B : ℕ → ℝ)
    (h : ((23), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5848e-4 ∧ B 2 = 1.0545e-2 ∧ B 3 = 2.4254e-1 ∧
      B 4 = 5.5783e0 ∧ B 5 = 1.2830e2 :=
  table_10_values_of_mem_aux 3 (table_10_length_eq ▸ (by norm_num : 3 < 287)) rfl h

theorem table_10_row24_values_of_mem (B : ℕ → ℝ)
    (h : ((24), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8945e-4 ∧ B 2 = 6.9468e-3 ∧ B 3 = 1.6672e-1 ∧
      B 4 = 4.0013e0 ∧ B 5 = 9.6032e1 :=
  table_10_values_of_mem_aux 4 (table_10_length_eq ▸ (by norm_num : 4 < 287)) rfl h

theorem table_10_row25_values_of_mem (B : ℕ → ℝ)
    (h : ((25), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8251e-4 ∧ B 2 = 4.5626e-3 ∧ B 3 = 1.1407e-1 ∧
      B 4 = 2.8516e0 ∧ B 5 = 7.1291e1 :=
  table_10_values_of_mem_aux 5 (table_10_length_eq ▸ (by norm_num : 5 < 287)) rfl h

theorem table_10_row26_values_of_mem (B : ℕ → ℝ)
    (h : ((26), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1493e-4 ∧ B 2 = 2.9882e-3 ∧ B 3 = 7.7694e-2 ∧
      B 4 = 2.0200e0 ∧ B 5 = 5.2521e1 :=
  table_10_values_of_mem_aux 6 (table_10_length_eq ▸ (by norm_num : 6 < 287)) rfl h

theorem table_10_row27_values_of_mem (B : ℕ → ℝ)
    (h : ((27), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.2293e-5 ∧ B 2 = 1.9519e-3 ∧ B 3 = 5.2702e-2 ∧
      B 4 = 1.4229e0 ∧ B 5 = 3.8419e1 :=
  table_10_values_of_mem_aux 7 (table_10_length_eq ▸ (by norm_num : 7 < 287)) rfl h

theorem table_10_row28_values_of_mem (B : ℕ → ℝ)
    (h : ((28), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5421e-5 ∧ B 2 = 1.2718e-3 ∧ B 3 = 3.5610e-2 ∧
      B 4 = 9.9708e-1 ∧ B 5 = 2.7918e1 :=
  table_10_values_of_mem_aux 8 (table_10_length_eq ▸ (by norm_num : 8 < 287)) rfl h

theorem table_10_row29_values_of_mem (B : ℕ → ℝ)
    (h : ((29), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8507e-5 ∧ B 2 = 8.2670e-4 ∧ B 3 = 2.3974e-2 ∧
      B 4 = 6.9525e-1 ∧ B 5 = 2.0162e1 :=
  table_10_values_of_mem_aux 9 (table_10_length_eq ▸ (by norm_num : 9 < 287)) rfl h

theorem table_10_row30_values_of_mem (B : ℕ → ℝ)
    (h : ((30), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7873e-5 ∧ B 2 = 5.3619e-4 ∧ B 3 = 1.6086e-2 ∧
      B 4 = 4.8257e-1 ∧ B 5 = 1.4477e1 :=
  table_10_values_of_mem_aux 10 (table_10_length_eq ▸ (by norm_num : 10 < 287)) rfl h

theorem table_10_row31_values_of_mem (B : ℕ → ℝ)
    (h : ((31), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1195e-5 ∧ B 2 = 3.4704e-4 ∧ B 3 = 1.0758e-2 ∧
      B 4 = 3.3350e-1 ∧ B 5 = 1.0339e1 :=
  table_10_values_of_mem_aux 11 (table_10_length_eq ▸ (by norm_num : 11 < 287)) rfl h

theorem table_10_row32_values_of_mem (B : ℕ → ℝ)
    (h : ((32), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.0053e-6 ∧ B 2 = 2.2417e-4 ∧ B 3 = 7.1734e-3 ∧
      B 4 = 2.2955e-1 ∧ B 5 = 7.3456e0 :=
  table_10_values_of_mem_aux 12 (table_10_length_eq ▸ (by norm_num : 12 < 287)) rfl h

theorem table_10_row33_values_of_mem (B : ℕ → ℝ)
    (h : ((33), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3798e-6 ∧ B 2 = 1.4453e-4 ∧ B 3 = 4.7696e-3 ∧
      B 4 = 1.5740e-1 ∧ B 5 = 5.1941e0 :=
  table_10_values_of_mem_aux 13 (table_10_length_eq ▸ (by norm_num : 13 < 287)) rfl h

theorem table_10_row34_values_of_mem (B : ℕ → ℝ)
    (h : ((34), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7360e-6 ∧ B 2 = 9.3023e-5 ∧ B 3 = 3.1628e-3 ∧
      B 4 = 1.0754e-1 ∧ B 5 = 3.6562e0 :=
  table_10_values_of_mem_aux 14 (table_10_length_eq ▸ (by norm_num : 14 < 287)) rfl h

theorem table_10_row35_values_of_mem (B : ℕ → ℝ)
    (h : ((35), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7077e-6 ∧ B 2 = 5.9770e-5 ∧ B 3 = 2.0920e-3 ∧
      B 4 = 7.3219e-2 ∧ B 5 = 2.5627e0 :=
  table_10_values_of_mem_aux 15 (table_10_length_eq ▸ (by norm_num : 15 < 287)) rfl h

theorem table_10_row36_values_of_mem (B : ℕ → ℝ)
    (h : ((36), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2459e-6 ∧ B 2 = 4.4852e-5 ∧ B 3 = 1.6147e-3 ∧
      B 4 = 5.8128e-2 ∧ B 5 = 2.0926e0 :=
  table_10_values_of_mem_aux 16 (table_10_length_eq ▸ (by norm_num : 16 < 287)) rfl h

theorem table_10_row37_values_of_mem (B : ℕ → ℝ)
    (h : ((37), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0581e-6 ∧ B 2 = 3.9148e-5 ∧ B 3 = 1.4485e-3 ∧
      B 4 = 5.3593e-2 ∧ B 5 = 1.9830e0 :=
  table_10_values_of_mem_aux 17 (table_10_length_eq ▸ (by norm_num : 17 < 287)) rfl h

theorem table_10_row38_values_of_mem (B : ℕ → ℝ)
    (h : ((38), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.4814e-7 ∧ B 2 = 3.6029e-5 ∧ B 3 = 1.3691e-3 ∧
      B 4 = 5.2611e-2 ∧ B 5 = 2.0518e0 :=
  table_10_values_of_mem_aux 18 (table_10_length_eq ▸ (by norm_num : 18 < 287)) rfl h

theorem table_10_row39_values_of_mem (B : ℕ → ℝ)
    (h : ((39), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.8692e-7 ∧ B 2 = 3.4590e-5 ∧ B 3 = 1.3697e-3 ∧
      B 4 = 5.4788e-2 ∧ B 5 = 2.1915e0 :=
  table_10_values_of_mem_aux 19 (table_10_length_eq ▸ (by norm_num : 19 < 287)) rfl h

theorem table_10_row40_values_of_mem (B : ℕ → ℝ)
    (h : ((40), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5607e-7 ∧ B 2 = 3.4611e-5 ∧ B 3 = 1.4190e-3 ∧
      B 4 = 5.8181e-2 ∧ B 5 = 2.3854e0 :=
  table_10_values_of_mem_aux 20 (table_10_length_eq ▸ (by norm_num : 20 < 287)) rfl h

theorem table_10_row41_values_of_mem (B : ℕ → ℝ)
    (h : ((41), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.4416e-7 ∧ B 2 = 3.5451e-5 ∧ B 3 = 1.4889e-3 ∧
      B 4 = 6.2535e-2 ∧ B 5 = 2.6265e0 :=
  table_10_values_of_mem_aux 21 (table_10_length_eq ▸ (by norm_num : 21 < 287)) rfl h

theorem table_10_row42_values_of_mem (B : ℕ → ℝ)
    (h : ((42), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5132e-7 ∧ B 2 = 3.6607e-5 ∧ B 3 = 1.5741e-3 ∧
      B 4 = 6.7686e-2 ∧ B 5 = 2.9105e0 :=
  table_10_values_of_mem_aux 22 (table_10_length_eq ▸ (by norm_num : 22 < 287)) rfl h

theorem table_10_row43_values_of_mem (B : ℕ → ℝ)
    (h : ((43), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5986e-7 ∧ B 2 = 3.7618e-5 ∧ B 3 = 1.6458e-3 ∧
      B 4 = 7.2000e-2 ∧ B 5 = 3.1500e0 :=
  table_10_values_of_mem_aux 23 (table_10_length_eq ▸ (by norm_num : 23 < 287)) rfl h

theorem table_10_row19log10_values_of_mem (B : ℕ → ℝ)
    (h : ((19 * Real.log 10), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.6315e-7 ∧ B 2 = 3.7978e-5 ∧ B 3 = 1.6711e-3 ∧
      B 4 = 7.3526e-2 ∧ B 5 = 3.2352e0 :=
  table_10_values_of_mem_aux 24 (table_10_length_eq ▸ (by norm_num : 24 < 287)) rfl h

theorem table_10_row44_values_of_mem (B : ℕ → ℝ)
    (h : ((44), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.8162e-7 ∧ B 2 = 3.5173e-5 ∧ B 3 = 1.5828e-3 ∧
      B 4 = 7.1225e-2 ∧ B 5 = 3.2052e0 :=
  table_10_values_of_mem_aux 25 (table_10_length_eq ▸ (by norm_num : 25 < 287)) rfl h

theorem table_10_row45_values_of_mem (B : ℕ → ℝ)
    (h : ((45), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0646e-7 ∧ B 2 = 2.3297e-5 ∧ B 3 = 1.0717e-3 ∧
      B 4 = 4.9297e-2 ∧ B 5 = 2.2677e0 :=
  table_10_values_of_mem_aux 26 (table_10_length_eq ▸ (by norm_num : 26 < 287)) rfl h

theorem table_10_row46_values_of_mem (B : ℕ → ℝ)
    (h : ((46), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2935e-7 ∧ B 2 = 1.5479e-5 ∧ B 3 = 7.2752e-4 ∧
      B 4 = 3.4194e-2 ∧ B 5 = 1.6071e0 :=
  table_10_values_of_mem_aux 27 (table_10_length_eq ▸ (by norm_num : 27 < 287)) rfl h

theorem table_10_row47_values_of_mem (B : ℕ → ℝ)
    (h : ((47), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1307e-7 ∧ B 2 = 1.0228e-5 ∧ B 3 = 4.9092e-4 ∧
      B 4 = 2.3564e-2 ∧ B 5 = 1.1311e0 :=
  table_10_values_of_mem_aux 28 (table_10_length_eq ▸ (by norm_num : 28 < 287)) rfl h

theorem table_10_row48_values_of_mem (B : ℕ → ℝ)
    (h : ((48), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3790e-7 ∧ B 2 = 6.7572e-6 ∧ B 3 = 3.3110e-4 ∧
      B 4 = 1.6224e-2 ∧ B 5 = 7.9498e-1 :=
  table_10_values_of_mem_aux 29 (table_10_length_eq ▸ (by norm_num : 29 < 287)) rfl h

theorem table_10_row49_values_of_mem (B : ℕ → ℝ)
    (h : ((49), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.9139e-8 ∧ B 2 = 4.4570e-6 ∧ B 3 = 2.2285e-4 ∧
      B 4 = 1.1142e-2 ∧ B 5 = 5.5712e-1 :=
  table_10_values_of_mem_aux 30 (table_10_length_eq ▸ (by norm_num : 30 < 287)) rfl h

theorem table_10_row50_values_of_mem (B : ℕ → ℝ)
    (h : ((50), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7545e-8 ∧ B 2 = 2.9348e-6 ∧ B 3 = 1.4967e-4 ∧
      B 4 = 7.6334e-3 ∧ B 5 = 3.8930e-1 :=
  table_10_values_of_mem_aux 31 (table_10_length_eq ▸ (by norm_num : 31 < 287)) rfl h

theorem table_10_row51_values_of_mem (B : ℕ → ℝ)
    (h : ((51), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7146e-8 ∧ B 2 = 1.9316e-6 ∧ B 3 = 1.0044e-4 ∧
      B 4 = 5.2231e-3 ∧ B 5 = 2.7160e-1 :=
  table_10_values_of_mem_aux 32 (table_10_length_eq ▸ (by norm_num : 32 < 287)) rfl h

theorem table_10_row52_values_of_mem (B : ℕ → ℝ)
    (h : ((52), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3898e-8 ∧ B 2 = 1.2666e-6 ∧ B 3 = 6.7130e-5 ∧
      B 4 = 3.5579e-3 ∧ B 5 = 1.8857e-1 :=
  table_10_values_of_mem_aux 33 (table_10_length_eq ▸ (by norm_num : 33 < 287)) rfl h

theorem table_10_row53_values_of_mem (B : ℕ → ℝ)
    (h : ((53), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5373e-8 ∧ B 2 = 8.3012e-7 ∧ B 3 = 4.4826e-5 ∧
      B 4 = 2.4206e-3 ∧ B 5 = 1.3071e-1 :=
  table_10_values_of_mem_aux 34 (table_10_length_eq ▸ (by norm_num : 34 < 287)) rfl h

theorem table_10_row54_values_of_mem (B : ℕ → ℝ)
    (h : ((54), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8777e-9 ∧ B 2 = 5.4328e-7 ∧ B 3 = 2.9880e-5 ∧
      B 4 = 1.6434e-3 ∧ B 5 = 9.0388e-2 :=
  table_10_values_of_mem_aux 35 (table_10_length_eq ▸ (by norm_num : 35 < 287)) rfl h

theorem table_10_row55_values_of_mem (B : ℕ → ℝ)
    (h : ((55), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.3417e-9 ∧ B 2 = 3.5514e-7 ∧ B 3 = 1.9888e-5 ∧
      B 4 = 1.1137e-3 ∧ B 5 = 6.2367e-2 :=
  table_10_values_of_mem_aux 36 (table_10_length_eq ▸ (by norm_num : 36 < 287)) rfl h

theorem table_10_row56_values_of_mem (B : ℕ → ℝ)
    (h : ((56), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0668e-9 ∧ B 2 = 2.3181e-7 ∧ B 3 = 1.3213e-5 ∧
      B 4 = 7.5315e-4 ∧ B 5 = 4.2929e-2 :=
  table_10_values_of_mem_aux 37 (table_10_length_eq ▸ (by norm_num : 37 < 287)) rfl h

theorem table_10_row57_values_of_mem (B : ℕ → ℝ)
    (h : ((57), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6047e-9 ∧ B 2 = 1.5107e-7 ∧ B 3 = 8.7623e-6 ∧
      B 4 = 5.0821e-4 ∧ B 5 = 2.9476e-2 :=
  table_10_values_of_mem_aux 38 (table_10_length_eq ▸ (by norm_num : 38 < 287)) rfl h

theorem table_10_row58_values_of_mem (B : ℕ → ℝ)
    (h : ((58), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6805e-9 ∧ B 2 = 9.9147e-8 ∧ B 3 = 5.8497e-6 ∧
      B 4 = 3.4513e-4 ∧ B 5 = 2.0363e-2 :=
  table_10_values_of_mem_aux 39 (table_10_length_eq ▸ (by norm_num : 39 < 287)) rfl h

theorem table_10_row59_values_of_mem (B : ℕ → ℝ)
    (h : ((59), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1120e-9 ∧ B 2 = 6.6721e-8 ∧ B 3 = 4.0033e-6 ∧
      B 4 = 2.4020e-4 ∧ B 5 = 1.4412e-2 :=
  table_10_values_of_mem_aux 40 (table_10_length_eq ▸ (by norm_num : 40 < 287)) rfl h

theorem table_10_row60_values_of_mem (B : ℕ → ℝ)
    (h : ((60), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9446e-10 ∧ B 2 = 5.1640e-8 ∧ B 3 = 3.3566e-6 ∧
      B 4 = 2.1818e-4 ∧ B 5 = 1.4182e-2 :=
  table_10_values_of_mem_aux 41 (table_10_length_eq ▸ (by norm_num : 41 < 287)) rfl h

theorem table_10_row65_values_of_mem (B : ℕ → ℝ)
    (h : ((65), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5003e-10 ∧ B 2 = 1.7502e-8 ∧ B 3 = 1.2252e-6 ∧
      B 4 = 8.5761e-5 ∧ B 5 = 6.0033e-3 :=
  table_10_values_of_mem_aux 42 (table_10_length_eq ▸ (by norm_num : 42 < 287)) rfl h

theorem table_10_row70_values_of_mem (B : ℕ → ℝ)
    (h : ((70), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0943e-10 ∧ B 2 = 1.5707e-8 ∧ B 3 = 1.1780e-6 ∧
      B 4 = 8.8353e-5 ∧ B 5 = 6.6265e-3 :=
  table_10_values_of_mem_aux 43 (table_10_length_eq ▸ (by norm_num : 43 < 287)) rfl h

theorem table_10_row75_values_of_mem (B : ℕ → ℝ)
    (h : ((75), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1629e-10 ∧ B 2 = 1.7303e-8 ∧ B 3 = 1.3842e-6 ∧
      B 4 = 1.1074e-4 ∧ B 5 = 8.8591e-3 :=
  table_10_values_of_mem_aux 44 (table_10_length_eq ▸ (by norm_num : 44 < 287)) rfl h

theorem table_10_row80_values_of_mem (B : ℕ → ℝ)
    (h : ((80), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2192e-10 ∧ B 2 = 1.8863e-8 ∧ B 3 = 1.6034e-6 ∧
      B 4 = 1.3629e-4 ∧ B 5 = 1.1584e-2 :=
  table_10_values_of_mem_aux 45 (table_10_length_eq ▸ (by norm_num : 45 < 287)) rfl h

theorem table_10_row85_values_of_mem (B : ℕ → ℝ)
    (h : ((85), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3123e-10 ∧ B 2 = 2.0811e-8 ∧ B 3 = 1.8730e-6 ∧
      B 4 = 1.6857e-4 ∧ B 5 = 1.5171e-2 :=
  table_10_values_of_mem_aux 46 (table_10_length_eq ▸ (by norm_num : 46 < 287)) rfl h

theorem table_10_row90_values_of_mem (B : ℕ → ℝ)
    (h : ((90), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3952e-10 ∧ B 2 = 2.2755e-8 ∧ B 3 = 2.1617e-6 ∧
      B 4 = 2.0536e-4 ∧ B 5 = 1.9509e-2 :=
  table_10_values_of_mem_aux 47 (table_10_length_eq ▸ (by norm_num : 47 < 287)) rfl h

theorem table_10_row95_values_of_mem (B : ℕ → ℝ)
    (h : ((95), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4919e-10 ∧ B 2 = 2.4919e-8 ∧ B 3 = 2.4919e-6 ∧
      B 4 = 2.4919e-4 ∧ B 5 = 2.4919e-2 :=
  table_10_values_of_mem_aux 48 (table_10_length_eq ▸ (by norm_num : 48 < 287)) rfl h

theorem table_10_row100_values_of_mem (B : ℕ → ℝ)
    (h : ((100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.9060e-10 ∧ B 2 = 9.8120e-8 ∧ B 3 = 1.9624e-5 ∧
      B 4 = 3.9248e-3 ∧ B 5 = 7.8496e-1 :=
  table_10_values_of_mem_aux 49 (table_10_length_eq ▸ (by norm_num : 49 < 287)) rfl h

theorem table_10_row200_values_of_mem (B : ℕ → ℝ)
    (h : ((200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5446e-10 ∧ B 2 = 1.9634e-7 ∧ B 3 = 5.8902e-5 ∧
      B 4 = 1.7671e-2 ∧ B 5 = 5.3012e0 :=
  table_10_values_of_mem_aux 50 (table_10_length_eq ▸ (by norm_num : 50 < 287)) rfl h

theorem table_10_row300_values_of_mem (B : ℕ → ℝ)
    (h : ((300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.3609e-10 ∧ B 2 = 3.3444e-7 ∧ B 3 = 1.3378e-4 ∧
      B 4 = 5.3510e-2 ∧ B 5 = 2.1404e1 :=
  table_10_values_of_mem_aux 51 (table_10_length_eq ▸ (by norm_num : 51 < 287)) rfl h

theorem table_10_row400_values_of_mem (B : ℕ → ℝ)
    (h : ((400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0199e-9 ∧ B 2 = 5.0995e-7 ∧ B 3 = 2.5498e-4 ∧
      B 4 = 1.2749e-1 ∧ B 5 = 6.3744e1 :=
  table_10_values_of_mem_aux 52 (table_10_length_eq ▸ (by norm_num : 52 < 287)) rfl h

theorem table_10_row500_values_of_mem (B : ℕ → ℝ)
    (h : ((500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1999e-9 ∧ B 2 = 7.1995e-7 ∧ B 3 = 4.3197e-4 ∧
      B 4 = 2.5918e-1 ∧ B 5 = 1.5551e2 :=
  table_10_values_of_mem_aux 53 (table_10_length_eq ▸ (by norm_num : 53 < 287)) rfl h

theorem table_10_row600_values_of_mem (B : ℕ → ℝ)
    (h : ((600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3923e-9 ∧ B 2 = 9.7458e-7 ∧ B 3 = 6.8221e-4 ∧
      B 4 = 4.7755e-1 ∧ B 5 = 3.3428e2 :=
  table_10_values_of_mem_aux 54 (table_10_length_eq ▸ (by norm_num : 54 < 287)) rfl h

theorem table_10_row700_values_of_mem (B : ℕ → ℝ)
    (h : ((700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5812e-9 ∧ B 2 = 1.2649e-6 ∧ B 3 = 1.0119e-3 ∧
      B 4 = 8.0955e-1 ∧ B 5 = 6.4764e2 :=
  table_10_values_of_mem_aux 55 (table_10_length_eq ▸ (by norm_num : 55 < 287)) rfl h

theorem table_10_row800_values_of_mem (B : ℕ → ℝ)
    (h : ((800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7704e-9 ∧ B 2 = 1.5934e-6 ∧ B 3 = 1.4340e-3 ∧
      B 4 = 1.2906e0 ∧ B 5 = 1.1616e3 :=
  table_10_values_of_mem_aux 56 (table_10_length_eq ▸ (by norm_num : 56 < 287)) rfl h

theorem table_10_row900_values_of_mem (B : ℕ → ℝ)
    (h : ((900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9599e-9 ∧ B 2 = 1.9599e-6 ∧ B 3 = 1.9599e-3 ∧
      B 4 = 1.9599e0 ∧ B 5 = 1.9599e3 :=
  table_10_values_of_mem_aux 57 (table_10_length_eq ▸ (by norm_num : 57 < 287)) rfl h

theorem table_10_row1000_values_of_mem (B : ℕ → ℝ)
    (h : ((1000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9213e-9 ∧ B 2 = 4.3819e-6 ∧ B 3 = 6.5729e-3 ∧
      B 4 = 9.8593e0 ∧ B 5 = 1.4789e4 :=
  table_10_values_of_mem_aux 58 (table_10_length_eq ▸ (by norm_num : 58 < 287)) rfl h

theorem table_10_row1500_values_of_mem (B : ℕ → ℝ)
    (h : ((1500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0988e-9 ∧ B 2 = 4.9581e-6 ∧ B 3 = 7.9330e-3 ∧
      B 4 = 1.2693e1 ∧ B 5 = 2.0309e4 :=
  table_10_values_of_mem_aux 59 (table_10_length_eq ▸ (by norm_num : 59 < 287)) rfl h

theorem table_10_row1600_values_of_mem (B : ℕ → ℝ)
    (h : ((1600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2797e-9 ∧ B 2 = 5.5755e-6 ∧ B 3 = 9.4783e-3 ∧
      B 4 = 1.6113e1 ∧ B 5 = 2.7392e4 :=
  table_10_values_of_mem_aux 60 (table_10_length_eq ▸ (by norm_num : 60 < 287)) rfl h

theorem table_10_row1700_values_of_mem (B : ℕ → ℝ)
    (h : ((1700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3247e-9 ∧ B 2 = 5.7350e-6 ∧ B 3 = 9.8929e-3 ∧
      B 4 = 1.7065e1 ∧ B 5 = 2.9438e4 :=
  table_10_values_of_mem_aux 61 (table_10_length_eq ▸ (by norm_num : 61 < 287)) rfl h

theorem table_10_row1725_values_of_mem (B : ℕ → ℝ)
    (h : ((1725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3721e-9 ∧ B 2 = 5.9011e-6 ∧ B 3 = 1.0327e-2 ∧
      B 4 = 1.8072e1 ∧ B 5 = 3.1626e4 :=
  table_10_values_of_mem_aux 62 (table_10_length_eq ▸ (by norm_num : 62 < 287)) rfl h

theorem table_10_row1750_values_of_mem (B : ℕ → ℝ)
    (h : ((1750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4195e-9 ∧ B 2 = 6.0696e-6 ∧ B 3 = 1.0774e-2 ∧
      B 4 = 1.9123e1 ∧ B 5 = 3.3943e4 :=
  table_10_values_of_mem_aux 63 (table_10_length_eq ▸ (by norm_num : 63 < 287)) rfl h

theorem table_10_row1775_values_of_mem (B : ℕ → ℝ)
    (h : ((1775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4669e-9 ∧ B 2 = 6.2404e-6 ∧ B 3 = 1.1233e-2 ∧
      B 4 = 2.0219e1 ∧ B 5 = 3.6394e4 :=
  table_10_values_of_mem_aux 64 (table_10_length_eq ▸ (by norm_num : 64 < 287)) rfl h

theorem table_10_row1800_values_of_mem (B : ℕ → ℝ)
    (h : ((1800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5143e-9 ∧ B 2 = 6.4136e-6 ∧ B 3 = 1.1705e-2 ∧
      B 4 = 2.1361e1 ∧ B 5 = 3.8984e4 :=
  table_10_values_of_mem_aux 65 (table_10_length_eq ▸ (by norm_num : 65 < 287)) rfl h

theorem table_10_row1825_values_of_mem (B : ℕ → ℝ)
    (h : ((1825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5617e-9 ∧ B 2 = 6.5892e-6 ∧ B 3 = 1.2190e-2 ∧
      B 4 = 2.2552e1 ∧ B 5 = 4.1720e4 :=
  table_10_values_of_mem_aux 66 (table_10_length_eq ▸ (by norm_num : 66 < 287)) rfl h

theorem table_10_row1850_values_of_mem (B : ℕ → ℝ)
    (h : ((1850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6091e-9 ∧ B 2 = 6.7671e-6 ∧ B 3 = 1.2688e-2 ∧
      B 4 = 2.3791e1 ∧ B 5 = 4.4608e4 :=
  table_10_values_of_mem_aux 67 (table_10_length_eq ▸ (by norm_num : 67 < 287)) rfl h

theorem table_10_row1875_values_of_mem (B : ℕ → ℝ)
    (h : ((1875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6566e-9 ∧ B 2 = 6.9475e-6 ∧ B 3 = 1.3200e-2 ∧
      B 4 = 2.5080e1 ∧ B 5 = 4.7653e4 :=
  table_10_values_of_mem_aux 68 (table_10_length_eq ▸ (by norm_num : 68 < 287)) rfl h

theorem table_10_row1900_values_of_mem (B : ℕ → ℝ)
    (h : ((1900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7040e-9 ∧ B 2 = 7.1302e-6 ∧ B 3 = 1.3726e-2 ∧
      B 4 = 2.6422e1 ∧ B 5 = 5.0862e4 :=
  table_10_values_of_mem_aux 69 (table_10_length_eq ▸ (by norm_num : 69 < 287)) rfl h

theorem table_10_row1925_values_of_mem (B : ℕ → ℝ)
    (h : ((1925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7514e-9 ∧ B 2 = 7.3152e-6 ∧ B 3 = 1.4265e-2 ∧
      B 4 = 2.7816e1 ∧ B 5 = 5.4241e4 :=
  table_10_values_of_mem_aux 70 (table_10_length_eq ▸ (by norm_num : 70 < 287)) rfl h

theorem table_10_row1950_values_of_mem (B : ℕ → ℝ)
    (h : ((1950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7988e-9 ∧ B 2 = 7.5026e-6 ∧ B 3 = 1.4818e-2 ∧
      B 4 = 2.9265e1 ∧ B 5 = 5.7798e4 :=
  table_10_values_of_mem_aux 71 (table_10_length_eq ▸ (by norm_num : 71 < 287)) rfl h

theorem table_10_row1975_values_of_mem (B : ℕ → ℝ)
    (h : ((1975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8462e-9 ∧ B 2 = 7.6924e-6 ∧ B 3 = 1.5385e-2 ∧
      B 4 = 3.0770e1 ∧ B 5 = 6.1540e4 :=
  table_10_values_of_mem_aux 72 (table_10_length_eq ▸ (by norm_num : 72 < 287)) rfl h

theorem table_10_row2000_values_of_mem (B : ℕ → ℝ)
    (h : ((2000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8937e-9 ∧ B 2 = 7.8847e-6 ∧ B 3 = 1.5966e-2 ∧
      B 4 = 3.2332e1 ∧ B 5 = 6.5472e4 :=
  table_10_values_of_mem_aux 73 (table_10_length_eq ▸ (by norm_num : 73 < 287)) rfl h

theorem table_10_row2025_values_of_mem (B : ℕ → ℝ)
    (h : ((2025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9411e-9 ∧ B 2 = 8.0792e-6 ∧ B 3 = 1.6562e-2 ∧
      B 4 = 3.3953e1 ∧ B 5 = 6.9603e4 :=
  table_10_values_of_mem_aux 74 (table_10_length_eq ▸ (by norm_num : 74 < 287)) rfl h

theorem table_10_row2050_values_of_mem (B : ℕ → ℝ)
    (h : ((2050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9885e-9 ∧ B 2 = 8.2761e-6 ∧ B 3 = 1.7173e-2 ∧
      B 4 = 3.5634e1 ∧ B 5 = 7.3940e4 :=
  table_10_values_of_mem_aux 75 (table_10_length_eq ▸ (by norm_num : 75 < 287)) rfl h

theorem table_10_row2075_values_of_mem (B : ℕ → ℝ)
    (h : ((2075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0359e-9 ∧ B 2 = 8.4754e-6 ∧ B 3 = 1.7798e-2 ∧
      B 4 = 3.7377e1 ∧ B 5 = 7.8491e4 :=
  table_10_values_of_mem_aux 76 (table_10_length_eq ▸ (by norm_num : 76 < 287)) rfl h

theorem table_10_row2100_values_of_mem (B : ℕ → ℝ)
    (h : ((2100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0833e-9 ∧ B 2 = 8.6771e-6 ∧ B 3 = 1.8439e-2 ∧
      B 4 = 3.9182e1 ∧ B 5 = 8.3262e4 :=
  table_10_values_of_mem_aux 77 (table_10_length_eq ▸ (by norm_num : 77 < 287)) rfl h

theorem table_10_row2125_values_of_mem (B : ℕ → ℝ)
    (h : ((2125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1308e-9 ∧ B 2 = 8.8811e-6 ∧ B 3 = 1.9095e-2 ∧
      B 4 = 4.1053e1 ∧ B 5 = 8.8264e4 :=
  table_10_values_of_mem_aux 78 (table_10_length_eq ▸ (by norm_num : 78 < 287)) rfl h

theorem table_10_row2150_values_of_mem (B : ℕ → ℝ)
    (h : ((2150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1782e-9 ∧ B 2 = 9.0875e-6 ∧ B 3 = 1.9765e-2 ∧
      B 4 = 4.2990e1 ∧ B 5 = 9.3503e4 :=
  table_10_values_of_mem_aux 79 (table_10_length_eq ▸ (by norm_num : 79 < 287)) rfl h

theorem table_10_row2175_values_of_mem (B : ℕ → ℝ)
    (h : ((2175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2256e-9 ∧ B 2 = 9.2963e-6 ∧ B 3 = 2.0452e-2 ∧
      B 4 = 4.4994e1 ∧ B 5 = 9.8987e4 :=
  table_10_values_of_mem_aux 80 (table_10_length_eq ▸ (by norm_num : 80 < 287)) rfl h

theorem table_10_row2200_values_of_mem (B : ℕ → ℝ)
    (h : ((2200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2730e-9 ∧ B 2 = 9.5075e-6 ∧ B 3 = 2.1154e-2 ∧
      B 4 = 4.7068e1 ∧ B 5 = 1.0473e5 :=
  table_10_values_of_mem_aux 81 (table_10_length_eq ▸ (by norm_num : 81 < 287)) rfl h

theorem table_10_row2225_values_of_mem (B : ℕ → ℝ)
    (h : ((2225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3204e-9 ∧ B 2 = 9.7210e-6 ∧ B 3 = 2.1872e-2 ∧
      B 4 = 4.9212e1 ∧ B 5 = 1.1073e5 :=
  table_10_values_of_mem_aux 82 (table_10_length_eq ▸ (by norm_num : 82 < 287)) rfl h

theorem table_10_row2250_values_of_mem (B : ℕ → ℝ)
    (h : ((2250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3679e-9 ∧ B 2 = 9.9369e-6 ∧ B 3 = 2.2607e-2 ∧
      B 4 = 5.1430e1 ∧ B 5 = 1.1700e5 :=
  table_10_values_of_mem_aux 83 (table_10_length_eq ▸ (by norm_num : 83 < 287)) rfl h

theorem table_10_row2275_values_of_mem (B : ℕ → ℝ)
    (h : ((2275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4153e-9 ∧ B 2 = 1.0155e-5 ∧ B 3 = 2.3357e-2 ∧
      B 4 = 5.3721e1 ∧ B 5 = 1.2356e5 :=
  table_10_values_of_mem_aux 84 (table_10_length_eq ▸ (by norm_num : 84 < 287)) rfl h

theorem table_10_row2300_values_of_mem (B : ℕ → ℝ)
    (h : ((2300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4627e-9 ∧ B 2 = 1.0376e-5 ∧ B 3 = 2.4124e-2 ∧
      B 4 = 5.6088e1 ∧ B 5 = 1.3040e5 :=
  table_10_values_of_mem_aux 85 (table_10_length_eq ▸ (by norm_num : 85 < 287)) rfl h

theorem table_10_row2325_values_of_mem (B : ℕ → ℝ)
    (h : ((2325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4062e-9 ∧ B 2 = 1.0355e-5 ∧ B 3 = 2.4333e-2 ∧
      B 4 = 5.7184e1 ∧ B 5 = 1.3438e5 :=
  table_10_values_of_mem_aux 86 (table_10_length_eq ▸ (by norm_num : 86 < 287)) rfl h

theorem table_10_row2350_values_of_mem (B : ℕ → ℝ)
    (h : ((2350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2245e-9 ∧ B 2 = 1.0033e-5 ∧ B 3 = 2.3829e-2 ∧
      B 4 = 5.6593e1 ∧ B 5 = 1.3441e5 :=
  table_10_values_of_mem_aux 87 (table_10_length_eq ▸ (by norm_num : 87 < 287)) rfl h

theorem table_10_row2375_values_of_mem (B : ℕ → ℝ)
    (h : ((2375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.0498e-9 ∧ B 2 = 9.7196e-6 ∧ B 3 = 2.3327e-2 ∧
      B 4 = 5.5985e1 ∧ B 5 = 1.3436e5 :=
  table_10_values_of_mem_aux 88 (table_10_length_eq ▸ (by norm_num : 88 < 287)) rfl h

theorem table_10_row2400_values_of_mem (B : ℕ → ℝ)
    (h : ((2400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8820e-9 ∧ B 2 = 9.4139e-6 ∧ B 3 = 2.2829e-2 ∧
      B 4 = 5.5360e1 ∧ B 5 = 1.3425e5 :=
  table_10_values_of_mem_aux 89 (table_10_length_eq ▸ (by norm_num : 89 < 287)) rfl h

theorem table_10_row2425_values_of_mem (B : ℕ → ℝ)
    (h : ((2425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4832e-9 ∧ B 2 = 8.5339e-6 ∧ B 3 = 2.0908e-2 ∧
      B 4 = 5.1225e1 ∧ B 5 = 1.2550e5 :=
  table_10_values_of_mem_aux 90 (table_10_length_eq ▸ (by norm_num : 90 < 287)) rfl h

theorem table_10_row2450_values_of_mem (B : ℕ → ℝ)
    (h : ((2450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0228e-9 ∧ B 2 = 7.4814e-6 ∧ B 3 = 1.8517e-2 ∧
      B 4 = 4.5828e1 ∧ B 5 = 1.1343e5 :=
  table_10_values_of_mem_aux 91 (table_10_length_eq ▸ (by norm_num : 91 < 287)) rfl h

theorem table_10_row2475_values_of_mem (B : ℕ → ℝ)
    (h : ((2475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6278e-9 ∧ B 2 = 6.5696e-6 ∧ B 3 = 1.6424e-2 ∧
      B 4 = 4.1060e1 ∧ B 5 = 1.0265e5 :=
  table_10_values_of_mem_aux 92 (table_10_length_eq ▸ (by norm_num : 92 < 287)) rfl h

theorem table_10_row2500_values_of_mem (B : ℕ → ℝ)
    (h : ((2500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2884e-9 ∧ B 2 = 5.7783e-6 ∧ B 3 = 1.4590e-2 ∧
      B 4 = 3.6840e1 ∧ B 5 = 9.3021e4 :=
  table_10_values_of_mem_aux 93 (table_10_length_eq ▸ (by norm_num : 93 < 287)) rfl h

theorem table_10_row2525_values_of_mem (B : ℕ → ℝ)
    (h : ((2525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9873e-9 ∧ B 2 = 5.0676e-6 ∧ B 3 = 1.2922e-2 ∧
      B 4 = 3.2952e1 ∧ B 5 = 8.4027e4 :=
  table_10_values_of_mem_aux 94 (table_10_length_eq ▸ (by norm_num : 94 < 287)) rfl h

theorem table_10_row2550_values_of_mem (B : ℕ → ℝ)
    (h : ((2550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7270e-9 ∧ B 2 = 4.4470e-6 ∧ B 3 = 1.1451e-2 ∧
      B 4 = 2.9487e1 ∧ B 5 = 7.5928e4 :=
  table_10_values_of_mem_aux 95 (table_10_length_eq ▸ (by norm_num : 95 < 287)) rfl h

theorem table_10_row2575_values_of_mem (B : ℕ → ℝ)
    (h : ((2575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4992e-9 ∧ B 2 = 3.8979e-6 ∧ B 3 = 1.0135e-2 ∧
      B 4 = 2.6350e1 ∧ B 5 = 6.8509e4 :=
  table_10_values_of_mem_aux 96 (table_10_length_eq ▸ (by norm_num : 96 < 287)) rfl h

theorem table_10_row2600_values_of_mem (B : ℕ → ℝ)
    (h : ((2600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3022e-9 ∧ B 2 = 3.4184e-6 ∧ B 3 = 8.9732e-3 ∧
      B 4 = 2.3555e1 ∧ B 5 = 6.1831e4 :=
  table_10_values_of_mem_aux 97 (table_10_length_eq ▸ (by norm_num : 97 < 287)) rfl h

theorem table_10_row2625_values_of_mem (B : ℕ → ℝ)
    (h : ((2625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1314e-9 ∧ B 2 = 2.9981e-6 ∧ B 3 = 7.9449e-3 ∧
      B 4 = 2.1054e1 ∧ B 5 = 5.5793e4 :=
  table_10_values_of_mem_aux 98 (table_10_length_eq ▸ (by norm_num : 98 < 287)) rfl h

theorem table_10_row2650_values_of_mem (B : ℕ → ℝ)
    (h : ((2650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8296e-10 ∧ B 2 = 2.6294e-6 ∧ B 3 = 7.0337e-3 ∧
      B 4 = 1.8815e1 ∧ B 5 = 5.0330e4 :=
  table_10_values_of_mem_aux 99 (table_10_length_eq ▸ (by norm_num : 99 < 287)) rfl h

theorem table_10_row2675_values_of_mem (B : ℕ → ℝ)
    (h : ((2675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.5431e-10 ∧ B 2 = 2.3067e-6 ∧ B 3 = 6.2279e-3 ∧
      B 4 = 1.6816e1 ∧ B 5 = 4.5402e4 :=
  table_10_values_of_mem_aux 100 (table_10_length_eq ▸ (by norm_num : 100 < 287)) rfl h

theorem table_10_row2700_values_of_mem (B : ℕ → ℝ)
    (h : ((2700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.4234e-10 ∧ B 2 = 2.0229e-6 ∧ B 3 = 5.5123e-3 ∧
      B 4 = 1.5021e1 ∧ B 5 = 4.0932e4 :=
  table_10_values_of_mem_aux 101 (table_10_length_eq ▸ (by norm_num : 101 < 287)) rfl h

theorem table_10_row2725_values_of_mem (B : ℕ → ℝ)
    (h : ((2725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.4498e-10 ∧ B 2 = 1.7737e-6 ∧ B 3 = 4.8777e-3 ∧
      B 4 = 1.3414e1 ∧ B 5 = 3.6887e4 :=
  table_10_values_of_mem_aux 102 (table_10_length_eq ▸ (by norm_num : 102 < 287)) rfl h

theorem table_10_row2750_values_of_mem (B : ℕ → ℝ)
    (h : ((2750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.6071e-10 ∧ B 2 = 1.5560e-6 ∧ B 3 = 4.3178e-3 ∧
      B 4 = 1.1982e1 ∧ B 5 = 3.3250e4 :=
  table_10_values_of_mem_aux 103 (table_10_length_eq ▸ (by norm_num : 103 < 287)) rfl h

theorem table_10_row2775_values_of_mem (B : ℕ → ℝ)
    (h : ((2775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.8730e-10 ∧ B 2 = 1.3644e-6 ∧ B 3 = 3.8204e-3 ∧
      B 4 = 1.0697e1 ∧ B 5 = 2.9952e4 :=
  table_10_values_of_mem_aux 104 (table_10_length_eq ▸ (by norm_num : 104 < 287)) rfl h

theorem table_10_row2800_values_of_mem (B : ℕ → ℝ)
    (h : ((2800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2388e-10 ∧ B 2 = 1.1975e-6 ∧ B 3 = 3.3829e-3 ∧
      B 4 = 9.5565e0 ∧ B 5 = 2.6997e4 :=
  table_10_values_of_mem_aux 105 (table_10_length_eq ▸ (by norm_num : 105 < 287)) rfl h

theorem table_10_row2825_values_of_mem (B : ℕ → ℝ)
    (h : ((2825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6911e-10 ∧ B 2 = 1.0520e-6 ∧ B 3 = 2.9981e-3 ∧
      B 4 = 8.5446e0 ∧ B 5 = 2.4352e4 :=
  table_10_values_of_mem_aux 106 (table_10_length_eq ▸ (by norm_num : 106 < 287)) rfl h

theorem table_10_row2850_values_of_mem (B : ℕ → ℝ)
    (h : ((2850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2167e-10 ∧ B 2 = 9.2481e-7 ∧ B 3 = 2.6588e-3 ∧
      B 4 = 7.6442e0 ∧ B 5 = 2.1977e4 :=
  table_10_values_of_mem_aux 107 (table_10_length_eq ▸ (by norm_num : 107 < 287)) rfl h

theorem table_10_row2875_values_of_mem (B : ℕ → ℝ)
    (h : ((2875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7953e-10 ∧ B 2 = 8.1062e-7 ∧ B 3 = 2.3508e-3 ∧
      B 4 = 6.8173e0 ∧ B 5 = 1.9770e4 :=
  table_10_values_of_mem_aux 108 (table_10_length_eq ▸ (by norm_num : 108 < 287)) rfl h

theorem table_10_row2900_values_of_mem (B : ℕ → ℝ)
    (h : ((2900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4326e-10 ∧ B 2 = 7.1154e-7 ∧ B 3 = 2.0813e-3 ∧
      B 4 = 6.0877e0 ∧ B 5 = 1.7806e4 :=
  table_10_values_of_mem_aux 109 (table_10_length_eq ▸ (by norm_num : 109 < 287)) rfl h

theorem table_10_row2925_values_of_mem (B : ℕ → ℝ)
    (h : ((2925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1140e-10 ∧ B 2 = 6.2363e-7 ∧ B 3 = 1.8397e-3 ∧
      B 4 = 5.4272e0 ∧ B 5 = 1.6010e4 :=
  table_10_values_of_mem_aux 110 (table_10_length_eq ▸ (by norm_num : 110 < 287)) rfl h

theorem table_10_row2950_values_of_mem (B : ℕ → ℝ)
    (h : ((2950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8391e-10 ∧ B 2 = 5.4712e-7 ∧ B 3 = 1.6277e-3 ∧
      B 4 = 4.8423e0 ∧ B 5 = 1.4406e4 :=
  table_10_values_of_mem_aux 111 (table_10_length_eq ▸ (by norm_num : 111 < 287)) rfl h

theorem table_10_row2975_values_of_mem (B : ℕ → ℝ)
    (h : ((2975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6015e-10 ∧ B 2 = 4.8044e-7 ∧ B 3 = 1.4413e-3 ∧
      B 4 = 4.3240e0 ∧ B 5 = 1.2972e4 :=
  table_10_values_of_mem_aux 112 (table_10_length_eq ▸ (by norm_num : 112 < 287)) rfl h

theorem table_10_row3000_values_of_mem (B : ℕ → ℝ)
    (h : ((3000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3914e-10 ∧ B 2 = 4.2090e-7 ∧ B 3 = 1.2732e-3 ∧
      B 4 = 3.8515e0 ∧ B 5 = 1.1651e4 :=
  table_10_values_of_mem_aux 113 (table_10_length_eq ▸ (by norm_num : 113 < 287)) rfl h

theorem table_10_row3025_values_of_mem (B : ℕ → ℝ)
    (h : ((3025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2115e-10 ∧ B 2 = 3.6949e-7 ∧ B 3 = 1.1270e-3 ∧
      B 4 = 3.4372e0 ∧ B 5 = 1.0484e4 :=
  table_10_values_of_mem_aux 114 (table_10_length_eq ▸ (by norm_num : 114 < 287)) rfl h

theorem table_10_row3050_values_of_mem (B : ℕ → ℝ)
    (h : ((3050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0531e-10 ∧ B 2 = 3.2382e-7 ∧ B 3 = 9.9573e-4 ∧
      B 4 = 3.0619e0 ∧ B 5 = 9.4152e3 :=
  table_10_values_of_mem_aux 115 (table_10_length_eq ▸ (by norm_num : 115 < 287)) rfl h

theorem table_10_row3075_values_of_mem (B : ℕ → ℝ)
    (h : ((3075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.1684e-11 ∧ B 2 = 2.8422e-7 ∧ B 3 = 8.8108e-4 ∧
      B 4 = 2.7314e0 ∧ B 5 = 8.4672e3 :=
  table_10_values_of_mem_aux 116 (table_10_length_eq ▸ (by norm_num : 116 < 287)) rfl h

theorem table_10_row3100_values_of_mem (B : ℕ → ℝ)
    (h : ((3100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9793e-11 ∧ B 2 = 2.4935e-7 ∧ B 3 = 7.7922e-4 ∧
      B 4 = 2.4351e0 ∧ B 5 = 7.6096e3 :=
  table_10_values_of_mem_aux 117 (table_10_length_eq ▸ (by norm_num : 117 < 287)) rfl h

theorem table_10_row3125_values_of_mem (B : ℕ → ℝ)
    (h : ((3125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.9396e-11 ∧ B 2 = 2.1860e-7 ∧ B 3 = 6.8858e-4 ∧
      B 4 = 2.1690e0 ∧ B 5 = 6.8325e3 :=
  table_10_values_of_mem_aux 118 (table_10_length_eq ▸ (by norm_num : 118 < 287)) rfl h

theorem table_10_row3150_values_of_mem (B : ℕ → ℝ)
    (h : ((3150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0410e-11 ∧ B 2 = 1.9180e-7 ∧ B 3 = 6.0897e-4 ∧
      B 4 = 1.9335e0 ∧ B 5 = 6.1388e3 :=
  table_10_values_of_mem_aux 119 (table_10_length_eq ▸ (by norm_num : 119 < 287)) rfl h

theorem table_10_row3175_values_of_mem (B : ℕ → ℝ)
    (h : ((3175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.2572e-11 ∧ B 2 = 1.6823e-7 ∧ B 3 = 5.3834e-4 ∧
      B 4 = 1.7227e0 ∧ B 5 = 5.5126e3 :=
  table_10_values_of_mem_aux 120 (table_10_length_eq ▸ (by norm_num : 120 < 287)) rfl h

theorem table_10_row3200_values_of_mem (B : ℕ → ℝ)
    (h : ((3200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5782e-11 ∧ B 2 = 1.4765e-7 ∧ B 3 = 4.7616e-4 ∧
      B 4 = 1.5356e0 ∧ B 5 = 4.9524e3 :=
  table_10_values_of_mem_aux 121 (table_10_length_eq ▸ (by norm_num : 121 < 287)) rfl h

theorem table_10_row3225_values_of_mem (B : ℕ → ℝ)
    (h : ((3225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9901e-11 ∧ B 2 = 1.2968e-7 ∧ B 3 = 4.2146e-4 ∧
      B 4 = 1.3697e0 ∧ B 5 = 4.4516e3 :=
  table_10_values_of_mem_aux 122 (table_10_length_eq ▸ (by norm_num : 122 < 287)) rfl h

theorem table_10_row3250_values_of_mem (B : ℕ → ℝ)
    (h : ((3250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4800e-11 ∧ B 2 = 1.1397e-7 ∧ B 3 = 3.7326e-4 ∧
      B 4 = 1.2224e0 ∧ B 5 = 4.0034e3 :=
  table_10_values_of_mem_aux 123 (table_10_length_eq ▸ (by norm_num : 123 < 287)) rfl h

theorem table_10_row3275_values_of_mem (B : ℕ → ℝ)
    (h : ((3275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0332e-11 ∧ B 2 = 1.0009e-7 ∧ B 3 = 3.3031e-4 ∧
      B 4 = 1.0900e0 ∧ B 5 = 3.5971e3 :=
  table_10_values_of_mem_aux 124 (table_10_length_eq ▸ (by norm_num : 124 < 287)) rfl h

theorem table_10_row3300_values_of_mem (B : ℕ → ℝ)
    (h : ((3300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6412e-11 ∧ B 2 = 8.7820e-8 ∧ B 3 = 2.9200e-4 ∧
      B 4 = 9.7090e-1 ∧ B 5 = 3.2283e3 :=
  table_10_values_of_mem_aux 125 (table_10_length_eq ▸ (by norm_num : 125 < 287)) rfl h

theorem table_10_row3325_values_of_mem (B : ℕ → ℝ)
    (h : ((3325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3015e-11 ∧ B 2 = 7.7100e-8 ∧ B 3 = 2.5829e-4 ∧
      B 4 = 8.6525e-1 ∧ B 5 = 2.8986e3 :=
  table_10_values_of_mem_aux 126 (table_10_length_eq ▸ (by norm_num : 126 < 287)) rfl h

theorem table_10_row3350_values_of_mem (B : ℕ → ℝ)
    (h : ((3350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0043e-11 ∧ B 2 = 6.7644e-8 ∧ B 3 = 2.2830e-4 ∧
      B 4 = 7.7051e-1 ∧ B 5 = 2.6005e3 :=
  table_10_values_of_mem_aux 127 (table_10_length_eq ▸ (by norm_num : 127 < 287)) rfl h

theorem table_10_row3375_values_of_mem (B : ℕ → ℝ)
    (h : ((3375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7453e-11 ∧ B 2 = 5.9340e-8 ∧ B 3 = 2.0176e-4 ∧
      B 4 = 6.8597e-1 ∧ B 5 = 2.3323e3 :=
  table_10_values_of_mem_aux 128 (table_10_length_eq ▸ (by norm_num : 128 < 287)) rfl h

theorem table_10_row3400_values_of_mem (B : ℕ → ℝ)
    (h : ((3400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5212e-11 ∧ B 2 = 5.2099e-8 ∧ B 3 = 1.7844e-4 ∧
      B 4 = 6.1116e-1 ∧ B 5 = 2.0932e3 :=
  table_10_values_of_mem_aux 129 (table_10_length_eq ▸ (by norm_num : 129 < 287)) rfl h

theorem table_10_row3425_values_of_mem (B : ℕ → ℝ)
    (h : ((3425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3266e-11 ∧ B 2 = 4.5768e-8 ∧ B 3 = 1.5790e-4 ∧
      B 4 = 5.4476e-1 ∧ B 5 = 1.8794e3 :=
  table_10_values_of_mem_aux 130 (table_10_length_eq ▸ (by norm_num : 130 < 287)) rfl h

theorem table_10_row3450_values_of_mem (B : ℕ → ℝ)
    (h : ((3450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1554e-11 ∧ B 2 = 4.0151e-8 ∧ B 3 = 1.3953e-4 ∧
      B 4 = 4.8485e-1 ∧ B 5 = 1.6849e3 :=
  table_10_values_of_mem_aux 131 (table_10_length_eq ▸ (by norm_num : 131 < 287)) rfl h

theorem table_10_row3475_values_of_mem (B : ℕ → ℝ)
    (h : ((3475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0059e-11 ∧ B 2 = 3.5206e-8 ∧ B 3 = 1.2322e-4 ∧
      B 4 = 4.3127e-1 ∧ B 5 = 1.5095e3 :=
  table_10_values_of_mem_aux 132 (table_10_length_eq ▸ (by norm_num : 132 < 287)) rfl h

theorem table_10_row3500_values_of_mem (B : ℕ → ℝ)
    (h : ((3500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.7646e-12 ∧ B 2 = 3.0895e-8 ∧ B 3 = 1.0891e-4 ∧
      B 4 = 3.8389e-1 ∧ B 5 = 1.3532e3 :=
  table_10_values_of_mem_aux 133 (table_10_length_eq ▸ (by norm_num : 133 < 287)) rfl h

theorem table_10_row3525_values_of_mem (B : ℕ → ℝ)
    (h : ((3525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6403e-12 ∧ B 2 = 2.7123e-8 ∧ B 3 = 9.6287e-5 ∧
      B 4 = 3.4182e-1 ∧ B 5 = 1.2135e3 :=
  table_10_values_of_mem_aux 134 (table_10_length_eq ▸ (by norm_num : 134 < 287)) rfl h

theorem table_10_row3550_values_of_mem (B : ℕ → ℝ)
    (h : ((3550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6608e-12 ∧ B 2 = 2.3812e-8 ∧ B 3 = 8.5129e-5 ∧
      B 4 = 3.0434e-1 ∧ B 5 = 1.0880e3 :=
  table_10_values_of_mem_aux 135 (table_10_length_eq ▸ (by norm_num : 135 < 287)) rfl h

theorem table_10_row3575_values_of_mem (B : ℕ → ℝ)
    (h : ((3575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8042e-12 ∧ B 2 = 2.0895e-8 ∧ B 3 = 7.5222e-5 ∧
      B 4 = 2.7080e-1 ∧ B 5 = 9.7488e2 :=
  table_10_values_of_mem_aux 136 (table_10_length_eq ▸ (by norm_num : 136 < 287)) rfl h

theorem table_10_row3600_values_of_mem (B : ℕ → ℝ)
    (h : ((3600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0621e-12 ∧ B 2 = 1.8350e-8 ∧ B 3 = 6.6520e-5 ∧
      B 4 = 2.4113e-1 ∧ B 5 = 8.7411e2 :=
  table_10_values_of_mem_aux 137 (table_10_length_eq ▸ (by norm_num : 137 < 287)) rfl h

theorem table_10_row3625_values_of_mem (B : ℕ → ℝ)
    (h : ((3625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4165e-12 ∧ B 2 = 1.6120e-8 ∧ B 3 = 5.8839e-5 ∧
      B 4 = 2.1476e-1 ∧ B 5 = 7.8388e2 :=
  table_10_values_of_mem_aux 138 (table_10_length_eq ▸ (by norm_num : 138 < 287)) rfl h

theorem table_10_row3650_values_of_mem (B : ℕ → ℝ)
    (h : ((3650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8475e-12 ∧ B 2 = 1.4140e-8 ∧ B 3 = 5.1963e-5 ∧
      B 4 = 1.9096e-1 ∧ B 5 = 7.0179e2 :=
  table_10_values_of_mem_aux 139 (table_10_length_eq ▸ (by norm_num : 139 < 287)) rfl h

theorem table_10_row3675_values_of_mem (B : ℕ → ℝ)
    (h : ((3675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3560e-12 ∧ B 2 = 1.2417e-8 ∧ B 3 = 4.5944e-5 ∧
      B 4 = 1.6999e-1 ∧ B 5 = 6.2897e2 :=
  table_10_values_of_mem_aux 140 (table_10_length_eq ▸ (by norm_num : 140 < 287)) rfl h

theorem table_10_row3700_values_of_mem (B : ℕ → ℝ)
    (h : ((3700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9296e-12 ∧ B 2 = 1.0913e-8 ∧ B 3 = 4.0649e-5 ∧
      B 4 = 1.5142e-1 ∧ B 5 = 5.6404e2 :=
  table_10_values_of_mem_aux 141 (table_10_length_eq ▸ (by norm_num : 141 < 287)) rfl h

theorem table_10_row3725_values_of_mem (B : ℕ → ℝ)
    (h : ((3725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5580e-12 ∧ B 2 = 9.5924e-9 ∧ B 3 = 3.5971e-5 ∧
      B 4 = 1.3489e-1 ∧ B 5 = 5.0585e2 :=
  table_10_values_of_mem_aux 142 (table_10_length_eq ▸ (by norm_num : 142 < 287)) rfl h

theorem table_10_row3750_values_of_mem (B : ℕ → ℝ)
    (h : ((3750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2346e-12 ∧ B 2 = 8.4357e-9 ∧ B 3 = 3.1845e-5 ∧
      B 4 = 1.2022e-1 ∧ B 5 = 4.5381e2 :=
  table_10_values_of_mem_aux 143 (table_10_length_eq ▸ (by norm_num : 143 < 287)) rfl h

theorem table_10_row3775_values_of_mem (B : ℕ → ℝ)
    (h : ((3775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9513e-12 ∧ B 2 = 7.4151e-9 ∧ B 3 = 2.8177e-5 ∧
      B 4 = 1.0707e-1 ∧ B 5 = 4.0688e2 :=
  table_10_values_of_mem_aux 144 (table_10_length_eq ▸ (by norm_num : 144 < 287)) rfl h

theorem table_10_row3800_values_of_mem (B : ℕ → ℝ)
    (h : ((3800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7020e-12 ∧ B 2 = 6.5099e-9 ∧ B 3 = 2.4901e-5 ∧
      B 4 = 9.5244e-2 ∧ B 5 = 3.6431e2 :=
  table_10_values_of_mem_aux 145 (table_10_length_eq ▸ (by norm_num : 145 < 287)) rfl h

theorem table_10_row3825_values_of_mem (B : ℕ → ℝ)
    (h : ((3825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4854e-12 ∧ B 2 = 5.7189e-9 ∧ B 3 = 2.2018e-5 ∧
      B 4 = 8.4768e-2 ∧ B 5 = 3.2636e2 :=
  table_10_values_of_mem_aux 146 (table_10_length_eq ▸ (by norm_num : 146 < 287)) rfl h

theorem table_10_row3850_values_of_mem (B : ℕ → ℝ)
    (h : ((3850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2972e-12 ∧ B 2 = 5.0267e-9 ∧ B 3 = 1.9478e-5 ∧
      B 4 = 7.5479e-2 ∧ B 5 = 2.9248e2 :=
  table_10_values_of_mem_aux 147 (table_10_length_eq ▸ (by norm_num : 147 < 287)) rfl h

theorem table_10_row3875_values_of_mem (B : ℕ → ℝ)
    (h : ((3875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1314e-12 ∧ B 2 = 4.4124e-9 ∧ B 3 = 1.7208e-5 ∧
      B 4 = 6.7112e-2 ∧ B 5 = 2.6174e2 :=
  table_10_values_of_mem_aux 148 (table_10_length_eq ▸ (by norm_num : 148 < 287)) rfl h

theorem table_10_row3900_values_of_mem (B : ℕ → ℝ)
    (h : ((3900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.8800e-13 ∧ B 2 = 3.8779e-9 ∧ B 3 = 1.5221e-5 ∧
      B 4 = 5.9741e-2 ∧ B 5 = 2.3449e2 :=
  table_10_values_of_mem_aux 149 (table_10_length_eq ▸ (by norm_num : 149 < 287)) rfl h

theorem table_10_row3925_values_of_mem (B : ℕ → ℝ)
    (h : ((3925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.6323e-13 ∧ B 2 = 3.4098e-9 ∧ B 3 = 1.3469e-5 ∧
      B 4 = 5.3201e-2 ∧ B 5 = 2.1014e2 :=
  table_10_values_of_mem_aux 150 (table_10_length_eq ▸ (by norm_num : 150 < 287)) rfl h

theorem table_10_row3950_values_of_mem (B : ℕ → ℝ)
    (h : ((3950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.5449e-13 ∧ B 2 = 2.9991e-9 ∧ B 3 = 1.1922e-5 ∧
      B 4 = 4.7388e-2 ∧ B 5 = 1.8837e2 :=
  table_10_values_of_mem_aux 151 (table_10_length_eq ▸ (by norm_num : 151 < 287)) rfl h

theorem table_10_row3975_values_of_mem (B : ℕ → ℝ)
    (h : ((3975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5788e-13 ∧ B 2 = 2.6315e-9 ∧ B 3 = 1.0526e-5 ∧
      B 4 = 4.2104e-2 ∧ B 5 = 1.6842e2 :=
  table_10_values_of_mem_aux 152 (table_10_length_eq ▸ (by norm_num : 152 < 287)) rfl h

theorem table_10_row4000_values_of_mem (B : ℕ → ℝ)
    (h : ((4000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7409e-13 ∧ B 2 = 2.3107e-9 ∧ B 3 = 9.3007e-6 ∧
      B 4 = 3.7435e-2 ∧ B 5 = 1.5068e2 :=
  table_10_values_of_mem_aux 153 (table_10_length_eq ▸ (by norm_num : 153 < 287)) rfl h

theorem table_10_row4025_values_of_mem (B : ℕ → ℝ)
    (h : ((4025), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.0264e-13 ∧ B 2 = 2.0357e-9 ∧ B 3 = 8.2446e-6 ∧
      B 4 = 3.3391e-2 ∧ B 5 = 1.3523e2 :=
  table_10_values_of_mem_aux 154 (table_10_length_eq ▸ (by norm_num : 154 < 287)) rfl h

theorem table_10_row4050_values_of_mem (B : ℕ → ℝ)
    (h : ((4050), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3803e-13 ∧ B 2 = 1.7850e-9 ∧ B 3 = 7.2737e-6 ∧
      B 4 = 2.9640e-2 ∧ B 5 = 1.2078e2 :=
  table_10_values_of_mem_aux 155 (table_10_length_eq ▸ (by norm_num : 155 < 287)) rfl h

theorem table_10_row4075_values_of_mem (B : ℕ → ℝ)
    (h : ((4075), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8285e-13 ∧ B 2 = 1.5697e-9 ∧ B 3 = 6.4356e-6 ∧
      B 4 = 2.6386e-2 ∧ B 5 = 1.0818e2 :=
  table_10_values_of_mem_aux 156 (table_10_length_eq ▸ (by norm_num : 156 < 287)) rfl h

theorem table_10_row4100_values_of_mem (B : ℕ → ℝ)
    (h : ((4100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3428e-13 ∧ B 2 = 1.3789e-9 ∧ B 3 = 5.6879e-6 ∧
      B 4 = 2.3463e-2 ∧ B 5 = 9.6783e1 :=
  table_10_values_of_mem_aux 157 (table_10_length_eq ▸ (by norm_num : 157 < 287)) rfl h

theorem table_10_row4125_values_of_mem (B : ℕ → ℝ)
    (h : ((4125), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9206e-13 ∧ B 2 = 1.2120e-9 ∧ B 3 = 5.0299e-6 ∧
      B 4 = 2.0874e-2 ∧ B 5 = 8.6628e1 :=
  table_10_values_of_mem_aux 158 (table_10_length_eq ▸ (by norm_num : 158 < 287)) rfl h

theorem table_10_row4150_values_of_mem (B : ℕ → ℝ)
    (h : ((4150), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5566e-13 ∧ B 2 = 1.0674e-9 ∧ B 3 = 4.4563e-6 ∧
      B 4 = 1.8605e-2 ∧ B 5 = 7.7676e1 :=
  table_10_values_of_mem_aux 159 (table_10_length_eq ▸ (by norm_num : 159 < 287)) rfl h

theorem table_10_row4175_values_of_mem (B : ℕ → ℝ)
    (h : ((4175), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2309e-13 ∧ B 2 = 9.3698e-10 ∧ B 3 = 3.9353e-6 ∧
      B 4 = 1.6528e-2 ∧ B 5 = 6.9419e1 :=
  table_10_values_of_mem_aux 160 (table_10_length_eq ▸ (by norm_num : 160 < 287)) rfl h

theorem table_10_row4200_values_of_mem (B : ℕ → ℝ)
    (h : ((4200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9496e-13 ∧ B 2 = 8.2370e-10 ∧ B 3 = 3.4801e-6 ∧
      B 4 = 1.4704e-2 ∧ B 5 = 6.2122e1 :=
  table_10_values_of_mem_aux 161 (table_10_length_eq ▸ (by norm_num : 161 < 287)) rfl h

theorem table_10_row4225_values_of_mem (B : ℕ → ℝ)
    (h : ((4225), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7047e-13 ∧ B 2 = 7.2449e-10 ∧ B 3 = 3.0791e-6 ∧
      B 4 = 1.3086e-2 ∧ B 5 = 5.5616e1 :=
  table_10_values_of_mem_aux 162 (table_10_length_eq ▸ (by norm_num : 162 < 287)) rfl h

theorem table_10_row4250_values_of_mem (B : ℕ → ℝ)
    (h : ((4250), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4913e-13 ∧ B 2 = 6.3751e-10 ∧ B 3 = 2.7254e-6 ∧
      B 4 = 1.1651e-2 ∧ B 5 = 4.9808e1 :=
  table_10_values_of_mem_aux 163 (table_10_length_eq ▸ (by norm_num : 163 < 287)) rfl h

theorem table_10_row4275_values_of_mem (B : ℕ → ℝ)
    (h : ((4275), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3036e-13 ∧ B 2 = 5.6056e-10 ∧ B 3 = 2.4104e-6 ∧
      B 4 = 1.0365e-2 ∧ B 5 = 4.4568e1 :=
  table_10_values_of_mem_aux 164 (table_10_length_eq ▸ (by norm_num : 164 < 287)) rfl h

theorem table_10_row4300_values_of_mem (B : ℕ → ℝ)
    (h : ((4300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1396e-13 ∧ B 2 = 4.9288e-10 ∧ B 3 = 2.1317e-6 ∧
      B 4 = 9.2195e-3 ∧ B 5 = 3.9875e1 :=
  table_10_values_of_mem_aux 165 (table_10_length_eq ▸ (by norm_num : 165 < 287)) rfl h

theorem table_10_row4325_values_of_mem (B : ℕ → ℝ)
    (h : ((4325), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.9670e-14 ∧ B 2 = 4.3356e-10 ∧ B 3 = 1.8860e-6 ∧
      B 4 = 8.2041e-3 ∧ B 5 = 3.5688e1 :=
  table_10_values_of_mem_aux 166 (table_10_length_eq ▸ (by norm_num : 166 < 287)) rfl h

theorem table_10_row4350_values_of_mem (B : ℕ → ℝ)
    (h : ((4350), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.7210e-14 ∧ B 2 = 3.8154e-10 ∧ B 3 = 1.6693e-6 ∧
      B 4 = 7.3030e-3 ∧ B 5 = 3.1951e1 :=
  table_10_values_of_mem_aux 167 (table_10_length_eq ▸ (by norm_num : 167 < 287)) rfl h

theorem table_10_row4375_values_of_mem (B : ℕ → ℝ)
    (h : ((4375), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6274e-14 ∧ B 2 = 3.3561e-10 ∧ B 3 = 1.4767e-6 ∧
      B 4 = 6.4973e-3 ∧ B 5 = 2.8588e1 :=
  table_10_values_of_mem_aux 168 (table_10_length_eq ▸ (by norm_num : 168 < 287)) rfl h

theorem table_10_row4400_values_of_mem (B : ℕ → ℝ)
    (h : ((4400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6744e-14 ∧ B 2 = 2.9534e-10 ∧ B 3 = 1.3069e-6 ∧
      B 4 = 5.7829e-3 ∧ B 5 = 2.5590e1 :=
  table_10_values_of_mem_aux 169 (table_10_length_eq ▸ (by norm_num : 169 < 287)) rfl h

theorem table_10_row4425_values_of_mem (B : ℕ → ℝ)
    (h : ((4425), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8436e-14 ∧ B 2 = 2.6004e-10 ∧ B 3 = 1.1572e-6 ∧
      B 4 = 5.1495e-3 ∧ B 5 = 2.2915e1 :=
  table_10_values_of_mem_aux 170 (table_10_length_eq ▸ (by norm_num : 170 < 287)) rfl h

theorem table_10_row4450_values_of_mem (B : ℕ → ℝ)
    (h : ((4450), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.1174e-14 ∧ B 2 = 2.2901e-10 ∧ B 3 = 1.0248e-6 ∧
      B 4 = 4.5860e-3 ∧ B 5 = 2.0522e1 :=
  table_10_values_of_mem_aux 171 (table_10_length_eq ▸ (by norm_num : 171 < 287)) rfl h

theorem table_10_row4475_values_of_mem (B : ℕ → ℝ)
    (h : ((4475), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.4832e-14 ∧ B 2 = 2.0174e-10 ∧ B 3 = 9.0785e-7 ∧
      B 4 = 4.0853e-3 ∧ B 5 = 1.8384e1 :=
  table_10_values_of_mem_aux 172 (table_10_length_eq ▸ (by norm_num : 172 < 287)) rfl h

theorem table_10_row4500_values_of_mem (B : ℕ → ℝ)
    (h : ((4500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9290e-14 ∧ B 2 = 1.7779e-10 ∧ B 3 = 8.0450e-7 ∧
      B 4 = 3.6403e-3 ∧ B 5 = 1.6473e1 :=
  table_10_values_of_mem_aux 173 (table_10_length_eq ▸ (by norm_num : 173 < 287)) rfl h

theorem table_10_row4525_values_of_mem (B : ℕ → ℝ)
    (h : ((4525), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.4446e-14 ∧ B 2 = 1.5673e-10 ∧ B 3 = 7.1312e-7 ∧
      B 4 = 3.2447e-3 ∧ B 5 = 1.4763e1 :=
  table_10_values_of_mem_aux 174 (table_10_length_eq ▸ (by norm_num : 174 < 287)) rfl h

theorem table_10_row4550_values_of_mem (B : ℕ → ℝ)
    (h : ((4550), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.0155e-14 ∧ B 2 = 1.3796e-10 ∧ B 3 = 6.3117e-7 ∧
      B 4 = 2.8876e-3 ∧ B 5 = 1.3211e1 :=
  table_10_values_of_mem_aux 175 (table_10_length_eq ▸ (by norm_num : 175 < 287)) rfl h

theorem table_10_row4575_values_of_mem (B : ℕ → ℝ)
    (h : ((4575), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6404e-14 ∧ B 2 = 1.2146e-10 ∧ B 3 = 5.5870e-7 ∧
      B 4 = 2.5700e-3 ∧ B 5 = 1.1822e1 :=
  table_10_values_of_mem_aux 176 (table_10_length_eq ▸ (by norm_num : 176 < 287)) rfl h

theorem table_10_row4600_values_of_mem (B : ℕ → ℝ)
    (h : ((4600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3157e-14 ∧ B 2 = 1.0710e-10 ∧ B 3 = 4.9535e-7 ∧
      B 4 = 2.2910e-3 ∧ B 5 = 1.0596e1 :=
  table_10_values_of_mem_aux 177 (table_10_length_eq ▸ (by norm_num : 177 < 287)) rfl h

theorem table_10_row4625_values_of_mem (B : ℕ → ℝ)
    (h : ((4625), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.0259e-14 ∧ B 2 = 9.4206e-11 ∧ B 3 = 4.3806e-7 ∧
      B 4 = 2.0370e-3 ∧ B 5 = 9.4719e0 :=
  table_10_values_of_mem_aux 178 (table_10_length_eq ▸ (by norm_num : 178 < 287)) rfl h

theorem table_10_row4650_values_of_mem (B : ℕ → ℝ)
    (h : ((4650), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7753e-14 ∧ B 2 = 8.2997e-11 ∧ B 3 = 3.8801e-7 ∧
      B 4 = 1.8140e-3 ∧ B 5 = 8.4802e0 :=
  table_10_values_of_mem_aux 179 (table_10_length_eq ▸ (by norm_num : 179 < 287)) rfl h

theorem table_10_row4675_values_of_mem (B : ℕ → ℝ)
    (h : ((4675), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5563e-14 ∧ B 2 = 7.3144e-11 ∧ B 3 = 3.4378e-7 ∧
      B 4 = 1.6158e-3 ∧ B 5 = 7.5941e0 :=
  table_10_values_of_mem_aux 180 (table_10_length_eq ▸ (by norm_num : 180 < 287)) rfl h

theorem table_10_row4700_values_of_mem (B : ℕ → ℝ)
    (h : ((4700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3648e-14 ∧ B 2 = 6.4486e-11 ∧ B 3 = 3.0470e-7 ∧
      B 4 = 1.4397e-3 ∧ B 5 = 6.8026e0 :=
  table_10_values_of_mem_aux 181 (table_10_length_eq ▸ (by norm_num : 181 < 287)) rfl h

theorem table_10_row4725_values_of_mem (B : ℕ → ℝ)
    (h : ((4725), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1976e-14 ∧ B 2 = 5.6887e-11 ∧ B 3 = 2.7021e-7 ∧
      B 4 = 1.2835e-3 ∧ B 5 = 6.0967e0 :=
  table_10_values_of_mem_aux 182 (table_10_length_eq ▸ (by norm_num : 182 < 287)) rfl h

theorem table_10_row4750_values_of_mem (B : ℕ → ℝ)
    (h : ((4750), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0491e-14 ∧ B 2 = 5.0095e-11 ∧ B 3 = 2.3920e-7 ∧
      B 4 = 1.1422e-3 ∧ B 5 = 5.4540e0 :=
  table_10_values_of_mem_aux 183 (table_10_length_eq ▸ (by norm_num : 183 < 287)) rfl h

theorem table_10_row4775_values_of_mem (B : ℕ → ℝ)
    (h : ((4775), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.1894e-15 ∧ B 2 = 4.4109e-11 ∧ B 3 = 2.1172e-7 ∧
      B 4 = 1.0163e-3 ∧ B 5 = 4.8781e0 :=
  table_10_values_of_mem_aux 184 (table_10_length_eq ▸ (by norm_num : 184 < 287)) rfl h

theorem table_10_row4800_values_of_mem (B : ℕ → ℝ)
    (h : ((4800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.0537e-15 ∧ B 2 = 3.8859e-11 ∧ B 3 = 1.8750e-7 ∧
      B 4 = 9.0466e-4 ∧ B 5 = 4.3650e0 :=
  table_10_values_of_mem_aux 185 (table_10_length_eq ▸ (by norm_num : 185 < 287)) rfl h

theorem table_10_row4825_values_of_mem (B : ℕ → ℝ)
    (h : ((4825), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.0614e-15 ∧ B 2 = 3.4248e-11 ∧ B 3 = 1.6610e-7 ∧
      B 4 = 8.0560e-4 ∧ B 5 = 3.9072e0 :=
  table_10_values_of_mem_aux 186 (table_10_length_eq ▸ (by norm_num : 186 < 287)) rfl h

theorem table_10_row4850_values_of_mem (B : ℕ → ℝ)
    (h : ((4850), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.1951e-15 ∧ B 2 = 3.0201e-11 ∧ B 3 = 1.4723e-7 ∧
      B 4 = 7.1775e-4 ∧ B 5 = 3.4990e0 :=
  table_10_values_of_mem_aux 187 (table_10_length_eq ▸ (by norm_num : 187 < 287)) rfl h

theorem table_10_row4875_values_of_mem (B : ℕ → ℝ)
    (h : ((4875), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4361e-15 ∧ B 2 = 2.6637e-11 ∧ B 3 = 1.3052e-7 ∧
      B 4 = 6.3955e-4 ∧ B 5 = 3.1338e0 :=
  table_10_values_of_mem_aux 188 (table_10_length_eq ▸ (by norm_num : 188 < 287)) rfl h

theorem table_10_row4900_values_of_mem (B : ℕ → ℝ)
    (h : ((4900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.7720e-15 ∧ B 2 = 2.3502e-11 ∧ B 3 = 1.1575e-7 ∧
      B 4 = 5.7006e-4 ∧ B 5 = 2.8076e0 :=
  table_10_values_of_mem_aux 189 (table_10_length_eq ▸ (by norm_num : 189 < 287)) rfl h

theorem table_10_row4925_values_of_mem (B : ℕ → ℝ)
    (h : ((4925), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1878e-15 ∧ B 2 = 2.0729e-11 ∧ B 3 = 1.0261e-7 ∧
      B 4 = 5.0792e-4 ∧ B 5 = 2.5142e0 :=
  table_10_values_of_mem_aux 190 (table_10_length_eq ▸ (by norm_num : 190 < 287)) rfl h

theorem table_10_row4950_values_of_mem (B : ℕ → ℝ)
    (h : ((4950), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6731e-15 ∧ B 2 = 1.8274e-11 ∧ B 3 = 9.0911e-8 ∧
      B 4 = 4.5228e-4 ∧ B 5 = 2.2501e0 :=
  table_10_values_of_mem_aux 191 (table_10_length_eq ▸ (by norm_num : 191 < 287)) rfl h

theorem table_10_row4975_values_of_mem (B : ℕ → ℝ)
    (h : ((4975), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.2229e-15 ∧ B 2 = 1.6114e-11 ∧ B 3 = 8.0571e-8 ∧
      B 4 = 4.0286e-4 ∧ B 5 = 2.0143e0 :=
  table_10_values_of_mem_aux 192 (table_10_length_eq ▸ (by norm_num : 192 < 287)) rfl h

theorem table_10_row5000_values_of_mem (B : ℕ → ℝ)
    (h : ((5000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8715e-15 ∧ B 2 = 1.4645e-11 ∧ B 3 = 7.4687e-8 ∧
      B 4 = 3.8090e-4 ∧ B 5 = 1.9426e0 :=
  table_10_values_of_mem_aux 193 (table_10_length_eq ▸ (by norm_num : 193 < 287)) rfl h

theorem table_10_row5100_values_of_mem (B : ℕ → ℝ)
    (h : ((5100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7087e-15 ∧ B 2 = 8.8850e-12 ∧ B 3 = 4.6202e-8 ∧
      B 4 = 2.4025e-4 ∧ B 5 = 1.2493e0 :=
  table_10_values_of_mem_aux 194 (table_10_length_eq ▸ (by norm_num : 194 < 287)) rfl h

theorem table_10_row5200_values_of_mem (B : ℕ → ℝ)
    (h : ((5200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0185e-15 ∧ B 2 = 5.3980e-12 ∧ B 3 = 2.8610e-8 ∧
      B 4 = 1.5163e-4 ∧ B 5 = 8.0364e-1 :=
  table_10_values_of_mem_aux 195 (table_10_length_eq ▸ (by norm_num : 195 < 287)) rfl h

theorem table_10_row5300_values_of_mem (B : ℕ → ℝ)
    (h : ((5300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0977e-16 ∧ B 2 = 3.2927e-12 ∧ B 3 = 1.7781e-8 ∧
      B 4 = 9.6016e-5 ∧ B 5 = 5.1849e-1 :=
  table_10_values_of_mem_aux 196 (table_10_length_eq ▸ (by norm_num : 196 < 287)) rfl h

theorem table_10_row5400_values_of_mem (B : ℕ → ℝ)
    (h : ((5400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6472e-16 ∧ B 2 = 2.0059e-12 ∧ B 3 = 1.1033e-8 ∧
      B 4 = 6.0679e-5 ∧ B 5 = 3.3374e-1 :=
  table_10_values_of_mem_aux 197 (table_10_length_eq ▸ (by norm_num : 197 < 287)) rfl h

theorem table_10_row5500_values_of_mem (B : ℕ → ℝ)
    (h : ((5500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.1916e-16 ∧ B 2 = 1.2273e-12 ∧ B 3 = 6.8727e-9 ∧
      B 4 = 3.8487e-5 ∧ B 5 = 2.1553e-1 :=
  table_10_values_of_mem_aux 198 (table_10_length_eq ▸ (by norm_num : 198 < 287)) rfl h

theorem table_10_row5600_values_of_mem (B : ℕ → ℝ)
    (h : ((5600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3217e-16 ∧ B 2 = 7.5337e-13 ∧ B 3 = 4.2942e-9 ∧
      B 4 = 2.4477e-5 ∧ B 5 = 1.3952e-1 :=
  table_10_values_of_mem_aux 199 (table_10_length_eq ▸ (by norm_num : 199 < 287)) rfl h

theorem table_10_row5700_values_of_mem (B : ℕ → ℝ)
    (h : ((5700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.0079e-17 ∧ B 2 = 4.6446e-13 ∧ B 3 = 2.6938e-9 ∧
      B 4 = 1.5624e-5 ∧ B 5 = 9.0621e-2 :=
  table_10_values_of_mem_aux 200 (table_10_length_eq ▸ (by norm_num : 200 < 287)) rfl h

theorem table_10_row5800_values_of_mem (B : ℕ → ℝ)
    (h : ((5800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.8518e-17 ∧ B 2 = 2.8626e-13 ∧ B 3 = 1.6889e-9 ∧
      B 4 = 9.9646e-6 ∧ B 5 = 5.8791e-2 :=
  table_10_values_of_mem_aux 201 (table_10_length_eq ▸ (by norm_num : 201 < 287)) rfl h

theorem table_10_row5900_values_of_mem (B : ℕ → ℝ)
    (h : ((5900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.9482e-17 ∧ B 2 = 1.7689e-13 ∧ B 3 = 1.0614e-9 ∧
      B 4 = 6.3682e-6 ∧ B 5 = 3.8209e-2 :=
  table_10_values_of_mem_aux 202 (table_10_length_eq ▸ (by norm_num : 202 < 287)) rfl h

theorem table_10_row6000_values_of_mem (B : ℕ → ℝ)
    (h : ((6000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7952e-17 ∧ B 2 = 1.0951e-13 ∧ B 3 = 6.6798e-10 ∧
      B 4 = 4.0747e-6 ∧ B 5 = 2.4855e-2 :=
  table_10_values_of_mem_aux 203 (table_10_length_eq ▸ (by norm_num : 203 < 287)) rfl h

theorem table_10_row6100_values_of_mem (B : ℕ → ℝ)
    (h : ((6100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0987e-17 ∧ B 2 = 6.8120e-14 ∧ B 3 = 4.2234e-10 ∧
      B 4 = 2.6185e-6 ∧ B 5 = 1.6235e-2 :=
  table_10_values_of_mem_aux 204 (table_10_length_eq ▸ (by norm_num : 204 < 287)) rfl h

theorem table_10_row6200_values_of_mem (B : ℕ → ℝ)
    (h : ((6200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.7178e-18 ∧ B 2 = 4.2322e-14 ∧ B 3 = 2.6663e-10 ∧
      B 4 = 1.6798e-6 ∧ B 5 = 1.0583e-2 :=
  table_10_values_of_mem_aux 205 (table_10_length_eq ▸ (by norm_num : 205 < 287)) rfl h

theorem table_10_row6300_values_of_mem (B : ℕ → ℝ)
    (h : ((6300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.1267e-18 ∧ B 2 = 2.6411e-14 ∧ B 3 = 1.6903e-10 ∧
      B 4 = 1.0818e-6 ∧ B 5 = 6.9235e-3 :=
  table_10_values_of_mem_aux 206 (table_10_length_eq ▸ (by norm_num : 206 < 287)) rfl h

theorem table_10_row6400_values_of_mem (B : ℕ → ℝ)
    (h : ((6400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5481e-18 ∧ B 2 = 1.6563e-14 ∧ B 3 = 1.0766e-10 ∧
      B 4 = 6.9977e-7 ∧ B 5 = 4.5485e-3 :=
  table_10_values_of_mem_aux 207 (table_10_length_eq ▸ (by norm_num : 207 < 287)) rfl h

theorem table_10_row6500_values_of_mem (B : ℕ → ℝ)
    (h : ((6500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5741e-18 ∧ B 2 = 1.0389e-14 ∧ B 3 = 6.8566e-11 ∧
      B 4 = 4.5253e-7 ∧ B 5 = 2.9867e-3 :=
  table_10_values_of_mem_aux 208 (table_10_length_eq ▸ (by norm_num : 208 < 287)) rfl h

theorem table_10_row6600_values_of_mem (B : ℕ → ℝ)
    (h : ((6600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.7287e-19 ∧ B 2 = 6.5182e-15 ∧ B 3 = 4.3672e-11 ∧
      B 4 = 2.9260e-7 ∧ B 5 = 1.9604e-3 :=
  table_10_values_of_mem_aux 209 (table_10_length_eq ▸ (by norm_num : 209 < 287)) rfl h

theorem table_10_row6700_values_of_mem (B : ℕ → ℝ)
    (h : ((6700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0447e-19 ∧ B 2 = 4.1104e-15 ∧ B 3 = 2.7951e-11 ∧
      B 4 = 1.9007e-7 ∧ B 5 = 1.2924e-3 :=
  table_10_values_of_mem_aux 210 (table_10_length_eq ▸ (by norm_num : 210 < 287)) rfl h

theorem table_10_row6800_values_of_mem (B : ℕ → ℝ)
    (h : ((6800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7651e-19 ∧ B 2 = 2.5979e-15 ∧ B 3 = 1.7926e-11 ∧
      B 4 = 1.2369e-7 ∧ B 5 = 8.5344e-4 :=
  table_10_values_of_mem_aux 211 (table_10_length_eq ▸ (by norm_num : 211 < 287)) rfl h

theorem table_10_row6900_values_of_mem (B : ℕ → ℝ)
    (h : ((6900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3554e-19 ∧ B 2 = 1.6488e-15 ∧ B 3 = 1.1542e-11 ∧
      B 4 = 8.0791e-8 ∧ B 5 = 5.6554e-4 :=
  table_10_values_of_mem_aux 212 (table_10_length_eq ▸ (by norm_num : 212 < 287)) rfl h

theorem table_10_row7000_values_of_mem (B : ℕ → ℝ)
    (h : ((7000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4744e-19 ∧ B 2 = 1.0468e-15 ∧ B 3 = 7.4322e-12 ∧
      B 4 = 5.2769e-8 ∧ B 5 = 3.7466e-4 :=
  table_10_values_of_mem_aux 213 (table_10_length_eq ▸ (by norm_num : 213 < 287)) rfl h

theorem table_10_row7100_values_of_mem (B : ℕ → ℝ)
    (h : ((7100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.2826e-20 ∧ B 2 = 6.6834e-16 ∧ B 3 = 4.8121e-12 ∧
      B 4 = 3.4647e-8 ∧ B 5 = 2.4946e-4 :=
  table_10_values_of_mem_aux 214 (table_10_length_eq ▸ (by norm_num : 214 < 287)) rfl h

theorem table_10_row7200_values_of_mem (B : ℕ → ℝ)
    (h : ((7200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.8601e-20 ∧ B 2 = 4.2779e-16 ∧ B 3 = 3.1229e-12 ∧
      B 4 = 2.2797e-8 ∧ B 5 = 1.6642e-4 :=
  table_10_values_of_mem_aux 215 (table_10_length_eq ▸ (by norm_num : 215 < 287)) rfl h

theorem table_10_row7300_values_of_mem (B : ℕ → ℝ)
    (h : ((7300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7014e-20 ∧ B 2 = 2.7390e-16 ∧ B 3 = 2.0269e-12 ∧
      B 4 = 1.4999e-8 ∧ B 5 = 1.1099e-4 :=
  table_10_values_of_mem_aux 216 (table_10_length_eq ▸ (by norm_num : 216 < 287)) rfl h

theorem table_10_row7400_values_of_mem (B : ℕ → ℝ)
    (h : ((7400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.3488e-20 ∧ B 2 = 1.7616e-16 ∧ B 3 = 1.3212e-12 ∧
      B 4 = 9.9091e-9 ∧ B 5 = 7.4318e-5 :=
  table_10_values_of_mem_aux 217 (table_10_length_eq ▸ (by norm_num : 217 < 287)) rfl h

theorem table_10_row7500_values_of_mem (B : ℕ → ℝ)
    (h : ((7500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4907e-20 ∧ B 2 = 1.1330e-16 ∧ B 3 = 8.6105e-13 ∧
      B 4 = 6.5440e-9 ∧ B 5 = 4.9734e-5 :=
  table_10_values_of_mem_aux 218 (table_10_length_eq ▸ (by norm_num : 218 < 287)) rfl h

theorem table_10_row7600_values_of_mem (B : ℕ → ℝ)
    (h : ((7600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.4822e-21 ∧ B 2 = 7.3013e-17 ∧ B 3 = 5.6220e-13 ∧
      B 4 = 4.3289e-9 ∧ B 5 = 3.3333e-5 :=
  table_10_values_of_mem_aux 219 (table_10_length_eq ▸ (by norm_num : 219 < 287)) rfl h

theorem table_10_row7700_values_of_mem (B : ℕ → ℝ)
    (h : ((7700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.0569e-21 ∧ B 2 = 4.7244e-17 ∧ B 3 = 3.6850e-13 ∧
      B 4 = 2.8743e-9 ∧ B 5 = 2.2420e-5 :=
  table_10_values_of_mem_aux 220 (table_10_length_eq ▸ (by norm_num : 220 < 287)) rfl h

theorem table_10_row7800_values_of_mem (B : ℕ → ℝ)
    (h : ((7800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8811e-21 ∧ B 2 = 3.0661e-17 ∧ B 3 = 2.4222e-13 ∧
      B 4 = 1.9136e-9 ∧ B 5 = 1.5117e-5 :=
  table_10_values_of_mem_aux 221 (table_10_length_eq ▸ (by norm_num : 221 < 287)) rfl h

theorem table_10_row7900_values_of_mem (B : ℕ → ℝ)
    (h : ((7900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.4928e-21 ∧ B 2 = 1.9942e-17 ∧ B 3 = 1.5954e-13 ∧
      B 4 = 1.2763e-9 ∧ B 5 = 1.0211e-5 :=
  table_10_values_of_mem_aux 222 (table_10_length_eq ▸ (by norm_num : 222 < 287)) rfl h

theorem table_10_row8000_values_of_mem (B : ℕ → ℝ)
    (h : ((8000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.6007e-21 ∧ B 2 = 1.2965e-17 ∧ B 3 = 1.0502e-13 ∧
      B 4 = 8.5065e-10 ∧ B 5 = 6.8903e-6 :=
  table_10_values_of_mem_aux 223 (table_10_length_eq ▸ (by norm_num : 223 < 287)) rfl h

theorem table_10_row8100_values_of_mem (B : ℕ → ℝ)
    (h : ((8100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0326e-21 ∧ B 2 = 8.4674e-18 ∧ B 3 = 6.9433e-14 ∧
      B 4 = 5.6935e-10 ∧ B 5 = 4.6687e-6 :=
  table_10_values_of_mem_aux 224 (table_10_length_eq ▸ (by norm_num : 224 < 287)) rfl h

theorem table_10_row8200_values_of_mem (B : ℕ → ℝ)
    (h : ((8200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.6828e-22 ∧ B 2 = 5.5467e-18 ∧ B 3 = 4.6038e-14 ∧
      B 4 = 3.8212e-10 ∧ B 5 = 3.1716e-6 :=
  table_10_values_of_mem_aux 225 (table_10_length_eq ▸ (by norm_num : 225 < 287)) rfl h

theorem table_10_row8300_values_of_mem (B : ℕ → ℝ)
    (h : ((8300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.3257e-22 ∧ B 2 = 3.6336e-18 ∧ B 3 = 3.0522e-14 ∧
      B 4 = 2.5639e-10 ∧ B 5 = 2.1536e-6 :=
  table_10_values_of_mem_aux 226 (table_10_length_eq ▸ (by norm_num : 226 < 287)) rfl h

theorem table_10_row8400_values_of_mem (B : ℕ → ℝ)
    (h : ((8400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8105e-22 ∧ B 2 = 2.3889e-18 ∧ B 3 = 2.0306e-14 ∧
      B 4 = 1.7260e-10 ∧ B 5 = 1.4671e-6 :=
  table_10_values_of_mem_aux 227 (table_10_length_eq ▸ (by norm_num : 227 < 287)) rfl h

theorem table_10_row8500_values_of_mem (B : ℕ → ℝ)
    (h : ((8500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8315e-22 ∧ B 2 = 1.5751e-18 ∧ B 3 = 1.3546e-14 ∧
      B 4 = 1.1650e-10 ∧ B 5 = 1.0019e-6 :=
  table_10_values_of_mem_aux 228 (table_10_length_eq ▸ (by norm_num : 228 < 287)) rfl h

theorem table_10_row8600_values_of_mem (B : ℕ → ℝ)
    (h : ((8600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1981e-22 ∧ B 2 = 1.0423e-18 ∧ B 3 = 9.0682e-15 ∧
      B 4 = 7.8893e-11 ∧ B 5 = 6.8637e-7 :=
  table_10_values_of_mem_aux 229 (table_10_length_eq ▸ (by norm_num : 229 < 287)) rfl h

theorem table_10_row8700_values_of_mem (B : ℕ → ℝ)
    (h : ((8700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.8220e-23 ∧ B 2 = 6.8834e-19 ∧ B 3 = 6.0574e-15 ∧
      B 4 = 5.3305e-11 ∧ B 5 = 4.6908e-7 :=
  table_10_values_of_mem_aux 230 (table_10_length_eq ▸ (by norm_num : 230 < 287)) rfl h

theorem table_10_row8800_values_of_mem (B : ℕ → ℝ)
    (h : ((8800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.1585e-23 ∧ B 2 = 4.5910e-19 ∧ B 3 = 4.0860e-15 ∧
      B 4 = 3.6366e-11 ∧ B 5 = 3.2365e-7 :=
  table_10_values_of_mem_aux 231 (table_10_length_eq ▸ (by norm_num : 231 < 287)) rfl h

theorem table_10_row8900_values_of_mem (B : ℕ → ℝ)
    (h : ((8900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.3882e-23 ∧ B 2 = 3.0494e-19 ∧ B 3 = 2.7445e-15 ∧
      B 4 = 2.4700e-11 ∧ B 5 = 2.2230e-7 :=
  table_10_values_of_mem_aux 232 (table_10_length_eq ▸ (by norm_num : 232 < 287)) rfl h

theorem table_10_row9000_values_of_mem (B : ℕ → ℝ)
    (h : ((9000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2252e-23 ∧ B 2 = 2.0250e-19 ∧ B 3 = 1.8427e-15 ∧
      B 4 = 1.6769e-11 ∧ B 5 = 1.5260e-7 :=
  table_10_values_of_mem_aux 233 (table_10_length_eq ▸ (by norm_num : 233 < 287)) rfl h

theorem table_10_row9100_values_of_mem (B : ℕ → ℝ)
    (h : ((9100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.4641e-23 ∧ B 2 = 1.3470e-19 ∧ B 3 = 1.2392e-15 ∧
      B 4 = 1.1401e-11 ∧ B 5 = 1.0489e-7 :=
  table_10_values_of_mem_aux 234 (table_10_length_eq ▸ (by norm_num : 234 < 287)) rfl h

theorem table_10_row9200_values_of_mem (B : ℕ → ℝ)
    (h : ((9200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.6777e-24 ∧ B 2 = 9.0003e-20 ∧ B 3 = 8.3703e-16 ∧
      B 4 = 7.7844e-12 ∧ B 5 = 7.2395e-8 :=
  table_10_values_of_mem_aux 235 (table_10_length_eq ▸ (by norm_num : 235 < 287)) rfl h

theorem table_10_row9300_values_of_mem (B : ℕ → ℝ)
    (h : ((9300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.4195e-24 ∧ B 2 = 6.0343e-20 ∧ B 3 = 5.6723e-16 ∧
      B 4 = 5.3319e-12 ∧ B 5 = 5.0120e-8 :=
  table_10_values_of_mem_aux 236 (table_10_length_eq ▸ (by norm_num : 236 < 287)) rfl h

theorem table_10_row9400_values_of_mem (B : ℕ → ℝ)
    (h : ((9400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.2972e-24 ∧ B 2 = 4.0823e-20 ∧ B 3 = 3.8782e-16 ∧
      B 4 = 3.6843e-12 ∧ B 5 = 3.5001e-8 :=
  table_10_values_of_mem_aux 237 (table_10_length_eq ▸ (by norm_num : 237 < 287)) rfl h

theorem table_10_row9500_values_of_mem (B : ℕ → ℝ)
    (h : ((9500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.8512e-24 ∧ B 2 = 2.7372e-20 ∧ B 3 = 2.6277e-16 ∧
      B 4 = 2.5226e-12 ∧ B 5 = 2.4217e-8 :=
  table_10_values_of_mem_aux 238 (table_10_length_eq ▸ (by norm_num : 238 < 287)) rfl h

theorem table_10_row9600_values_of_mem (B : ℕ → ℝ)
    (h : ((9600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9059e-24 ∧ B 2 = 1.8487e-20 ∧ B 3 = 1.7932e-16 ∧
      B 4 = 1.7395e-12 ∧ B 5 = 1.6873e-8 :=
  table_10_values_of_mem_aux 239 (table_10_length_eq ▸ (by norm_num : 239 < 287)) rfl h

theorem table_10_row9700_values_of_mem (B : ℕ → ℝ)
    (h : ((9700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2689e-24 ∧ B 2 = 1.2435e-20 ∧ B 3 = 1.2187e-16 ∧
      B 4 = 1.1943e-12 ∧ B 5 = 1.1704e-8 :=
  table_10_values_of_mem_aux 240 (table_10_length_eq ▸ (by norm_num : 240 < 287)) rfl h

theorem table_10_row9800_values_of_mem (B : ℕ → ℝ)
    (h : ((9800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.4841e-25 ∧ B 2 = 8.3992e-21 ∧ B 3 = 8.3152e-17 ∧
      B 4 = 8.2321e-13 ∧ B 5 = 8.1497e-9 :=
  table_10_values_of_mem_aux 241 (table_10_length_eq ▸ (by norm_num : 241 < 287)) rfl h

theorem table_10_row9900_values_of_mem (B : ℕ → ℝ)
    (h : ((9900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7395e-25 ∧ B 2 = 5.7395e-21 ∧ B 3 = 5.7395e-17 ∧
      B 4 = 5.7395e-13 ∧ B 5 = 5.7395e-9 :=
  table_10_values_of_mem_aux 242 (table_10_length_eq ▸ (by norm_num : 242 < 287)) rfl h

theorem table_10_row10000_values_of_mem (B : ℕ → ℝ)
    (h : ((10000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.8228e-25 ∧ B 2 = 3.8610e-21 ∧ B 3 = 3.8996e-17 ∧
      B 4 = 3.9386e-13 ∧ B 5 = 3.9780e-9 :=
  table_10_values_of_mem_aux 243 (table_10_length_eq ▸ (by norm_num : 243 < 287)) rfl h

theorem table_10_row10100_values_of_mem (B : ℕ → ℝ)
    (h : ((10100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5745e-25 ∧ B 2 = 2.6260e-21 ∧ B 3 = 2.6785e-17 ∧
      B 4 = 2.7321e-13 ∧ B 5 = 2.7867e-9 :=
  table_10_values_of_mem_aux 244 (table_10_length_eq ▸ (by norm_num : 244 < 287)) rfl h

theorem table_10_row10200_values_of_mem (B : ℕ → ℝ)
    (h : ((10200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7389e-25 ∧ B 2 = 1.7911e-21 ∧ B 3 = 1.8448e-17 ∧
      B 4 = 1.9001e-13 ∧ B 5 = 1.9571e-9 :=
  table_10_values_of_mem_aux 245 (table_10_length_eq ▸ (by norm_num : 245 < 287)) rfl h

theorem table_10_row10300_values_of_mem (B : ℕ → ℝ)
    (h : ((10300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1734e-25 ∧ B 2 = 1.2203e-21 ∧ B 3 = 1.2691e-17 ∧
      B 4 = 1.3199e-13 ∧ B 5 = 1.3727e-9 :=
  table_10_values_of_mem_aux 246 (table_10_length_eq ▸ (by norm_num : 246 < 287)) rfl h

theorem table_10_row10400_values_of_mem (B : ℕ → ℝ)
    (h : ((10400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9556e-26 ∧ B 2 = 8.3534e-22 ∧ B 3 = 8.7710e-18 ∧
      B 4 = 9.2096e-14 ∧ B 5 = 9.6701e-10 :=
  table_10_values_of_mem_aux 247 (table_10_length_eq ▸ (by norm_num : 247 < 287)) rfl h

theorem table_10_row10500_values_of_mem (B : ℕ → ℝ)
    (h : ((10500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4076e-26 ∧ B 2 = 5.7321e-22 ∧ B 3 = 6.0760e-18 ∧
      B 4 = 6.4406e-14 ∧ B 5 = 6.8270e-10 :=
  table_10_values_of_mem_aux 248 (table_10_length_eq ▸ (by norm_num : 248 < 287)) rfl h

theorem table_10_row10600_values_of_mem (B : ℕ → ℝ)
    (h : ((10600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.6845e-26 ∧ B 2 = 3.9424e-22 ∧ B 3 = 4.2184e-18 ∧
      B 4 = 4.5136e-14 ∧ B 5 = 4.8296e-10 :=
  table_10_values_of_mem_aux 249 (table_10_length_eq ▸ (by norm_num : 249 < 287)) rfl h

theorem table_10_row10700_values_of_mem (B : ℕ → ℝ)
    (h : ((10700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5150e-26 ∧ B 2 = 2.7162e-22 ∧ B 3 = 2.9335e-18 ∧
      B 4 = 3.1682e-14 ∧ B 5 = 3.4216e-10 :=
  table_10_values_of_mem_aux 250 (table_10_length_eq ▸ (by norm_num : 250 < 287)) rfl h

theorem table_10_row10800_values_of_mem (B : ℕ → ℝ)
    (h : ((10800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7201e-26 ∧ B 2 = 1.8749e-22 ∧ B 3 = 2.0436e-18 ∧
      B 4 = 2.2276e-14 ∧ B 5 = 2.4280e-10 :=
  table_10_values_of_mem_aux 251 (table_10_length_eq ▸ (by norm_num : 251 < 287)) rfl h

theorem table_10_row10900_values_of_mem (B : ℕ → ℝ)
    (h : ((10900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1639e-26 ∧ B 2 = 1.2803e-22 ∧ B 3 = 1.4083e-18 ∧
      B 4 = 1.5492e-14 ∧ B 5 = 1.7041e-10 :=
  table_10_values_of_mem_aux 252 (table_10_length_eq ▸ (by norm_num : 252 < 287)) rfl h

theorem table_10_row11000_values_of_mem (B : ℕ → ℝ)
    (h : ((11000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.9283e-27 ∧ B 2 = 8.8005e-23 ∧ B 3 = 9.7685e-19 ∧
      B 4 = 1.0843e-14 ∧ B 5 = 1.2036e-10 :=
  table_10_values_of_mem_aux 253 (table_10_length_eq ▸ (by norm_num : 253 < 287)) rfl h

theorem table_10_row11100_values_of_mem (B : ℕ → ℝ)
    (h : ((11100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.4156e-27 ∧ B 2 = 6.0654e-23 ∧ B 3 = 6.7933e-19 ∧
      B 4 = 7.6085e-15 ∧ B 5 = 8.5215e-11 :=
  table_10_values_of_mem_aux 254 (table_10_length_eq ▸ (by norm_num : 254 < 287)) rfl h

theorem table_10_row11200_values_of_mem (B : ℕ → ℝ)
    (h : ((11200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7120e-27 ∧ B 2 = 4.1945e-23 ∧ B 3 = 4.7398e-19 ∧
      B 4 = 5.3560e-15 ∧ B 5 = 6.0522e-11 :=
  table_10_values_of_mem_aux 255 (table_10_length_eq ▸ (by norm_num : 255 < 287)) rfl h

theorem table_10_row11300_values_of_mem (B : ℕ → ℝ)
    (h : ((11300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5509e-27 ∧ B 2 = 2.9080e-23 ∧ B 3 = 3.3151e-19 ∧
      B 4 = 3.7792e-15 ∧ B 5 = 4.3083e-11 :=
  table_10_values_of_mem_aux 256 (table_10_length_eq ▸ (by norm_num : 256 < 287)) rfl h

theorem table_10_row11400_values_of_mem (B : ℕ → ℝ)
    (h : ((11400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.7569e-27 ∧ B 2 = 2.0205e-23 ∧ B 3 = 2.3235e-19 ∧
      B 4 = 2.6721e-15 ∧ B 5 = 3.0729e-11 :=
  table_10_values_of_mem_aux 257 (table_10_length_eq ▸ (by norm_num : 257 < 287)) rfl h

theorem table_10_row11500_values_of_mem (B : ℕ → ℝ)
    (h : ((11500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.2102e-27 ∧ B 2 = 1.4039e-23 ∧ B 3 = 1.6285e-19 ∧
      B 4 = 1.8890e-15 ∧ B 5 = 2.1913e-11 :=
  table_10_values_of_mem_aux 258 (table_10_length_eq ▸ (by norm_num : 258 < 287)) rfl h

theorem table_10_row11600_values_of_mem (B : ℕ → ℝ)
    (h : ((11600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 8.3444e-28 ∧ B 2 = 9.7630e-24 ∧ B 3 = 1.1423e-19 ∧
      B 4 = 1.3365e-15 ∧ B 5 = 1.5637e-11 :=
  table_10_values_of_mem_aux 259 (table_10_length_eq ▸ (by norm_num : 259 < 287)) rfl h

theorem table_10_row11700_values_of_mem (B : ℕ → ℝ)
    (h : ((11700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.7692e-28 ∧ B 2 = 6.8076e-24 ∧ B 3 = 8.0330e-20 ∧
      B 4 = 9.4789e-16 ∧ B 5 = 1.1185e-11 :=
  table_10_values_of_mem_aux 260 (table_10_length_eq ▸ (by norm_num : 260 < 287)) rfl h

theorem table_10_row11800_values_of_mem (B : ℕ → ℝ)
    (h : ((11800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.9987e-28 ∧ B 2 = 4.7584e-24 ∧ B 3 = 5.6625e-20 ∧
      B 4 = 6.7384e-16 ∧ B 5 = 8.0187e-12 :=
  table_10_values_of_mem_aux 261 (table_10_length_eq ▸ (by norm_num : 261 < 287)) rfl h

theorem table_10_row11900_values_of_mem (B : ℕ → ℝ)
    (h : ((11900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7776e-28 ∧ B 2 = 3.3331e-24 ∧ B 3 = 3.9997e-20 ∧
      B 4 = 4.7996e-16 ∧ B 5 = 5.7595e-12 :=
  table_10_values_of_mem_aux 262 (table_10_length_eq ▸ (by norm_num : 262 < 287)) rfl h

theorem table_10_row12000_values_of_mem (B : ℕ → ℝ)
    (h : ((12000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.9330e-28 ∧ B 2 = 2.3390e-24 ∧ B 3 = 2.8302e-20 ∧
      B 4 = 3.4245e-16 ∧ B 5 = 4.1436e-12 :=
  table_10_values_of_mem_aux 263 (table_10_length_eq ▸ (by norm_num : 263 < 287)) rfl h

theorem table_10_row12100_values_of_mem (B : ℕ → ℝ)
    (h : ((12100), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.3477e-28 ∧ B 2 = 1.6442e-24 ∧ B 3 = 2.0060e-20 ∧
      B 4 = 2.4473e-16 ∧ B 5 = 2.9857e-12 :=
  table_10_values_of_mem_aux 264 (table_10_length_eq ▸ (by norm_num : 264 < 287)) rfl h

theorem table_10_row12200_values_of_mem (B : ℕ → ℝ)
    (h : ((12200), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.3146e-29 ∧ B 2 = 1.1457e-24 ∧ B 3 = 1.4092e-20 ∧
      B 4 = 1.7333e-16 ∧ B 5 = 2.1320e-12 :=
  table_10_values_of_mem_aux 265 (table_10_length_eq ▸ (by norm_num : 265 < 287)) rfl h

theorem table_10_row12300_values_of_mem (B : ℕ → ℝ)
    (h : ((12300), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5069e-29 ∧ B 2 = 8.0685e-25 ∧ B 3 = 1.0005e-20 ∧
      B 4 = 1.2406e-16 ∧ B 5 = 1.5384e-12 :=
  table_10_values_of_mem_aux 266 (table_10_length_eq ▸ (by norm_num : 266 < 287)) rfl h

theorem table_10_row12400_values_of_mem (B : ℕ → ℝ)
    (h : ((12400), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 4.5539e-29 ∧ B 2 = 5.6924e-25 ∧ B 3 = 7.1155e-21 ∧
      B 4 = 8.8944e-17 ∧ B 5 = 1.1118e-12 :=
  table_10_values_of_mem_aux 267 (table_10_length_eq ▸ (by norm_num : 267 < 287)) rfl h

theorem table_10_row12500_values_of_mem (B : ℕ → ℝ)
    (h : ((12500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.1924e-29 ∧ B 2 = 4.0224e-25 ∧ B 3 = 5.0682e-21 ∧
      B 4 = 6.3859e-17 ∧ B 5 = 8.0462e-13 :=
  table_10_values_of_mem_aux 268 (table_10_length_eq ▸ (by norm_num : 268 < 287)) rfl h

theorem table_10_row12600_values_of_mem (B : ℕ → ℝ)
    (h : ((12600), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.2307e-29 ∧ B 2 = 2.8330e-25 ∧ B 3 = 3.5979e-21 ∧
      B 4 = 4.5693e-17 ∧ B 5 = 5.8030e-13 :=
  table_10_values_of_mem_aux 269 (table_10_length_eq ▸ (by norm_num : 269 < 287)) rfl h

theorem table_10_row12700_values_of_mem (B : ℕ → ℝ)
    (h : ((12700), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5599e-29 ∧ B 2 = 1.9967e-25 ∧ B 3 = 2.5558e-21 ∧
      B 4 = 3.2714e-17 ∧ B 5 = 4.1873e-13 :=
  table_10_values_of_mem_aux 270 (table_10_length_eq ▸ (by norm_num : 270 < 287)) rfl h

theorem table_10_row12800_values_of_mem (B : ℕ → ℝ)
    (h : ((12800), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.0940e-29 ∧ B 2 = 1.4112e-25 ∧ B 3 = 1.8205e-21 ∧
      B 4 = 2.3484e-17 ∧ B 5 = 3.0294e-13 :=
  table_10_values_of_mem_aux 271 (table_10_length_eq ▸ (by norm_num : 271 < 287)) rfl h

theorem table_10_row12900_values_of_mem (B : ℕ → ℝ)
    (h : ((12900), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 7.6899e-30 ∧ B 2 = 9.9969e-26 ∧ B 3 = 1.2996e-21 ∧
      B 4 = 1.6895e-17 ∧ B 5 = 2.1963e-13 :=
  table_10_values_of_mem_aux 272 (table_10_length_eq ▸ (by norm_num : 272 < 287)) rfl h

theorem table_10_row13000_values_of_mem (B : ℕ → ℝ)
    (h : ((13000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.5830e-30 ∧ B 2 = 7.5370e-26 ∧ B 3 = 1.0175e-21 ∧
      B 4 = 1.3736e-17 ∧ B 5 = 1.8544e-13 :=
  table_10_values_of_mem_aux 273 (table_10_length_eq ▸ (by norm_num : 273 < 287)) rfl h

theorem table_10_row13500_values_of_mem (B : ℕ → ℝ)
    (h : ((13500), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.9578e-31 ∧ B 2 = 1.3743e-26 ∧ B 3 = 1.8966e-22 ∧
      B 4 = 2.6174e-18 ∧ B 5 = 3.6122e-14 :=
  table_10_values_of_mem_aux 274 (table_10_length_eq ▸ (by norm_num : 274 < 287)) rfl h

theorem table_10_row13800_7464_values_of_mem (B : ℕ → ℝ)
    (h : ((13800.7464), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.5592e-31 ∧ B 2 = 4.9829e-27 ∧ B 3 = 6.9761e-23 ∧
      B 4 = 9.7665e-19 ∧ B 5 = 1.3673e-14 :=
  table_10_values_of_mem_aux 275 (table_10_length_eq ▸ (by norm_num : 275 < 287)) rfl h

theorem table_10_row14000_values_of_mem (B : ℕ → ℝ)
    (h : ((14000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.8398e-31 ∧ B 2 = 2.7597e-27 ∧ B 3 = 4.1396e-23 ∧
      B 4 = 6.2094e-19 ∧ B 5 = 9.3141e-15 :=
  table_10_values_of_mem_aux 276 (table_10_length_eq ▸ (by norm_num : 276 < 287)) rfl h

theorem table_10_row15000_values_of_mem (B : ℕ → ℝ)
    (h : ((15000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 6.5711e-33 ∧ B 2 = 1.0514e-28 ∧ B 3 = 1.6822e-24 ∧
      B 4 = 2.6915e-20 ∧ B 5 = 4.3065e-16 :=
  table_10_values_of_mem_aux 277 (table_10_length_eq ▸ (by norm_num : 277 < 287)) rfl h

theorem table_10_row16000_values_of_mem (B : ℕ → ℝ)
    (h : ((16000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.5738e-34 ∧ B 2 = 4.3755e-30 ∧ B 3 = 7.4384e-26 ∧
      B 4 = 1.2645e-21 ∧ B 5 = 2.1497e-17 :=
  table_10_values_of_mem_aux 278 (table_10_length_eq ▸ (by norm_num : 278 < 287)) rfl h

theorem table_10_row17000_values_of_mem (B : ℕ → ℝ)
    (h : ((17000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.1167e-35 ∧ B 2 = 2.0101e-31 ∧ B 3 = 3.6182e-27 ∧
      B 4 = 6.5127e-23 ∧ B 5 = 1.1723e-18 :=
  table_10_values_of_mem_aux 279 (table_10_length_eq ▸ (by norm_num : 279 < 287)) rfl h

theorem table_10_row18000_values_of_mem (B : ℕ → ℝ)
    (h : ((18000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.3738e-37 ∧ B 2 = 1.0210e-32 ∧ B 3 = 1.9400e-28 ∧
      B 4 = 3.6859e-24 ∧ B 5 = 7.0032e-20 :=
  table_10_values_of_mem_aux 280 (table_10_length_eq ▸ (by norm_num : 280 < 287)) rfl h

theorem table_10_row19000_values_of_mem (B : ℕ → ℝ)
    (h : ((19000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.7357e-38 ∧ B 2 = 5.4714e-34 ∧ B 3 = 1.0943e-29 ∧
      B 4 = 2.1886e-25 ∧ B 5 = 4.3771e-21 :=
  table_10_values_of_mem_aux 281 (table_10_length_eq ▸ (by norm_num : 281 < 287)) rfl h

theorem table_10_row20000_values_of_mem (B : ℕ → ℝ)
    (h : ((20000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 1.5040e-39 ∧ B 2 = 3.1585e-35 ∧ B 3 = 6.6328e-31 ∧
      B 4 = 1.3929e-26 ∧ B 5 = 2.9251e-22 :=
  table_10_values_of_mem_aux 282 (table_10_length_eq ▸ (by norm_num : 282 < 287)) rfl h

theorem table_10_row21000_values_of_mem (B : ℕ → ℝ)
    (h : ((21000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 9.0605e-41 ∧ B 2 = 1.9933e-36 ∧ B 3 = 4.3853e-32 ∧
      B 4 = 9.6476e-28 ∧ B 5 = 2.1225e-23 :=
  table_10_values_of_mem_aux 283 (table_10_length_eq ▸ (by norm_num : 283 < 287)) rfl h

theorem table_10_row22000_values_of_mem (B : ℕ → ℝ)
    (h : ((22000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 5.6101e-42 ∧ B 2 = 1.2903e-37 ∧ B 3 = 2.9677e-33 ∧
      B 4 = 6.8258e-29 ∧ B 5 = 1.5699e-24 :=
  table_10_values_of_mem_aux 284 (table_10_length_eq ▸ (by norm_num : 284 < 287)) rfl h

theorem table_10_row23000_values_of_mem (B : ℕ → ℝ)
    (h : ((23000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 3.7554e-43 ∧ B 2 = 9.0129e-39 ∧ B 3 = 2.1631e-34 ∧
      B 4 = 5.1914e-30 ∧ B 5 = 1.2460e-25 :=
  table_10_values_of_mem_aux 285 (table_10_length_eq ▸ (by norm_num : 285 < 287)) rfl h

theorem table_10_row24000_values_of_mem (B : ℕ → ℝ)
    (h : ((24000), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 1 = 2.6755e-44 ∧ B 2 = 6.6888e-40 ∧ B 3 = 1.6722e-35 ∧
      B 4 = 4.1805e-31 ∧ B 5 = 1.0451e-26 :=
  table_10_values_of_mem_aux 286 (table_10_length_eq ▸ (by norm_num : 286 < 287)) rfl h

end BKLNW
