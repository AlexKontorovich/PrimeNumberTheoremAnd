import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_dispatch

/-! # Table-11 suffix bound over the Table-10 grid

A Table-11 entry has to dominate the Table-10 strip constants over the whole **suffix**
`b ≥ max b₀ (19 log 10)`, not just at `b₀`. Checking that directly would pit each of the 43
Table-11 rows against each of the 287 Table-10 rows.

Instead this file walks the grid once, from the top down. `table_11_suffix_from_<b>` states
the running suffix maximum of the five printed columns from row `b` onwards, and is proved
from its own successor in one step: by `eq_or_ge_next` a Table-10 entry `≥ b` is either `b`
itself (use that row's printed values) or already at `table_10_next b` (use the successor
lemma, then widen). That is 263 cheap steps instead of ~12000 comparisons.

The chain runs from `19 log 10` (row 24, the `10^19` node) to `24000` (row 286, the last);
rows below the `10^19` node never enter an above-`10^19` suffix. `table_11_suffix_dominates`
then reads off each Table-11 row against the suffix maximum at its own starting node.
-/

namespace BKLNW

open Chebyshev Finset Real

/-- Recover a full Table-10 row from one of its `b`-entries. `table_10_entries` only
remembers the first component, but every consumer of a strip bound
(`bklnw_table_10_verification`) needs the row's five printed values as a function
`B : ℕ → ℝ`. -/
lemma table_10_row_of_entry {b : ℝ} (hb : b ∈ table_10_entries) :
    ∃ B : ℕ → ℝ, (b, B 1, B 2, B 3, B 4, B 5) ∈ table_10 := by
  simp only [List.mem_toFinset, List.mem_map] at hb
  obtain ⟨p, hp, rfl⟩ := hb
  refine ⟨fun i ↦ if i = 1 then p.2.1 else if i = 2 then p.2.2.1 else
    if i = 3 then p.2.2.2.1 else if i = 4 then p.2.2.2.2.1 else p.2.2.2.2.2, ?_⟩
  simpa using hp

/-- Membership of a Table-10 row's `b`-entry in `table_10_entries`, addressed by list
index. Addressing rows by index (rather than searching the 287-element list with `simp`)
is what keeps the per-row certificates below cheap; it is the same device
`table_10_values_of_mem_aux` uses. -/
lemma mem_entries_get (N : ℕ) (hN : N < table_10.length) :
    (table_10.get ⟨N, hN⟩).1 ∈ table_10_entries := by
  simp only [List.mem_toFinset, List.mem_map]
  exact ⟨_, List.get_mem _ _, rfl⟩

/-- `mem_entries_get` with the row contents supplied by `rfl` at the call site. -/
lemma mem_entries_idx (N : ℕ) (hN : N < 287) (b : ℝ)
    (hb : (table_10.get ⟨N, table_10_length_eq ▸ hN⟩).1 = b) : b ∈ table_10_entries :=
  hb ▸ mem_entries_get N _

/-- `10^19 = e^{19 log 10}` is itself a Table-10 grid node (row 24), sitting between the
rows `43` and `44`. This is what makes the split at `10^19` land on a strip boundary
instead of cutting a strip in half. -/
lemma mem_entries_19log10 : (19 : ℝ) * log 10 ∈ table_10_entries :=
  mem_entries_idx 24 (by norm_num) _ rfl

lemma table_10_next_le_of_mem {b b' : ℝ} (hb' : b' ∈ table_10_bs) (hlt : b < b') :
    table_10_next b ≤ b' := by
  have hmem : b' ∈ table_10_bs.filter (b < ·) := Finset.mem_filter.mpr ⟨hb', hlt⟩
  rw [table_10_next_eq_min' b ⟨b', hmem⟩]
  exact Finset.min'_le _ _ hmem

/-- **Gap principle.** There is no Table-10 entry strictly between `b` and
`table_10_next b` — immediate from `table_10_next` being an infimum. So an entry `≥ b` is
either `b` itself or already at the next grid node.

This is what makes a suffix bound over the 287-row grid provable by a *chain* of 287 cheap
steps (each row versus the next) instead of a quadratic sweep of every row against every
Table-11 row. -/
lemma eq_or_ge_next {b b' : ℝ} (hb' : b' ∈ table_10_entries) (hge : b ≤ b') :
    b' = b ∨ table_10_next b ≤ b' := by
  rcases eq_or_lt_of_le hge with h | h
  · exact Or.inl h.symm
  · exact Or.inr (table_10_next_le_of_mem (Finset.mem_union_left _ hb') h)

private lemma table_11_suffix_from_24000 :
    ∀ b ∈ table_10_entries, ((24000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.6755e-44 ∧ Bt 2 ≤ 6.6888e-40 ∧ Bt 3 ≤ 1.6722e-35 ∧ Bt 4 ≤ 4.1805e-31 ∧
        Bt 5 ≤ 1.0451e-26 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row24000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · exfalso
    rw [table_10_next_cert_24000] at hnext
    have hK := table_10_entry_lt_K b hb
    norm_num [K] at hK
    linarith

private lemma table_11_suffix_from_23000 :
    ∀ b ∈ table_10_entries, ((23000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.7554e-43 ∧ Bt 2 ≤ 9.0129e-39 ∧ Bt 3 ≤ 2.1631e-34 ∧ Bt 4 ≤ 5.1914e-30 ∧
        Bt 5 ≤ 1.2460e-25 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row23000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_23000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_24000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_22000 :
    ∀ b ∈ table_10_entries, ((22000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.6101e-42 ∧ Bt 2 ≤ 1.2903e-37 ∧ Bt 3 ≤ 2.9677e-33 ∧ Bt 4 ≤ 6.8258e-29 ∧
        Bt 5 ≤ 1.5699e-24 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row22000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_22000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_23000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_21000 :
    ∀ b ∈ table_10_entries, ((21000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.0605e-41 ∧ Bt 2 ≤ 1.9933e-36 ∧ Bt 3 ≤ 4.3853e-32 ∧ Bt 4 ≤ 9.6476e-28 ∧
        Bt 5 ≤ 2.1225e-23 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row21000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_21000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_22000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_20000 :
    ∀ b ∈ table_10_entries, ((20000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5040e-39 ∧ Bt 2 ≤ 3.1585e-35 ∧ Bt 3 ≤ 6.6328e-31 ∧ Bt 4 ≤ 1.3929e-26 ∧
        Bt 5 ≤ 2.9251e-22 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row20000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_20000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_21000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_19000 :
    ∀ b ∈ table_10_entries, ((19000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.7357e-38 ∧ Bt 2 ≤ 5.4714e-34 ∧ Bt 3 ≤ 1.0943e-29 ∧ Bt 4 ≤ 2.1886e-25 ∧
        Bt 5 ≤ 4.3771e-21 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row19000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_19000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_20000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_18000 :
    ∀ b ∈ table_10_entries, ((18000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.3738e-37 ∧ Bt 2 ≤ 1.0210e-32 ∧ Bt 3 ≤ 1.9400e-28 ∧ Bt 4 ≤ 3.6859e-24 ∧
        Bt 5 ≤ 7.0032e-20 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row18000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_18000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_19000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_17000 :
    ∀ b ∈ table_10_entries, ((17000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1167e-35 ∧ Bt 2 ≤ 2.0101e-31 ∧ Bt 3 ≤ 3.6182e-27 ∧ Bt 4 ≤ 6.5127e-23 ∧
        Bt 5 ≤ 1.1723e-18 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row17000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_17000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_18000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_16000 :
    ∀ b ∈ table_10_entries, ((16000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5738e-34 ∧ Bt 2 ≤ 4.3755e-30 ∧ Bt 3 ≤ 7.4384e-26 ∧ Bt 4 ≤ 1.2645e-21 ∧
        Bt 5 ≤ 2.1497e-17 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row16000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_16000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_17000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_15000 :
    ∀ b ∈ table_10_entries, ((15000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.5711e-33 ∧ Bt 2 ≤ 1.0514e-28 ∧ Bt 3 ≤ 1.6822e-24 ∧ Bt 4 ≤ 2.6915e-20 ∧
        Bt 5 ≤ 4.3065e-16 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row15000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_15000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_16000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_14000 :
    ∀ b ∈ table_10_entries, ((14000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.8398e-31 ∧ Bt 2 ≤ 2.7597e-27 ∧ Bt 3 ≤ 4.1396e-23 ∧ Bt 4 ≤ 6.2094e-19 ∧
        Bt 5 ≤ 9.3141e-15 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row14000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_14000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_15000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_13800_7464 :
    ∀ b ∈ table_10_entries, ((13800.7464) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.5592e-31 ∧ Bt 2 ≤ 4.9829e-27 ∧ Bt 3 ≤ 6.9761e-23 ∧ Bt 4 ≤ 9.7665e-19 ∧
        Bt 5 ≤ 1.3673e-14 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row13800_7464_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_13800_7464] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_14000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_13500 :
    ∀ b ∈ table_10_entries, ((13500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.9578e-31 ∧ Bt 2 ≤ 1.3743e-26 ∧ Bt 3 ≤ 1.8966e-22 ∧ Bt 4 ≤ 2.6174e-18 ∧
        Bt 5 ≤ 3.6122e-14 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row13500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_13500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_13800_7464 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_13000 :
    ∀ b ∈ table_10_entries, ((13000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.5830e-30 ∧ Bt 2 ≤ 7.5370e-26 ∧ Bt 3 ≤ 1.0175e-21 ∧ Bt 4 ≤ 1.3736e-17 ∧
        Bt 5 ≤ 1.8544e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row13000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_13000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_13500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12900 :
    ∀ b ∈ table_10_entries, ((12900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.6899e-30 ∧ Bt 2 ≤ 9.9969e-26 ∧ Bt 3 ≤ 1.2996e-21 ∧ Bt 4 ≤ 1.6895e-17 ∧
        Bt 5 ≤ 2.1963e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_13000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12800 :
    ∀ b ∈ table_10_entries, ((12800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0940e-29 ∧ Bt 2 ≤ 1.4112e-25 ∧ Bt 3 ≤ 1.8205e-21 ∧ Bt 4 ≤ 2.3484e-17 ∧
        Bt 5 ≤ 3.0294e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12700 :
    ∀ b ∈ table_10_entries, ((12700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5599e-29 ∧ Bt 2 ≤ 1.9967e-25 ∧ Bt 3 ≤ 2.5558e-21 ∧ Bt 4 ≤ 3.2714e-17 ∧
        Bt 5 ≤ 4.1873e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12600 :
    ∀ b ∈ table_10_entries, ((12600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.2307e-29 ∧ Bt 2 ≤ 2.8330e-25 ∧ Bt 3 ≤ 3.5979e-21 ∧ Bt 4 ≤ 4.5693e-17 ∧
        Bt 5 ≤ 5.8030e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12500 :
    ∀ b ∈ table_10_entries, ((12500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.1924e-29 ∧ Bt 2 ≤ 4.0224e-25 ∧ Bt 3 ≤ 5.0682e-21 ∧ Bt 4 ≤ 6.3859e-17 ∧
        Bt 5 ≤ 8.0462e-13 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12400 :
    ∀ b ∈ table_10_entries, ((12400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.5539e-29 ∧ Bt 2 ≤ 5.6924e-25 ∧ Bt 3 ≤ 7.1155e-21 ∧ Bt 4 ≤ 8.8944e-17 ∧
        Bt 5 ≤ 1.1118e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12300 :
    ∀ b ∈ table_10_entries, ((12300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.5069e-29 ∧ Bt 2 ≤ 8.0685e-25 ∧ Bt 3 ≤ 1.0005e-20 ∧ Bt 4 ≤ 1.2406e-16 ∧
        Bt 5 ≤ 1.5384e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12200 :
    ∀ b ∈ table_10_entries, ((12200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.3146e-29 ∧ Bt 2 ≤ 1.1457e-24 ∧ Bt 3 ≤ 1.4092e-20 ∧ Bt 4 ≤ 1.7333e-16 ∧
        Bt 5 ≤ 2.1320e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12100 :
    ∀ b ∈ table_10_entries, ((12100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3477e-28 ∧ Bt 2 ≤ 1.6442e-24 ∧ Bt 3 ≤ 2.0060e-20 ∧ Bt 4 ≤ 2.4473e-16 ∧
        Bt 5 ≤ 2.9857e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_12000 :
    ∀ b ∈ table_10_entries, ((12000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.9330e-28 ∧ Bt 2 ≤ 2.3390e-24 ∧ Bt 3 ≤ 2.8302e-20 ∧ Bt 4 ≤ 3.4245e-16 ∧
        Bt 5 ≤ 4.1436e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row12000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_12000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11900 :
    ∀ b ∈ table_10_entries, ((11900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.7776e-28 ∧ Bt 2 ≤ 3.3331e-24 ∧ Bt 3 ≤ 3.9997e-20 ∧ Bt 4 ≤ 4.7996e-16 ∧
        Bt 5 ≤ 5.7595e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_12000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11800 :
    ∀ b ∈ table_10_entries, ((11800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.9987e-28 ∧ Bt 2 ≤ 4.7584e-24 ∧ Bt 3 ≤ 5.6625e-20 ∧ Bt 4 ≤ 6.7384e-16 ∧
        Bt 5 ≤ 8.0187e-12 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11700 :
    ∀ b ∈ table_10_entries, ((11700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.7692e-28 ∧ Bt 2 ≤ 6.8076e-24 ∧ Bt 3 ≤ 8.0330e-20 ∧ Bt 4 ≤ 9.4789e-16 ∧
        Bt 5 ≤ 1.1185e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11600 :
    ∀ b ∈ table_10_entries, ((11600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.3444e-28 ∧ Bt 2 ≤ 9.7630e-24 ∧ Bt 3 ≤ 1.1423e-19 ∧ Bt 4 ≤ 1.3365e-15 ∧
        Bt 5 ≤ 1.5637e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11500 :
    ∀ b ∈ table_10_entries, ((11500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.2102e-27 ∧ Bt 2 ≤ 1.4039e-23 ∧ Bt 3 ≤ 1.6285e-19 ∧ Bt 4 ≤ 1.8890e-15 ∧
        Bt 5 ≤ 2.1913e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11400 :
    ∀ b ∈ table_10_entries, ((11400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7569e-27 ∧ Bt 2 ≤ 2.0205e-23 ∧ Bt 3 ≤ 2.3235e-19 ∧ Bt 4 ≤ 2.6721e-15 ∧
        Bt 5 ≤ 3.0729e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11300 :
    ∀ b ∈ table_10_entries, ((11300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5509e-27 ∧ Bt 2 ≤ 2.9080e-23 ∧ Bt 3 ≤ 3.3151e-19 ∧ Bt 4 ≤ 3.7792e-15 ∧
        Bt 5 ≤ 4.3083e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11200 :
    ∀ b ∈ table_10_entries, ((11200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.7120e-27 ∧ Bt 2 ≤ 4.1945e-23 ∧ Bt 3 ≤ 4.7398e-19 ∧ Bt 4 ≤ 5.3560e-15 ∧
        Bt 5 ≤ 6.0522e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11100 :
    ∀ b ∈ table_10_entries, ((11100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.4156e-27 ∧ Bt 2 ≤ 6.0654e-23 ∧ Bt 3 ≤ 6.7933e-19 ∧ Bt 4 ≤ 7.6085e-15 ∧
        Bt 5 ≤ 8.5215e-11 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_11000 :
    ∀ b ∈ table_10_entries, ((11000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.9283e-27 ∧ Bt 2 ≤ 8.8005e-23 ∧ Bt 3 ≤ 9.7685e-19 ∧ Bt 4 ≤ 1.0843e-14 ∧
        Bt 5 ≤ 1.2036e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row11000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_11000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10900 :
    ∀ b ∈ table_10_entries, ((10900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1639e-26 ∧ Bt 2 ≤ 1.2803e-22 ∧ Bt 3 ≤ 1.4083e-18 ∧ Bt 4 ≤ 1.5492e-14 ∧
        Bt 5 ≤ 1.7041e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_11000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10800 :
    ∀ b ∈ table_10_entries, ((10800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7201e-26 ∧ Bt 2 ≤ 1.8749e-22 ∧ Bt 3 ≤ 2.0436e-18 ∧ Bt 4 ≤ 2.2276e-14 ∧
        Bt 5 ≤ 2.4280e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10700 :
    ∀ b ∈ table_10_entries, ((10700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5150e-26 ∧ Bt 2 ≤ 2.7162e-22 ∧ Bt 3 ≤ 2.9335e-18 ∧ Bt 4 ≤ 3.1682e-14 ∧
        Bt 5 ≤ 3.4216e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10600 :
    ∀ b ∈ table_10_entries, ((10600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.6845e-26 ∧ Bt 2 ≤ 3.9424e-22 ∧ Bt 3 ≤ 4.2184e-18 ∧ Bt 4 ≤ 4.5136e-14 ∧
        Bt 5 ≤ 4.8296e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10500 :
    ∀ b ∈ table_10_entries, ((10500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.4076e-26 ∧ Bt 2 ≤ 5.7321e-22 ∧ Bt 3 ≤ 6.0760e-18 ∧ Bt 4 ≤ 6.4406e-14 ∧
        Bt 5 ≤ 6.8270e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10400 :
    ∀ b ∈ table_10_entries, ((10400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.9556e-26 ∧ Bt 2 ≤ 8.3534e-22 ∧ Bt 3 ≤ 8.7710e-18 ∧ Bt 4 ≤ 9.2096e-14 ∧
        Bt 5 ≤ 9.6701e-10 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10300 :
    ∀ b ∈ table_10_entries, ((10300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1734e-25 ∧ Bt 2 ≤ 1.2203e-21 ∧ Bt 3 ≤ 1.2691e-17 ∧ Bt 4 ≤ 1.3199e-13 ∧
        Bt 5 ≤ 1.3727e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10200 :
    ∀ b ∈ table_10_entries, ((10200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7389e-25 ∧ Bt 2 ≤ 1.7911e-21 ∧ Bt 3 ≤ 1.8448e-17 ∧ Bt 4 ≤ 1.9001e-13 ∧
        Bt 5 ≤ 1.9571e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10100 :
    ∀ b ∈ table_10_entries, ((10100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5745e-25 ∧ Bt 2 ≤ 2.6260e-21 ∧ Bt 3 ≤ 2.6785e-17 ∧ Bt 4 ≤ 2.7321e-13 ∧
        Bt 5 ≤ 2.7867e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_10000 :
    ∀ b ∈ table_10_entries, ((10000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.8228e-25 ∧ Bt 2 ≤ 3.8610e-21 ∧ Bt 3 ≤ 3.8996e-17 ∧ Bt 4 ≤ 3.9386e-13 ∧
        Bt 5 ≤ 3.9780e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row10000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_10000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9900 :
    ∀ b ∈ table_10_entries, ((9900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.7395e-25 ∧ Bt 2 ≤ 5.7395e-21 ∧ Bt 3 ≤ 5.7395e-17 ∧ Bt 4 ≤ 5.7395e-13 ∧
        Bt 5 ≤ 5.7395e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_10000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9800 :
    ∀ b ∈ table_10_entries, ((9800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.4841e-25 ∧ Bt 2 ≤ 8.3992e-21 ∧ Bt 3 ≤ 8.3152e-17 ∧ Bt 4 ≤ 8.2321e-13 ∧
        Bt 5 ≤ 8.1497e-9 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9700 :
    ∀ b ∈ table_10_entries, ((9700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.2689e-24 ∧ Bt 2 ≤ 1.2435e-20 ∧ Bt 3 ≤ 1.2187e-16 ∧ Bt 4 ≤ 1.1943e-12 ∧
        Bt 5 ≤ 1.1704e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9600 :
    ∀ b ∈ table_10_entries, ((9600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.9059e-24 ∧ Bt 2 ≤ 1.8487e-20 ∧ Bt 3 ≤ 1.7932e-16 ∧ Bt 4 ≤ 1.7395e-12 ∧
        Bt 5 ≤ 1.6873e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9500 :
    ∀ b ∈ table_10_entries, ((9500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.8512e-24 ∧ Bt 2 ≤ 2.7372e-20 ∧ Bt 3 ≤ 2.6277e-16 ∧ Bt 4 ≤ 2.5226e-12 ∧
        Bt 5 ≤ 2.4217e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9400 :
    ∀ b ∈ table_10_entries, ((9400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.2972e-24 ∧ Bt 2 ≤ 4.0823e-20 ∧ Bt 3 ≤ 3.8782e-16 ∧ Bt 4 ≤ 3.6843e-12 ∧
        Bt 5 ≤ 3.5001e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9300 :
    ∀ b ∈ table_10_entries, ((9300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.4195e-24 ∧ Bt 2 ≤ 6.0343e-20 ∧ Bt 3 ≤ 5.6723e-16 ∧ Bt 4 ≤ 5.3319e-12 ∧
        Bt 5 ≤ 5.0120e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9200 :
    ∀ b ∈ table_10_entries, ((9200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.6777e-24 ∧ Bt 2 ≤ 9.0003e-20 ∧ Bt 3 ≤ 8.3703e-16 ∧ Bt 4 ≤ 7.7844e-12 ∧
        Bt 5 ≤ 7.2395e-8 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9100 :
    ∀ b ∈ table_10_entries, ((9100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4641e-23 ∧ Bt 2 ≤ 1.3470e-19 ∧ Bt 3 ≤ 1.2392e-15 ∧ Bt 4 ≤ 1.1401e-11 ∧
        Bt 5 ≤ 1.0489e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_9000 :
    ∀ b ∈ table_10_entries, ((9000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.2252e-23 ∧ Bt 2 ≤ 2.0250e-19 ∧ Bt 3 ≤ 1.8427e-15 ∧ Bt 4 ≤ 1.6769e-11 ∧
        Bt 5 ≤ 1.5260e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row9000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_9000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8900 :
    ∀ b ∈ table_10_entries, ((8900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.3882e-23 ∧ Bt 2 ≤ 3.0494e-19 ∧ Bt 3 ≤ 2.7445e-15 ∧ Bt 4 ≤ 2.4700e-11 ∧
        Bt 5 ≤ 2.2230e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_9000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8800 :
    ∀ b ∈ table_10_entries, ((8800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.1585e-23 ∧ Bt 2 ≤ 4.5910e-19 ∧ Bt 3 ≤ 4.0860e-15 ∧ Bt 4 ≤ 3.6366e-11 ∧
        Bt 5 ≤ 3.2365e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8700 :
    ∀ b ∈ table_10_entries, ((8700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.8220e-23 ∧ Bt 2 ≤ 6.8834e-19 ∧ Bt 3 ≤ 6.0574e-15 ∧ Bt 4 ≤ 5.3305e-11 ∧
        Bt 5 ≤ 4.6908e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8600 :
    ∀ b ∈ table_10_entries, ((8600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1981e-22 ∧ Bt 2 ≤ 1.0423e-18 ∧ Bt 3 ≤ 9.0682e-15 ∧ Bt 4 ≤ 7.8893e-11 ∧
        Bt 5 ≤ 6.8637e-7 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8500 :
    ∀ b ∈ table_10_entries, ((8500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.8315e-22 ∧ Bt 2 ≤ 1.5751e-18 ∧ Bt 3 ≤ 1.3546e-14 ∧ Bt 4 ≤ 1.1650e-10 ∧
        Bt 5 ≤ 1.0019e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8400 :
    ∀ b ∈ table_10_entries, ((8400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.8105e-22 ∧ Bt 2 ≤ 2.3889e-18 ∧ Bt 3 ≤ 2.0306e-14 ∧ Bt 4 ≤ 1.7260e-10 ∧
        Bt 5 ≤ 1.4671e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8300 :
    ∀ b ∈ table_10_entries, ((8300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.3257e-22 ∧ Bt 2 ≤ 3.6336e-18 ∧ Bt 3 ≤ 3.0522e-14 ∧ Bt 4 ≤ 2.5639e-10 ∧
        Bt 5 ≤ 2.1536e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8200 :
    ∀ b ∈ table_10_entries, ((8200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.6828e-22 ∧ Bt 2 ≤ 5.5467e-18 ∧ Bt 3 ≤ 4.6038e-14 ∧ Bt 4 ≤ 3.8212e-10 ∧
        Bt 5 ≤ 3.1716e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8100 :
    ∀ b ∈ table_10_entries, ((8100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0326e-21 ∧ Bt 2 ≤ 8.4674e-18 ∧ Bt 3 ≤ 6.9433e-14 ∧ Bt 4 ≤ 5.6935e-10 ∧
        Bt 5 ≤ 4.6687e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_8000 :
    ∀ b ∈ table_10_entries, ((8000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.6007e-21 ∧ Bt 2 ≤ 1.2965e-17 ∧ Bt 3 ≤ 1.0502e-13 ∧ Bt 4 ≤ 8.5065e-10 ∧
        Bt 5 ≤ 6.8903e-6 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row8000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_8000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7900 :
    ∀ b ∈ table_10_entries, ((7900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.4928e-21 ∧ Bt 2 ≤ 1.9942e-17 ∧ Bt 3 ≤ 1.5954e-13 ∧ Bt 4 ≤ 1.2763e-9 ∧
        Bt 5 ≤ 1.0211e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_8000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7800 :
    ∀ b ∈ table_10_entries, ((7800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.8811e-21 ∧ Bt 2 ≤ 3.0661e-17 ∧ Bt 3 ≤ 2.4222e-13 ∧ Bt 4 ≤ 1.9136e-9 ∧
        Bt 5 ≤ 1.5117e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7700 :
    ∀ b ∈ table_10_entries, ((7700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.0569e-21 ∧ Bt 2 ≤ 4.7244e-17 ∧ Bt 3 ≤ 3.6850e-13 ∧ Bt 4 ≤ 2.8743e-9 ∧
        Bt 5 ≤ 2.2420e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7600 :
    ∀ b ∈ table_10_entries, ((7600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.4822e-21 ∧ Bt 2 ≤ 7.3013e-17 ∧ Bt 3 ≤ 5.6220e-13 ∧ Bt 4 ≤ 4.3289e-9 ∧
        Bt 5 ≤ 3.3333e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7500 :
    ∀ b ∈ table_10_entries, ((7500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4907e-20 ∧ Bt 2 ≤ 1.1330e-16 ∧ Bt 3 ≤ 8.6105e-13 ∧ Bt 4 ≤ 6.5440e-9 ∧
        Bt 5 ≤ 4.9734e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7400 :
    ∀ b ∈ table_10_entries, ((7400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.3488e-20 ∧ Bt 2 ≤ 1.7616e-16 ∧ Bt 3 ≤ 1.3212e-12 ∧ Bt 4 ≤ 9.9091e-9 ∧
        Bt 5 ≤ 7.4318e-5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7300 :
    ∀ b ∈ table_10_entries, ((7300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.7014e-20 ∧ Bt 2 ≤ 2.7390e-16 ∧ Bt 3 ≤ 2.0269e-12 ∧ Bt 4 ≤ 1.4999e-8 ∧
        Bt 5 ≤ 1.1099e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7200 :
    ∀ b ∈ table_10_entries, ((7200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.8601e-20 ∧ Bt 2 ≤ 4.2779e-16 ∧ Bt 3 ≤ 3.1229e-12 ∧ Bt 4 ≤ 2.2797e-8 ∧
        Bt 5 ≤ 1.6642e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7100 :
    ∀ b ∈ table_10_entries, ((7100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.2826e-20 ∧ Bt 2 ≤ 6.6834e-16 ∧ Bt 3 ≤ 4.8121e-12 ∧ Bt 4 ≤ 3.4647e-8 ∧
        Bt 5 ≤ 2.4946e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_7000 :
    ∀ b ∈ table_10_entries, ((7000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4744e-19 ∧ Bt 2 ≤ 1.0468e-15 ∧ Bt 3 ≤ 7.4322e-12 ∧ Bt 4 ≤ 5.2769e-8 ∧
        Bt 5 ≤ 3.7466e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row7000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_7000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6900 :
    ∀ b ∈ table_10_entries, ((6900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.3554e-19 ∧ Bt 2 ≤ 1.6488e-15 ∧ Bt 3 ≤ 1.1542e-11 ∧ Bt 4 ≤ 8.0791e-8 ∧
        Bt 5 ≤ 5.6554e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_7000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6800 :
    ∀ b ∈ table_10_entries, ((6800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.7651e-19 ∧ Bt 2 ≤ 2.5979e-15 ∧ Bt 3 ≤ 1.7926e-11 ∧ Bt 4 ≤ 1.2369e-7 ∧
        Bt 5 ≤ 8.5344e-4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6700 :
    ∀ b ∈ table_10_entries, ((6700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.0447e-19 ∧ Bt 2 ≤ 4.1104e-15 ∧ Bt 3 ≤ 2.7951e-11 ∧ Bt 4 ≤ 1.9007e-7 ∧
        Bt 5 ≤ 1.2924e-3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6600 :
    ∀ b ∈ table_10_entries, ((6600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.7287e-19 ∧ Bt 2 ≤ 6.5182e-15 ∧ Bt 3 ≤ 4.3672e-11 ∧ Bt 4 ≤ 2.9260e-7 ∧
        Bt 5 ≤ 1.9604e-3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6500 :
    ∀ b ∈ table_10_entries, ((6500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5741e-18 ∧ Bt 2 ≤ 1.0389e-14 ∧ Bt 3 ≤ 6.8566e-11 ∧ Bt 4 ≤ 4.5253e-7 ∧
        Bt 5 ≤ 2.9867e-3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6400 :
    ∀ b ∈ table_10_entries, ((6400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5481e-18 ∧ Bt 2 ≤ 1.6563e-14 ∧ Bt 3 ≤ 1.0766e-10 ∧ Bt 4 ≤ 6.9977e-7 ∧
        Bt 5 ≤ 4.5485e-3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6300 :
    ∀ b ∈ table_10_entries, ((6300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.1267e-18 ∧ Bt 2 ≤ 2.6411e-14 ∧ Bt 3 ≤ 1.6903e-10 ∧ Bt 4 ≤ 1.0818e-6 ∧
        Bt 5 ≤ 6.9235e-3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6200 :
    ∀ b ∈ table_10_entries, ((6200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.7178e-18 ∧ Bt 2 ≤ 4.2322e-14 ∧ Bt 3 ≤ 2.6663e-10 ∧ Bt 4 ≤ 1.6798e-6 ∧
        Bt 5 ≤ 1.0583e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6100 :
    ∀ b ∈ table_10_entries, ((6100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0987e-17 ∧ Bt 2 ≤ 6.8120e-14 ∧ Bt 3 ≤ 4.2234e-10 ∧ Bt 4 ≤ 2.6185e-6 ∧
        Bt 5 ≤ 1.6235e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_6000 :
    ∀ b ∈ table_10_entries, ((6000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7952e-17 ∧ Bt 2 ≤ 1.0951e-13 ∧ Bt 3 ≤ 6.6798e-10 ∧ Bt 4 ≤ 4.0747e-6 ∧
        Bt 5 ≤ 2.4855e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row6000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_6000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5900 :
    ∀ b ∈ table_10_entries, ((5900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.9482e-17 ∧ Bt 2 ≤ 1.7689e-13 ∧ Bt 3 ≤ 1.0614e-9 ∧ Bt 4 ≤ 6.3682e-6 ∧
        Bt 5 ≤ 3.8209e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_6000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5800 :
    ∀ b ∈ table_10_entries, ((5800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.8518e-17 ∧ Bt 2 ≤ 2.8626e-13 ∧ Bt 3 ≤ 1.6889e-9 ∧ Bt 4 ≤ 9.9646e-6 ∧
        Bt 5 ≤ 5.8791e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5700 :
    ∀ b ∈ table_10_entries, ((5700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.0079e-17 ∧ Bt 2 ≤ 4.6446e-13 ∧ Bt 3 ≤ 2.6938e-9 ∧ Bt 4 ≤ 1.5624e-5 ∧
        Bt 5 ≤ 9.0621e-2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5600 :
    ∀ b ∈ table_10_entries, ((5600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3217e-16 ∧ Bt 2 ≤ 7.5337e-13 ∧ Bt 3 ≤ 4.2942e-9 ∧ Bt 4 ≤ 2.4477e-5 ∧
        Bt 5 ≤ 1.3952e-1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5500 :
    ∀ b ∈ table_10_entries, ((5500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.1916e-16 ∧ Bt 2 ≤ 1.2273e-12 ∧ Bt 3 ≤ 6.8727e-9 ∧ Bt 4 ≤ 3.8487e-5 ∧
        Bt 5 ≤ 2.1553e-1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5400 :
    ∀ b ∈ table_10_entries, ((5400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.6472e-16 ∧ Bt 2 ≤ 2.0059e-12 ∧ Bt 3 ≤ 1.1033e-8 ∧ Bt 4 ≤ 6.0679e-5 ∧
        Bt 5 ≤ 3.3374e-1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5300 :
    ∀ b ∈ table_10_entries, ((5300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.0977e-16 ∧ Bt 2 ≤ 3.2927e-12 ∧ Bt 3 ≤ 1.7781e-8 ∧ Bt 4 ≤ 9.6016e-5 ∧
        Bt 5 ≤ 5.1849e-1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5200 :
    ∀ b ∈ table_10_entries, ((5200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0185e-15 ∧ Bt 2 ≤ 5.3980e-12 ∧ Bt 3 ≤ 2.8610e-8 ∧ Bt 4 ≤ 1.5163e-4 ∧
        Bt 5 ≤ 8.0364e-1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5100 :
    ∀ b ∈ table_10_entries, ((5100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7087e-15 ∧ Bt 2 ≤ 8.8850e-12 ∧ Bt 3 ≤ 4.6202e-8 ∧ Bt 4 ≤ 2.4025e-4 ∧
        Bt 5 ≤ 1.2493e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_5000 :
    ∀ b ∈ table_10_entries, ((5000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.8715e-15 ∧ Bt 2 ≤ 1.4645e-11 ∧ Bt 3 ≤ 7.4687e-8 ∧ Bt 4 ≤ 3.8090e-4 ∧
        Bt 5 ≤ 1.9426e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row5000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_5000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4975 :
    ∀ b ∈ table_10_entries, ((4975) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.2229e-15 ∧ Bt 2 ≤ 1.6114e-11 ∧ Bt 3 ≤ 8.0571e-8 ∧ Bt 4 ≤ 4.0286e-4 ∧
        Bt 5 ≤ 2.0143e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4975_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4975] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_5000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4950 :
    ∀ b ∈ table_10_entries, ((4950) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.6731e-15 ∧ Bt 2 ≤ 1.8274e-11 ∧ Bt 3 ≤ 9.0911e-8 ∧ Bt 4 ≤ 4.5228e-4 ∧
        Bt 5 ≤ 2.2501e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4950_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4950] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4975 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4925 :
    ∀ b ∈ table_10_entries, ((4925) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.1878e-15 ∧ Bt 2 ≤ 2.0729e-11 ∧ Bt 3 ≤ 1.0261e-7 ∧ Bt 4 ≤ 5.0792e-4 ∧
        Bt 5 ≤ 2.5142e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4925_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4925] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4950 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4900 :
    ∀ b ∈ table_10_entries, ((4900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.7720e-15 ∧ Bt 2 ≤ 2.3502e-11 ∧ Bt 3 ≤ 1.1575e-7 ∧ Bt 4 ≤ 5.7006e-4 ∧
        Bt 5 ≤ 2.8076e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4925 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4875 :
    ∀ b ∈ table_10_entries, ((4875) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.4361e-15 ∧ Bt 2 ≤ 2.6637e-11 ∧ Bt 3 ≤ 1.3052e-7 ∧ Bt 4 ≤ 6.3955e-4 ∧
        Bt 5 ≤ 3.1338e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4875_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4875] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4850 :
    ∀ b ∈ table_10_entries, ((4850) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.1951e-15 ∧ Bt 2 ≤ 3.0201e-11 ∧ Bt 3 ≤ 1.4723e-7 ∧ Bt 4 ≤ 7.1775e-4 ∧
        Bt 5 ≤ 3.4990e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4850_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4850] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4875 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4825 :
    ∀ b ∈ table_10_entries, ((4825) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.0614e-15 ∧ Bt 2 ≤ 3.4248e-11 ∧ Bt 3 ≤ 1.6610e-7 ∧ Bt 4 ≤ 8.0560e-4 ∧
        Bt 5 ≤ 3.9072e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4825_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4825] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4850 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4800 :
    ∀ b ∈ table_10_entries, ((4800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.0537e-15 ∧ Bt 2 ≤ 3.8859e-11 ∧ Bt 3 ≤ 1.8750e-7 ∧ Bt 4 ≤ 9.0466e-4 ∧
        Bt 5 ≤ 4.3650e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4825 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4775 :
    ∀ b ∈ table_10_entries, ((4775) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.1894e-15 ∧ Bt 2 ≤ 4.4109e-11 ∧ Bt 3 ≤ 2.1172e-7 ∧ Bt 4 ≤ 1.0163e-3 ∧
        Bt 5 ≤ 4.8781e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4775_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4775] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4750 :
    ∀ b ∈ table_10_entries, ((4750) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0491e-14 ∧ Bt 2 ≤ 5.0095e-11 ∧ Bt 3 ≤ 2.3920e-7 ∧ Bt 4 ≤ 1.1422e-3 ∧
        Bt 5 ≤ 5.4540e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4750_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4750] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4775 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4725 :
    ∀ b ∈ table_10_entries, ((4725) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1976e-14 ∧ Bt 2 ≤ 5.6887e-11 ∧ Bt 3 ≤ 2.7021e-7 ∧ Bt 4 ≤ 1.2835e-3 ∧
        Bt 5 ≤ 6.0967e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4725_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4725] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4750 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4700 :
    ∀ b ∈ table_10_entries, ((4700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3648e-14 ∧ Bt 2 ≤ 6.4486e-11 ∧ Bt 3 ≤ 3.0470e-7 ∧ Bt 4 ≤ 1.4397e-3 ∧
        Bt 5 ≤ 6.8026e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4725 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4675 :
    ∀ b ∈ table_10_entries, ((4675) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5563e-14 ∧ Bt 2 ≤ 7.3144e-11 ∧ Bt 3 ≤ 3.4378e-7 ∧ Bt 4 ≤ 1.6158e-3 ∧
        Bt 5 ≤ 7.5941e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4675_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4675] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4650 :
    ∀ b ∈ table_10_entries, ((4650) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7753e-14 ∧ Bt 2 ≤ 8.2997e-11 ∧ Bt 3 ≤ 3.8801e-7 ∧ Bt 4 ≤ 1.8140e-3 ∧
        Bt 5 ≤ 8.4802e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4650_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4650] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4675 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4625 :
    ∀ b ∈ table_10_entries, ((4625) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.0259e-14 ∧ Bt 2 ≤ 9.4206e-11 ∧ Bt 3 ≤ 4.3806e-7 ∧ Bt 4 ≤ 2.0370e-3 ∧
        Bt 5 ≤ 9.4719e0 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4625_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4625] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4650 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4600 :
    ∀ b ∈ table_10_entries, ((4600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.3157e-14 ∧ Bt 2 ≤ 1.0710e-10 ∧ Bt 3 ≤ 4.9535e-7 ∧ Bt 4 ≤ 2.2910e-3 ∧
        Bt 5 ≤ 1.0596e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4625 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4575 :
    ∀ b ∈ table_10_entries, ((4575) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.6404e-14 ∧ Bt 2 ≤ 1.2146e-10 ∧ Bt 3 ≤ 5.5870e-7 ∧ Bt 4 ≤ 2.5700e-3 ∧
        Bt 5 ≤ 1.1822e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4575_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4575] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4550 :
    ∀ b ∈ table_10_entries, ((4550) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.0155e-14 ∧ Bt 2 ≤ 1.3796e-10 ∧ Bt 3 ≤ 6.3117e-7 ∧ Bt 4 ≤ 2.8876e-3 ∧
        Bt 5 ≤ 1.3211e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4550_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4550] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4575 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4525 :
    ∀ b ∈ table_10_entries, ((4525) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.4446e-14 ∧ Bt 2 ≤ 1.5673e-10 ∧ Bt 3 ≤ 7.1312e-7 ∧ Bt 4 ≤ 3.2447e-3 ∧
        Bt 5 ≤ 1.4763e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4525_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4525] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4550 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4500 :
    ∀ b ∈ table_10_entries, ((4500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.9290e-14 ∧ Bt 2 ≤ 1.7779e-10 ∧ Bt 3 ≤ 8.0450e-7 ∧ Bt 4 ≤ 3.6403e-3 ∧
        Bt 5 ≤ 1.6473e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4525 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4475 :
    ∀ b ∈ table_10_entries, ((4475) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4832e-14 ∧ Bt 2 ≤ 2.0174e-10 ∧ Bt 3 ≤ 9.0785e-7 ∧ Bt 4 ≤ 4.0853e-3 ∧
        Bt 5 ≤ 1.8384e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4475_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4475] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4450 :
    ∀ b ∈ table_10_entries, ((4450) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.1174e-14 ∧ Bt 2 ≤ 2.2901e-10 ∧ Bt 3 ≤ 1.0248e-6 ∧ Bt 4 ≤ 4.5860e-3 ∧
        Bt 5 ≤ 2.0522e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4450_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4450] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4475 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4425 :
    ∀ b ∈ table_10_entries, ((4425) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.8436e-14 ∧ Bt 2 ≤ 2.6004e-10 ∧ Bt 3 ≤ 1.1572e-6 ∧ Bt 4 ≤ 5.1495e-3 ∧
        Bt 5 ≤ 2.2915e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4425_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4425] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4450 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4400 :
    ∀ b ∈ table_10_entries, ((4400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.6744e-14 ∧ Bt 2 ≤ 2.9534e-10 ∧ Bt 3 ≤ 1.3069e-6 ∧ Bt 4 ≤ 5.7829e-3 ∧
        Bt 5 ≤ 2.5590e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4425 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4375 :
    ∀ b ∈ table_10_entries, ((4375) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.6274e-14 ∧ Bt 2 ≤ 3.3561e-10 ∧ Bt 3 ≤ 1.4767e-6 ∧ Bt 4 ≤ 6.4973e-3 ∧
        Bt 5 ≤ 2.8588e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4375_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4375] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4350 :
    ∀ b ∈ table_10_entries, ((4350) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.7210e-14 ∧ Bt 2 ≤ 3.8154e-10 ∧ Bt 3 ≤ 1.6693e-6 ∧ Bt 4 ≤ 7.3030e-3 ∧
        Bt 5 ≤ 3.1951e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4350_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4350] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4375 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4325 :
    ∀ b ∈ table_10_entries, ((4325) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.9670e-14 ∧ Bt 2 ≤ 4.3356e-10 ∧ Bt 3 ≤ 1.8860e-6 ∧ Bt 4 ≤ 8.2041e-3 ∧
        Bt 5 ≤ 3.5688e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4325_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4325] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4350 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4300 :
    ∀ b ∈ table_10_entries, ((4300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1396e-13 ∧ Bt 2 ≤ 4.9288e-10 ∧ Bt 3 ≤ 2.1317e-6 ∧ Bt 4 ≤ 9.2195e-3 ∧
        Bt 5 ≤ 3.9875e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4325 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4275 :
    ∀ b ∈ table_10_entries, ((4275) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3036e-13 ∧ Bt 2 ≤ 5.6056e-10 ∧ Bt 3 ≤ 2.4104e-6 ∧ Bt 4 ≤ 1.0365e-2 ∧
        Bt 5 ≤ 4.4568e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4275_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4275] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4250 :
    ∀ b ∈ table_10_entries, ((4250) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4913e-13 ∧ Bt 2 ≤ 6.3751e-10 ∧ Bt 3 ≤ 2.7254e-6 ∧ Bt 4 ≤ 1.1651e-2 ∧
        Bt 5 ≤ 4.9808e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4250_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4250] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4275 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4225 :
    ∀ b ∈ table_10_entries, ((4225) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7047e-13 ∧ Bt 2 ≤ 7.2449e-10 ∧ Bt 3 ≤ 3.0791e-6 ∧ Bt 4 ≤ 1.3086e-2 ∧
        Bt 5 ≤ 5.5616e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4225_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4225] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4250 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4200 :
    ∀ b ∈ table_10_entries, ((4200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.9496e-13 ∧ Bt 2 ≤ 8.2370e-10 ∧ Bt 3 ≤ 3.4801e-6 ∧ Bt 4 ≤ 1.4704e-2 ∧
        Bt 5 ≤ 6.2122e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4225 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4175 :
    ∀ b ∈ table_10_entries, ((4175) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.2309e-13 ∧ Bt 2 ≤ 9.3698e-10 ∧ Bt 3 ≤ 3.9353e-6 ∧ Bt 4 ≤ 1.6528e-2 ∧
        Bt 5 ≤ 6.9419e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4175_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4175] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4150 :
    ∀ b ∈ table_10_entries, ((4150) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5566e-13 ∧ Bt 2 ≤ 1.0674e-9 ∧ Bt 3 ≤ 4.4563e-6 ∧ Bt 4 ≤ 1.8605e-2 ∧
        Bt 5 ≤ 7.7676e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4150_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4150] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4175 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4125 :
    ∀ b ∈ table_10_entries, ((4125) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.9206e-13 ∧ Bt 2 ≤ 1.2120e-9 ∧ Bt 3 ≤ 5.0299e-6 ∧ Bt 4 ≤ 2.0874e-2 ∧
        Bt 5 ≤ 8.6628e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4125_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4125] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4150 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4100 :
    ∀ b ∈ table_10_entries, ((4100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.3428e-13 ∧ Bt 2 ≤ 1.3789e-9 ∧ Bt 3 ≤ 5.6879e-6 ∧ Bt 4 ≤ 2.3463e-2 ∧
        Bt 5 ≤ 9.6783e1 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4125 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4075 :
    ∀ b ∈ table_10_entries, ((4075) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.8285e-13 ∧ Bt 2 ≤ 1.5697e-9 ∧ Bt 3 ≤ 6.4356e-6 ∧ Bt 4 ≤ 2.6386e-2 ∧
        Bt 5 ≤ 1.0818e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4075_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4075] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4050 :
    ∀ b ∈ table_10_entries, ((4050) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.3803e-13 ∧ Bt 2 ≤ 1.7850e-9 ∧ Bt 3 ≤ 7.2737e-6 ∧ Bt 4 ≤ 2.9640e-2 ∧
        Bt 5 ≤ 1.2078e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4050_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4050] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4075 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4025 :
    ∀ b ∈ table_10_entries, ((4025) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.0264e-13 ∧ Bt 2 ≤ 2.0357e-9 ∧ Bt 3 ≤ 8.2446e-6 ∧ Bt 4 ≤ 3.3391e-2 ∧
        Bt 5 ≤ 1.3523e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4025_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4025] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4050 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_4000 :
    ∀ b ∈ table_10_entries, ((4000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.7409e-13 ∧ Bt 2 ≤ 2.3107e-9 ∧ Bt 3 ≤ 9.3007e-6 ∧ Bt 4 ≤ 3.7435e-2 ∧
        Bt 5 ≤ 1.5068e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row4000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_4000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4025 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3975 :
    ∀ b ∈ table_10_entries, ((3975) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.5788e-13 ∧ Bt 2 ≤ 2.6315e-9 ∧ Bt 3 ≤ 1.0526e-5 ∧ Bt 4 ≤ 4.2104e-2 ∧
        Bt 5 ≤ 1.6842e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3975_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3975] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_4000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3950 :
    ∀ b ∈ table_10_entries, ((3950) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.5449e-13 ∧ Bt 2 ≤ 2.9991e-9 ∧ Bt 3 ≤ 1.1922e-5 ∧ Bt 4 ≤ 4.7388e-2 ∧
        Bt 5 ≤ 1.8837e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3950_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3950] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3975 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3925 :
    ∀ b ∈ table_10_entries, ((3925) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.6323e-13 ∧ Bt 2 ≤ 3.4098e-9 ∧ Bt 3 ≤ 1.3469e-5 ∧ Bt 4 ≤ 5.3201e-2 ∧
        Bt 5 ≤ 2.1014e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3925_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3925] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3950 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3900 :
    ∀ b ∈ table_10_entries, ((3900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.8800e-13 ∧ Bt 2 ≤ 3.8779e-9 ∧ Bt 3 ≤ 1.5221e-5 ∧ Bt 4 ≤ 5.9741e-2 ∧
        Bt 5 ≤ 2.3449e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3925 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3875 :
    ∀ b ∈ table_10_entries, ((3875) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1314e-12 ∧ Bt 2 ≤ 4.4124e-9 ∧ Bt 3 ≤ 1.7208e-5 ∧ Bt 4 ≤ 6.7112e-2 ∧
        Bt 5 ≤ 2.6174e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3875_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3875] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3850 :
    ∀ b ∈ table_10_entries, ((3850) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.2972e-12 ∧ Bt 2 ≤ 5.0267e-9 ∧ Bt 3 ≤ 1.9478e-5 ∧ Bt 4 ≤ 7.5479e-2 ∧
        Bt 5 ≤ 2.9248e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3850_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3850] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3875 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3825 :
    ∀ b ∈ table_10_entries, ((3825) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4854e-12 ∧ Bt 2 ≤ 5.7189e-9 ∧ Bt 3 ≤ 2.2018e-5 ∧ Bt 4 ≤ 8.4768e-2 ∧
        Bt 5 ≤ 3.2636e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3825_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3825] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3850 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3800 :
    ∀ b ∈ table_10_entries, ((3800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7020e-12 ∧ Bt 2 ≤ 6.5099e-9 ∧ Bt 3 ≤ 2.4901e-5 ∧ Bt 4 ≤ 9.5244e-2 ∧
        Bt 5 ≤ 3.6431e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3825 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3775 :
    ∀ b ∈ table_10_entries, ((3775) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.9513e-12 ∧ Bt 2 ≤ 7.4151e-9 ∧ Bt 3 ≤ 2.8177e-5 ∧ Bt 4 ≤ 1.0707e-1 ∧
        Bt 5 ≤ 4.0688e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3775_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3775] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3750 :
    ∀ b ∈ table_10_entries, ((3750) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.2346e-12 ∧ Bt 2 ≤ 8.4357e-9 ∧ Bt 3 ≤ 3.1845e-5 ∧ Bt 4 ≤ 1.2022e-1 ∧
        Bt 5 ≤ 4.5381e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3750_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3750] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3775 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3725 :
    ∀ b ∈ table_10_entries, ((3725) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.5580e-12 ∧ Bt 2 ≤ 9.5924e-9 ∧ Bt 3 ≤ 3.5971e-5 ∧ Bt 4 ≤ 1.3489e-1 ∧
        Bt 5 ≤ 5.0585e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3725_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3725] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3750 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3700 :
    ∀ b ∈ table_10_entries, ((3700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.9296e-12 ∧ Bt 2 ≤ 1.0913e-8 ∧ Bt 3 ≤ 4.0649e-5 ∧ Bt 4 ≤ 1.5142e-1 ∧
        Bt 5 ≤ 5.6404e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3725 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3675 :
    ∀ b ∈ table_10_entries, ((3675) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.3560e-12 ∧ Bt 2 ≤ 1.2417e-8 ∧ Bt 3 ≤ 4.5944e-5 ∧ Bt 4 ≤ 1.6999e-1 ∧
        Bt 5 ≤ 6.2897e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3675_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3675] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3650 :
    ∀ b ∈ table_10_entries, ((3650) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.8475e-12 ∧ Bt 2 ≤ 1.4140e-8 ∧ Bt 3 ≤ 5.1963e-5 ∧ Bt 4 ≤ 1.9096e-1 ∧
        Bt 5 ≤ 7.0179e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3650_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3650] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3675 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3625 :
    ∀ b ∈ table_10_entries, ((3625) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4165e-12 ∧ Bt 2 ≤ 1.6120e-8 ∧ Bt 3 ≤ 5.8839e-5 ∧ Bt 4 ≤ 2.1476e-1 ∧
        Bt 5 ≤ 7.8388e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3625_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3625] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3650 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3600 :
    ∀ b ∈ table_10_entries, ((3600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.0621e-12 ∧ Bt 2 ≤ 1.8350e-8 ∧ Bt 3 ≤ 6.6520e-5 ∧ Bt 4 ≤ 2.4113e-1 ∧
        Bt 5 ≤ 8.7411e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3625 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3575 :
    ∀ b ∈ table_10_entries, ((3575) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.8042e-12 ∧ Bt 2 ≤ 2.0895e-8 ∧ Bt 3 ≤ 7.5222e-5 ∧ Bt 4 ≤ 2.7080e-1 ∧
        Bt 5 ≤ 9.7488e2 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3575_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3575] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3550 :
    ∀ b ∈ table_10_entries, ((3550) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.6608e-12 ∧ Bt 2 ≤ 2.3812e-8 ∧ Bt 3 ≤ 8.5129e-5 ∧ Bt 4 ≤ 3.0434e-1 ∧
        Bt 5 ≤ 1.0880e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3550_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3550] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3575 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3525 :
    ∀ b ∈ table_10_entries, ((3525) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.6403e-12 ∧ Bt 2 ≤ 2.7123e-8 ∧ Bt 3 ≤ 9.6287e-5 ∧ Bt 4 ≤ 3.4182e-1 ∧
        Bt 5 ≤ 1.2135e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3525_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3525] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3550 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3500 :
    ∀ b ∈ table_10_entries, ((3500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.7646e-12 ∧ Bt 2 ≤ 3.0895e-8 ∧ Bt 3 ≤ 1.0891e-4 ∧ Bt 4 ≤ 3.8389e-1 ∧
        Bt 5 ≤ 1.3532e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3525 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3475 :
    ∀ b ∈ table_10_entries, ((3475) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0059e-11 ∧ Bt 2 ≤ 3.5206e-8 ∧ Bt 3 ≤ 1.2322e-4 ∧ Bt 4 ≤ 4.3127e-1 ∧
        Bt 5 ≤ 1.5095e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3475_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3475] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3450 :
    ∀ b ∈ table_10_entries, ((3450) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1554e-11 ∧ Bt 2 ≤ 4.0151e-8 ∧ Bt 3 ≤ 1.3953e-4 ∧ Bt 4 ≤ 4.8485e-1 ∧
        Bt 5 ≤ 1.6849e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3450_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3450] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3475 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3425 :
    ∀ b ∈ table_10_entries, ((3425) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3266e-11 ∧ Bt 2 ≤ 4.5768e-8 ∧ Bt 3 ≤ 1.5790e-4 ∧ Bt 4 ≤ 5.4476e-1 ∧
        Bt 5 ≤ 1.8794e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3425_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3425] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3450 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3400 :
    ∀ b ∈ table_10_entries, ((3400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5212e-11 ∧ Bt 2 ≤ 5.2099e-8 ∧ Bt 3 ≤ 1.7844e-4 ∧ Bt 4 ≤ 6.1116e-1 ∧
        Bt 5 ≤ 2.0932e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3425 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3375 :
    ∀ b ∈ table_10_entries, ((3375) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7453e-11 ∧ Bt 2 ≤ 5.9340e-8 ∧ Bt 3 ≤ 2.0176e-4 ∧ Bt 4 ≤ 6.8597e-1 ∧
        Bt 5 ≤ 2.3323e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3375_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3375] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3350 :
    ∀ b ∈ table_10_entries, ((3350) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.0043e-11 ∧ Bt 2 ≤ 6.7644e-8 ∧ Bt 3 ≤ 2.2830e-4 ∧ Bt 4 ≤ 7.7051e-1 ∧
        Bt 5 ≤ 2.6005e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3350_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3350] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3375 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3325 :
    ∀ b ∈ table_10_entries, ((3325) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.3015e-11 ∧ Bt 2 ≤ 7.7100e-8 ∧ Bt 3 ≤ 2.5829e-4 ∧ Bt 4 ≤ 8.6525e-1 ∧
        Bt 5 ≤ 2.8986e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3325_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3325] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3350 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3300 :
    ∀ b ∈ table_10_entries, ((3300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.6412e-11 ∧ Bt 2 ≤ 8.7820e-8 ∧ Bt 3 ≤ 2.9200e-4 ∧ Bt 4 ≤ 9.7090e-1 ∧
        Bt 5 ≤ 3.2283e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3325 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3275 :
    ∀ b ∈ table_10_entries, ((3275) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.0332e-11 ∧ Bt 2 ≤ 1.0009e-7 ∧ Bt 3 ≤ 3.3031e-4 ∧ Bt 4 ≤ 1.0900e0 ∧
        Bt 5 ≤ 3.5971e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3275_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3275] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3250 :
    ∀ b ∈ table_10_entries, ((3250) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.4800e-11 ∧ Bt 2 ≤ 1.1397e-7 ∧ Bt 3 ≤ 3.7326e-4 ∧ Bt 4 ≤ 1.2224e0 ∧
        Bt 5 ≤ 4.0034e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3250_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3250] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3275 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3225 :
    ∀ b ∈ table_10_entries, ((3225) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.9901e-11 ∧ Bt 2 ≤ 1.2968e-7 ∧ Bt 3 ≤ 4.2146e-4 ∧ Bt 4 ≤ 1.3697e0 ∧
        Bt 5 ≤ 4.4516e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3225_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3225] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3250 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3200 :
    ∀ b ∈ table_10_entries, ((3200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.5782e-11 ∧ Bt 2 ≤ 1.4765e-7 ∧ Bt 3 ≤ 4.7616e-4 ∧ Bt 4 ≤ 1.5356e0 ∧
        Bt 5 ≤ 4.9524e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3225 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3175 :
    ∀ b ∈ table_10_entries, ((3175) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.2572e-11 ∧ Bt 2 ≤ 1.6823e-7 ∧ Bt 3 ≤ 5.3834e-4 ∧ Bt 4 ≤ 1.7227e0 ∧
        Bt 5 ≤ 5.5126e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3175_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3175] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3150 :
    ∀ b ∈ table_10_entries, ((3150) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.0410e-11 ∧ Bt 2 ≤ 1.9180e-7 ∧ Bt 3 ≤ 6.0897e-4 ∧ Bt 4 ≤ 1.9335e0 ∧
        Bt 5 ≤ 6.1388e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3150_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3150] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3175 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3125 :
    ∀ b ∈ table_10_entries, ((3125) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.9396e-11 ∧ Bt 2 ≤ 2.1860e-7 ∧ Bt 3 ≤ 6.8858e-4 ∧ Bt 4 ≤ 2.1690e0 ∧
        Bt 5 ≤ 6.8325e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3125_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3125] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3150 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3100 :
    ∀ b ∈ table_10_entries, ((3100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.9793e-11 ∧ Bt 2 ≤ 2.4935e-7 ∧ Bt 3 ≤ 7.7922e-4 ∧ Bt 4 ≤ 2.4351e0 ∧
        Bt 5 ≤ 7.6096e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3125 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3075 :
    ∀ b ∈ table_10_entries, ((3075) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.1684e-11 ∧ Bt 2 ≤ 2.8422e-7 ∧ Bt 3 ≤ 8.8108e-4 ∧ Bt 4 ≤ 2.7314e0 ∧
        Bt 5 ≤ 8.4672e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3075_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3075] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3050 :
    ∀ b ∈ table_10_entries, ((3050) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.0531e-10 ∧ Bt 2 ≤ 3.2382e-7 ∧ Bt 3 ≤ 9.9573e-4 ∧ Bt 4 ≤ 3.0619e0 ∧
        Bt 5 ≤ 9.4152e3 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3050_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3050] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3075 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3025 :
    ∀ b ∈ table_10_entries, ((3025) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.2115e-10 ∧ Bt 2 ≤ 3.6949e-7 ∧ Bt 3 ≤ 1.1270e-3 ∧ Bt 4 ≤ 3.4372e0 ∧
        Bt 5 ≤ 1.0484e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3025_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3025] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3050 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_3000 :
    ∀ b ∈ table_10_entries, ((3000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3914e-10 ∧ Bt 2 ≤ 4.2090e-7 ∧ Bt 3 ≤ 1.2732e-3 ∧ Bt 4 ≤ 3.8515e0 ∧
        Bt 5 ≤ 1.1651e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row3000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_3000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3025 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2975 :
    ∀ b ∈ table_10_entries, ((2975) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.6015e-10 ∧ Bt 2 ≤ 4.8044e-7 ∧ Bt 3 ≤ 1.4413e-3 ∧ Bt 4 ≤ 4.3240e0 ∧
        Bt 5 ≤ 1.2972e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2975_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2975] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_3000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2950 :
    ∀ b ∈ table_10_entries, ((2950) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.8391e-10 ∧ Bt 2 ≤ 5.4712e-7 ∧ Bt 3 ≤ 1.6277e-3 ∧ Bt 4 ≤ 4.8423e0 ∧
        Bt 5 ≤ 1.4406e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2950_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2950] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2975 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2925 :
    ∀ b ∈ table_10_entries, ((2925) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.1140e-10 ∧ Bt 2 ≤ 6.2363e-7 ∧ Bt 3 ≤ 1.8397e-3 ∧ Bt 4 ≤ 5.4272e0 ∧
        Bt 5 ≤ 1.6010e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2925_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2925] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2950 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2900 :
    ∀ b ∈ table_10_entries, ((2900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.4326e-10 ∧ Bt 2 ≤ 7.1154e-7 ∧ Bt 3 ≤ 2.0813e-3 ∧ Bt 4 ≤ 6.0877e0 ∧
        Bt 5 ≤ 1.7806e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2925 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2875 :
    ∀ b ∈ table_10_entries, ((2875) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.7953e-10 ∧ Bt 2 ≤ 8.1062e-7 ∧ Bt 3 ≤ 2.3508e-3 ∧ Bt 4 ≤ 6.8173e0 ∧
        Bt 5 ≤ 1.9770e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2875_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2875] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2850 :
    ∀ b ∈ table_10_entries, ((2850) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.2167e-10 ∧ Bt 2 ≤ 9.2481e-7 ∧ Bt 3 ≤ 2.6588e-3 ∧ Bt 4 ≤ 7.6442e0 ∧
        Bt 5 ≤ 2.1977e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2850_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2850] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2875 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2825 :
    ∀ b ∈ table_10_entries, ((2825) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.6911e-10 ∧ Bt 2 ≤ 1.0520e-6 ∧ Bt 3 ≤ 2.9981e-3 ∧ Bt 4 ≤ 8.5446e0 ∧
        Bt 5 ≤ 2.4352e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2825_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2825] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2850 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2800 :
    ∀ b ∈ table_10_entries, ((2800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.2388e-10 ∧ Bt 2 ≤ 1.1975e-6 ∧ Bt 3 ≤ 3.3829e-3 ∧ Bt 4 ≤ 9.5565e0 ∧
        Bt 5 ≤ 2.6997e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2825 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2775 :
    ∀ b ∈ table_10_entries, ((2775) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.8730e-10 ∧ Bt 2 ≤ 1.3644e-6 ∧ Bt 3 ≤ 3.8204e-3 ∧ Bt 4 ≤ 1.0697e1 ∧
        Bt 5 ≤ 2.9952e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2775_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2775] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2750 :
    ∀ b ∈ table_10_entries, ((2750) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.6071e-10 ∧ Bt 2 ≤ 1.5560e-6 ∧ Bt 3 ≤ 4.3178e-3 ∧ Bt 4 ≤ 1.1982e1 ∧
        Bt 5 ≤ 3.3250e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2750_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2750] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2775 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2725 :
    ∀ b ∈ table_10_entries, ((2725) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.4498e-10 ∧ Bt 2 ≤ 1.7737e-6 ∧ Bt 3 ≤ 4.8777e-3 ∧ Bt 4 ≤ 1.3414e1 ∧
        Bt 5 ≤ 3.6887e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2725_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2725] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2750 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2700 :
    ∀ b ∈ table_10_entries, ((2700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.4234e-10 ∧ Bt 2 ≤ 2.0229e-6 ∧ Bt 3 ≤ 5.5123e-3 ∧ Bt 4 ≤ 1.5021e1 ∧
        Bt 5 ≤ 4.0932e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2725 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2675 :
    ∀ b ∈ table_10_entries, ((2675) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.5431e-10 ∧ Bt 2 ≤ 2.3067e-6 ∧ Bt 3 ≤ 6.2279e-3 ∧ Bt 4 ≤ 1.6816e1 ∧
        Bt 5 ≤ 4.5402e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2675_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2675] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2650 :
    ∀ b ∈ table_10_entries, ((2650) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.8296e-10 ∧ Bt 2 ≤ 2.6294e-6 ∧ Bt 3 ≤ 7.0337e-3 ∧ Bt 4 ≤ 1.8815e1 ∧
        Bt 5 ≤ 5.0330e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2650_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2650] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2675 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2625 :
    ∀ b ∈ table_10_entries, ((2625) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.1314e-9 ∧ Bt 2 ≤ 2.9981e-6 ∧ Bt 3 ≤ 7.9449e-3 ∧ Bt 4 ≤ 2.1054e1 ∧
        Bt 5 ≤ 5.5793e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2625_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2625] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2650 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2600 :
    ∀ b ∈ table_10_entries, ((2600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3022e-9 ∧ Bt 2 ≤ 3.4184e-6 ∧ Bt 3 ≤ 8.9732e-3 ∧ Bt 4 ≤ 2.3555e1 ∧
        Bt 5 ≤ 6.1831e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2625 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2575 :
    ∀ b ∈ table_10_entries, ((2575) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.4992e-9 ∧ Bt 2 ≤ 3.8979e-6 ∧ Bt 3 ≤ 1.0135e-2 ∧ Bt 4 ≤ 2.6350e1 ∧
        Bt 5 ≤ 6.8509e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2575_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2575] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2550 :
    ∀ b ∈ table_10_entries, ((2550) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.7270e-9 ∧ Bt 2 ≤ 4.4470e-6 ∧ Bt 3 ≤ 1.1451e-2 ∧ Bt 4 ≤ 2.9487e1 ∧
        Bt 5 ≤ 7.5928e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2550_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2550] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2575 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2525 :
    ∀ b ∈ table_10_entries, ((2525) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.9873e-9 ∧ Bt 2 ≤ 5.0676e-6 ∧ Bt 3 ≤ 1.2922e-2 ∧ Bt 4 ≤ 3.2952e1 ∧
        Bt 5 ≤ 8.4027e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2525_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2525] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2550 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2500 :
    ∀ b ∈ table_10_entries, ((2500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.2884e-9 ∧ Bt 2 ≤ 5.7783e-6 ∧ Bt 3 ≤ 1.4590e-2 ∧ Bt 4 ≤ 3.6840e1 ∧
        Bt 5 ≤ 9.3021e4 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2525 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2475 :
    ∀ b ∈ table_10_entries, ((2475) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.6278e-9 ∧ Bt 2 ≤ 6.5696e-6 ∧ Bt 3 ≤ 1.6424e-2 ∧ Bt 4 ≤ 4.1060e1 ∧
        Bt 5 ≤ 1.0265e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2475_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2475] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2450 :
    ∀ b ∈ table_10_entries, ((2450) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.0228e-9 ∧ Bt 2 ≤ 7.4814e-6 ∧ Bt 3 ≤ 1.8517e-2 ∧ Bt 4 ≤ 4.5828e1 ∧
        Bt 5 ≤ 1.1343e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2450_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2450] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2475 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2425 :
    ∀ b ∈ table_10_entries, ((2425) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.4832e-9 ∧ Bt 2 ≤ 8.5339e-6 ∧ Bt 3 ≤ 2.0908e-2 ∧ Bt 4 ≤ 5.1225e1 ∧
        Bt 5 ≤ 1.2550e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2425_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2425] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2450 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2400 :
    ∀ b ∈ table_10_entries, ((2400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.8820e-9 ∧ Bt 2 ≤ 9.4139e-6 ∧ Bt 3 ≤ 2.2829e-2 ∧ Bt 4 ≤ 5.5360e1 ∧
        Bt 5 ≤ 1.3425e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2425 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2375 :
    ∀ b ∈ table_10_entries, ((2375) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.0498e-9 ∧ Bt 2 ≤ 9.7196e-6 ∧ Bt 3 ≤ 2.3327e-2 ∧ Bt 4 ≤ 5.5985e1 ∧
        Bt 5 ≤ 1.3436e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2375_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2375] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2350 :
    ∀ b ∈ table_10_entries, ((2350) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.2245e-9 ∧ Bt 2 ≤ 1.0033e-5 ∧ Bt 3 ≤ 2.3829e-2 ∧ Bt 4 ≤ 5.6593e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2350_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2350] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2375 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2325 :
    ∀ b ∈ table_10_entries, ((2325) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4062e-9 ∧ Bt 2 ≤ 1.0355e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2325_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2325] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2350 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2300 :
    ∀ b ∈ table_10_entries, ((2300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2325 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2275 :
    ∀ b ∈ table_10_entries, ((2275) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2275_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2275] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2250 :
    ∀ b ∈ table_10_entries, ((2250) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2250_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2250] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2275 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2225 :
    ∀ b ∈ table_10_entries, ((2225) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2225_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2225] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2250 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2200 :
    ∀ b ∈ table_10_entries, ((2200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2225 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2175 :
    ∀ b ∈ table_10_entries, ((2175) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2175_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2175] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2150 :
    ∀ b ∈ table_10_entries, ((2150) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2150_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2150] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2175 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2125 :
    ∀ b ∈ table_10_entries, ((2125) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2125_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2125] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2150 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2100 :
    ∀ b ∈ table_10_entries, ((2100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2125 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2075 :
    ∀ b ∈ table_10_entries, ((2075) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2075_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2075] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2050 :
    ∀ b ∈ table_10_entries, ((2050) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2050_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2050] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2075 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2025 :
    ∀ b ∈ table_10_entries, ((2025) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2025_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2025] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2050 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_2000 :
    ∀ b ∈ table_10_entries, ((2000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row2000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_2000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2025 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1975 :
    ∀ b ∈ table_10_entries, ((1975) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1975_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1975] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_2000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1950 :
    ∀ b ∈ table_10_entries, ((1950) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1950_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1950] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1975 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1925 :
    ∀ b ∈ table_10_entries, ((1925) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1925_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1925] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1950 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1900 :
    ∀ b ∈ table_10_entries, ((1900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1925 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1875 :
    ∀ b ∈ table_10_entries, ((1875) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1875_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1875] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1850 :
    ∀ b ∈ table_10_entries, ((1850) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1850_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1850] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1875 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1825 :
    ∀ b ∈ table_10_entries, ((1825) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1825_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1825] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1850 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1800 :
    ∀ b ∈ table_10_entries, ((1800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1825 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1775 :
    ∀ b ∈ table_10_entries, ((1775) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1775_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1775] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1750 :
    ∀ b ∈ table_10_entries, ((1750) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1750_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1750] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1775 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1725 :
    ∀ b ∈ table_10_entries, ((1725) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1725_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1725] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1750 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1700 :
    ∀ b ∈ table_10_entries, ((1700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1725 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1600 :
    ∀ b ∈ table_10_entries, ((1600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1500 :
    ∀ b ∈ table_10_entries, ((1500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_1000 :
    ∀ b ∈ table_10_entries, ((1000) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row1000_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_1000] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_900 :
    ∀ b ∈ table_10_entries, ((900) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row900_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_900] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_1000 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_800 :
    ∀ b ∈ table_10_entries, ((800) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row800_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_800] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_900 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_700 :
    ∀ b ∈ table_10_entries, ((700) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row700_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_700] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_800 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_600 :
    ∀ b ∈ table_10_entries, ((600) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row600_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_600] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_700 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_500 :
    ∀ b ∈ table_10_entries, ((500) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row500_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_500] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_600 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_400 :
    ∀ b ∈ table_10_entries, ((400) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row400_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_400] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_500 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_300 :
    ∀ b ∈ table_10_entries, ((300) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row300_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_300] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_400 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_200 :
    ∀ b ∈ table_10_entries, ((200) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row200_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_200] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_300 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_100 :
    ∀ b ∈ table_10_entries, ((100) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row100_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_100] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_200 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_95 :
    ∀ b ∈ table_10_entries, ((95) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row95_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_95] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_100 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_90 :
    ∀ b ∈ table_10_entries, ((90) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row90_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_90] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_95 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_85 :
    ∀ b ∈ table_10_entries, ((85) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row85_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_85] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_90 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_80 :
    ∀ b ∈ table_10_entries, ((80) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row80_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_80] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_85 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_75 :
    ∀ b ∈ table_10_entries, ((75) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row75_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_75] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_80 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_70 :
    ∀ b ∈ table_10_entries, ((70) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row70_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_70] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_75 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_65 :
    ∀ b ∈ table_10_entries, ((65) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row65_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_65] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_70 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_60 :
    ∀ b ∈ table_10_entries, ((60) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row60_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_60] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_65 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_59 :
    ∀ b ∈ table_10_entries, ((59) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row59_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_59] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_60 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_58 :
    ∀ b ∈ table_10_entries, ((58) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row58_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_58] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_59 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_57 :
    ∀ b ∈ table_10_entries, ((57) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row57_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_57] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_58 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_56 :
    ∀ b ∈ table_10_entries, ((56) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 4.4627e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row56_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_56] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_57 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_55 :
    ∀ b ∈ table_10_entries, ((55) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 6.3417e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row55_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_55] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_56 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_54 :
    ∀ b ∈ table_10_entries, ((54) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 9.8777e-9 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row54_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_54] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_55 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_53 :
    ∀ b ∈ table_10_entries, ((53) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.5373e-8 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row53_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_53] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_54 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_52 :
    ∀ b ∈ table_10_entries, ((52) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.3898e-8 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row52_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_52] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_53 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_51 :
    ∀ b ∈ table_10_entries, ((51) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.7146e-8 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row51_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_51] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_52 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_50 :
    ∀ b ∈ table_10_entries, ((50) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.7545e-8 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row50_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_50] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_51 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_49 :
    ∀ b ∈ table_10_entries, ((49) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.9139e-8 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row49_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_49] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_50 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_48 :
    ∀ b ∈ table_10_entries, ((48) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 1.3790e-7 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row48_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_48] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_49 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_47 :
    ∀ b ∈ table_10_entries, ((47) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 2.1307e-7 ∧ Bt 2 ≤ 1.0376e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row47_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_47] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_48 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_46 :
    ∀ b ∈ table_10_entries, ((46) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 3.2935e-7 ∧ Bt 2 ≤ 1.5479e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row46_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_46] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_47 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_45 :
    ∀ b ∈ table_10_entries, ((45) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 5.0646e-7 ∧ Bt 2 ≤ 2.3297e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row45_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_45] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_46 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_44 :
    ∀ b ∈ table_10_entries, ((44) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 7.8162e-7 ∧ Bt 2 ≤ 3.5173e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row44_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_44] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_45 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

private lemma table_11_suffix_from_19log10 :
    ∀ b ∈ table_10_entries, ((19 * Real.log 10) : ℝ) ≤ b → ∀ Bt : ℕ → ℝ,
      (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      Bt 1 ≤ 8.6315e-7 ∧ Bt 2 ≤ 3.7978e-5 ∧ Bt 3 ≤ 2.4333e-2 ∧ Bt 4 ≤ 5.7184e1 ∧
        Bt 5 ≤ 1.3441e5 := by
  intro b hb hge Bt hBt
  rcases eq_or_ge_next hb hge with rfl | hnext
  · obtain ⟨e1, e2, e3, e4, e5⟩ := table_10_row19log10_values_of_mem Bt hBt
    exact ⟨e1.le.trans (by norm_num), e2.le.trans (by norm_num),
      e3.le.trans (by norm_num), e4.le.trans (by norm_num), e5.le.trans (by norm_num)⟩
  · rw [table_10_next_cert_19log10] at hnext
    obtain ⟨h1, h2, h3, h4, h5⟩ :=
      table_11_suffix_from_44 b hb hnext Bt hBt
    exact ⟨h1.trans (by norm_num), h2.trans (by norm_num),
      h3.trans (by norm_num), h4.trans (by norm_num), h5.trans (by norm_num)⟩

-- The row dispatch below enumerates all 43 Table-11 rows and, inside each, all five
-- k-cases, so both the elaboration and the recursion budgets have to be raised — the
-- same reason `BKLNW_table10_dispatch.lean` raises them for its 287-row enumeration.
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 40000 in
lemma table_11_suffix_dominates (b₀ : ℝ) (B : ℕ → ℝ)
    (h : (b₀, B 1, B 2, B 3, B 4, B 5) ∈ BKLNW.table_11) (k : ℕ) (hk : k ∈ Finset.Icc 1 5) :
    ∀ b ∈ table_10_entries, ∀ Bt : ℕ → ℝ, (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      max b₀ (19 * log 10) ≤ b → Bt k * table_10_margin ≤ B k * table_11_margin := by
  have hgt := LogTables.log_10_gt
  have hlt := LogTables.log_10_lt
  have hm : (0 : ℝ) ≤ table_10_margin := by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin]
  obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
  intro b hb Bt hBt hge
  simp only [table_11, List.mem_cons, List.not_mem_nil, Prod.mk.injEq] at h
  casesm* _ ∨ _
  all_goals try contradiction
  all_goals obtain ⟨rfl, e1, e2, e3, e4, e5⟩ := h
  · rw [max_eq_right (by linarith : (20 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (21 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (22 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (23 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (24 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (25 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (26 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (27 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (28 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (29 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (30 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_right (by linarith : (43 : ℝ) ≤ 19 * log 10)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19log10 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 44)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_44 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 45)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_45 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 46)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_46 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 47)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_47 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 54)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_54 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 55)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_55 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 56)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_56 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2275)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2275 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2300)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2300 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2325)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2325 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2350)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2350 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2375)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2375 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 2400)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_2400 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 9800)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_9800 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 9900)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_9900 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 10000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_10000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 11000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_11000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 12000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_12000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 13000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_13000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 14000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_14000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 15000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_15000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 16000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_16000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 17000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_17000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 18000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_18000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 19000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_19000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 20000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_20000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 21000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_21000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 22000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_22000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 23000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_23000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 24000)] at hge
    obtain ⟨c1, c2, c3, c4, c5⟩ :=
      table_11_suffix_from_24000 b hb hge Bt hBt
    interval_cases k
    · rw [e1]
      exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e2]
      exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e3]
      exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e4]
      exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
    · rw [e5]
      exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · exfalso
    rw [max_eq_left (by linarith : (19 : ℝ) * log 10 ≤ 25000)] at hge
    have hK := table_10_entry_lt_K b hb
    norm_num [K] at hK
    linarith

/-- The degenerate top Table-11 row `b₀ = K`, whose domain is the single point `e^K`.
It is not itself a Table-10 entry, so it is served by the last real strip, `[24000, K]`. -/
lemma table_11_top_row_dominates (B : ℕ → ℝ) (k : ℕ) (hk : k ∈ Finset.Icc 1 5)
    (v1 : B 1 = 1.3804e-43) (v2 : B 2 = 3.4508e-39) (v3 : B 3 = 8.6269e-35)
    (v4 : B 4 = 2.1568e-30) (v5 : B 5 = 5.3919e-26) :
    ∀ b ∈ table_10_entries, ∀ Bt : ℕ → ℝ, (b, Bt 1, Bt 2, Bt 3, Bt 4, Bt 5) ∈ table_10 →
      (24000 : ℝ) ≤ b → Bt k * table_10_margin ≤ B k * table_11_margin := by
  obtain ⟨hk1, hk5⟩ := Finset.mem_Icc.mp hk
  have hm : (0 : ℝ) ≤ table_10_margin := by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin]
  intro b hb Bt hBt hge
  obtain ⟨c1, c2, c3, c4, c5⟩ := table_11_suffix_from_24000 b hb hge Bt hBt
  interval_cases k
  · rw [v1]
    exact (mul_le_mul_of_nonneg_right c1 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [v2]
    exact (mul_le_mul_of_nonneg_right c2 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [v3]
    exact (mul_le_mul_of_nonneg_right c3 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [v4]
    exact (mul_le_mul_of_nonneg_right c4 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])
  · rw [v5]
    exact (mul_le_mul_of_nonneg_right c5 hm).trans (by norm_num [table_10_margin, table_11_margin, BKLNW_app.table_8_margin])

end BKLNW
