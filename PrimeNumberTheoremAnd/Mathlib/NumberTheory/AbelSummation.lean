/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.NumberTheory.AbelSummation

/-!
# Finite-sum reindexing for Abel summation

Elementary reindexing lemmas for sums over initial intervals, used when passing between
floor sums and range sums.
-/

@[expose] public section

open Finset
open scoped BigOperators

variable {𝕜 : Type*} [AddCommGroup 𝕜]

/-- Reindex `∑ k ∈ Icc 1 N, f k` as `∑ n ∈ range N, f (n + 1)`. -/
theorem _root_.Finset.sum_Icc_one_eq_sum_range {N : ℕ} (f : ℕ → 𝕜) :
    ∑ k ∈ Icc 1 N, f k = ∑ n ∈ range N, f (n + 1) := by
  symm
  refine sum_bij (s := range N) (t := Icc 1 N)
    (f := fun n => f (n + 1)) (g := fun k => f k)
    (i := fun n _ => n + 1)
    ?hi ?hinj ?hsurj ?hcongr
  · intro n hn
    have hlt : n < N := mem_range.mp hn
    exact mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le n), Nat.succ_le_of_lt hlt⟩
  · intro a ha b hb h
    exact Nat.succ_injective h
  · intro k hk
    rcases mem_Icc.mp hk with ⟨hk1, hk2⟩
    refine ⟨k - 1, mem_range.mpr ?_, ?_⟩
    · have hsucc : (k - 1) + 1 = k := Nat.sub_add_cancel hk1
      exact lt_of_lt_of_le (Nat.lt_succ_self _) (by simpa [hsucc] using hk2)
    · simp [Nat.sub_add_cancel hk1]
  · intro n hn
    rfl

/-- If `f 0 = 0`, the term at `0` in `Icc 0 N` is redundant. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_Icc_one {N : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ Icc 1 N, f k := by
  have hdecomp : insert 0 (Icc 1 N) = Icc 0 N := by
    simpa [Nat.succ_eq_add_one] using
      insert_Icc_succ_left_eq_Icc (a := 0) (b := N) (h := Nat.zero_le N)
  have hnotmem : (0 : ℕ) ∉ Icc 1 N := by
    intro h
    exact (not_le.mpr (Nat.lt_succ_self 0)) (mem_Icc.mp h).1
  calc
    ∑ k ∈ Icc 0 N, f k = ∑ k ∈ insert 0 (Icc 1 N), f k := by simp [hdecomp]
    _ = f 0 + ∑ k ∈ Icc 1 N, f k := by simp
    _ = ∑ k ∈ Icc 1 N, f k := by simp [h0]

/-- If `f 0 = 0`, summing over `Icc 0 m` equals summing `f (n + 1)` over `range m`. -/
theorem _root_.Finset.sum_Icc_zero_eq_sum_range_succ {m : ℕ} {f : ℕ → 𝕜} (h0 : f 0 = 0) :
    ∑ k ∈ Icc 0 m, f k = ∑ n ∈ range m, f (n + 1) := by
  rw [sum_Icc_zero_eq_sum_Icc_one h0, sum_Icc_one_eq_sum_range]

/-- Floor-summation reindexing for sequences with `c 0 = 0`. -/
theorem _root_.sum_Icc_zero_floor_eq_sum_range {c : ℕ → 𝕜} (hc0 : c 0 = 0) (t : ℝ) :
    ∑ k ∈ Icc 0 ⌊t⌋₊, c k = ∑ n ∈ range ⌊t⌋₊, c (n + 1) :=
  Finset.sum_Icc_zero_eq_sum_range_succ (m := ⌊t⌋₊) (f := c) hc0
