import RSBounds.BacklundLowCount

/-!
# Reusable certified tables of the first zeta zeros

`first29` packages the existing height-100 certificates once. Consumers obtain
rational brackets, ordered exact ordinates, simplicity, and completeness by
importing this module. No zero-location computation is repeated here.

The type is indexed by the table length and certified height so a later table
can use the same interface. Only the instance `CertifiedTable 29 100` is
constructed in this file; no height-280 or first-1000 certificate is asserted.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.ZetaZeroTable
open BacklundCountIdentity BacklundLowCount

/-- A complete ordered table of simple critical-line zeros through `height`,
with rational open brackets for their exact ordinates. -/
structure CertifiedTable (n : ℕ) (height : ℝ) where
  lower : Fin n → ℚ
  upper : Fin n → ℚ
  ordinate : Fin n → ℝ
  strictMono : StrictMono ordinate
  bracket : ∀ i, (lower i : ℝ) < ordinate i ∧ ordinate i < (upper i : ℝ)
  positive : ∀ i, 0 < ordinate i
  le_height : ∀ i, ordinate i ≤ height
  zero : ∀ i, riemannZeta (1 / 2 + ordinate i * I) = 0
  simple : ∀ i, analyticOrderAt riemannZeta (1 / 2 + ordinate i * I) = 1
  complete : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.im → ρ.im ≤ height →
    ∃ i, ρ = 1 / 2 + ordinate i * I

private noncomputable def selectedOrdinate : Fin 29 → ℝ :=
  Classical.choose exists_certified_zeros_with_brackets

private theorem selected_spec : StrictMono selectedOrdinate ∧
    (∀ k, 1413 / 100 < selectedOrdinate k ∧ selectedOrdinate k < 100 ∧
      riemannZeta (1 / 2 + selectedOrdinate k * I) = 0 ∧
      (k.val : ℝ) < rosserF (selectedOrdinate k) ∧
        rosserF (selectedOrdinate k) < k.val + 1) ∧
    ∀ k, (bracketLower k : ℝ) < selectedOrdinate k ∧
      selectedOrdinate k < (bracketUpper k : ℝ) :=
  Classical.choose_spec exists_certified_zeros_with_brackets

private theorem selected_zeros : ∀ i, 0 < selectedOrdinate i ∧
    selectedOrdinate i ≤ 100 ∧ riemannZeta (1 / 2 + selectedOrdinate i * I) = 0 := by
  intro i
  have h := selected_spec.2.1 i
  exact ⟨by linarith [h.1], h.2.1.le, h.2.2.1⟩

/-- The complete first 29 zeros, with their existing rational certificates.
Index `0` is the first positive-ordinate zero. -/
noncomputable def first29 : CertifiedTable 29 100 where
  lower := bracketLower
  upper := bracketUpper
  ordinate := selectedOrdinate
  strictMono := selected_spec.1
  bracket := selected_spec.2.2
  positive := fun i => (selected_zeros i).1
  le_height := fun i => (selected_zeros i).2.1
  zero := fun i => (selected_zeros i).2.2
  simple := by
    intro i
    exact (zero_simple_below_hundred (selected_zeros i).2.2
      (by simpa using (selected_zeros i).1)
      (by simpa using (selected_zeros i).2.1)).2
  complete := by
    classical
    intro ρ hz h0 h100
    have hmem : ρ ∈ closedPositiveZeros 100 :=
      (mem_closedPositiveZeros_iff (by norm_num)).mpr ⟨hz, h0, h100⟩
    rw [← listed_zeros_eq_closedPositiveZeros selected_spec.1 selected_zeros
      (by norm_num : (0 : ℝ) < 100) le_rfl] at hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    exact ⟨i, hi.symm⟩

theorem first29_bracket (i : Fin 29) :
    (bracketLower i : ℝ) < first29.ordinate i ∧
      first29.ordinate i < (bracketUpper i : ℝ) := first29.bracket i

theorem first29_simple (i : Fin 29) :
    analyticOrderAt riemannZeta (1 / 2 + first29.ordinate i * I) = 1 := first29.simple i

/-- Every zero in the height-100 window occurs in the table, including any
zero at the upper endpoint. There is no real-part hypothesis. -/
theorem zero_iff_exists_index {ρ : ℂ} (h0 : 0 < ρ.im) (h100 : ρ.im ≤ 100) :
    riemannZeta ρ = 0 ↔ ∃ i : Fin 29, ρ = 1 / 2 + first29.ordinate i * I := by
  constructor
  · exact fun hz => first29.complete ρ hz h0 h100
  · rintro ⟨i, rfl⟩
    exact first29.zero i

/-- Exact inclusive count at every real threshold in the certified range. -/
theorem positiveZeroCount_eq_table {T : ℝ} (hT : 0 ≤ T) (h100 : T ≤ 100) :
    Rosser1941.positiveZeroCount T = ((indicesBelow first29.ordinate T).card : ℝ) := by
  classical
  by_cases hzero : T = 0
  · subst T
    have hempty : indicesBelow first29.ordinate 0 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact (not_le_of_gt (first29.positive i)) (mem_indicesBelow.mp hi)
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    unfold Rosser1941.positiveZeroCount
    calc
      _ = ∑' _ρ : ℂ, (0 : ℝ) := by
        apply tsum_congr
        intro ρ
        have hi : ¬ (0 < ρ.im ∧ ρ.im ≤ 0) := by rintro ⟨h1, h2⟩; linarith
        simp [hi]
      _ = 0 := tsum_zero
  · have hpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
    rw [Rosser1941.positiveZeroCount_eq hpos,
      count_eq_indicesBelow first29.strictMono
        (fun i => ⟨first29.positive i, first29.le_height i, first29.zero i⟩) hpos h100]

/-- A computable lower count: a bracket entirely below `T` guarantees a zero. -/
def lowerCount (T : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 29 => bracketUpper i ≤ T)).card

/-- A computable upper count: every zero at most `T` has its lower endpoint
strictly below `T`, because the certified brackets are open. -/
def upperCount (T : ℚ) : ℕ :=
  (Finset.univ.filter (fun i : Fin 29 => bracketLower i < T)).card

/-- Rational endpoint comparisons bound the exact zero count without
evaluating the noncomputable exact ordinates. -/
theorem bracket_count_bounds {T : ℚ} (hT : 0 ≤ T) (h100 : T ≤ 100) :
    (lowerCount T : ℝ) ≤ Rosser1941.positiveZeroCount (T : ℝ) ∧
      Rosser1941.positiveZeroCount (T : ℝ) ≤ (upperCount T : ℝ) := by
  classical
  rw [positiveZeroCount_eq_table (by exact_mod_cast hT) (by exact_mod_cast h100)]
  constructor
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    have hiq : bracketUpper i ≤ T := (Finset.mem_filter.mp hi).2
    exact mem_indicesBelow.mpr ((first29_bracket i).2.le.trans (by exact_mod_cast hiq))
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro i hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ i, ?_⟩
    have hir : (bracketLower i : ℝ) < (T : ℝ) :=
      (first29_bracket i).1.trans_le (mem_indicesBelow.mp hi)
    exact_mod_cast hir

theorem positiveZeroCount_hundred : Rosser1941.positiveZeroCount 100 = 29 := by
  rw [Rosser1941.positiveZeroCount_eq (by norm_num), closed_count_hundred]
  norm_num

end TernaryGoldbach.RSBounds.ZetaZeroTable
