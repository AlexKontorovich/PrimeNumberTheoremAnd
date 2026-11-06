import RSBounds.ZetaZeroTableHead

/-!
# The actual multiplicity-weighted zero head through height 100

The existing completeness theorem identifies the finite set of positive zeros
with the image of the certified first-29 table. Strict monotonicity makes that
enumeration injective, and certified simplicity reduces every multiplicity to
one. No new zero evaluation or Riemann-hypothesis assumption is used.
-/

open Complex

namespace TernaryGoldbach.RSBounds.ZetaZeroHeadBound
open BacklundCountIdentity BacklundLowCount ZetaZeroTable

/-- The already certified table enumerates exactly the inclusive height-100 head. -/
theorem first29_image_eq_closedPositiveZeros :
    Finset.univ.image (fun i : Fin 29 => (1 / 2 : ℂ) + first29.ordinate i * I) =
      closedPositiveZeros 100 := by
  classical
  have hindices : indicesBelow first29.ordinate 100 = Finset.univ := by
    ext i
    simp only [mem_indicesBelow, Finset.mem_univ, iff_true]
    exact first29.le_height i
  simpa only [hindices] using
    (listed_zeros_eq_closedPositiveZeros first29.strictMono
      (fun i => ⟨first29.positive i, first29.le_height i, first29.zero i⟩)
      (by norm_num : (0 : ℝ) < 100) le_rfl)

/-- Exact bridge from actual analytic multiplicities to the certified table sum. -/
theorem weighted_head_eq_first29 :
    (∑ ρ ∈ closedPositiveZeros 100,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) =
    ∑ i : Fin 29, 1 / ‖(1 / 2 : ℂ) + first29.ordinate i * I‖ := by
  classical
  rw [← first29_image_eq_closedPositiveZeros, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i _
    simp only [first29.simple, ENat.toNat_one, Nat.cast_one]
  · intro i _ j _ hij
    apply first29.strictMono.injective
    simpa using congrArg Complex.im hij

/-- Unconditional strict bound for the actual multiplicity-weighted head. -/
theorem weighted_head_lt :
    (∑ ρ ∈ closedPositiveZeros 100,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) < 0.592316 := by
  rw [weighted_head_eq_first29]
  exact ZetaZeroTableHead.first29_reciprocal_norm_sum_lt

theorem weighted_head_le :
    (∑ ρ ∈ closedPositiveZeros 100,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) ≤ 0.592316 :=
  weighted_head_lt.le

/-- Every finite subset of the positive height-100 head has the same upper bound. -/
theorem weighted_subset_sum_lt (s : Finset ℂ) (hs : s ⊆ closedPositiveZeros 100) :
    (∑ ρ ∈ s, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) < 0.592316 := by
  apply lt_of_le_of_lt _ weighted_head_lt
  exact Finset.sum_le_sum_of_subset_of_nonneg hs
    (fun ρ _ _ => div_nonneg (Nat.cast_nonneg _) (norm_nonneg ρ))

theorem weighted_subset_sum_le (s : Finset ℂ) (hs : s ⊆ closedPositiveZeros 100) :
    (∑ ρ ∈ s, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ‖ρ‖) ≤ 0.592316 :=
  (weighted_subset_sum_lt s hs).le

end TernaryGoldbach.RSBounds.ZetaZeroHeadBound
