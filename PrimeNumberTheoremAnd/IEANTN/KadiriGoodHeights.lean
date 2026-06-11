import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import Mathlib.Order.Interval.Set.Infinite

/-!
# Zero-free horizontal heights for Kadiri contour shifts

This file packages the finite-avoidance selector used to choose horizontal
contour heights away from zeta zeros.
-/

namespace Kadiri

open Complex

noncomputable section

/-- Both horizontal sides of the rectangle strip between `σ₁` and `σ₂` avoid
zeta zeros, and the pole point `1`. -/
def horizontalSegmentZeroFree (σ₁ σ₂ T : ℝ) : Prop :=
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → z.im = T →
    riemannZeta z ≠ 0 ∧ z ≠ 1) ∧
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → z.im = -T →
    riemannZeta z ≠ 0 ∧ z ≠ 1)

private lemma mem_Icc_min_max_of_mem_uIcc {σ₁ σ₂ x : ℝ}
    (hx : x ∈ Set.uIcc σ₁ σ₂) :
    x ∈ Set.Icc (min σ₁ σ₂) (max σ₁ σ₂) := by
  simpa [Set.uIcc] using hx

private lemma horizontal_height_selector_core (σ₁ σ₂ T₀ : ℝ) :
    ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧ horizontalSegmentZeroFree σ₁ σ₂ T := by
  classical
  let B : ℝ := max T₀ 0
  let R : ℝ := B + 1
  let rect : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc (-R) R)
  have hrect_compact : IsCompact rect := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  have hzeros_fin : (rect ∩ riemannZeta.zeroes : Set ℂ).Finite :=
    riemannZeta.zeroes_on_Compact_finite' hrect_compact
  let badHeights : Set ℝ := (fun z : ℂ => |z.im|) '' (rect ∩ riemannZeta.zeroes) ∪ {0}
  have hbad_fin : badHeights.Finite :=
    (hzeros_fin.image fun z : ℂ => |z.im|).union (Set.finite_singleton 0)
  have hBR : B < R := by
    dsimp [R]
    linarith
  obtain ⟨T, hT_interval, hT_not_bad⟩ :=
    (Set.Ioo_infinite hBR).exists_notMem_finite hbad_fin
  have hT_ge_T₀ : T₀ ≤ T := by
    exact (le_max_left T₀ 0).trans hT_interval.1.le
  have hT_pos : 0 < T := by
    exact lt_of_le_of_lt (le_max_right T₀ 0) hT_interval.1
  have hR_pos : 0 < R := by
    linarith [le_max_right T₀ 0]
  refine ⟨T, hT_ge_T₀, hT_pos, ?_⟩
  constructor
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hz_rect : z ∈ rect := by
        refine ⟨mem_Icc_min_max_of_mem_uIcc hzre, ?_⟩
        change z.im ∈ Set.Icc (-R) R
        rw [Set.mem_Icc, hzim]
        constructor
        · linarith
        · exact hT_interval.2.le
      have hz_zero : z ∈ riemannZeta.zeroes := by
        simpa [riemannZeta.zeroes] using hzeta
      have hT_bad : T ∈ badHeights := by
        left
        refine ⟨z, ⟨hz_rect, hz_zero⟩, ?_⟩
        change |z.im| = T
        rw [hzim, abs_of_pos hT_pos]
      exact hT_not_bad hT_bad
    · intro hz_one
      have hT_zero : T = 0 := by
        rw [hz_one] at hzim
        simpa using hzim.symm
      exact hT_pos.ne' hT_zero
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hz_rect : z ∈ rect := by
        refine ⟨mem_Icc_min_max_of_mem_uIcc hzre, ?_⟩
        change z.im ∈ Set.Icc (-R) R
        rw [Set.mem_Icc, hzim]
        constructor
        · linarith [hT_interval.2]
        · linarith
      have hz_zero : z ∈ riemannZeta.zeroes := by
        simpa [riemannZeta.zeroes] using hzeta
      have hT_bad : T ∈ badHeights := by
        left
        refine ⟨z, ⟨hz_rect, hz_zero⟩, ?_⟩
        change |z.im| = T
        rw [hzim, abs_neg, abs_of_pos hT_pos]
      exact hT_not_bad hT_bad
    · intro hz_one
      rw [hz_one] at hzim
      simp at hzim
      linarith

/-- Cofinal zero-free horizontal heights for the two sides of a Kadiri
rectangle.  This is the selector shape used before pulling contours at a
sequence of large heights. -/
theorem exists_arbitrarily_large_horizontalSegmentZeroFree (σ₁ σ₂ : ℝ) :
    ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧ horizontalSegmentZeroFree σ₁ σ₂ T :=
  horizontal_height_selector_core σ₁ σ₂

end

end Kadiri
