import RSBounds.BacklundLowCountGeneric
import RSBounds.BacklundLowZeros
import RSBounds.BacklundRH100Bridge
import RSBounds.RosserCountDefinition

/-!
# The actual zero-count estimate through height 100

The public, replayed height-100 certificate supplies completeness and
simplicity. The 29 separate interval certificates locate those zeros.
Finite ordered enumeration and the checked logarithm bounds then give
the strict error `< 1` at every height, including the zero ordinates.
There is no RH assumption in any theorem below.
-/

open Complex Set

namespace TernaryGoldbach.RSBounds.BacklundLowCount
open BacklundCountIdentity BacklundLowScalar

/-- Completeness of any 29 distinct listed zeros in the certified range,
as an equality of the actual finite zero sets. -/
theorem listed_zeros_eq_closedPositiveZeros {ts : Fin 29 → ℝ} (hm : StrictMono ts)
    (hz : ∀ i, 0 < ts i ∧ ts i ≤ 100 ∧ riemannZeta (1 / 2 + ts i * I) = 0)
    {T : ℝ} (hT : 0 < T) (h100 : T ≤ 100) :
    (indicesBelow ts T).image (fun i => (1 / 2 : ℂ) + ts i * I) =
      closedPositiveZeros T := by
  classical
  let ρ : Fin 29 → ℂ := fun i => 1 / 2 + ts i * I
  have him (i : Fin 29) : (ρ i).im = ts i := by simp [ρ]
  have hinj : Function.Injective ρ := by
    intro i j hij
    apply hm.injective
    simpa only [him] using congrArg Complex.im hij
  have hsub : Finset.univ.image ρ ⊆ closedPositiveZeros 100 := by
    intro z hz'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz'
    apply (mem_closedPositiveZeros_iff (by norm_num)).mpr
    exact ⟨(hz i).2.2, by simpa only [him] using (hz i).1,
      by simpa only [him] using (hz i).2.1⟩
  have hcard : (closedPositiveZeros 100).card = 29 := by
    rw [← closed_count_eq_card (by norm_num) le_rfl]
    exact closed_count_hundred
  have hall : Finset.univ.image ρ = closedPositiveZeros 100 := by
    apply Finset.eq_of_subset_of_card_le hsub
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, hcard]
  have hset : (indicesBelow ts T).image ρ = closedPositiveZeros T := by
    ext z
    constructor
    · intro hz'
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz'
      apply (mem_closedPositiveZeros_iff hT).mpr
      exact ⟨(hz i).2.2, by simpa only [him] using (hz i).1,
        by simpa only [him] using mem_indicesBelow.mp hi⟩
    · intro hz'
      obtain ⟨hzeta, hi0, hiT⟩ := (mem_closedPositiveZeros_iff hT).mp hz'
      have hz100 : z ∈ closedPositiveZeros 100 :=
        (mem_closedPositiveZeros_iff (by norm_num)).mpr ⟨hzeta, hi0, hiT.trans h100⟩
      rw [← hall] at hz100
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz100
      exact Finset.mem_image.mpr ⟨i, mem_indicesBelow.mpr (by simpa only [him] using hiT), rfl⟩
  exact hset

/-- The inclusive multiplicity count is the number of listed ordinates
at most the threshold. -/
theorem count_eq_indicesBelow {ts : Fin 29 → ℝ} (hm : StrictMono ts)
    (hz : ∀ i, 0 < ts i ∧ ts i ≤ 100 ∧ riemannZeta (1 / 2 + ts i * I) = 0)
    {T : ℝ} (hT : 0 < T) (h100 : T ≤ 100) :
    N_le T = (indicesBelow ts T).card := by
  classical
  have hinj : Function.Injective (fun i => (1 / 2 : ℂ) + ts i * I) := by
    intro i j hij
    apply hm.injective
    simpa using congrArg Complex.im hij
  rw [closed_count_eq_card hT h100,
    ← listed_zeros_eq_closedPositiveZeros hm hz hT h100,
    Finset.card_image_of_injective _ hinj]

/-- Unconditional finite-height estimate for the inclusive actual count. -/
theorem count_error_lt_one {T : ℝ} (hT : 0 < T) (h100 : T ≤ 100) :
    |(N_le T : ℝ) - rosserF T| < 1 := by
  classical
  obtain ⟨ts, hm, hz⟩ := exists_certified_zeros
  have hz' : ∀ i, 0 < ts i ∧ ts i ≤ 100 ∧ riemannZeta (1 / 2 + ts i * I) = 0 := by
    intro i
    exact ⟨by linarith [(hz i).1], (hz i).2.1.le, (hz i).2.2.1⟩
  rw [count_eq_indicesBelow hm hz' (by linarith) h100]
  by_cases hsmall : T ≤ 1413 / 100
  · have hempty : indicesBelow ts T = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      have := mem_indicesBelow.mp hi
      linarith [(hz i).1]
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
    rw [abs_lt]
    exact ⟨by have := rosserF_lower (show 0 < T by linarith); linarith,
      rosserF_lt_one_small (by linarith) hsmall⟩
  · have hpi : 2 * Real.pi ≤ (1413 / 100 : ℝ) := by
      have := Real.pi_lt_four
      linarith
    apply finite_count_error_lt_one hm.monotone
      (a := 1413 / 100) (b := 100)
    · intro x hx y hy hxy
      exact rosserF_monotone (hpi.trans hx) (hpi.trans hy) hxy
    · intro i
      exact ⟨(hz i).1.le, (hz i).2.1.le⟩
    · intro i
      exact (hz i).2.2.2
    · exact (lt_of_not_ge hsmall).le
    · exact h100
    · have := rosserF_lower (show 0 < T by linarith)
      linarith
    · norm_num
      exact rosserF_hundred_lt

/-- Rosser's stated envelope holds on the finite handoff range. -/
theorem rosser_bound_low {T : ℝ} (hT : 2 ≤ T) (h100 : T ≤ 100) :
    |(N_le T : ℝ) - rosserF T| < rosserR 1.588 T :=
  (count_error_lt_one (by linarith) h100).trans (one_lt_rosserR hT)

end TernaryGoldbach.RSBounds.BacklundLowCount

namespace TernaryGoldbach.RSBounds.Rosser1941

/-- The reusable, unconditional strict error bound through height 100 for
the actual inclusive positive-ordinate zero count, with multiplicity. -/
theorem zero_count_error_lt_one_to_100 (T : ℝ) (hT : 0 ≤ T) (h100 : T ≤ 100) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) - T / (2 * Real.pi) + 7 / 8)| < 1 := by
  by_cases hzero : T = 0
  · subst T
    have hc : positiveZeroCount 0 = 0 := by
      classical
      have hi (ρ : ℂ) : ¬ (0 < ρ.im ∧ ρ.im ≤ 0) := by
        rintro ⟨h1, h2⟩
        linarith
      simp [positiveZeroCount, hi]
    rw [hc]
    norm_num
  · have hTpos : 0 < T := lt_of_le_of_ne hT (Ne.symm hzero)
    rw [positiveZeroCount_eq hTpos]
    exact BacklundLowCount.count_error_lt_one hTpos h100

end TernaryGoldbach.RSBounds.Rosser1941
