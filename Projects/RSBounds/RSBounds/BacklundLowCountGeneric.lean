import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Tactic

/-! A finite ordered enumeration turns main-term estimates at the enumerated
points into a strict error bound at every real threshold, including jumps. -/

open Set

namespace TernaryGoldbach.RSBounds.BacklundLowCount

noncomputable def indicesBelow {n : ℕ} (ts : Fin n → ℝ) (T : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ts i ≤ T)

@[simp] theorem mem_indicesBelow {n : ℕ} {ts : Fin n → ℝ} {T : ℝ} {i : Fin n} :
    i ∈ indicesBelow ts T ↔ ts i ≤ T := by
  classical
  simp [indicesBelow]

theorem card_indicesBelow_le {n : ℕ} (ts : Fin n → ℝ) (T : ℝ) :
    (indicesBelow ts T).card ≤ n := by
  classical
  simpa only [indicesBelow, Finset.card_univ, Fintype.card_fin] using
    (Finset.card_le_card (Finset.filter_subset (fun i => ts i ≤ T) Finset.univ))

/-- The cut in an increasing finite list is precisely its initial segment. -/
theorem le_iff_lt_card {n : ℕ} {ts : Fin n → ℝ} (hm : Monotone ts)
    (T : ℝ) (i : Fin n) : ts i ≤ T ↔ i.val < (indicesBelow ts T).card := by
  classical
  constructor
  · intro hi
    have hsub : Finset.Iic i ⊆ indicesBelow ts T := by
      intro j hj
      exact mem_indicesBelow.mpr ((hm (Finset.mem_Iic.mp hj)).trans hi)
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at hc
    omega
  · intro hi
    by_contra hti
    have hsub : indicesBelow ts T ⊆ Finset.Iio i := by
      intro j hj
      apply Finset.mem_Iio.mpr
      by_contra hij
      exact hti ((hm (le_of_not_gt hij)).trans (mem_indicesBelow.mp hj))
    have hc := Finset.card_le_card hsub
    simp only [Fin.card_Iio] at hc
    omega

theorem finite_count_error_lt_one {n : ℕ} {ts : Fin n → ℝ} {F : ℝ → ℝ}
    {a b T : ℝ} (hm : Monotone ts) (hF : MonotoneOn F (Ici a))
    (hts : ∀ i, a ≤ ts i ∧ ts i ≤ b)
    (hvalues : ∀ i, (i.val : ℝ) < F (ts i) ∧ F (ts i) < i.val + 1)
    (hTa : a ≤ T) (hTb : T ≤ b) (hlow : -1 < F T)
    (hhigh : F b < (n : ℝ) + 1) :
    |((indicesBelow ts T).card : ℝ) - F T| < 1 := by
  classical
  let k := (indicesBelow ts T).card
  have hkn : k ≤ n := card_indicesBelow_le ts T
  have hl : (k : ℝ) - 1 < F T := by
    by_cases hk : k = 0
    · simpa [hk] using hlow
    · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
      let i : Fin n := ⟨k - 1, by omega⟩
      have hit : ts i ≤ T := (le_iff_lt_card hm T i).mpr (by dsimp [i, k]; omega)
      have hfi := (hvalues i).1
      have hmono := hF (hts i).1 hTa hit
      have hcast : (i.val : ℝ) = (k : ℝ) - 1 := by
        dsimp [i]
        rw [Nat.cast_sub (by omega)]
        norm_num
      rw [hcast] at hfi
      exact hfi.trans_le hmono
  have hu : F T < (k : ℝ) + 1 := by
    by_cases hk : k = n
    · rw [hk]
      exact (hF hTa (hTa.trans hTb) hTb).trans_lt hhigh
    · let i : Fin n := ⟨k, by omega⟩
      have hit : T < ts i := by
        apply lt_of_not_ge
        intro h
        have := (le_iff_lt_card hm T i).mp h
        dsimp [i, k] at this
        omega
      exact (hF hTa (hts i).1 hit.le).trans_lt (hvalues i).2
  change |(k : ℝ) - F T| < 1
  rw [abs_lt]
  constructor <;> linarith

end TernaryGoldbach.RSBounds.BacklundLowCount
