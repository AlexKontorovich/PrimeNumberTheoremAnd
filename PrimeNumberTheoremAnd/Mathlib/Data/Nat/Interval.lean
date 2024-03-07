import Mathlib.Data.Nat.Interval

open Nat Finset

namespace Nat

theorem card_Icc_filter_dvd {n k : ℕ} (hk : 0 < k) (hn : 1 ≤ n) :
    card ((Icc 1 n).filter (k ∣ ·)) = n / k := by
  have h : (Icc 1 n).filter (k ∣ ·) = image (k * ·) (Icc 1 (n / k)) := by
    ext x
    simp only [not_lt_zero', mem_Icc, _root_.zero_le, true_and, mem_filter, mem_image]
    constructor <;> intro h
    · use x / k, ⟨?_, ?_⟩, Nat.mul_div_cancel' h.right
      · exact (Nat.one_le_div_iff hk).mpr $ le_of_dvd h.left.left h.right
      · exact Nat.div_le_div_right h.left.right
    · rcases h with ⟨h₁, h₂, h₃⟩
      refine ⟨?_, Dvd.intro h₁ h₃⟩
      have := mul_le_mul h₂.left hk zero_le_one (zero_le_one.trans h₂.left)
      simp only [reduceSucc, mul_one] at this
      rw [← h₃, mul_comm, ← Nat.le_div_iff_mul_le hk]
      exact ⟨this, h₂.right⟩
  have h_inj : Function.Injective (k * ·) :=
      fun _ _ h ↦ (mul_right_inj' (Nat.ne_zero_iff_zero_lt.mpr hk)).mp h
  rw [h, card_image_of_injective _ h_inj, card_Icc, Nat.add_sub_cancel]
