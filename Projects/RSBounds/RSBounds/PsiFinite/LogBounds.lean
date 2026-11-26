import TernaryGoldbach.Prelim.RamareHarm
import RSBounds.PsiFinite.Kernel

/-!
# The directed logarithm increments

`logInc_bounds`: for `A, h ≥ 1`,
`logIncLo A h ≤ D (log (A+h) - log A) ≤ logIncHi A h`.
It specializes `TernaryGoldbach.Prelim.RamPf.log_one_add_inv_bounds`
(three terms of the `artanh` series plus a geometric tail) to `a = A/h`.
-/

namespace PsiFinite

open Real

theorem floor_div_le (n m : ℕ) : ((n / m : ℕ) : ℝ) ≤ (n : ℝ) / m := Nat.cast_div_le

theorem le_floor_div_add_one (n m : ℕ) (hm : 0 < m) : (n : ℝ) / m ≤ ((n / m : ℕ) : ℝ) + 1 := by
  have h2 := Nat.lt_div_mul_add (a := n) hm
  have hq : (0 : ℝ) < m := by exact_mod_cast hm
  have : (n : ℝ) < ((n / m : ℕ) : ℝ) * m + m := by exact_mod_cast h2
  rw [div_le_iff₀ hq]; linarith

theorem D_pos : (0 : ℝ) < (D : ℝ) := by norm_num [D]

theorem logInc_bounds {A h : ℕ} (hA : 1 ≤ A) (hh : 1 ≤ h) :
    (logIncLo A h : ℝ) ≤ (D : ℝ) * (Real.log (A + h) - Real.log A) ∧
      (D : ℝ) * (Real.log (A + h) - Real.log A) ≤ (logIncHi A h : ℝ) := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hh0 : (0 : ℝ) < h := by exact_mod_cast hh
  set a : ℝ := (A : ℝ) / h with ha
  have ha0 : 0 < a := by positivity
  obtain ⟨hlo, hhi⟩ := TernaryGoldbach.Prelim.RamPf.log_one_add_inv_bounds ha0 3
  have hlog : Real.log (1 + a⁻¹) = Real.log (A + h) - Real.log A := by
    rw [← Real.log_div (by positivity) hA0.ne']; congr 1; rw [ha]; field_simp
  rw [hlog] at hlo hhi
  have hy : 1 / (2 * a + 1) = (h : ℝ) / (2 * A + h) := by rw [ha]; field_simp
  rw [hy] at hlo hhi
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hlo hhi
  have hqpos : (0 : ℝ) < 2 * A + h := by positivity
  have hApos : (0 : ℝ) < 4 * A * (A + h) := by positivity
  have L1 : 2 * (h : ℝ) / (2 * A + h) + 2 * (h : ℝ) ^ 3 / (3 * (2 * A + h) ^ 3) +
      2 * (h : ℝ) ^ 5 / (5 * (2 * A + h) ^ 5) ≤ Real.log (A + h) - Real.log A := by
    refine le_trans (le_of_eq ?_) hlo; push_cast; field_simp; ring
  have L2 : Real.log (A + h) - Real.log A ≤ 2 * (h : ℝ) / (2 * A + h) +
      2 * (h : ℝ) ^ 3 / (3 * (2 * A + h) ^ 3) + 2 * (h : ℝ) ^ 5 / (5 * (2 * A + h) ^ 5) +
      2 * (h : ℝ) ^ 7 / (7 * (2 * A + h) ^ 5 * (4 * A * (A + h))) := by
    refine le_trans hhi (le_of_eq ?_)
    have e1 : 1 - ((h : ℝ) / (2 * A + h)) ^ 2 = 4 * A * (A + h) / (2 * A + h) ^ 2 := by
      field_simp; ring
    rw [e1]; push_cast; field_simp; ring
  have hD := D_pos
  have M1 := mul_le_mul_of_nonneg_left L1 hD.le
  have M2 := mul_le_mul_of_nonneg_left L2 hD.le
  have a0 := floor_div_le (2 * D * h) (2 * A + h)
  have a1 := floor_div_le (2 * D * h ^ 3) (3 * (2 * A + h) ^ 3)
  have a2 := floor_div_le (2 * D * h ^ 5) (5 * (2 * A + h) ^ 5)
  have b0 := le_floor_div_add_one (2 * D * h) (2 * A + h) (by omega)
  have b1 := le_floor_div_add_one (2 * D * h ^ 3) (3 * (2 * A + h) ^ 3) (by positivity)
  have b2 := le_floor_div_add_one (2 * D * h ^ 5) (5 * (2 * A + h) ^ 5) (by positivity)
  have b3 := le_floor_div_add_one (2 * D * h ^ 7) (7 * (2 * A + h) ^ 5 * (4 * A * (A + h)))
    (by positivity)
  push_cast at a0 a1 a2 b0 b1 b2 b3
  have e1 : (D : ℝ) * (2 * (h : ℝ) / (2 * A + h) + 2 * (h : ℝ) ^ 3 / (3 * (2 * A + h) ^ 3) +
      2 * (h : ℝ) ^ 5 / (5 * (2 * A + h) ^ 5)) = 2 * D * h / (2 * A + h) +
      2 * D * h ^ 3 / (3 * (2 * A + h) ^ 3) + 2 * D * h ^ 5 / (5 * (2 * A + h) ^ 5) := by ring
  have e2 : (D : ℝ) * (2 * (h : ℝ) / (2 * A + h) + 2 * (h : ℝ) ^ 3 / (3 * (2 * A + h) ^ 3) +
      2 * (h : ℝ) ^ 5 / (5 * (2 * A + h) ^ 5) +
      2 * (h : ℝ) ^ 7 / (7 * (2 * A + h) ^ 5 * (4 * A * (A + h)))) = 2 * D * h / (2 * A + h) +
      2 * D * h ^ 3 / (3 * (2 * A + h) ^ 3) + 2 * D * h ^ 5 / (5 * (2 * A + h) ^ 5) +
      2 * D * h ^ 7 / (7 * (2 * A + h) ^ 5 * (4 * A * (A + h))) := by ring
  rw [e1] at M1; rw [e2] at M2
  unfold logIncHi logIncLo
  simp only
  push_cast
  constructor <;> linarith

end PsiFinite
