import RSBounds.PsiFinite.SmallWalkData
import RSBounds.PsiFinite.Segment

/-!
# The range `8 < x < 10^4`, and the enclosures at `10^4`

Chains the kernel-checked chunks of `SmallWalkData`.
-/

namespace PsiFinite

open Real
open PsiFinite.SmallWalkData

theorem GapsOK.trans {a b c : ℕ} (h1 : GapsOK a b) (h2 : GapsOK b c) : GapsOK a c := by
  intro m hm1 hm2 hm8 x hx1 hx2
  by_cases h : m < b
  · exact h1 m hm1 h hm8 x hx1 hx2
  · exact h2 m (by omega) hm2 hm8 x hx1 hx2

/-- The state of the walk at `10^4`. -/
def wsTenK : WS := ⟨9210340371976077481578637322766, 9210340371976219110227839171900,
  10013396693262983521053440538486993, 10013396693263160145856910841316409⟩

theorem small_walk : WInv 10000 wsTenK ∧ GapsOK 1 10000 := by
  have c0 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) winv_one wk_0
  have c1 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c0.1 wk_1
  have c2 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c1.1 wk_2
  have c3 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c2.1 wk_3
  have c4 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c3.1 wk_4
  have c5 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c4.1 wk_5
  have c6 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c5.1 wk_6
  have c7 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c6.1 wk_7
  have c8 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c7.1 wk_8
  have c9 := walkK_sound _ _ _ _ (by norm_num) (by norm_num) c8.1 wk_9
  exact ⟨c9.1, c0.2.trans (c1.2.trans (c2.2.trans (c3.2.trans (c4.2.trans (c5.2.trans
    (c6.2.trans (c7.2.trans (c8.2.trans c9.2))))))))⟩

/-- The campaign's starting enclosures, at `10^4`. -/
def stTenK : St := ⟨10013396693262983521053440538486993, 10013396693263160145856910841316409,
  9210340371976077481578637322766, 9210340371976219110227839171900⟩

theorem encl_tenK : Encl 10000 stTenK := by
  obtain ⟨⟨l1, l2, p1, p2⟩, -⟩ := small_walk
  exact ⟨p1, p2, l1, l2⟩

theorem gap_bound {x : ℝ} (h8 : 8 ≤ x) (h2 : x < 10000) :
    |Chebyshev.psi x - x| ≤ ((kNum ⌊x⌋₊ : ℝ) / kDen ⌊x⌋₊) * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hm8 : 8 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h8)
  have hm : ⌊x⌋₊ < 10000 := (Nat.floor_lt hx0).mpr (by exact_mod_cast h2)
  exact small_walk.2 ⌊x⌋₊ (by omega) hm hm8 x (Nat.floor_le hx0) (Nat.lt_floor_add_one x)

/-- `|ψ x - x| ≤ (4/5) √x` for `1500 ≤ x < 10^4`. -/
theorem small_four_fifths {x : ℝ} (h1 : 1500 ≤ x) (h2 : x < 10000) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x := by
  have h := gap_bound (by linarith) h2
  have hm : 1500 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hk : ((kNum ⌊x⌋₊ : ℝ) / kDen ⌊x⌋₊) = 4 / 5 := by
    unfold kNum kDen; rw [ite_eq_right (by omega), ite_eq_right (by omega)]; norm_num
  rwa [hk] at h

/-- `|ψ x - x| ≤ √x` for `8 ≤ x < 10^4`. -/
theorem small_sqrt {x : ℝ} (h1 : 8 ≤ x) (h2 : x < 10000) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x := by
  have h := gap_bound h1 h2
  have hk : ((kNum ⌊x⌋₊ : ℝ) / kDen ⌊x⌋₊) ≤ 1 := by
    unfold kNum kDen; split_ifs <;> norm_num
  calc |Chebyshev.psi x - x| ≤ _ := h
    _ ≤ 1 * Real.sqrt x := mul_le_mul_of_nonneg_right hk (Real.sqrt_nonneg x)
    _ = Real.sqrt x := one_mul _

end PsiFinite
