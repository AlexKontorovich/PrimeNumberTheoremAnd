import RSBounds.BacklundLowMainTerm
import RHHeight100.TwentyNineZeros

/-! The 29 public interval certificates, retaining their main-term bounds.
The decimal diagnostics in the provenance JSON are not used by this proof. -/

open Complex Set Real

namespace TernaryGoldbach.RSBounds.BacklundLowCount
open BacklundLowScalar

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Lower rational endpoint of the `k`-th public zero bracket. -/
def bracketLower (k : Fin 29) : ℚ :=
  (certificate ⟨2 * k.val, by have := k.isLt; omega⟩).t

/-- Upper rational endpoint of the `k`-th public zero bracket. -/
def bracketUpper (k : Fin 29) : ℚ :=
  (certificate ⟨2 * k.val + 1, by have := k.isLt; omega⟩).t

private theorem value_in_bracket {a b t : ℝ} {k : ℕ}
    (ha : 2 * Real.pi ≤ a) (ht : a < t ∧ t < b)
    (hl : (k : ℝ) < rosserF a) (hu : rosserF b < (k : ℝ) + 1) :
    (k : ℝ) < rosserF t ∧ rosserF t < (k : ℝ) + 1 := by
  exact ⟨hl.trans_le (rosserF_monotone ha (ha.trans ht.1.le) ht.1.le),
    (rosserF_monotone (ha.trans ht.1.le) (ha.trans (ht.1.trans ht.2).le) ht.2.le).trans_lt hu⟩

/-- One actual zero in each disjoint certified bracket, with its main term
strictly between the adjacent integers. This asserts no completeness by itself. -/
theorem exists_certified_zeros_with_brackets :
    ∃ ts : Fin 29 → ℝ, StrictMono ts ∧
      (∀ k, 1413 / 100 < ts k ∧ ts k < 100 ∧
        riemannZeta (1 / 2 + ts k * I) = 0 ∧
        (k.val : ℝ) < rosserF (ts k) ∧ rosserF (ts k) < k.val + 1) ∧
      ∀ k, (bracketLower k : ℝ) < ts k ∧ ts k < (bracketUpper k : ℝ) := by
  obtain ⟨t0, h0, z0⟩ := HardyFirstZero.first_zero_on_line
  obtain ⟨t1, h1, z1⟩ := HardyTenZeros.zero_in_2102
  obtain ⟨t2, h2, z2⟩ := HardyTenZeros.zero_in_2501
  obtain ⟨t3, h3, z3⟩ := HardyTenZeros.zero_in_3042
  obtain ⟨t4, h4, z4⟩ := HardyTenZeros.zero_in_3293
  obtain ⟨t5, h5, z5⟩ := HardyTenZeros.zero_in_3758
  obtain ⟨t6, h6, z6⟩ := HardyTenZeros.zero_in_4091
  obtain ⟨t7, h7, z7⟩ := HardyTenZeros.zero_in_4332
  obtain ⟨t8, h8, z8⟩ := HardyTenZeros.zero_in_4800
  obtain ⟨t9, h9, z9⟩ := HardyTenZeros.zero_in_4977
  obtain ⟨t10, h10, z10⟩ := RHHeight100.zero_in_5297
  obtain ⟨t11, h11, z11⟩ := RHHeight100.zero_in_5644
  obtain ⟨t12, h12, z12⟩ := RHHeight100.zero_in_5934
  obtain ⟨t13, h13, z13⟩ := RHHeight100.zero_in_6083
  obtain ⟨t14, h14, z14⟩ := RHHeight100.zero_in_6511
  obtain ⟨t15, h15, z15⟩ := RHHeight100.zero_in_67075
  obtain ⟨t16, h16, z16⟩ := RHHeight100.zero_in_6954
  obtain ⟨t17, h17, z17⟩ := RHHeight100.zero_in_7206
  obtain ⟨t18, h18, z18⟩ := RHHeight100.zero_in_7570
  obtain ⟨t19, h19, z19⟩ := RHHeight100.zero_in_7714
  obtain ⟨t20, h20, z20⟩ := RHHeight100.zero_in_7933
  obtain ⟨t21, h21, z21⟩ := RHHeight100.zero_in_8291
  obtain ⟨t22, h22, z22⟩ := RHHeight100.zero_in_8473
  obtain ⟨t23, h23, z23⟩ := RHHeight100.zero_in_8742
  obtain ⟨t24, h24, z24⟩ := RHHeight100.zero_in_8880
  obtain ⟨t25, h25, z25⟩ := RHHeight100.zero_in_9249
  obtain ⟨t26, h26, z26⟩ := RHHeight100.zero_in_9465
  obtain ⟨t27, h27, z27⟩ := RHHeight100.zero_in_95865
  obtain ⟨t28, h28, z28⟩ := RHHeight100.zero_in_9883
  have f0 : ((0 : ℕ) : ℝ) < rosserF t0 ∧ rosserF t0 < ((0 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 1413/100) (b := 707/50) (k := 0)
    · linarith only [Real.pi_lt_four]
    · exact h0
    · have hc := (certificate_bounds ⟨0, by decide⟩).1
      change ((0 : ℚ) : ℝ) < rosserF ((1413 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨1, by decide⟩).2
      change rosserF ((707 / 50 : ℚ) : ℝ) < ((1 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f1 : ((1 : ℕ) : ℝ) < rosserF t1 ∧ rosserF t1 < ((1 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 2102/100) (b := 2103/100) (k := 1)
    · linarith only [Real.pi_lt_four]
    · exact h1
    · have hc := (certificate_bounds ⟨2, by decide⟩).1
      change ((1 : ℚ) : ℝ) < rosserF ((1051 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨3, by decide⟩).2
      change rosserF ((2103 / 100 : ℚ) : ℝ) < ((2 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f2 : ((2 : ℕ) : ℝ) < rosserF t2 ∧ rosserF t2 < ((2 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 2501/100) (b := 2502/100) (k := 2)
    · linarith only [Real.pi_lt_four]
    · exact h2
    · have hc := (certificate_bounds ⟨4, by decide⟩).1
      change ((2 : ℚ) : ℝ) < rosserF ((2501 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨5, by decide⟩).2
      change rosserF ((1251 / 50 : ℚ) : ℝ) < ((3 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f3 : ((3 : ℕ) : ℝ) < rosserF t3 ∧ rosserF t3 < ((3 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 3042/100) (b := 3043/100) (k := 3)
    · linarith only [Real.pi_lt_four]
    · exact h3
    · have hc := (certificate_bounds ⟨6, by decide⟩).1
      change ((3 : ℚ) : ℝ) < rosserF ((1521 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨7, by decide⟩).2
      change rosserF ((3043 / 100 : ℚ) : ℝ) < ((4 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f4 : ((4 : ℕ) : ℝ) < rosserF t4 ∧ rosserF t4 < ((4 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 3293/100) (b := 3294/100) (k := 4)
    · linarith only [Real.pi_lt_four]
    · exact h4
    · have hc := (certificate_bounds ⟨8, by decide⟩).1
      change ((4 : ℚ) : ℝ) < rosserF ((3293 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨9, by decide⟩).2
      change rosserF ((1647 / 50 : ℚ) : ℝ) < ((5 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f5 : ((5 : ℕ) : ℝ) < rosserF t5 ∧ rosserF t5 < ((5 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 3758/100) (b := 3759/100) (k := 5)
    · linarith only [Real.pi_lt_four]
    · exact h5
    · have hc := (certificate_bounds ⟨10, by decide⟩).1
      change ((5 : ℚ) : ℝ) < rosserF ((1879 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨11, by decide⟩).2
      change rosserF ((3759 / 100 : ℚ) : ℝ) < ((6 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f6 : ((6 : ℕ) : ℝ) < rosserF t6 ∧ rosserF t6 < ((6 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 4091/100) (b := 4092/100) (k := 6)
    · linarith only [Real.pi_lt_four]
    · exact h6
    · have hc := (certificate_bounds ⟨12, by decide⟩).1
      change ((6 : ℚ) : ℝ) < rosserF ((4091 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨13, by decide⟩).2
      change rosserF ((1023 / 25 : ℚ) : ℝ) < ((7 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f7 : ((7 : ℕ) : ℝ) < rosserF t7 ∧ rosserF t7 < ((7 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 4332/100) (b := 4333/100) (k := 7)
    · linarith only [Real.pi_lt_four]
    · exact h7
    · have hc := (certificate_bounds ⟨14, by decide⟩).1
      change ((7 : ℚ) : ℝ) < rosserF ((1083 / 25 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨15, by decide⟩).2
      change rosserF ((4333 / 100 : ℚ) : ℝ) < ((8 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f8 : ((8 : ℕ) : ℝ) < rosserF t8 ∧ rosserF t8 < ((8 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 4800/100) (b := 4801/100) (k := 8)
    · linarith only [Real.pi_lt_four]
    · exact h8
    · have hc := (certificate_bounds ⟨16, by decide⟩).1
      change ((8 : ℚ) : ℝ) < rosserF ((48 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨17, by decide⟩).2
      change rosserF ((4801 / 100 : ℚ) : ℝ) < ((9 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f9 : ((9 : ℕ) : ℝ) < rosserF t9 ∧ rosserF t9 < ((9 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 4977/100) (b := 4978/100) (k := 9)
    · linarith only [Real.pi_lt_four]
    · exact h9
    · have hc := (certificate_bounds ⟨18, by decide⟩).1
      change ((9 : ℚ) : ℝ) < rosserF ((4977 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨19, by decide⟩).2
      change rosserF ((2489 / 50 : ℚ) : ℝ) < ((10 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f10 : ((10 : ℕ) : ℝ) < rosserF t10 ∧ rosserF t10 < ((10 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 5297/100) (b := 5298/100) (k := 10)
    · linarith only [Real.pi_lt_four]
    · exact h10
    · have hc := (certificate_bounds ⟨20, by decide⟩).1
      change ((10 : ℚ) : ℝ) < rosserF ((5297 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨21, by decide⟩).2
      change rosserF ((2649 / 50 : ℚ) : ℝ) < ((11 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f11 : ((11 : ℕ) : ℝ) < rosserF t11 ∧ rosserF t11 < ((11 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 5644/100) (b := 5645/100) (k := 11)
    · linarith only [Real.pi_lt_four]
    · exact h11
    · have hc := (certificate_bounds ⟨22, by decide⟩).1
      change ((11 : ℚ) : ℝ) < rosserF ((1411 / 25 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨23, by decide⟩).2
      change rosserF ((1129 / 20 : ℚ) : ℝ) < ((12 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f12 : ((12 : ℕ) : ℝ) < rosserF t12 ∧ rosserF t12 < ((12 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 5934/100) (b := 5935/100) (k := 12)
    · linarith only [Real.pi_lt_four]
    · exact h12
    · have hc := (certificate_bounds ⟨24, by decide⟩).1
      change ((12 : ℚ) : ℝ) < rosserF ((2967 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨25, by decide⟩).2
      change rosserF ((1187 / 20 : ℚ) : ℝ) < ((13 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f13 : ((13 : ℕ) : ℝ) < rosserF t13 ∧ rosserF t13 < ((13 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 6083/100) (b := 6084/100) (k := 13)
    · linarith only [Real.pi_lt_four]
    · exact h13
    · have hc := (certificate_bounds ⟨26, by decide⟩).1
      change ((13 : ℚ) : ℝ) < rosserF ((6083 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨27, by decide⟩).2
      change rosserF ((1521 / 25 : ℚ) : ℝ) < ((14 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f14 : ((14 : ℕ) : ℝ) < rosserF t14 ∧ rosserF t14 < ((14 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 6511/100) (b := 6512/100) (k := 14)
    · linarith only [Real.pi_lt_four]
    · exact h14
    · have hc := (certificate_bounds ⟨28, by decide⟩).1
      change ((14 : ℚ) : ℝ) < rosserF ((6511 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨29, by decide⟩).2
      change rosserF ((1628 / 25 : ℚ) : ℝ) < ((15 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f15 : ((15 : ℕ) : ℝ) < rosserF t15 ∧ rosserF t15 < ((15 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 67075/1000) (b := 67085/1000) (k := 15)
    · linarith only [Real.pi_lt_four]
    · exact h15
    · have hc := (certificate_bounds ⟨30, by decide⟩).1
      change ((15 : ℚ) : ℝ) < rosserF ((2683 / 40 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨31, by decide⟩).2
      change rosserF ((13417 / 200 : ℚ) : ℝ) < ((16 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f16 : ((16 : ℕ) : ℝ) < rosserF t16 ∧ rosserF t16 < ((16 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 6954/100) (b := 6955/100) (k := 16)
    · linarith only [Real.pi_lt_four]
    · exact h16
    · have hc := (certificate_bounds ⟨32, by decide⟩).1
      change ((16 : ℚ) : ℝ) < rosserF ((3477 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨33, by decide⟩).2
      change rosserF ((1391 / 20 : ℚ) : ℝ) < ((17 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f17 : ((17 : ℕ) : ℝ) < rosserF t17 ∧ rosserF t17 < ((17 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 7206/100) (b := 7207/100) (k := 17)
    · linarith only [Real.pi_lt_four]
    · exact h17
    · have hc := (certificate_bounds ⟨34, by decide⟩).1
      change ((17 : ℚ) : ℝ) < rosserF ((3603 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨35, by decide⟩).2
      change rosserF ((7207 / 100 : ℚ) : ℝ) < ((18 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f18 : ((18 : ℕ) : ℝ) < rosserF t18 ∧ rosserF t18 < ((18 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 7570/100) (b := 7571/100) (k := 18)
    · linarith only [Real.pi_lt_four]
    · exact h18
    · have hc := (certificate_bounds ⟨36, by decide⟩).1
      change ((18 : ℚ) : ℝ) < rosserF ((757 / 10 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨37, by decide⟩).2
      change rosserF ((7571 / 100 : ℚ) : ℝ) < ((19 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f19 : ((19 : ℕ) : ℝ) < rosserF t19 ∧ rosserF t19 < ((19 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 7714/100) (b := 7715/100) (k := 19)
    · linarith only [Real.pi_lt_four]
    · exact h19
    · have hc := (certificate_bounds ⟨38, by decide⟩).1
      change ((19 : ℚ) : ℝ) < rosserF ((3857 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨39, by decide⟩).2
      change rosserF ((1543 / 20 : ℚ) : ℝ) < ((20 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f20 : ((20 : ℕ) : ℝ) < rosserF t20 ∧ rosserF t20 < ((20 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 7933/100) (b := 7934/100) (k := 20)
    · linarith only [Real.pi_lt_four]
    · exact h20
    · have hc := (certificate_bounds ⟨40, by decide⟩).1
      change ((20 : ℚ) : ℝ) < rosserF ((7933 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨41, by decide⟩).2
      change rosserF ((3967 / 50 : ℚ) : ℝ) < ((21 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f21 : ((21 : ℕ) : ℝ) < rosserF t21 ∧ rosserF t21 < ((21 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 8291/100) (b := 8292/100) (k := 21)
    · linarith only [Real.pi_lt_four]
    · exact h21
    · have hc := (certificate_bounds ⟨42, by decide⟩).1
      change ((21 : ℚ) : ℝ) < rosserF ((8291 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨43, by decide⟩).2
      change rosserF ((2073 / 25 : ℚ) : ℝ) < ((22 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f22 : ((22 : ℕ) : ℝ) < rosserF t22 ∧ rosserF t22 < ((22 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 8473/100) (b := 8474/100) (k := 22)
    · linarith only [Real.pi_lt_four]
    · exact h22
    · have hc := (certificate_bounds ⟨44, by decide⟩).1
      change ((22 : ℚ) : ℝ) < rosserF ((8473 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨45, by decide⟩).2
      change rosserF ((4237 / 50 : ℚ) : ℝ) < ((23 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f23 : ((23 : ℕ) : ℝ) < rosserF t23 ∧ rosserF t23 < ((23 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 8742/100) (b := 8743/100) (k := 23)
    · linarith only [Real.pi_lt_four]
    · exact h23
    · have hc := (certificate_bounds ⟨46, by decide⟩).1
      change ((23 : ℚ) : ℝ) < rosserF ((4371 / 50 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨47, by decide⟩).2
      change rosserF ((8743 / 100 : ℚ) : ℝ) < ((24 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f24 : ((24 : ℕ) : ℝ) < rosserF t24 ∧ rosserF t24 < ((24 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 8880/100) (b := 8881/100) (k := 24)
    · linarith only [Real.pi_lt_four]
    · exact h24
    · have hc := (certificate_bounds ⟨48, by decide⟩).1
      change ((24 : ℚ) : ℝ) < rosserF ((444 / 5 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨49, by decide⟩).2
      change rosserF ((8881 / 100 : ℚ) : ℝ) < ((25 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f25 : ((25 : ℕ) : ℝ) < rosserF t25 ∧ rosserF t25 < ((25 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 9249/100) (b := 9250/100) (k := 25)
    · linarith only [Real.pi_lt_four]
    · exact h25
    · have hc := (certificate_bounds ⟨50, by decide⟩).1
      change ((25 : ℚ) : ℝ) < rosserF ((9249 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨51, by decide⟩).2
      change rosserF ((185 / 2 : ℚ) : ℝ) < ((26 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f26 : ((26 : ℕ) : ℝ) < rosserF t26 ∧ rosserF t26 < ((26 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 9465/100) (b := 9466/100) (k := 26)
    · linarith only [Real.pi_lt_four]
    · exact h26
    · have hc := (certificate_bounds ⟨52, by decide⟩).1
      change ((26 : ℚ) : ℝ) < rosserF ((1893 / 20 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨53, by decide⟩).2
      change rosserF ((4733 / 50 : ℚ) : ℝ) < ((27 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f27 : ((27 : ℕ) : ℝ) < rosserF t27 ∧ rosserF t27 < ((27 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 95865/1000) (b := 95875/1000) (k := 27)
    · linarith only [Real.pi_lt_four]
    · exact h27
    · have hc := (certificate_bounds ⟨54, by decide⟩).1
      change ((27 : ℚ) : ℝ) < rosserF ((19173 / 200 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨55, by decide⟩).2
      change rosserF ((767 / 8 : ℚ) : ℝ) < ((28 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  have f28 : ((28 : ℕ) : ℝ) < rosserF t28 ∧ rosserF t28 < ((28 : ℕ) : ℝ) + 1 := by
    apply value_in_bracket (a := 9883/100) (b := 9884/100) (k := 28)
    · linarith only [Real.pi_lt_four]
    · exact h28
    · have hc := (certificate_bounds ⟨56, by decide⟩).1
      change ((28 : ℚ) : ℝ) < rosserF ((9883 / 100 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
    · have hc := (certificate_bounds ⟨57, by decide⟩).2
      change rosserF ((2471 / 25 : ℚ) : ℝ) < ((29 : ℚ) : ℝ) at hc
      norm_num at hc ⊢
      exact hc
  norm_num [Set.mem_Ioo] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27 h28
  refine ⟨![t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28], ?_, ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · dsimp
      linarith only [h0.2, h1.1]
    · dsimp
      linarith only [h1.2, h2.1]
    · dsimp
      linarith only [h2.2, h3.1]
    · dsimp
      linarith only [h3.2, h4.1]
    · dsimp
      linarith only [h4.2, h5.1]
    · dsimp
      linarith only [h5.2, h6.1]
    · dsimp
      linarith only [h6.2, h7.1]
    · dsimp
      linarith only [h7.2, h8.1]
    · dsimp
      linarith only [h8.2, h9.1]
    · dsimp
      linarith only [h9.2, h10.1]
    · dsimp
      linarith only [h10.2, h11.1]
    · dsimp
      linarith only [h11.2, h12.1]
    · dsimp
      linarith only [h12.2, h13.1]
    · dsimp
      linarith only [h13.2, h14.1]
    · dsimp
      linarith only [h14.2, h15.1]
    · dsimp
      linarith only [h15.2, h16.1]
    · dsimp
      linarith only [h16.2, h17.1]
    · dsimp
      linarith only [h17.2, h18.1]
    · dsimp
      linarith only [h18.2, h19.1]
    · dsimp
      linarith only [h19.2, h20.1]
    · dsimp
      linarith only [h20.2, h21.1]
    · dsimp
      linarith only [h21.2, h22.1]
    · dsimp
      linarith only [h22.2, h23.1]
    · dsimp
      linarith only [h23.2, h24.1]
    · dsimp
      linarith only [h24.2, h25.1]
    · dsimp
      linarith only [h25.2, h26.1]
    · dsimp
      linarith only [h26.2, h27.1]
    · dsimp
      linarith only [h27.2, h28.1]
  · intro k
    fin_cases k
    · dsimp
      exact ⟨by linarith only [h0.1], by linarith only [h0.2], z0, f0⟩
    · dsimp
      exact ⟨by linarith only [h1.1], by linarith only [h1.2], z1, f1⟩
    · dsimp
      exact ⟨by linarith only [h2.1], by linarith only [h2.2], z2, f2⟩
    · dsimp
      exact ⟨by linarith only [h3.1], by linarith only [h3.2], z3, f3⟩
    · dsimp
      exact ⟨by linarith only [h4.1], by linarith only [h4.2], z4, f4⟩
    · dsimp
      exact ⟨by linarith only [h5.1], by linarith only [h5.2], z5, f5⟩
    · dsimp
      exact ⟨by linarith only [h6.1], by linarith only [h6.2], z6, f6⟩
    · dsimp
      exact ⟨by linarith only [h7.1], by linarith only [h7.2], z7, f7⟩
    · dsimp
      exact ⟨by linarith only [h8.1], by linarith only [h8.2], z8, f8⟩
    · dsimp
      exact ⟨by linarith only [h9.1], by linarith only [h9.2], z9, f9⟩
    · dsimp
      exact ⟨by linarith only [h10.1], by linarith only [h10.2], z10, f10⟩
    · dsimp
      exact ⟨by linarith only [h11.1], by linarith only [h11.2], z11, f11⟩
    · dsimp
      exact ⟨by linarith only [h12.1], by linarith only [h12.2], z12, f12⟩
    · dsimp
      exact ⟨by linarith only [h13.1], by linarith only [h13.2], z13, f13⟩
    · dsimp
      exact ⟨by linarith only [h14.1], by linarith only [h14.2], z14, f14⟩
    · dsimp
      exact ⟨by linarith only [h15.1], by linarith only [h15.2], z15, f15⟩
    · dsimp
      exact ⟨by linarith only [h16.1], by linarith only [h16.2], z16, f16⟩
    · dsimp
      exact ⟨by linarith only [h17.1], by linarith only [h17.2], z17, f17⟩
    · dsimp
      exact ⟨by linarith only [h18.1], by linarith only [h18.2], z18, f18⟩
    · dsimp
      exact ⟨by linarith only [h19.1], by linarith only [h19.2], z19, f19⟩
    · dsimp
      exact ⟨by linarith only [h20.1], by linarith only [h20.2], z20, f20⟩
    · dsimp
      exact ⟨by linarith only [h21.1], by linarith only [h21.2], z21, f21⟩
    · dsimp
      exact ⟨by linarith only [h22.1], by linarith only [h22.2], z22, f22⟩
    · dsimp
      exact ⟨by linarith only [h23.1], by linarith only [h23.2], z23, f23⟩
    · dsimp
      exact ⟨by linarith only [h24.1], by linarith only [h24.2], z24, f24⟩
    · dsimp
      exact ⟨by linarith only [h25.1], by linarith only [h25.2], z25, f25⟩
    · dsimp
      exact ⟨by linarith only [h26.1], by linarith only [h26.2], z26, f26⟩
    · dsimp
      exact ⟨by linarith only [h27.1], by linarith only [h27.2], z27, f27⟩
    · dsimp
      exact ⟨by linarith only [h28.1], by linarith only [h28.2], z28, f28⟩
  · intro k
    fin_cases k
    · change ((1413 / 100 : ℚ) : ℝ) < t0 ∧ t0 < ((707 / 50 : ℚ) : ℝ)
      norm_num
      exact h0
    · change ((1051 / 50 : ℚ) : ℝ) < t1 ∧ t1 < ((2103 / 100 : ℚ) : ℝ)
      norm_num
      exact h1
    · change ((2501 / 100 : ℚ) : ℝ) < t2 ∧ t2 < ((1251 / 50 : ℚ) : ℝ)
      norm_num
      exact h2
    · change ((1521 / 50 : ℚ) : ℝ) < t3 ∧ t3 < ((3043 / 100 : ℚ) : ℝ)
      norm_num
      exact h3
    · change ((3293 / 100 : ℚ) : ℝ) < t4 ∧ t4 < ((1647 / 50 : ℚ) : ℝ)
      norm_num
      exact h4
    · change ((1879 / 50 : ℚ) : ℝ) < t5 ∧ t5 < ((3759 / 100 : ℚ) : ℝ)
      norm_num
      exact h5
    · change ((4091 / 100 : ℚ) : ℝ) < t6 ∧ t6 < ((1023 / 25 : ℚ) : ℝ)
      norm_num
      exact h6
    · change ((1083 / 25 : ℚ) : ℝ) < t7 ∧ t7 < ((4333 / 100 : ℚ) : ℝ)
      norm_num
      exact h7
    · change ((48 : ℚ) : ℝ) < t8 ∧ t8 < ((4801 / 100 : ℚ) : ℝ)
      norm_num
      exact h8
    · change ((4977 / 100 : ℚ) : ℝ) < t9 ∧ t9 < ((2489 / 50 : ℚ) : ℝ)
      norm_num
      exact h9
    · change ((5297 / 100 : ℚ) : ℝ) < t10 ∧ t10 < ((2649 / 50 : ℚ) : ℝ)
      norm_num
      exact h10
    · change ((1411 / 25 : ℚ) : ℝ) < t11 ∧ t11 < ((1129 / 20 : ℚ) : ℝ)
      norm_num
      exact h11
    · change ((2967 / 50 : ℚ) : ℝ) < t12 ∧ t12 < ((1187 / 20 : ℚ) : ℝ)
      norm_num
      exact h12
    · change ((6083 / 100 : ℚ) : ℝ) < t13 ∧ t13 < ((1521 / 25 : ℚ) : ℝ)
      norm_num
      exact h13
    · change ((6511 / 100 : ℚ) : ℝ) < t14 ∧ t14 < ((1628 / 25 : ℚ) : ℝ)
      norm_num
      exact h14
    · change ((2683 / 40 : ℚ) : ℝ) < t15 ∧ t15 < ((13417 / 200 : ℚ) : ℝ)
      norm_num
      exact h15
    · change ((3477 / 50 : ℚ) : ℝ) < t16 ∧ t16 < ((1391 / 20 : ℚ) : ℝ)
      norm_num
      exact h16
    · change ((3603 / 50 : ℚ) : ℝ) < t17 ∧ t17 < ((7207 / 100 : ℚ) : ℝ)
      norm_num
      exact h17
    · change ((757 / 10 : ℚ) : ℝ) < t18 ∧ t18 < ((7571 / 100 : ℚ) : ℝ)
      norm_num
      exact h18
    · change ((3857 / 50 : ℚ) : ℝ) < t19 ∧ t19 < ((1543 / 20 : ℚ) : ℝ)
      norm_num
      exact h19
    · change ((7933 / 100 : ℚ) : ℝ) < t20 ∧ t20 < ((3967 / 50 : ℚ) : ℝ)
      norm_num
      exact h20
    · change ((8291 / 100 : ℚ) : ℝ) < t21 ∧ t21 < ((2073 / 25 : ℚ) : ℝ)
      norm_num
      exact h21
    · change ((8473 / 100 : ℚ) : ℝ) < t22 ∧ t22 < ((4237 / 50 : ℚ) : ℝ)
      norm_num
      exact h22
    · change ((4371 / 50 : ℚ) : ℝ) < t23 ∧ t23 < ((8743 / 100 : ℚ) : ℝ)
      norm_num
      exact h23
    · change ((444 / 5 : ℚ) : ℝ) < t24 ∧ t24 < ((8881 / 100 : ℚ) : ℝ)
      norm_num
      exact h24
    · change ((9249 / 100 : ℚ) : ℝ) < t25 ∧ t25 < ((185 / 2 : ℚ) : ℝ)
      norm_num
      exact h25
    · change ((1893 / 20 : ℚ) : ℝ) < t26 ∧ t26 < ((4733 / 50 : ℚ) : ℝ)
      norm_num
      exact h26
    · change ((19173 / 200 : ℚ) : ℝ) < t27 ∧ t27 < ((767 / 8 : ℚ) : ℝ)
      norm_num
      exact h27
    · change ((9883 / 100 : ℚ) : ℝ) < t28 ∧ t28 < ((2471 / 25 : ℚ) : ℝ)
      norm_num
      exact h28

/-- Rosser-specific projection of the same bracketed witnesses. -/
theorem exists_certified_zeros :
    ∃ ts : Fin 29 → ℝ, StrictMono ts ∧
      ∀ k, 1413 / 100 < ts k ∧ ts k < 100 ∧
        riemannZeta (1 / 2 + ts k * I) = 0 ∧
        (k.val : ℝ) < rosserF (ts k) ∧ rosserF (ts k) < k.val + 1 := by
  obtain ⟨ts, hm, hz, _⟩ := exists_certified_zeros_with_brackets
  exact ⟨ts, hm, hz⟩

end TernaryGoldbach.RSBounds.BacklundLowCount
