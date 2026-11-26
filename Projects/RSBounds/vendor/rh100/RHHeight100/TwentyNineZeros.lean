module

public import HardyTenZeros.TenZeros
public import RHHeight100.Box5297
public import RHHeight100.Box5644
public import RHHeight100.Box5934
public import RHHeight100.Box6083
public import RHHeight100.Box6511
public import RHHeight100.Box67075
public import RHHeight100.Box6954
public import RHHeight100.Box7206
public import RHHeight100.Box7570
public import RHHeight100.Box7714
public import RHHeight100.Box7933
public import RHHeight100.Box8291
public import RHHeight100.Box8473
public import RHHeight100.Box8742
public import RHHeight100.Box8880
public import RHHeight100.Box9249
public import RHHeight100.Box9465
public import RHHeight100.Box95865
public import RHHeight100.Box9883

@[expose] public section

/-!
# Twenty-nine zeros of zeta on the critical line below height 100 (hunt #137)

The ten zeros of hunt #133 (`HardyTenZeros.ten_zeros_on_line_below_fifty`, one per bracket
`first_zero_on_line` and `zero_in_2102`, ..., `zero_in_4977`) followed by the nineteen
`RHHeight100.zero_in_*` brackets above 52.9. The brackets are disjoint and increasing, so the
chosen zeros are strictly increasing. The statement has the shape of `TwentyNineZerosOnLine`
(`RHHeight100/Skeleton100.lean`). It asserts at least these twenty-nine zeros, nothing about others.
-/

open Complex

namespace RHHeight100

theorem twenty_nine_zeros_on_line_below_hundred :
    ∃ ts : Fin 29 → ℝ, StrictMono ts ∧
      ∀ k, 0 < ts k ∧ ts k < 100 ∧ riemannZeta (1 / 2 + ts k * I) = 0 := by
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
  obtain ⟨t10, h10, z10⟩ := zero_in_5297
  obtain ⟨t11, h11, z11⟩ := zero_in_5644
  obtain ⟨t12, h12, z12⟩ := zero_in_5934
  obtain ⟨t13, h13, z13⟩ := zero_in_6083
  obtain ⟨t14, h14, z14⟩ := zero_in_6511
  obtain ⟨t15, h15, z15⟩ := zero_in_67075
  obtain ⟨t16, h16, z16⟩ := zero_in_6954
  obtain ⟨t17, h17, z17⟩ := zero_in_7206
  obtain ⟨t18, h18, z18⟩ := zero_in_7570
  obtain ⟨t19, h19, z19⟩ := zero_in_7714
  obtain ⟨t20, h20, z20⟩ := zero_in_7933
  obtain ⟨t21, h21, z21⟩ := zero_in_8291
  obtain ⟨t22, h22, z22⟩ := zero_in_8473
  obtain ⟨t23, h23, z23⟩ := zero_in_8742
  obtain ⟨t24, h24, z24⟩ := zero_in_8880
  obtain ⟨t25, h25, z25⟩ := zero_in_9249
  obtain ⟨t26, h26, z26⟩ := zero_in_9465
  obtain ⟨t27, h27, z27⟩ := zero_in_95865
  obtain ⟨t28, h28, z28⟩ := zero_in_9883
  obtain ⟨l0, u0⟩ := h0
  obtain ⟨l1, u1⟩ := h1
  obtain ⟨l2, u2⟩ := h2
  obtain ⟨l3, u3⟩ := h3
  obtain ⟨l4, u4⟩ := h4
  obtain ⟨l5, u5⟩ := h5
  obtain ⟨l6, u6⟩ := h6
  obtain ⟨l7, u7⟩ := h7
  obtain ⟨l8, u8⟩ := h8
  obtain ⟨l9, u9⟩ := h9
  obtain ⟨l10, u10⟩ := h10
  obtain ⟨l11, u11⟩ := h11
  obtain ⟨l12, u12⟩ := h12
  obtain ⟨l13, u13⟩ := h13
  obtain ⟨l14, u14⟩ := h14
  obtain ⟨l15, u15⟩ := h15
  obtain ⟨l16, u16⟩ := h16
  obtain ⟨l17, u17⟩ := h17
  obtain ⟨l18, u18⟩ := h18
  obtain ⟨l19, u19⟩ := h19
  obtain ⟨l20, u20⟩ := h20
  obtain ⟨l21, u21⟩ := h21
  obtain ⟨l22, u22⟩ := h22
  obtain ⟨l23, u23⟩ := h23
  obtain ⟨l24, u24⟩ := h24
  obtain ⟨l25, u25⟩ := h25
  obtain ⟨l26, u26⟩ := h26
  obtain ⟨l27, u27⟩ := h27
  obtain ⟨l28, u28⟩ := h28
  refine ⟨![t0, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15, t16, t17, t18, t19, t20, t21, t22, t23, t24, t25, t26, t27, t28], ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> dsimp <;> first
      | linarith only [u0, l1]
      | linarith only [u1, l2]
      | linarith only [u2, l3]
      | linarith only [u3, l4]
      | linarith only [u4, l5]
      | linarith only [u5, l6]
      | linarith only [u6, l7]
      | linarith only [u7, l8]
      | linarith only [u8, l9]
      | linarith only [u9, l10]
      | linarith only [u10, l11]
      | linarith only [u11, l12]
      | linarith only [u12, l13]
      | linarith only [u13, l14]
      | linarith only [u14, l15]
      | linarith only [u15, l16]
      | linarith only [u16, l17]
      | linarith only [u17, l18]
      | linarith only [u18, l19]
      | linarith only [u19, l20]
      | linarith only [u20, l21]
      | linarith only [u21, l22]
      | linarith only [u22, l23]
      | linarith only [u23, l24]
      | linarith only [u24, l25]
      | linarith only [u25, l26]
      | linarith only [u26, l27]
      | linarith only [u27, l28]
  · intro k
    fin_cases k <;> dsimp <;> first
      | exact ⟨by linarith only [l0], by linarith only [u0], z0⟩
      | exact ⟨by linarith only [l1], by linarith only [u1], z1⟩
      | exact ⟨by linarith only [l2], by linarith only [u2], z2⟩
      | exact ⟨by linarith only [l3], by linarith only [u3], z3⟩
      | exact ⟨by linarith only [l4], by linarith only [u4], z4⟩
      | exact ⟨by linarith only [l5], by linarith only [u5], z5⟩
      | exact ⟨by linarith only [l6], by linarith only [u6], z6⟩
      | exact ⟨by linarith only [l7], by linarith only [u7], z7⟩
      | exact ⟨by linarith only [l8], by linarith only [u8], z8⟩
      | exact ⟨by linarith only [l9], by linarith only [u9], z9⟩
      | exact ⟨by linarith only [l10], by linarith only [u10], z10⟩
      | exact ⟨by linarith only [l11], by linarith only [u11], z11⟩
      | exact ⟨by linarith only [l12], by linarith only [u12], z12⟩
      | exact ⟨by linarith only [l13], by linarith only [u13], z13⟩
      | exact ⟨by linarith only [l14], by linarith only [u14], z14⟩
      | exact ⟨by linarith only [l15], by linarith only [u15], z15⟩
      | exact ⟨by linarith only [l16], by linarith only [u16], z16⟩
      | exact ⟨by linarith only [l17], by linarith only [u17], z17⟩
      | exact ⟨by linarith only [l18], by linarith only [u18], z18⟩
      | exact ⟨by linarith only [l19], by linarith only [u19], z19⟩
      | exact ⟨by linarith only [l20], by linarith only [u20], z20⟩
      | exact ⟨by linarith only [l21], by linarith only [u21], z21⟩
      | exact ⟨by linarith only [l22], by linarith only [u22], z22⟩
      | exact ⟨by linarith only [l23], by linarith only [u23], z23⟩
      | exact ⟨by linarith only [l24], by linarith only [u24], z24⟩
      | exact ⟨by linarith only [l25], by linarith only [u25], z25⟩
      | exact ⟨by linarith only [l26], by linarith only [u26], z26⟩
      | exact ⟨by linarith only [l27], by linarith only [u27], z27⟩
      | exact ⟨by linarith only [l28], by linarith only [u28], z28⟩

end RHHeight100
