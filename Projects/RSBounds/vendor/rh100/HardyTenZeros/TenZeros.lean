module

public import HardyFirstZero.FirstZero
public import HardyTenZeros.Box2102
public import HardyTenZeros.Box2501
public import HardyTenZeros.Box3042
public import HardyTenZeros.Box3293
public import HardyTenZeros.Box3758
public import HardyTenZeros.Box4091
public import HardyTenZeros.Box4332
public import HardyTenZeros.Box4800
public import HardyTenZeros.Box4977

@[expose] public section

/-!
# At least ten zeros of zeta on the critical line below height 50 (hunt `hardy_ten_zeros`)

Ten disjoint two-decimal intervals, each holding a zero `1/2 + it` of `riemannZeta`:
`(14.13, 14.14)` from hunt #132 (`HardyFirstZero.first_zero_on_line`) and the nine
`zero_in_*` theorems of the generated `Box*.lean` files. Since the intervals are disjoint
and ordered, choosing one zero from each gives ten distinct ordinates in increasing order.

**What this does not say.** Nothing here says these are the ten lowest zeros, that an
interval holds exactly one zero, or that there are no other zeros below height 50: that
needs a zero count (Turing's method, for example), which is not attempted. Nothing here
bears on RH (`docs/08`).
-/

open Complex

namespace HardyTenZeros

/-- **At least ten zeros on the critical line below height 50**: ten distinct ordinates
`0 < t_0 < t_1 < ⋯ < t_9 < 50` with `ζ(1/2 + i t_k) = 0`. Each `t_k` lies in the two-decimal
interval of the corresponding `zero_in_*` theorem. -/
theorem ten_zeros_on_line_below_fifty :
    ∃ ts : Fin 10 → ℝ, StrictMono ts ∧
      ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * I) = 0 := by
  obtain ⟨t0, h0, z0⟩ := HardyFirstZero.first_zero_on_line
  obtain ⟨t1, h1, z1⟩ := zero_in_2102
  obtain ⟨t2, h2, z2⟩ := zero_in_2501
  obtain ⟨t3, h3, z3⟩ := zero_in_3042
  obtain ⟨t4, h4, z4⟩ := zero_in_3293
  obtain ⟨t5, h5, z5⟩ := zero_in_3758
  obtain ⟨t6, h6, z6⟩ := zero_in_4091
  obtain ⟨t7, h7, z7⟩ := zero_in_4332
  obtain ⟨t8, h8, z8⟩ := zero_in_4800
  obtain ⟨t9, h9, z9⟩ := zero_in_4977
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
  refine ⟨![t0, t1, t2, t3, t4, t5, t6, t7, t8, t9], ?_, ?_⟩
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simp <;> linarith
  · intro k
    simp only [one_div] at z0 z1 z2 z3 z4 z5 z6 z7 z8 z9
    fin_cases k <;> simp <;> refine ⟨by linarith, by linarith, by assumption⟩

end HardyTenZeros
