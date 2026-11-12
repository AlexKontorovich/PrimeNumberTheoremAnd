import RSBounds.RS75ZeroFreeScalars

/-! Exact optimization algebra following the closed scalar certificates.
This module does not assert the needed logarithmic-derivative inequality. -/
namespace TernaryGoldbach.RSBounds.RS75ZeroFreeScalars

theorem one_sub_k0_pos : 0 < 1 - k0 := by
  have hr : (1 : ℝ) < Real.sqrt 5 := by linarith [RS75Parameters.sqrt_five_bounds.1]
  have hp : (0 : ℝ) < Real.sqrt 5 := by positivity
  unfold k0
  exact sub_pos.2 ((div_lt_one hp).2 hr)

theorem h_pos : 0 < h := by
  unfold h
  exact div_pos (mul_pos one_sub_k0_pos A0_pos) (by norm_num)

theorem R1_pos : 0 < R1 := by linarith [R1_lower]

theorem sqrt_gap_pos : 0 < Real.sqrt a1 - Real.sqrt a0 :=
  sub_pos.2 (Real.sqrt_lt_sqrt a0_pos.le (by norm_num [a0, a1]))

theorem h_mul_v : h * v = Real.sqrt a0 * (Real.sqrt a1 - Real.sqrt a0) := by
  unfold h v
  field_simp [one_sub_k0_pos.ne', A0_pos.ne']
  <;> ring

theorem v_mul_R1 : v * R1 = Real.sqrt a0 / (Real.sqrt a1 - Real.sqrt a0) := by
  unfold v R1
  field_simp [one_sub_k0_pos.ne', A0_pos.ne', sqrt_gap_pos.ne']
  <;> ring

/-- The exact identity behind the optimal choice of v; no rounded parameters. -/
theorem optimal_identity : (a0 / v + h) * (v + 1 / R1) = a1 := by
  have hs0 : 0 < Real.sqrt a0 := Real.sqrt_pos.2 a0_pos
  have ha0 := Real.sq_sqrt a0_pos.le
  have ha1 := Real.sq_sqrt (show 0 ≤ a1 by norm_num [a1])
  have hd := (eq_div_iff sqrt_gap_pos.ne').1 v_mul_R1
  have hr : Real.sqrt a0 / R1 = v * (Real.sqrt a1 - Real.sqrt a0) := by
    apply (div_eq_iff R1_pos.ne').2
    calc
      _ = (v * R1) * (Real.sqrt a1 - Real.sqrt a0) := hd.symm
      _ = _ := by ring
  have hc : (a0 / v + h) * v = Real.sqrt a0 * Real.sqrt a1 := by
    rw [add_mul, div_mul_cancel₀ _ v_pos.ne', h_mul_v]
    nlinarith
  have hb : (v + 1 / R1) * Real.sqrt a0 = v * Real.sqrt a1 := by
    calc
      _ = v * Real.sqrt a0 + Real.sqrt a0 / R1 := by ring
      _ = v * Real.sqrt a0 + v * (Real.sqrt a1 - Real.sqrt a0) := by rw [hr]
      _ = _ := by ring
  apply mul_right_cancel₀ (mul_ne_zero v_pos.ne' hs0.ne')
  calc
    _ = ((a0 / v + h) * v) * ((v + 1 / R1) * Real.sqrt a0) := by ring
    _ = (Real.sqrt a0 * Real.sqrt a1) * (v * Real.sqrt a1) := by rw [hc, hb]
    _ = (v * Real.sqrt a0) * (Real.sqrt a1) ^ 2 := by ring
    _ = _ := by rw [ha1]; ring

/-- Convert the optimized scalar inequality into the strict R1 boundary. -/
theorem beta_lt_of_optimized_inequality {w β : ℝ} (hw : 0 < w) (hβ : β ≤ 1)
    (hineq : a1 / (1 + v / w - β) < (a0 / v + h) * w) :
    β < 1 - 1 / (R1 * w) := by
  have hd : 0 < 1 + v / w - β := by have hh := div_pos v_pos hw; linarith
  have hc : 0 < a0 / v + h := add_pos (div_pos a0_pos v_pos) h_pos
  have ha := (div_lt_iff₀ hd).1 hineq
  rw [← optimal_identity] at ha
  have hb : v + 1 / R1 < w * (1 + v / w - β) := by
    apply (mul_lt_mul_iff_right₀ hc).1
    convert ha using 1 <;> ring
  have hv : w * (v / w) = v := by field_simp [hw.ne']
  have hh : (1 / R1) / w < 1 - β := by
    apply (div_lt_iff₀ hw).2
    nlinarith
  have he : (1 / R1) / w = 1 / (R1 * w) := by field_simp [R1_pos.ne', hw.ne']
    <;> ring
  rw [he] at hh
  linarith

end TernaryGoldbach.RSBounds.RS75ZeroFreeScalars
