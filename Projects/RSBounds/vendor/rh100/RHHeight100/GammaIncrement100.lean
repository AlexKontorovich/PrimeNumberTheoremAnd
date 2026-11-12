module

public import RHHeight.GammaIncrement

@[expose] public section

/-!
# `gamma_increment100`: the Gamma side of hunt #137's count up to height 100, enclosed

The `(3, 100)` analogue of `RHHeight.gamma_increment`:

    281/10 ≤ ∫_3^100 μ ≤ 297/10,

with `μ = Zeta23.mu`. It reuses the general lemmas of `RHHeight.GammaSide`
(`abs_integral_mu_sub_le`, `log_one_sub_bounds`, `log_37_div_16_mem`, `log_pi_mem`, the bounds
on `π`) and adds only the `(3, 100)` constants: a rational enclosure of `log (40001/16)`, the
identity for `2π (F 100 - F 3)`, and the final assembly.

Measured (mpmath, one route): `F 100 - F 3 = 28.938695`, Stirling error
`(6/π)(1/3 - 1/100) = 0.617521`, so step 3 of the template confines the integral to
`[28.3212, 29.5562]`. With `arctan 200 - arctan 6` taken anywhere in `[0, π/2]` the provable
range is slightly wider; the stated `[28.1, 29.7]` leaves margin on both sides.
`log (40001/16)` is measured `7.824071`.
-/

noncomputable section

namespace RHHeight100

namespace GammaSide100

open RHHeight RHHeight.GammaSide

/-- `log(40001/16) = 11 log 2 + log(40001/32768)`, measured `7.824071`. -/
theorem log_40001_div_16_mem :
    (78240 / 10000 : ℝ) ≤ Real.log (40001 / 16) ∧ Real.log (40001 / 16) ≤ 78242 / 10000 := by
  have hsplit : Real.log (40001 / 16) = 11 * Real.log 2 + Real.log (40001 / 32768) := by
    rw [show (40001 / 16 : ℝ) = 2 ^ 11 * (40001 / 32768) by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have hx : |(-7233 / 32768 : ℝ)| = 7233 / 32768 := by
    rw [abs_of_neg (by norm_num)]; norm_num
  obtain ⟨hlo, hhi⟩ := log_one_sub_bounds (x := -7233 / 32768) (by rw [hx]; norm_num) 12
  rw [hx, show (1 : ℝ) - -7233 / 32768 = 40001 / 32768 by norm_num] at hlo hhi
  norm_num [Finset.sum_range_succ] at hlo hhi
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  rw [hsplit]
  constructor <;> linarith

/-- `F` at the two heights `3` and `100`. -/
theorem two_pi_mul_muPrim_sub100 :
    2 * Real.pi * (muPrim 100 - muPrim 3)
      = 50 * Real.log (40001 / 16) - 3 / 2 * Real.log (37 / 16) - 97
        - (1 / 2) * (Real.arctan 200 - Real.arctan 6) - 97 * Real.log Real.pi := by
  have hπ := Real.pi_pos
  unfold muPrim
  rw [show (1 + 4 * (100 : ℝ) ^ 2) / 16 = 40001 / 16 by norm_num,
    show (2 : ℝ) * 100 = 200 by norm_num, show (1 + 4 * (3 : ℝ) ^ 2) / 16 = 37 / 16 by norm_num,
    show (2 : ℝ) * 3 = 6 by norm_num]
  field_simp
  ring

end GammaSide100

open RHHeight RHHeight.GammaSide GammaSide100

/-- **`gamma_increment100`.** `281/10 ≤ ∫_3^100 μ ≤ 297/10`. -/
theorem gamma_increment100 :
    (281 / 10 : ℝ) ≤ ∫ t in (3 : ℝ)..100, Zeta23.mu t ∧
      ∫ t in (3 : ℝ)..100, Zeta23.mu t ≤ 297 / 10 := by
  have hπ := Real.pi_pos
  obtain ⟨hlo, hhi⟩ := abs_le.mp (abs_integral_mu_sub_le (T₁ := 3) (T₂ := 100)
    (by norm_num) (by norm_num))
  have hF := two_pi_mul_muPrim_sub100
  have herr : 6 / Real.pi * (1 / 3 - 1 / 100) = 97 / 25 / (2 * Real.pi) := by
    field_simp
    ring
  obtain ⟨ha1, ha2⟩ := log_40001_div_16_mem
  obtain ⟨hb1, hb2⟩ := log_37_div_16_mem
  obtain ⟨hc1, hc2⟩ := log_pi_mem
  have hA : Real.arctan 200 < Real.pi / 2 := Real.arctan_lt_pi_div_two 200
  have hB : 0 < Real.arctan 6 := Real.arctan_pos.mpr (by norm_num)
  have hAB : Real.arctan 6 ≤ Real.arctan 200 := Real.arctan_strictMono.monotone (by norm_num)
  have hp1 := pi_gt_6283_div_2000
  have hp2 := pi_lt_3927_div_1250
  set G := ∫ t in (3 : ℝ)..100, Zeta23.mu t
  have hGlo : (2 * Real.pi * (muPrim 100 - muPrim 3) - 97 / 25) / (2 * Real.pi) ≤ G := by
    have h : (2 * Real.pi * (muPrim 100 - muPrim 3) - 97 / 25) / (2 * Real.pi)
        = (muPrim 100 - muPrim 3) - 97 / 25 / (2 * Real.pi) := by
      field_simp
    rw [h, ← herr]
    linarith
  have hGhi : G ≤ (2 * Real.pi * (muPrim 100 - muPrim 3) + 97 / 25) / (2 * Real.pi) := by
    have h : (2 * Real.pi * (muPrim 100 - muPrim 3) + 97 / 25) / (2 * Real.pi)
        = (muPrim 100 - muPrim 3) + 97 / 25 / (2 * Real.pi) := by
      field_simp
    rw [h, ← herr]
    linarith
  rw [hF] at hGlo hGhi
  constructor
  · refine le_trans ?_ hGlo
    rw [le_div_iff₀ (by positivity)]
    linarith
  · refine le_trans hGhi ?_
    rw [div_le_iff₀ (by positivity)]
    linarith

end RHHeight100
