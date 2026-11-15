module

public import HardyTenZeros.TenSupport

/-!
# Support for zeros on the line below height 100: the phase lemma and the assembly

Hunt #133's `HardyTenZeros.gammaR_re_pos_short` covers short brackets below height 50
with `m = 8` and `L = 1/5`. Below height 100 the Gamma-side window's lower end, with the
same crude constants (`log π ≥ 0`, `log 8 ≤ 7`, `ab/4 ≤ 2500`, half-width `≤ 1/200`), is
about `-0.2355`, past `-1/5`; `L = 3/10` covers it, and `3/10 < π/2`. The upper end is
below `0.04`. The proof is hunt #133's with those two constants changed.

`zero_of_tables100` is hunt #133's `zero_of_tables` with `b ≤ 100` and this phase lemma;
every other ingredient (the order-4 remainder, the main-term boxes, the sign data) holds at
every height and is reused unchanged.
-/

@[expose] public section

open Complex Finset ZetaLean ZetaLean.ComplexInterval HardyFirstZero HardyTenZeros
open scoped ComplexConjugate

namespace RHHeight100

/-- **The phase lemma for every short bracket below height 100**: `0 ≤ a ≤ b ≤ 100` and
`b - a ≤ 1/100`, with `m = 8` and `L = 3/10`. -/
theorem gammaR_re_pos_short100 {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hw : b - a ≤ 1 / 100)
    (hb : b ≤ 100) :
    0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re := by
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hlogpi' : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpi3 : 3 < Real.pi := Real.pi_gt_three
  have hlog8 : Real.log ((8 : ℕ) : ℝ) ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((8 : ℕ) : ℝ) by norm_num)
    norm_num at this ⊢; linarith
  have hd0 : 0 ≤ dl a b := by unfold dl; linarith
  have hd : dl a b ≤ 1 / 200 := by unfold dl; linarith
  have hK0 : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  have hK : a * b / 4 ≤ 2500 := by nlinarith
  have hD : ((8 : ℕ) : ℝ) ^ 2 - 1 / 16 = 1023 / 16 := by norm_num
  have hdK : dl a b * (a * b / 4) ≤ 1 / 200 * 2500 := mul_le_mul hd hK hK0 (by norm_num)
  have hd3 : dl a b ^ 3 ≤ (1 / 200) ^ 3 := pow_le_pow_left₀ hd0 hd 3
  have hdl : dl a b * Real.log ((8 : ℕ) : ℝ) ≤ 1 / 200 * 7 :=
    mul_le_mul hd hlog8 (Real.log_nonneg (by norm_num)) (by norm_num)
  have hdpi : 0 ≤ dl a b * Real.log Real.pi := mul_nonneg hd0 hlogpi
  have hdpi' : dl a b * Real.log Real.pi ≤ 1 / 200 * 3 :=
    mul_le_mul hd (by linarith) hlogpi (by norm_num)
  refine gammaR_re_pos_tail (L := 3 / 10) (m := 8) ha hab (by norm_num) (by linarith) ?_ ?_
  · nlinarith
  · rw [hD]
    have e : dl a b * (Real.log Real.pi - 1 - Real.log ((8 : ℕ) : ℝ) - a * b / 4 / (1023 / 16))
        - dl a b ^ 3 / (1023 / 16)
        = dl a b * Real.log Real.pi - dl a b - dl a b * Real.log ((8 : ℕ) : ℝ)
          - dl a b * (a * b / 4) * (16 / 1023) - dl a b ^ 3 * (16 / 1023) := by ring
    rw [e]
    nlinarith

open HardyTenZeros in
/-- **One interval below height 100, from its two tables.** Hunt #133's `zero_of_tables`
with `b ≤ 100`. -/
theorem zero_of_tables100 {a b : ℚ} (ha : 0 < a) (hab : a < b) (hw : b - a ≤ 1 / 100)
    (hb : b ≤ 100) {Na Nb : ℕ} (hNa : 2 ≤ Na) (hNb : 2 ≤ Nb) {TA TB : ℕ → ComplexInterval}
    (hTA : ∀ m < Na + 1, (TA m).contains ((m : ℂ) ^ (-sOf (a : ℝ))))
    (hTB : ∀ m < Nb + 1, (TB m).contains ((m : ℂ) ^ (-sOf (b : ℝ))))
    {ra Ra ea rb Rb eb : ℚ}
    (hra : 0 < ra) (hra2 : ra ^ 2 ≤ Na - 1) (hRa0 : 0 ≤ Ra) (hRa : q4Q a ≤ Ra ^ 2)
    (hea : Ra / (((Na : ℚ) - 1) ^ 3 * ra * (7 / 2) * 720) ≤ ea)
    (hrb : 0 < rb) (hrb2 : rb ^ 2 ≤ Nb - 1) (hRb0 : 0 ≤ Rb) (hRb : q4Q b ≤ Rb ^ 2)
    (heb : Rb / (((Nb : ℚ) - 1) ^ 3 * rb * (7 / 2) * 720) ≤ eb)
    (hneg : prodHi ((mainBox TA Na a).inflate ea) ((mainBox TB Nb b).inflate eb) < 0) :
    ∃ t ∈ Set.Ioo (a : ℝ) b, riemannZeta (1 / 2 + t * I) = 0 := by
  have hA := zeta_mem_mainBox ha hNa hTA hra hra2 hRa0 hRa hea
  have hB := zeta_mem_mainBox (ha.trans hab) hNb hTB hrb hrb2 hRb0 hRb heb
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hab' : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hw' : (b : ℝ) - a ≤ 1 / 100 := by
    have h1 := (Rat.cast_le (K := ℝ)).mpr hw
    push_cast at h1
    exact h1
  have hb' : (b : ℝ) ≤ 100 := by exact_mod_cast hb
  refine exists_zero_of_sign_data hab' ?_ (gammaR_re_pos_short100 ha' hab'.le hw' hb')
  set z := riemannZeta (sOf (a : ℝ))
  set w := riemannZeta (sOf (b : ℝ))
  have hre : (z * conj w).re = z.re * w.re + z.im * w.im := by
    simp [Complex.mul_re]
  have hc := Interval.contains_add (Interval.contains_mul hA.1 hB.1)
    (Interval.contains_mul hA.2 hB.2)
  rw [hre]
  have hneg' : (prodHi ((mainBox TA Na a).inflate ea) ((mainBox TB Nb b).inflate eb) : ℝ) < 0 := by
    exact_mod_cast hneg
  exact lt_of_le_of_lt hc.2 hneg'

end RHHeight100
