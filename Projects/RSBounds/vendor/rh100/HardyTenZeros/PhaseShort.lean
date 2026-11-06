module

public import HardyFirstZero.Phase

@[expose] public section

/-!
# The phase of `Γℝ` turns slowly, at every height below 50 (hunt `hardy_ten_zeros`)

`HardyFirstZero/Phase.lean` proves `0 < Re (Γℝ(1/2 + ia) · conj Γℝ(1/2 + ib))` from a
window on the partial phases

    φ_n = δ log π - δ log n + Σ_{j ≤ n} arctan(δ c_j / (c_j² + K)),
    δ = (b - a)/2,  K = ab/4,  c_j = j + 1/4,

whose lower end `δ (log π - 1 - 2K) - 66 δ³` grows with `K`: at a two-decimal bracket
(`δ = 1/200`) it leaves the quarter turn once `K > 157.2`, above `t ≈ 25.1`.
The loss is in the first terms, where `c_j² < K` and the bound
`c_j / (c_j² + K) ≥ 1/c_j - K/c_j³` is useless. This file drops them: the arctangents are
nonnegative, so for `n ≥ m ≥ 1`

    φ_n ≥ δ (log π - 1 - log m - K/(m² - 1/16)) - δ³/(m² - 1/16)

(`le_phi_tail`), from `Σ_{j=m}^{n} 1/c_j ≥ log n - 1 - log m` (harmonic bounds) and the
telescoping `Σ_{j ≥ m} 1/c_j³ ≤ 1/(m² - 1/16)`. The window no longer grows with the
height once `m² ≳ K`. `gammaR_re_pos_tail` is the phase lemma with this lower end, and
`gammaR_re_pos_short` instantiates it once for every bracket of width at most `1/100`
below height 50 (`m = 8`, `L = 1/5`); the true increments at the ten brackets are below `0.0104`.
-/

open Complex Finset Filter HardyFirstZero
open scoped ComplexConjugate Topology

namespace HardyTenZeros

/-- `1/c_j² ≤ 1/(j - 1/4) - 1/(j + 3/4)` for `j ≥ 1`. -/
lemma inv_cj_sq_le {j : ℕ} (hj : 1 ≤ j) :
    1 / cj j ^ 2 ≤ 1 / ((j : ℝ) - 1 / 4) - 1 / ((j : ℝ) + 3 / 4) := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : (0 : ℝ) < (j : ℝ) - 1 / 4 := by linarith
  have h2 : (0 : ℝ) < (j : ℝ) + 3 / 4 := by linarith
  have hc : 0 < cj j := cj_pos j
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  unfold cj
  nlinarith

/-- The telescoping bound `Σ_{i<r} 1/c_{m+i}² ≤ 1/(m - 1/4)`. -/
lemma sum_inv_cj_sq_tail_le {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∑ i ∈ range r, 1 / cj (m + i) ^ 2 ≤ 1 / ((m : ℝ) - 1 / 4) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set f : ℕ → ℝ := fun i => 1 / ((m : ℝ) + i - 1 / 4) with hf
  have hstep : ∀ i ∈ range r, 1 / cj (m + i) ^ 2 ≤ f i - f (i + 1) := by
    intro i _
    have h := inv_cj_sq_le (j := m + i) (by omega)
    simp only [hf]
    push_cast at h ⊢
    have e1 : (m : ℝ) + i - 1 / 4 = ((m : ℝ) + i) - 1 / 4 := by ring
    have e2 : (m : ℝ) + (i + 1) - 1 / 4 = ((m : ℝ) + i) + 3 / 4 := by ring
    rw [e1, e2]
    exact h
  have hfr : 0 ≤ f r := by
    simp only [hf]
    apply div_nonneg zero_le_one
    have := (Nat.cast_nonneg r : (0 : ℝ) ≤ r)
    linarith
  calc ∑ i ∈ range r, 1 / cj (m + i) ^ 2 ≤ ∑ i ∈ range r, (f i - f (i + 1)) :=
        Finset.sum_le_sum hstep
    _ = f 0 - f r := Finset.sum_range_sub' f r
    _ ≤ f 0 := by linarith
    _ = 1 / ((m : ℝ) - 1 / 4) := by simp [hf]

/-- `Σ_{i<r} 1/c_{m+i}³ ≤ 1/(m² - 1/16)`. -/
lemma sum_inv_cj_cube_tail_le {m : ℕ} (hm : 1 ≤ m) (r : ℕ) :
    ∑ i ∈ range r, 1 / cj (m + i) ^ 3 ≤ 1 / ((m : ℝ) ^ 2 - 1 / 16) := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hcm : 0 < cj m := cj_pos m
  have hterm : ∀ i ∈ range r, 1 / cj (m + i) ^ 3 ≤ (1 / cj m) * (1 / cj (m + i) ^ 2) := by
    intro i _
    have hci : 0 < cj (m + i) := cj_pos (m + i)
    have hc : cj m ≤ cj (m + i) := by
      unfold cj; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have h1 : 1 / cj (m + i) ≤ 1 / cj m := one_div_le_one_div_of_le hcm hc
    calc 1 / cj (m + i) ^ 3 = (1 / cj (m + i)) * (1 / cj (m + i) ^ 2) := by
          field_simp
      _ ≤ (1 / cj m) * (1 / cj (m + i) ^ 2) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
  calc ∑ i ∈ range r, 1 / cj (m + i) ^ 3
      ≤ ∑ i ∈ range r, (1 / cj m) * (1 / cj (m + i) ^ 2) := Finset.sum_le_sum hterm
    _ = (1 / cj m) * ∑ i ∈ range r, 1 / cj (m + i) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / cj m) * (1 / ((m : ℝ) - 1 / 4)) :=
        mul_le_mul_of_nonneg_left (sum_inv_cj_sq_tail_le hm r) (by positivity)
    _ = 1 / ((m : ℝ) ^ 2 - 1 / 16) := by
        unfold cj
        rw [div_mul_div_comm, one_mul]
        congr 1
        ring

/-- `Σ_{i<r} 1/c_{m+i} ≥ log (m + r) - 1 - log m`. -/
lemma sum_inv_cj_tail_ge (m r : ℕ) :
    Real.log ((m : ℝ) + r) - 1 - Real.log m ≤ ∑ i ∈ range r, 1 / cj (m + i) := by
  have hterm : ∀ i ∈ range r, 1 / (((m + i : ℕ) : ℝ) + 1) ≤ 1 / cj (m + i) := by
    intro i _
    unfold cj
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hH : (harmonic (m + r) : ℝ) = harmonic m + ∑ i ∈ range r, 1 / (((m + i : ℕ) : ℝ) + 1) := by
    simp only [harmonic, Finset.sum_range_add, Rat.cast_add, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    push_cast
    simp only [one_div]
  have hlo := log_add_one_le_harmonic (m + r)
  have hup := harmonic_le_one_add_log m
  have hmono : Real.log ((m : ℝ) + r) ≤ Real.log (((m + r + 1 : ℕ) : ℝ)) := by
    rcases Nat.eq_zero_or_pos (m + r) with h0 | hpos
    · have hm0 : m = 0 := by omega
      have hr0 : r = 0 := by omega
      subst hm0; subst hr0
      simp
    · apply Real.log_le_log (by exact_mod_cast hpos)
      push_cast
      linarith
  have := Finset.sum_le_sum hterm
  push_cast at hlo hmono
  linarith

/-- **The lower end of the window, without the growth in `K`**: for `1 ≤ m ≤ n`,
`φ_n ≥ δ (log π - 1 - log m - K/(m² - 1/16)) - δ³/(m² - 1/16)`. -/
lemma le_phi_tail {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    dl a b * (Real.log Real.pi - 1 - Real.log m - (a * b / 4) / ((m : ℝ) ^ 2 - 1 / 16))
      - dl a b ^ 3 / ((m : ℝ) ^ 2 - 1 / 16) ≤ phi a b n := by
  obtain ⟨r, hr⟩ : ∃ r, n + 1 = m + r := ⟨n + 1 - m, by omega⟩
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hK : 0 ≤ a * b / 4 := by have := mul_nonneg ha (ha.trans hab); linarith
  have hD : 0 < (m : ℝ) ^ 2 - 1 / 16 := by nlinarith
  -- the head of the sum is nonnegative
  have hsplit : ∑ j ∈ range (n + 1), psi a b j
      = ∑ j ∈ range m, psi a b j + ∑ i ∈ range r, psi a b (m + i) := by
    rw [hr, Finset.sum_range_add]
  have hhead : 0 ≤ ∑ j ∈ range m, psi a b j :=
    Finset.sum_nonneg fun j _ => Real.arctan_nonneg.mpr (xj_nonneg ha hab j)
  -- the tail: arctangents against the linear terms, minus the cubes
  have h1 : ∑ i ∈ range r, (xj a b (m + i) - xj a b (m + i) ^ 3)
      ≤ ∑ i ∈ range r, psi a b (m + i) :=
    Finset.sum_le_sum fun i _ => psi_ge ha hab (m + i)
  rw [Finset.sum_sub_distrib] at h1
  -- the cubes
  have h2 : ∑ i ∈ range r, xj a b (m + i) ^ 3 ≤ dl a b ^ 3 * (1 / ((m : ℝ) ^ 2 - 1 / 16)) := by
    have hle : ∀ i ∈ range r, xj a b (m + i) ^ 3 ≤ dl a b ^ 3 * (1 / cj (m + i) ^ 3) := by
      intro i _
      have hx := xj_le ha hab (m + i)
      have hx0 := xj_nonneg ha hab (m + i)
      calc xj a b (m + i) ^ 3 ≤ (dl a b / cj (m + i)) ^ 3 := pow_le_pow_left₀ hx0 hx 3
        _ = dl a b ^ 3 * (1 / cj (m + i) ^ 3) := by rw [div_pow]; ring
    calc ∑ i ∈ range r, xj a b (m + i) ^ 3
        ≤ ∑ i ∈ range r, dl a b ^ 3 * (1 / cj (m + i) ^ 3) := Finset.sum_le_sum hle
      _ = dl a b ^ 3 * ∑ i ∈ range r, 1 / cj (m + i) ^ 3 := by rw [Finset.mul_sum]
      _ ≤ dl a b ^ 3 * (1 / ((m : ℝ) ^ 2 - 1 / 16)) :=
          mul_le_mul_of_nonneg_left (sum_inv_cj_cube_tail_le hm r) (pow_nonneg hd 3)
  -- the linear terms
  have h3 : ∑ i ∈ range r, dl a b * (1 / cj (m + i) - (a * b / 4) / cj (m + i) ^ 3)
      ≤ ∑ i ∈ range r, xj a b (m + i) :=
    Finset.sum_le_sum fun i _ => xj_ge ha hab (m + i)
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at h3
  have h4 : ∑ i ∈ range r, (a * b / 4) / cj (m + i) ^ 3
      ≤ (a * b / 4) * (1 / ((m : ℝ) ^ 2 - 1 / 16)) := by
    have : ∑ i ∈ range r, (a * b / 4) / cj (m + i) ^ 3
        = (a * b / 4) * ∑ i ∈ range r, 1 / cj (m + i) ^ 3 := by
      rw [Finset.mul_sum]; congr 1; funext i; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (sum_inv_cj_cube_tail_le hm r) hK
  have h5 := sum_inv_cj_tail_ge m r
  -- `log (m + r) = log (n + 1) ≥ log n`
  have hlogn : Real.log n ≤ Real.log ((m : ℝ) + r) := by
    have hmr : ((m : ℝ) + r) = ((n : ℝ) + 1) := by exact_mod_cast hr.symm
    rw [hmr]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp
    · exact Real.log_le_log (by exact_mod_cast hpos) (by linarith)
  have h6 : dl a b * (Real.log n - 1 - Real.log m - (a * b / 4) * (1 / ((m : ℝ) ^ 2 - 1 / 16)))
      ≤ dl a b * (∑ i ∈ range r, 1 / cj (m + i) - ∑ i ∈ range r, (a * b / 4) / cj (m + i) ^ 3) :=
    mul_le_mul_of_nonneg_left (by linarith) hd
  have e1 : (a * b / 4) / ((m : ℝ) ^ 2 - 1 / 16) = (a * b / 4) * (1 / ((m : ℝ) ^ 2 - 1 / 16)) := by
    ring
  have e2 : dl a b ^ 3 / ((m : ℝ) ^ 2 - 1 / 16) = dl a b ^ 3 * (1 / ((m : ℝ) ^ 2 - 1 / 16)) := by
    ring
  rw [e1, e2]
  unfold phi
  rw [hsplit]
  have e3 : dl a b * (Real.log Real.pi - 1 - Real.log m - (a * b / 4) * (1 / ((m : ℝ) ^ 2 - 1 / 16)))
      = dl a b * Real.log Real.pi - dl a b * Real.log n
        + dl a b * (Real.log n - 1 - Real.log m - (a * b / 4) * (1 / ((m : ℝ) ^ 2 - 1 / 16))) := by
    ring
  rw [e3]
  linarith

/-- **The phase lemma with the tail window.** If `[-L, L]`, `L < π/2`, holds the upper
end `δ (log π + 5)` and the lower end of `le_phi_tail` for some `m ≥ 1`, the product of
the two `Γℝ` values has positive real part. -/
theorem gammaR_re_pos_tail {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {L : ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hL : L < Real.pi / 2)
    (hup : dl a b * (Real.log Real.pi + 5) ≤ L)
    (hlo : -L ≤ dl a b * (Real.log Real.pi - 1 - Real.log m - (a * b / 4) / ((m : ℝ) ^ 2 - 1 / 16))
      - dl a b ^ 3 / ((m : ℝ) ^ 2 - 1 / 16)) :
    0 < (Gammaℝ (sOf a) * conj (Gammaℝ (sOf b))).re := by
  rw [gammaR_prod]
  set V := cpi a b * (Gamma (zA a) * Gamma (wB b)) with hVdef
  have hd : 0 ≤ dl a b := by unfold dl; linarith
  have hlogpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hL0 : 0 ≤ L := le_trans (mul_nonneg hd (by linarith)) hup
  have hcosL : 0 < Real.cos L :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hL⟩
  have hev : ∀ᶠ n in atTop, Real.cos L * ‖Vn a b n‖ ≤ (Vn a b n).re := by
    filter_upwards [eventually_ge_atTop m] with n hmn
    have hn0 : n ≠ 0 := by omega
    rw [Vn_re ha (ha.trans hab) hn0]
    have hphi : |phi a b n| ≤ L :=
      abs_le.mpr ⟨hlo.trans (le_phi_tail ha hab hm hmn), (phi_le ha hab n).trans hup⟩
    have hcos : Real.cos L ≤ Real.cos (phi a b n) := by
      rw [← Real.cos_abs (phi a b n)]
      exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
        (by linarith [Real.pi_pos]) hphi
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left hcos (norm_nonneg _)
  have hlim := tendsto_Vn a b
  have hre : Tendsto (fun n => (Vn a b n).re) atTop (𝓝 V.re) :=
    (Complex.continuous_re.tendsto _).comp hlim
  have hnorm : Tendsto (fun n => Real.cos L * ‖Vn a b n‖) atTop (𝓝 (Real.cos L * ‖V‖)) :=
    hlim.norm.const_mul _
  have hle : Real.cos L * ‖V‖ ≤ V.re := le_of_tendsto_of_tendsto hnorm hre hev
  have hV : V ≠ 0 := by
    refine mul_ne_zero (by unfold cpi; exact Complex.exp_ne_zero _) (mul_ne_zero ?_ ?_)
    · exact Gamma_ne_zero_of_re_pos (by rw [zA_re]; norm_num)
    · exact Gamma_ne_zero_of_re_pos (by rw [wB_re]; norm_num)
  have : 0 < Real.cos L * ‖V‖ := mul_pos hcosL (norm_pos_iff.mpr hV)
  linarith

/-- **The phase lemma for every short bracket below height 50**: `0 ≤ a ≤ b ≤ 50` and
`b - a ≤ 1/100`. With `m = 8` and `L = 1/5` the window is inside
`[-0.089, 0.04]` (`sizing.py`), against true increments below `0.0104` at the ten brackets. -/
theorem gammaR_re_pos_short {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hw : b - a ≤ 1 / 100)
    (hb : b ≤ 50) :
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
  have hK : a * b / 4 ≤ 625 := by nlinarith
  have hD : ((8 : ℕ) : ℝ) ^ 2 - 1 / 16 = 1023 / 16 := by norm_num
  have hdK : dl a b * (a * b / 4) ≤ 1 / 200 * 625 := mul_le_mul hd hK hK0 (by norm_num)
  have hd3 : dl a b ^ 3 ≤ (1 / 200) ^ 3 := pow_le_pow_left₀ hd0 hd 3
  have hdl : dl a b * Real.log ((8 : ℕ) : ℝ) ≤ 1 / 200 * 7 :=
    mul_le_mul hd hlog8 (Real.log_nonneg (by norm_num)) (by norm_num)
  have hdpi : 0 ≤ dl a b * Real.log Real.pi := mul_nonneg hd0 hlogpi
  have hdpi' : dl a b * Real.log Real.pi ≤ 1 / 200 * 3 :=
    mul_le_mul hd (by linarith) hlogpi (by norm_num)
  refine gammaR_re_pos_tail (L := 1 / 5) (m := 8) ha hab (by norm_num) (by linarith) ?_ ?_
  · nlinarith
  · rw [hD]
    have e : dl a b * (Real.log Real.pi - 1 - Real.log ((8 : ℕ) : ℝ) - a * b / 4 / (1023 / 16))
        - dl a b ^ 3 / (1023 / 16)
        = dl a b * Real.log Real.pi - dl a b - dl a b * Real.log ((8 : ℕ) : ℝ)
          - dl a b * (a * b / 4) * (16 / 1023) - dl a b ^ 3 * (16 / 1023) := by ring
    rw [e]
    nlinarith

/-- **Why the tail window is needed.** At the bracket `(49.77, 49.78)` the lower end of
hunt #132's window (`HardyFirstZero.le_phi`) is below `-π/2`, so the hypothesis `hlo` of
`HardyFirstZero.gammaR_re_pos` fails for every `L < π/2` there. -/
theorem window_132_fails_at_4977 :
    dl (4977 / 100) (4978 / 100) * (Real.log Real.pi - 1 - 2 * ((4977 / 100) * (4978 / 100) / 4))
      - 66 * dl (4977 / 100) (4978 / 100) ^ 3 < -(Real.pi / 2) := by
  have hlogpi' : Real.log Real.pi ≤ Real.pi - 1 := Real.log_le_sub_one_of_pos Real.pi_pos
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  unfold dl
  linarith

end HardyTenZeros
