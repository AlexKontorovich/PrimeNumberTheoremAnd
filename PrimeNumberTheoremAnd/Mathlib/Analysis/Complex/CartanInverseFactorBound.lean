import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.CartanBound
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.WeierstrassFactor

/-!
## Cartan/minimum-modulus: reusable pointwise inverse bounds for Weierstrass factors

This file bundles the two key pointwise estimates used in the Hadamard Cartan bounds:

- a **near regime** bound using `φ` and the general `log` lower bound for `weierstrassFactor`;
- a **far regime** bound when `‖u/a‖ ≤ 1/2` using the `-2‖z‖^{m+1}` bound.

Both are stated in a form convenient for intrinsic Hadamard factorization over `divisorZeroIndex₀`.
-/

noncomputable section

namespace Complex.Hadamard

open Complex Real

/-!
### Auxiliary: bound `max 1 (‖u/a‖^m)` by `1 + (r/‖a‖)^τ`

This is the small “exponent comparison” lemma that occurs everywhere in the near regime.
-/

lemma max_one_norm_div_pow_le_one_add_rpow
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r)
    (hmτ : (m : ℝ) ≤ τ) :
    max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ := by
  have hnorm : ‖u / a‖ = r / ‖a‖ := by
    simp [div_eq_mul_inv, hur, norm_inv]
  by_cases hx : ‖u / a‖ ≤ 1
  · have hpowm_le1 : ‖u / a‖ ^ m ≤ 1 := pow_le_one₀ (norm_nonneg (u / a)) hx
    have hr0 : 0 ≤ r := by simpa [hur] using (norm_nonneg u)
    have hbase : 0 ≤ r / ‖a‖ := div_nonneg hr0 (norm_nonneg a)
    have hnonneg : 0 ≤ (r / ‖a‖) ^ τ := Real.rpow_nonneg hbase τ
    have hle1 : (1 : ℝ) ≤ 1 + (r / ‖a‖) ^ τ := le_add_of_nonneg_right hnonneg
    have hle2 : ‖u / a‖ ^ m ≤ 1 + (r / ‖a‖) ^ τ := hpowm_le1.trans hle1
    exact (max_le_iff).2 ⟨hle1, hle2⟩
  · have hx1 : 1 < ‖u / a‖ := lt_of_not_ge hx
    have hpow :
        (‖u / a‖ : ℝ) ^ (m : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ :=
      Real.rpow_le_rpow_of_exponent_le (le_of_lt hx1) hmτ
    have hpow' : ‖u / a‖ ^ m ≤ (‖u / a‖ : ℝ) ^ τ := by
      simpa [Real.rpow_natCast] using hpow
    have hmax_add : max 1 (‖u / a‖ ^ m) ≤ 1 + ‖u / a‖ ^ m := by
      refine max_le (le_add_of_nonneg_right (by positivity)) (le_add_of_nonneg_left (by positivity))
    have : max 1 (‖u / a‖ ^ m) ≤ 1 + (‖u / a‖ : ℝ) ^ τ :=
      hmax_add.trans (by nlinarith [hpow'])
    -- rewrite `‖u/a‖` in terms of `r/‖a‖`
    simpa [hnorm, hur] using this

/-!
### Near regime: `‖(E_m(u/a))⁻¹‖` controlled by `φ(r/‖a‖)` plus an exponent term.
-/

lemma norm_inv_weierstrassFactor_le_exp_near
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0) (hr : r ≠ ‖a‖)
    (hmτ : (m : ℝ) ≤ τ) :
    ‖(weierstrassFactor m (u / a))⁻¹‖
      ≤ Real.exp (LogSingularity.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ)) := by
  -- bridge: `log ‖1 - u/a‖ ≥ -φ(r/‖a‖)`
  have hlog_one :
      Real.log ‖(1 : ℂ) - u / a‖ ≥ -LogSingularity.φ (r / ‖a‖) :=
    LogSingularity.log_norm_one_sub_div_ge_neg_phi (hur := hur) (ha := ha) (hr := hr)
  -- Weierstrass lower bound: `log ‖E_m(z)‖ ≥ log‖1-z‖ - m*max 1 ‖z‖^m`
  have hbase :=
    log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m := m) (z := (u / a))
  have hlogE :
      Real.log ‖weierstrassFactor m (u / a)‖
        ≥ -LogSingularity.φ (r / ‖a‖) - (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
    linarith [hbase, hlog_one]
  have hmax :
      max 1 (‖u / a‖ ^ m) ≤ 1 + (r / ‖a‖) ^ τ :=
    max_one_norm_div_pow_le_one_add_rpow (m := m) (τ := τ) (r := r) (u := u) (a := a) hur hmτ
  have hneglog :
      -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ LogSingularity.φ (r / ‖a‖) + (m : ℝ) * (1 + (r / ‖a‖) ^ τ) := by
    have : -Real.log ‖weierstrassFactor m (u / a)‖
        ≤ LogSingularity.φ (r / ‖a‖) + (m : ℝ) * max 1 (‖u / a‖ ^ m) := by
      linarith [hlogE]
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact this.trans (by nlinarith [mul_le_mul_of_nonneg_left hmax hm0])
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      -- `weierstrassFactor m z = 0 ↔ z = 1`
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff (m := m) (z := (u / a))).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      have : r = ‖a‖ := by simpa [this] using hur.symm
      exact (hr this).elim
    exact norm_pos_iff.2 this
  have hEq : ‖(weierstrassFactor m (u / a))⁻¹‖ = Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

/-!
### Far regime: if `‖u/a‖ ≤ 1/2` then `‖(E_m(u/a))⁻¹‖ ≤ exp(2*(r/‖a‖)^τ)`
-/

lemma norm_inv_weierstrassFactor_le_exp_far
    {m : ℕ} {τ r : ℝ} {u a : ℂ}
    (hur : ‖u‖ = r) (ha : a ≠ 0)
    (hz : ‖u / a‖ ≤ (1 / 2 : ℝ)) (hτ_le : τ ≤ (m + 1 : ℝ)) :
    ‖(weierstrassFactor m (u / a))⁻¹‖ ≤ Real.exp ((2 : ℝ) * (r / ‖a‖) ^ τ) := by
  by_cases hu : u = 0
  · subst hu
    have hr0 : r = 0 := by simpa [hur] using (norm_zero : ‖(0 : ℂ)‖ = 0)
    subst hr0
    have h0 : 0 ≤ ((0 : ℝ) / ‖a‖) ^ τ := Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 0 / ‖a‖) τ
    have h0' : 0 ≤ (2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ := mul_nonneg (by norm_num) h0
    have hexp : (1 : ℝ) ≤ Real.exp ((2 : ℝ) * ((0 : ℝ) / ‖a‖) ^ τ) :=
      (Real.one_le_exp_iff).2 h0'
    simpa using hexp
  have hlogE := log_norm_weierstrassFactor_ge_neg_two_pow (m := m) (z := (u / a)) hz
  have hneglog : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * (r / ‖a‖) ^ τ := by
    have h1 : -Real.log ‖weierstrassFactor m (u / a)‖ ≤ (2 : ℝ) * ‖u / a‖ ^ (m + 1) := by
      linarith [hlogE]
    have hx1 : (‖u / a‖ : ℝ) ≤ 1 := le_trans hz (by norm_num)
    have hposx : 0 < (‖u / a‖ : ℝ) :=
      norm_pos_iff.2 (div_ne_zero hu ha)
    have hτ_le' : τ ≤ ((m + 1 : ℕ) : ℝ) := by
      simpa [Nat.cast_add, Nat.cast_one] using hτ_le
    have hpow_norm :
        (‖u / a‖ : ℝ) ^ ((m + 1 : ℕ) : ℝ) ≤ (‖u / a‖ : ℝ) ^ τ := by
      apply Real.rpow_le_rpow_of_exponent_ge hposx hx1
      exact hτ_le'
    have hpow' : ‖u / a‖ ^ (m + 1) ≤ (‖u / a‖ : ℝ) ^ τ := by
      have : (‖u / a‖ : ℝ) ^ (m + 1) = (‖u / a‖ : ℝ) ^ ((m + 1 : ℕ) : ℝ) := by
        rw [norm_div, hur]; rw [rpow_natCast]
      rw [this]
      exact hpow_norm
    have h2 : (2 : ℝ) * ‖u / a‖ ^ (m + 1) ≤ (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ :=
      mul_le_mul_of_nonneg_left hpow' (by norm_num)
    have h3 : (2 : ℝ) * (‖u / a‖ : ℝ) ^ τ = (2 : ℝ) * (r / ‖a‖) ^ τ := by
      simp [div_eq_mul_inv, hur, norm_inv, mul_comm]
    exact (h1.trans h2).trans_eq h3
  have hpos : 0 < ‖weierstrassFactor m (u / a)‖ := by
    have : weierstrassFactor m (u / a) ≠ 0 := by
      intro h0
      have : u / a = (1 : ℂ) := (weierstrassFactor_eq_zero_iff (m := m) (z := (u / a))).1 h0
      have : u = a := (div_eq_one_iff_eq ha).1 this
      -- then `‖u/a‖ = 1`, contradicting `‖u/a‖ ≤ 1/2`
      have : (‖u / a‖ : ℝ) = 1 := by simpa [this] using (by simp [ha])
      linarith [hz, this]
    exact norm_pos_iff.2 this
  have hEq : ‖(weierstrassFactor m (u / a))⁻¹‖ = Real.exp (-Real.log ‖weierstrassFactor m (u / a)‖) := by
    simp [norm_inv, Real.exp_neg, Real.exp_log hpos]
  have := Real.exp_le_exp.2 hneglog
  simpa [hEq] using this

end Complex.Hadamard
