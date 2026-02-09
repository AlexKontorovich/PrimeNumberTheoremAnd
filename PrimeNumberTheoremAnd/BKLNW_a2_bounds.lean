/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import LeanCert.Tactic.IntervalAuto
import LeanCert.Examples.BKLNW_a2_pow2
import LeanCert.Examples.BKLNW_a2_bounds
import PrimeNumberTheoremAnd.BKLNW

/-!
# BKLNW a₂ Glue Proofs (Corollary 5.1 Remark)

Connects `a₂(b) = (1+α) * max(f(exp b), f(2^(⌊b/log2⌋₊+1)))` to certified bounds.
Proves `cor_5_1_rem` from PrimeNumberTheoremAnd.BKLNW.

Uses:
- `f` and `a₂` from PrimeNumberTheoremAnd.BKLNW
- Numerical certificates from LeanCert.Examples.BKLNW_a2_bounds and LeanCert.Examples.BKLNW_a2_pow2
- `interval_decide` tactic from LeanCert
-/

open Real BKLNW

-- Note: Don't open LeanCert.Examples.BKLNW_a2_pow2 to avoid `f` ambiguity with BKLNW.f

-- Connect PNT+'s f with LeanCert's f (definitionally equal)
private lemma f_eq_leancert_f : BKLNW.f = LeanCert.Examples.BKLNW_a2_pow2.f := rfl

-- Convert rpow with negative nat exponent to division
private lemma rpow_neg_nat (n : ℕ) : (10:ℝ) ^ (-(↑n : ℝ)) = (1:ℝ) / 10 ^ n := by
  rw [rpow_neg (show (0:ℝ) ≤ 10 by positivity), rpow_natCast, one_div]

-- ═══════════════════════ α connection ═══════════════════════

private lemma alpha_eq : Inputs.default.α = 193571378 / (10:ℝ)^16 := by
  change 1.93378e-8 * BKLNW_app.table_8_margin = 193571378 / (10:ℝ)^16
  simp [BKLNW_app.table_8_margin]
  norm_num

-- ═══════════════════════ b = 20 ═══════════════════════
private lemma floor_20 : ⌊(20 : ℝ) / log 2⌋₊ = 28 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 20 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_20_exp_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_20_exp_lower

private lemma a2_20_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (20:ℝ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_20_exp_upper

private lemma cert_pow29_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(29:ℕ)) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow29_upper

private lemma a2_20_lower :
    (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_20]
  calc (1.4262 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 20) := a2_20_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(28+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_20_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1))) ≤ (1.4262 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_20]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_20_exp_upper
  · exact cert_pow29_upper

theorem a2_20_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 20)) (f ((2:ℝ)^(⌊(20:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.4262 : ℝ) ((1.4262 : ℝ) + (1:ℝ) / 10^4) := by
  constructor
  · exact a2_20_lower
  · exact a2_20_upper


-- ═══════════════════════ b = 25 ═══════════════════════
private lemma floor_25 : ⌊(25 : ℝ) / log 2⌋₊ = 36 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 25 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_25_exp_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_25_exp_lower

private lemma a2_25_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (25:ℝ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_25_exp_upper

private lemma cert_pow37_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(37:ℕ)) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow37_upper

private lemma a2_25_lower :
    (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_25]
  calc (1.2195 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 25) := a2_25_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(36+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_25_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1))) ≤ (1.2195 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_25]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_25_exp_upper
  · exact cert_pow37_upper

theorem a2_25_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 25)) (f ((2:ℝ)^(⌊(25:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.2195 : ℝ) ((1.2195 : ℝ) + (1:ℝ) / 10^4) := by
  constructor
  · exact a2_25_lower
  · exact a2_25_upper


-- ═══════════════════════ b = 30 ═══════════════════════
private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 30 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_30_exp_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_30_exp_lower

private lemma a2_30_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (30:ℝ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_30_exp_upper

private lemma cert_pow44_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(44:ℕ)) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow44_upper

private lemma a2_30_lower :
    (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_30]
  calc (1.1210 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 30) := a2_30_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(43+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_30_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1))) ≤ (1.1210 : ℝ) + (1:ℝ) / 10^4 := by
  rw [floor_30]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_30_exp_upper
  · exact cert_pow44_upper

theorem a2_30_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 30)) (f ((2:ℝ)^(⌊(30:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.1210 : ℝ) ((1.1210 : ℝ) + (1:ℝ) / 10^4) := by
  constructor
  · exact a2_30_lower
  · exact a2_30_upper


-- ═══════════════════════ b = 35 ═══════════════════════
private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 35 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_35_exp_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_35_exp_lower

private lemma a2_35_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (35:ℝ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_35_exp_upper

private lemma cert_pow51_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(51:ℕ)) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow51_upper

private lemma a2_35_lower :
    (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_35]
  calc (1.07086 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 35) := a2_35_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(50+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_35_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1))) ≤ (1.07086 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_35]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_35_exp_upper
  · exact cert_pow51_upper

theorem a2_35_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 35)) (f ((2:ℝ)^(⌊(35:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.07086 : ℝ) ((1.07086 : ℝ) + (1:ℝ) / 10^5) := by
  constructor
  · exact a2_35_lower
  · exact a2_35_upper


-- ═══════════════════════ b = 40 ═══════════════════════
private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 40 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_40_exp_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_40_exp_lower

private lemma a2_40_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (40:ℝ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_40_exp_upper

private lemma cert_pow58_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(58:ℕ)) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow58_upper

private lemma a2_40_lower :
    (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_40]
  calc (1.04319 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 40) := a2_40_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(57+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_40_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1))) ≤ (1.04319 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_40]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_40_exp_upper
  · exact cert_pow58_upper

theorem a2_40_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 40)) (f ((2:ℝ)^(⌊(40:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.04319 : ℝ) ((1.04319 : ℝ) + (1:ℝ) / 10^5) := by
  constructor
  · exact a2_40_lower
  · exact a2_40_upper


-- ═══════════════════════ b = 43 ═══════════════════════
private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 43 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_43_exp_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_43_exp_lower

private lemma a2_43_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (43:ℝ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_43_exp_upper

private lemma cert_pow63_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(63:ℕ)) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow63_upper

private lemma a2_43_lower :
    (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_43]
  calc (1.03252 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 43) := a2_43_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(62+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_43_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1))) ≤ (1.03252 : ℝ) + (1:ℝ) / 10^5 := by
  rw [floor_43]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_43_exp_upper
  · exact cert_pow63_upper

theorem a2_43_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 43)) (f ((2:ℝ)^(⌊(43:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.03252 : ℝ) ((1.03252 : ℝ) + (1:ℝ) / 10^5) := by
  constructor
  · exact a2_43_lower
  · exact a2_43_upper


-- ═══════════════════════ b = 100 ═══════════════════════
private lemma floor_100 : ⌊(100 : ℝ) / log 2⌋₊ = 144 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 100 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_100_exp_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_100_exp_lower

private lemma a2_100_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (100:ℝ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_100_exp_upper

private lemma cert_pow145_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(145:ℕ)) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow145_upper

private lemma a2_100_lower :
    (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_100]
  calc (1.0002420 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 100) := a2_100_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(144+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_100_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1))) ≤ (1.0002420 : ℝ) + (1:ℝ) / 10^7 := by
  rw [floor_100]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_100_exp_upper
  · exact cert_pow145_upper

theorem a2_100_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 100)) (f ((2:ℝ)^(⌊(100:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.0002420 : ℝ) ((1.0002420 : ℝ) + (1:ℝ) / 10^7) := by
  constructor
  · exact a2_100_lower
  · exact a2_100_upper


-- ═══════════════════════ b = 150 ═══════════════════════
private lemma floor_150 : ⌊(150 : ℝ) / log 2⌋₊ = 216 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 150 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_150_exp_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_150_exp_lower

private lemma a2_150_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (150:ℝ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_150_exp_upper

private lemma cert_pow217_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(217:ℕ)) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow217_upper

private lemma a2_150_lower :
    (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_150]
  calc (1.000003748 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 150) := a2_150_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(216+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_150_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1))) ≤ (1.000003748 : ℝ) + (1:ℝ) / 10^8 := by
  rw [floor_150]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_150_exp_upper
  · exact cert_pow217_upper

theorem a2_150_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 150)) (f ((2:ℝ)^(⌊(150:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.000003748 : ℝ) ((1.000003748 : ℝ) + (1:ℝ) / 10^8) := by
  constructor
  · exact a2_150_lower
  · exact a2_150_upper


-- ═══════════════════════ b = 200 ═══════════════════════
private lemma floor_200 : ⌊(200 : ℝ) / log 2⌋₊ = 288 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 200 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_200_exp_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_200_exp_lower

private lemma a2_200_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (200:ℝ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_200_exp_upper

private lemma cert_pow289_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(289:ℕ)) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow289_upper

private lemma a2_200_lower :
    (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_200]
  calc (1.00000007713 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 200) := a2_200_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(288+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_200_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000007713 : ℝ) + (1:ℝ) / 10^9 := by
  rw [floor_200]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_200_exp_upper
  · exact cert_pow289_upper

theorem a2_200_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 200)) (f ((2:ℝ)^(⌊(200:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000007713 : ℝ) ((1.00000007713 : ℝ) + (1:ℝ) / 10^9) := by
  constructor
  · exact a2_200_lower
  · exact a2_200_upper


-- ═══════════════════════ b = 250 ═══════════════════════
private lemma floor_250 : ⌊(250 : ℝ) / log 2⌋₊ = 360 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 250 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_250_exp_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_250_exp_lower

private lemma a2_250_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (250:ℝ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_250_exp_upper

private lemma cert_pow361_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(361:ℕ)) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow361_upper

private lemma a2_250_lower :
    (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_250]
  calc (1.00000002025 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 250) := a2_250_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(360+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_250_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000002025 : ℝ) + (1:ℝ) / 10^9 := by
  rw [floor_250]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · exact a2_250_exp_upper
  · exact cert_pow361_upper

theorem a2_250_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 250)) (f ((2:ℝ)^(⌊(250:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000002025 : ℝ) ((1.00000002025 : ℝ) + (1:ℝ) / 10^9) := by
  constructor
  · exact a2_250_lower
  · exact a2_250_upper


-- ═══════════════════════ b = 300 ═══════════════════════
private lemma floor_300 : ⌊(300 : ℝ) / log 2⌋₊ = 432 := by
  rw [Nat.floor_eq_iff (by positivity : (0:ℝ) ≤ 300 / log 2)]
  constructor
  · rw [le_div_iff₀ (log_pos one_lt_two)]; interval_decide
  · rw [div_lt_iff₀ (log_pos one_lt_two)]; interval_decide

private lemma a2_300_exp_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_300_exp_lower

private lemma a2_300_exp_upper :
    (1 + 193571378 / (10:ℝ)^16) * f (exp (300:ℝ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := by
  simpa [f_eq_leancert_f] using LeanCert.Examples.BKLNW_a2_bounds.a2_300_exp_upper

private lemma cert_pow433_upper :
    (1 + 193571378 / (10:ℝ)^16) * f ((2:ℝ)^(433:ℕ)) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by
  calc _ ≤ (1.00000001938 : ℝ) + (1:ℝ) / 10^9 := by
        rw [f_eq_leancert_f]; exact LeanCert.Examples.BKLNW_a2_pow2.pow433_upper
    _ ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by norm_num

private lemma a2_300_lower :
    (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) := by
  rw [floor_300]
  calc (1.00000001937 : ℝ) ≤ (1 + 193571378 / (10:ℝ)^16) * f (exp 300) := a2_300_exp_lower
    _ ≤ (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(432+1))) :=
        mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

private lemma a2_300_upper :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1))) ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by
  rw [floor_300]
  rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ 1 + 193571378 / (10:ℝ)^16)]
  apply max_le
  · calc _ ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^9 := a2_300_exp_upper
      _ ≤ (1.00000001937 : ℝ) + (1:ℝ) / 10^8 := by norm_num
  · exact cert_pow433_upper

theorem a2_300_mem_Icc :
    (1 + 193571378 / (10:ℝ)^16) * max (f (exp 300)) (f ((2:ℝ)^(⌊(300:ℝ)/log 2⌋₊ + 1)))
      ∈ Set.Icc (1.00000001937 : ℝ) ((1.00000001937 : ℝ) + (1:ℝ) / 10^8) := by
  constructor
  · exact a2_300_lower
  · exact a2_300_upper


-- ═══════════════════════ Main Theorem ═══════════════════════

theorem cor_5_1_rem' (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := by
  -- Unfold a₂ to (1+α) * max(f(exp b), f(2^(⌊b/log2⌋₊+1)))
  unfold a₂ Inputs.a₂
  rw [alpha_eq]
  -- Case split on table membership
  simp only [table_cor_5_1, List.mem_cons, Prod.mk.injEq, List.mem_nil_iff,
    or_false] at hb
  rcases hb with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · -- b = 20
    rw [rpow_neg_nat]; exact a2_20_mem_Icc
  · -- b = 25
    rw [rpow_neg_nat]; exact a2_25_mem_Icc
  · -- b = 30
    rw [rpow_neg_nat]; exact a2_30_mem_Icc
  · -- b = 35
    rw [rpow_neg_nat]; exact a2_35_mem_Icc
  · -- b = 40
    rw [rpow_neg_nat]; exact a2_40_mem_Icc
  · -- b = 43
    rw [rpow_neg_nat]; exact a2_43_mem_Icc
  · -- b = 100
    rw [show (1 + 2.420e-4 : ℝ) = (1.0002420 : ℝ) from by norm_num, rpow_neg_nat]
    exact a2_100_mem_Icc
  · -- b = 150
    rw [show (1 + 3.748e-6 : ℝ) = (1.000003748 : ℝ) from by norm_num, rpow_neg_nat]
    exact a2_150_mem_Icc
  · -- b = 200
    rw [show (1 + 7.713e-8 : ℝ) = (1.00000007713 : ℝ) from by norm_num, rpow_neg_nat]
    exact a2_200_mem_Icc
  · -- b = 250
    rw [show (1 + 2.025e-8 : ℝ) = (1.00000002025 : ℝ) from by norm_num, rpow_neg_nat]
    exact a2_250_mem_Icc
  · -- b = 300
    rw [show (1 + 1.937e-8 : ℝ) = (1.00000001937 : ℝ) from by norm_num, rpow_neg_nat]
    exact a2_300_mem_Icc

-- Canonical theorem (replaces the sorry in BKLNW.lean)
@[blueprint
  "bklnw-cor-5-1-rem"
  (title := "Remark after BKLNW Corollary 5.1")
  (statement := /--  We have the following values for $a_2$, given by the table after \cite[Corollary 5.1]{BKLNW}. -/)
  (latexEnv := "remark")
  (discussion := 853)]
theorem BKLNW.cor_5_1_rem (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := cor_5_1_rem' b a₂b m hb
