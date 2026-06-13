import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Generated regime-3 pointwise Table 10 margin certificates.

This shard expects `row_bound_pointwise`
to be available from `BKLNW_table10_rows_core.lean`.
-/

namespace BKLNW

open Real Set Finset

/-! ## Cached exp(-x) bounds shared across this file's k-margin theorems. -/

private lemma exp_neg_1200_lt : Real.exp (-(1200 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2425_2_lt : Real.exp (-(2425/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1225_lt : Real.exp (-(1225 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2475_2_lt : Real.exp (-(2475/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1250_lt : Real.exp (-(1250 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2525_2_lt : Real.exp (-(2525/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1275_lt : Real.exp (-(1275 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2575_2_lt : Real.exp (-(2575/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1300_lt : Real.exp (-(1300 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2625_2_lt : Real.exp (-(2625/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1325_lt : Real.exp (-(1325 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2675_2_lt : Real.exp (-(2675/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1350_lt : Real.exp (-(1350 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2725_2_lt : Real.exp (-(2725/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1375_lt : Real.exp (-(1375 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2775_2_lt : Real.exp (-(2775/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1400_lt : Real.exp (-(1400 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2825_2_lt : Real.exp (-(2825/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1425_lt : Real.exp (-(1425 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2875_2_lt : Real.exp (-(2875/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1600_lt : Real.exp (-(1600 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4850_3_lt : Real.exp (-(4850/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4900_3_lt : Real.exp (-(4900/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1650_lt : Real.exp (-(1650 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5000_3_lt : Real.exp (-(5000/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5050_3_lt : Real.exp (-(5050/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1700_lt : Real.exp (-(1700 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5150_3_lt : Real.exp (-(5150/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5200_3_lt : Real.exp (-(5200/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1750_lt : Real.exp (-(1750 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5300_3_lt : Real.exp (-(5300/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5350_3_lt : Real.exp (-(5350/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1800_lt : Real.exp (-(1800 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5450_3_lt : Real.exp (-(5450/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5500_3_lt : Real.exp (-(5500/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1850_lt : Real.exp (-(1850 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5600_3_lt : Real.exp (-(5600/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5650_3_lt : Real.exp (-(5650/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1900_lt : Real.exp (-(1900 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_5750_3_lt : Real.exp (-(5750/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)



private lemma logx1_lt_44 : log Inputs.default.x₁ < 44 := by
  change log (1e19 : ℝ) < 44
  have h : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
  rw [h, Real.log_pow]; push_cast; nlinarith [LogTables.log_10_lt]

private lemma a1_large_le_two {b : ℝ} (hb : 100 ≤ b) : Inputs.default.a₁ b ≤ (2 : ℝ) := by
  rw [Inputs.a₁, if_neg (by linarith [logx1_lt_44] : ¬ (b ≤ 2 * log Inputs.default.x₁))]
  have heps : Inputs.default.ε (b / 2) ≤ 4.2676e-5 := by
    change BKLNW_app.table_8_ε (b / 2) ≤ 4.2676e-5
    exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_20 (by nlinarith)
  linarith


private lemma row2400_a2_le : Inputs.default.a₂ (2400 : ℝ) ≤ (3465 : ℝ) := by
  have h := a2_crude_le (2400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2400 : ℝ) / log 2⌋₊ : ℝ) ≤ (2400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2400 : ℝ) / log 2 ≤ 3463 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3463 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3465 := by norm_num


private lemma row2425_a2_le : Inputs.default.a₂ (2425 : ℝ) ≤ (3501 : ℝ) := by
  have h := a2_crude_le (2425 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2425 : ℝ) / log 2⌋₊ : ℝ) ≤ (2425 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2425 : ℝ) / log 2 ≤ 3499 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2425 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2425 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3499 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3501 := by norm_num


private lemma row2450_a2_le : Inputs.default.a₂ (2450 : ℝ) ≤ (3537 : ℝ) := by
  have h := a2_crude_le (2450 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2450 : ℝ) / log 2⌋₊ : ℝ) ≤ (2450 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2450 : ℝ) / log 2 ≤ 3535 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2450 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2450 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3535 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3537 := by norm_num


private lemma row2475_a2_le : Inputs.default.a₂ (2475 : ℝ) ≤ (3573 : ℝ) := by
  have h := a2_crude_le (2475 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2475 : ℝ) / log 2⌋₊ : ℝ) ≤ (2475 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2475 : ℝ) / log 2 ≤ 3571 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2475 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2475 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3571 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3573 := by norm_num


private lemma row2500_a2_le : Inputs.default.a₂ (2500 : ℝ) ≤ (3609 : ℝ) := by
  have h := a2_crude_le (2500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2500 : ℝ) / log 2⌋₊ : ℝ) ≤ (2500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2500 : ℝ) / log 2 ≤ 3607 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3607 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3609 := by norm_num


private lemma row2525_a2_le : Inputs.default.a₂ (2525 : ℝ) ≤ (3645 : ℝ) := by
  have h := a2_crude_le (2525 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2525 : ℝ) / log 2⌋₊ : ℝ) ≤ (2525 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2525 : ℝ) / log 2 ≤ 3643 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2525 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2525 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3643 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3645 := by norm_num


private lemma row2550_a2_le : Inputs.default.a₂ (2550 : ℝ) ≤ (3681 : ℝ) := by
  have h := a2_crude_le (2550 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2550 : ℝ) / log 2⌋₊ : ℝ) ≤ (2550 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2550 : ℝ) / log 2 ≤ 3679 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2550 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2550 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3679 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3681 := by norm_num


private lemma row2575_a2_le : Inputs.default.a₂ (2575 : ℝ) ≤ (3717 : ℝ) := by
  have h := a2_crude_le (2575 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2575 : ℝ) / log 2⌋₊ : ℝ) ≤ (2575 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2575 : ℝ) / log 2 ≤ 3715 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2575 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2575 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3715 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3717 := by norm_num


private lemma row2600_a2_le : Inputs.default.a₂ (2600 : ℝ) ≤ (3754 : ℝ) := by
  have h := a2_crude_le (2600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2600 : ℝ) / log 2⌋₊ : ℝ) ≤ (2600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2600 : ℝ) / log 2 ≤ 3752 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3752 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3754 := by norm_num


private lemma row2625_a2_le : Inputs.default.a₂ (2625 : ℝ) ≤ (3790 : ℝ) := by
  have h := a2_crude_le (2625 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2625 : ℝ) / log 2⌋₊ : ℝ) ≤ (2625 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2625 : ℝ) / log 2 ≤ 3788 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2625 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2625 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3788 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3790 := by norm_num


private lemma row2650_a2_le : Inputs.default.a₂ (2650 : ℝ) ≤ (3826 : ℝ) := by
  have h := a2_crude_le (2650 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2650 : ℝ) / log 2⌋₊ : ℝ) ≤ (2650 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2650 : ℝ) / log 2 ≤ 3824 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2650 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2650 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3824 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3826 := by norm_num


private lemma row2675_a2_le : Inputs.default.a₂ (2675 : ℝ) ≤ (3862 : ℝ) := by
  have h := a2_crude_le (2675 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2675 : ℝ) / log 2⌋₊ : ℝ) ≤ (2675 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2675 : ℝ) / log 2 ≤ 3860 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2675 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2675 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3860 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3862 := by norm_num


private lemma row2700_a2_le : Inputs.default.a₂ (2700 : ℝ) ≤ (3898 : ℝ) := by
  have h := a2_crude_le (2700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2700 : ℝ) / log 2⌋₊ : ℝ) ≤ (2700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2700 : ℝ) / log 2 ≤ 3896 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3896 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3898 := by norm_num


private lemma row2725_a2_le : Inputs.default.a₂ (2725 : ℝ) ≤ (3934 : ℝ) := by
  have h := a2_crude_le (2725 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2725 : ℝ) / log 2⌋₊ : ℝ) ≤ (2725 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2725 : ℝ) / log 2 ≤ 3932 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2725 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2725 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3932 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3934 := by norm_num


private lemma row2750_a2_le : Inputs.default.a₂ (2750 : ℝ) ≤ (3970 : ℝ) := by
  have h := a2_crude_le (2750 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2750 : ℝ) / log 2⌋₊ : ℝ) ≤ (2750 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2750 : ℝ) / log 2 ≤ 3968 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2750 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2750 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3968 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3970 := by norm_num


private lemma row2775_a2_le : Inputs.default.a₂ (2775 : ℝ) ≤ (4006 : ℝ) := by
  have h := a2_crude_le (2775 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2775 : ℝ) / log 2⌋₊ : ℝ) ≤ (2775 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2775 : ℝ) / log 2 ≤ 4004 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2775 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2775 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4004 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4006 := by norm_num


private lemma row2800_a2_le : Inputs.default.a₂ (2800 : ℝ) ≤ (4042 : ℝ) := by
  have h := a2_crude_le (2800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2800 : ℝ) / log 2⌋₊ : ℝ) ≤ (2800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2800 : ℝ) / log 2 ≤ 4040 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4040 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4042 := by norm_num


private lemma row2825_a2_le : Inputs.default.a₂ (2825 : ℝ) ≤ (4078 : ℝ) := by
  have h := a2_crude_le (2825 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2825 : ℝ) / log 2⌋₊ : ℝ) ≤ (2825 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2825 : ℝ) / log 2 ≤ 4076 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2825 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2825 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4076 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4078 := by norm_num


private lemma row2850_a2_le : Inputs.default.a₂ (2850 : ℝ) ≤ (4114 : ℝ) := by
  have h := a2_crude_le (2850 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2850 : ℝ) / log 2⌋₊ : ℝ) ≤ (2850 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2850 : ℝ) / log 2 ≤ 4112 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2850 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2850 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4112 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4114 := by norm_num


private lemma row2875_a2_le : Inputs.default.a₂ (2875 : ℝ) ≤ (4150 : ℝ) := by
  have h := a2_crude_le (2875 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2875 : ℝ) / log 2⌋₊ : ℝ) ≤ (2875 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2875 : ℝ) / log 2 ≤ 4148 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2875 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2875 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4148 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4150 := by norm_num


set_option maxRecDepth 10000 in
private lemma row2400_table8_mem : (2400, 1.6009e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2400_eps_le : Inputs.default.ε (2400 : ℝ) ≤ 1.6009e-12 := by
  change BKLNW_app.table_8_ε (2400 : ℝ) ≤ 1.6009e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2400)
    (ε := 1.6009e-12) row2400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2425_table8_mem : (2425, 1.4218e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2425_eps_le : Inputs.default.ε (2425 : ℝ) ≤ 1.4218e-12 := by
  change BKLNW_app.table_8_ε (2425 : ℝ) ≤ 1.4218e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2425)
    (ε := 1.4218e-12) row2425_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2450_table8_mem : (2450, 1.2214e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2450_eps_le : Inputs.default.ε (2450 : ℝ) ≤ 1.2214e-12 := by
  change BKLNW_app.table_8_ε (2450 : ℝ) ≤ 1.2214e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2450)
    (ε := 1.2214e-12) row2450_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2475_table8_mem : (2475, 1.0512e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2475_eps_le : Inputs.default.ε (2475 : ℝ) ≤ 1.0512e-12 := by
  change BKLNW_app.table_8_ε (2475 : ℝ) ≤ 1.0512e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2475)
    (ε := 1.0512e-12) row2475_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2500_table8_mem : (2500, 9.0631e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2500_eps_le : Inputs.default.ε (2500 : ℝ) ≤ 9.0631e-13 := by
  change BKLNW_app.table_8_ε (2500 : ℝ) ≤ 9.0631e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2500)
    (ε := 9.0631e-13) row2500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2525_table8_mem : (2525, 7.7933e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2525_eps_le : Inputs.default.ε (2525 : ℝ) ≤ 7.7933e-13 := by
  change BKLNW_app.table_8_ε (2525 : ℝ) ≤ 7.7933e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2525)
    (ε := 7.7933e-13) row2525_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2550_table8_mem : (2550, 6.7069e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2550_eps_le : Inputs.default.ε (2550 : ℝ) ≤ 6.7069e-13 := by
  change BKLNW_app.table_8_ε (2550 : ℝ) ≤ 6.7069e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2550)
    (ε := 6.7069e-13) row2550_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2575_table8_mem : (2575, 5.7662e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2575_eps_le : Inputs.default.ε (2575 : ℝ) ≤ 5.7662e-13 := by
  change BKLNW_app.table_8_ε (2575 : ℝ) ≤ 5.7662e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2575)
    (ε := 5.7662e-13) row2575_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2600_table8_mem : (2600, 4.9610e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2600_eps_le : Inputs.default.ε (2600 : ℝ) ≤ 4.9610e-13 := by
  change BKLNW_app.table_8_ε (2600 : ℝ) ≤ 4.9610e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2600)
    (ε := 4.9610e-13) row2600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2625_table8_mem : (2625, 4.2694e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2625_eps_le : Inputs.default.ε (2625 : ℝ) ≤ 4.2694e-13 := by
  change BKLNW_app.table_8_ε (2625 : ℝ) ≤ 4.2694e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2625)
    (ε := 4.2694e-13) row2625_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2650_table8_mem : (2650, 3.6747e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2650_eps_le : Inputs.default.ε (2650 : ℝ) ≤ 3.6747e-13 := by
  change BKLNW_app.table_8_ε (2650 : ℝ) ≤ 3.6747e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2650)
    (ε := 3.6747e-13) row2650_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2675_table8_mem : (2675, 3.1642e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2675_eps_le : Inputs.default.ε (2675 : ℝ) ≤ 3.1642e-13 := by
  change BKLNW_app.table_8_ε (2675 : ℝ) ≤ 3.1642e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2675)
    (ε := 3.1642e-13) row2675_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2700_table8_mem : (2700, 2.7243e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2700_eps_le : Inputs.default.ε (2700 : ℝ) ≤ 2.7243e-13 := by
  change BKLNW_app.table_8_ε (2700 : ℝ) ≤ 2.7243e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2700)
    (ε := 2.7243e-13) row2700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2725_table8_mem : (2725, 2.3455e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2725_eps_le : Inputs.default.ε (2725 : ℝ) ≤ 2.3455e-13 := by
  change BKLNW_app.table_8_ε (2725 : ℝ) ≤ 2.3455e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2725)
    (ε := 2.3455e-13) row2725_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2750_table8_mem : (2750, 2.0207e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2750_eps_le : Inputs.default.ε (2750 : ℝ) ≤ 2.0207e-13 := by
  change BKLNW_app.table_8_ε (2750 : ℝ) ≤ 2.0207e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2750)
    (ε := 2.0207e-13) row2750_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2775_table8_mem : (2775, 1.7404e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2775_eps_le : Inputs.default.ε (2775 : ℝ) ≤ 1.7404e-13 := by
  change BKLNW_app.table_8_ε (2775 : ℝ) ≤ 1.7404e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2775)
    (ε := 1.7404e-13) row2775_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2800_table8_mem : (2800, 1.5006e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2800_eps_le : Inputs.default.ε (2800 : ℝ) ≤ 1.5006e-13 := by
  change BKLNW_app.table_8_ε (2800 : ℝ) ≤ 1.5006e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2800)
    (ε := 1.5006e-13) row2800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2825_table8_mem : (2825, 1.2952e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2825_eps_le : Inputs.default.ε (2825 : ℝ) ≤ 1.2952e-13 := by
  change BKLNW_app.table_8_ε (2825 : ℝ) ≤ 1.2952e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2825)
    (ε := 1.2952e-13) row2825_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2850_table8_mem : (2850, 1.1190e-13) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2850_eps_le : Inputs.default.ε (2850 : ℝ) ≤ 1.1190e-13 := by
  change BKLNW_app.table_8_ε (2850 : ℝ) ≤ 1.1190e-13
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2850)
    (ε := 1.1190e-13) row2850_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row2875_table8_mem : (2875, 9.6389e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2875_eps_le : Inputs.default.ε (2875 : ℝ) ≤ 9.6389e-14 := by
  change BKLNW_app.table_8_ε (2875 : ℝ) ≤ 9.6389e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2875)
    (ε := 9.6389e-14) row2875_table8_mem (by norm_num)


/-- Row 2400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2400_k1_margin :
    B_8_exact 1 (2400 : ℝ) (2425 : ℝ) ≤ (0.0000000038820 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2400 : ℝ) (2425 : ℝ) 2 3465 1.6009e-12
    (0.0000000038820 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2400_a2_le row2400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1200_lt, exp_neg_1600_lt,
                   Real.exp_pos (-(1200:ℝ)), Real.exp_pos (-(1600:ℝ))])


/-- Row 2400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2400_k2_margin :
    B_8_exact 2 (2400 : ℝ) (2425 : ℝ) ≤ (0.0000094139 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2400 : ℝ) (2425 : ℝ) 2 3465 1.6009e-12
    (0.0000094139 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2400_a2_le row2400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1200_lt, exp_neg_1600_lt,
                   Real.exp_pos (-(1200:ℝ)), Real.exp_pos (-(1600:ℝ))])


/-- Row 2400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2400_k3_margin :
    B_8_exact 3 (2400 : ℝ) (2425 : ℝ) ≤ (0.022829 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2400 : ℝ) (2425 : ℝ) 2 3465 1.6009e-12
    (0.022829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2400_a2_le row2400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1200_lt, exp_neg_1600_lt,
                   Real.exp_pos (-(1200:ℝ)), Real.exp_pos (-(1600:ℝ))])


/-- Row 2400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2400_k4_margin :
    B_8_exact 4 (2400 : ℝ) (2425 : ℝ) ≤ (55.360 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2400 : ℝ) (2425 : ℝ) 2 3465 1.6009e-12
    (55.360 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2400_a2_le row2400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1200_lt, exp_neg_1600_lt,
                   Real.exp_pos (-(1200:ℝ)), Real.exp_pos (-(1600:ℝ))])


/-- Row 2400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2400_k5_margin :
    B_8_exact 5 (2400 : ℝ) (2425 : ℝ) ≤ (134250 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2400 : ℝ) (2425 : ℝ) 2 3465 1.6009e-12
    (134250 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2400_a2_le row2400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1200_lt, exp_neg_1600_lt,
                   Real.exp_pos (-(1200:ℝ)), Real.exp_pos (-(1600:ℝ))])


/-- Row 2425 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2425_k1_margin :
    B_8_exact 1 (2425 : ℝ) (2450 : ℝ) ≤ (0.0000000034832 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2425 : ℝ) (2450 : ℝ) 2 3501 1.4218e-12
    (0.0000000034832 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2425_a2_le row2425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2425_2_lt, exp_neg_4850_3_lt,
                   Real.exp_pos (-(2425/2:ℝ)), Real.exp_pos (-(4850/3:ℝ))])


/-- Row 2425 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2425_k2_margin :
    B_8_exact 2 (2425 : ℝ) (2450 : ℝ) ≤ (0.0000085339 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2425 : ℝ) (2450 : ℝ) 2 3501 1.4218e-12
    (0.0000085339 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2425_a2_le row2425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2425_2_lt, exp_neg_4850_3_lt,
                   Real.exp_pos (-(2425/2:ℝ)), Real.exp_pos (-(4850/3:ℝ))])


/-- Row 2425 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2425_k3_margin :
    B_8_exact 3 (2425 : ℝ) (2450 : ℝ) ≤ (0.020908 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2425 : ℝ) (2450 : ℝ) 2 3501 1.4218e-12
    (0.020908 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2425_a2_le row2425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2425_2_lt, exp_neg_4850_3_lt,
                   Real.exp_pos (-(2425/2:ℝ)), Real.exp_pos (-(4850/3:ℝ))])


/-- Row 2425 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2425_k4_margin :
    B_8_exact 4 (2425 : ℝ) (2450 : ℝ) ≤ (51.225 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2425 : ℝ) (2450 : ℝ) 2 3501 1.4218e-12
    (51.225 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2425_a2_le row2425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2425_2_lt, exp_neg_4850_3_lt,
                   Real.exp_pos (-(2425/2:ℝ)), Real.exp_pos (-(4850/3:ℝ))])


/-- Row 2425 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2425_k5_margin :
    B_8_exact 5 (2425 : ℝ) (2450 : ℝ) ≤ (125500 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2425 : ℝ) (2450 : ℝ) 2 3501 1.4218e-12
    (125500 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2425_a2_le row2425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2425_2_lt, exp_neg_4850_3_lt,
                   Real.exp_pos (-(2425/2:ℝ)), Real.exp_pos (-(4850/3:ℝ))])


/-- Row 2450 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2450_k1_margin :
    B_8_exact 1 (2450 : ℝ) (2475 : ℝ) ≤ (0.0000000030228 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2450 : ℝ) (2475 : ℝ) 2 3537 1.2214e-12
    (0.0000000030228 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2450_a2_le row2450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1225_lt, exp_neg_4900_3_lt,
                   Real.exp_pos (-(1225:ℝ)), Real.exp_pos (-(4900/3:ℝ))])


/-- Row 2450 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2450_k2_margin :
    B_8_exact 2 (2450 : ℝ) (2475 : ℝ) ≤ (0.0000074814 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2450 : ℝ) (2475 : ℝ) 2 3537 1.2214e-12
    (0.0000074814 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2450_a2_le row2450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1225_lt, exp_neg_4900_3_lt,
                   Real.exp_pos (-(1225:ℝ)), Real.exp_pos (-(4900/3:ℝ))])


/-- Row 2450 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2450_k3_margin :
    B_8_exact 3 (2450 : ℝ) (2475 : ℝ) ≤ (0.018517 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2450 : ℝ) (2475 : ℝ) 2 3537 1.2214e-12
    (0.018517 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2450_a2_le row2450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1225_lt, exp_neg_4900_3_lt,
                   Real.exp_pos (-(1225:ℝ)), Real.exp_pos (-(4900/3:ℝ))])


/-- Row 2450 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2450_k4_margin :
    B_8_exact 4 (2450 : ℝ) (2475 : ℝ) ≤ (45.828 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2450 : ℝ) (2475 : ℝ) 2 3537 1.2214e-12
    (45.828 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2450_a2_le row2450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1225_lt, exp_neg_4900_3_lt,
                   Real.exp_pos (-(1225:ℝ)), Real.exp_pos (-(4900/3:ℝ))])


/-- Row 2450 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2450_k5_margin :
    B_8_exact 5 (2450 : ℝ) (2475 : ℝ) ≤ (113430 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2450 : ℝ) (2475 : ℝ) 2 3537 1.2214e-12
    (113430 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2450_a2_le row2450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1225_lt, exp_neg_4900_3_lt,
                   Real.exp_pos (-(1225:ℝ)), Real.exp_pos (-(4900/3:ℝ))])


/-- Row 2475 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2475_k1_margin :
    B_8_exact 1 (2475 : ℝ) (2500 : ℝ) ≤ (0.0000000026278 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2475 : ℝ) (2500 : ℝ) 2 3573 1.0512e-12
    (0.0000000026278 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2475_a2_le row2475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_2_lt, exp_neg_1650_lt,
                   Real.exp_pos (-(2475/2:ℝ)), Real.exp_pos (-(1650:ℝ))])


/-- Row 2475 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2475_k2_margin :
    B_8_exact 2 (2475 : ℝ) (2500 : ℝ) ≤ (0.0000065696 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2475 : ℝ) (2500 : ℝ) 2 3573 1.0512e-12
    (0.0000065696 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2475_a2_le row2475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_2_lt, exp_neg_1650_lt,
                   Real.exp_pos (-(2475/2:ℝ)), Real.exp_pos (-(1650:ℝ))])


/-- Row 2475 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2475_k3_margin :
    B_8_exact 3 (2475 : ℝ) (2500 : ℝ) ≤ (0.016424 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2475 : ℝ) (2500 : ℝ) 2 3573 1.0512e-12
    (0.016424 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2475_a2_le row2475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_2_lt, exp_neg_1650_lt,
                   Real.exp_pos (-(2475/2:ℝ)), Real.exp_pos (-(1650:ℝ))])


/-- Row 2475 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2475_k4_margin :
    B_8_exact 4 (2475 : ℝ) (2500 : ℝ) ≤ (41.060 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2475 : ℝ) (2500 : ℝ) 2 3573 1.0512e-12
    (41.060 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2475_a2_le row2475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_2_lt, exp_neg_1650_lt,
                   Real.exp_pos (-(2475/2:ℝ)), Real.exp_pos (-(1650:ℝ))])


/-- Row 2475 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2475_k5_margin :
    B_8_exact 5 (2475 : ℝ) (2500 : ℝ) ≤ (102650 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2475 : ℝ) (2500 : ℝ) 2 3573 1.0512e-12
    (102650 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2475_a2_le row2475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_2_lt, exp_neg_1650_lt,
                   Real.exp_pos (-(2475/2:ℝ)), Real.exp_pos (-(1650:ℝ))])


/-- Row 2500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2500_k1_margin :
    B_8_exact 1 (2500 : ℝ) (2525 : ℝ) ≤ (0.0000000022884 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2500 : ℝ) (2525 : ℝ) 2 3609 9.0631e-13
    (0.0000000022884 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2500_a2_le row2500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1250_lt, exp_neg_5000_3_lt,
                   Real.exp_pos (-(1250:ℝ)), Real.exp_pos (-(5000/3:ℝ))])


/-- Row 2500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2500_k2_margin :
    B_8_exact 2 (2500 : ℝ) (2525 : ℝ) ≤ (0.0000057783 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2500 : ℝ) (2525 : ℝ) 2 3609 9.0631e-13
    (0.0000057783 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2500_a2_le row2500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1250_lt, exp_neg_5000_3_lt,
                   Real.exp_pos (-(1250:ℝ)), Real.exp_pos (-(5000/3:ℝ))])


/-- Row 2500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2500_k3_margin :
    B_8_exact 3 (2500 : ℝ) (2525 : ℝ) ≤ (0.014590 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2500 : ℝ) (2525 : ℝ) 2 3609 9.0631e-13
    (0.014590 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2500_a2_le row2500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1250_lt, exp_neg_5000_3_lt,
                   Real.exp_pos (-(1250:ℝ)), Real.exp_pos (-(5000/3:ℝ))])


/-- Row 2500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2500_k4_margin :
    B_8_exact 4 (2500 : ℝ) (2525 : ℝ) ≤ (36.840 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2500 : ℝ) (2525 : ℝ) 2 3609 9.0631e-13
    (36.840 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2500_a2_le row2500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1250_lt, exp_neg_5000_3_lt,
                   Real.exp_pos (-(1250:ℝ)), Real.exp_pos (-(5000/3:ℝ))])


/-- Row 2500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2500_k5_margin :
    B_8_exact 5 (2500 : ℝ) (2525 : ℝ) ≤ (93021 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2500 : ℝ) (2525 : ℝ) 2 3609 9.0631e-13
    (93021 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2500_a2_le row2500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1250_lt, exp_neg_5000_3_lt,
                   Real.exp_pos (-(1250:ℝ)), Real.exp_pos (-(5000/3:ℝ))])


/-- Row 2525 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2525_k1_margin :
    B_8_exact 1 (2525 : ℝ) (2550 : ℝ) ≤ (0.0000000019873 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2525 : ℝ) (2550 : ℝ) 2 3645 7.7933e-13
    (0.0000000019873 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2525_a2_le row2525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2525_2_lt, exp_neg_5050_3_lt,
                   Real.exp_pos (-(2525/2:ℝ)), Real.exp_pos (-(5050/3:ℝ))])


/-- Row 2525 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2525_k2_margin :
    B_8_exact 2 (2525 : ℝ) (2550 : ℝ) ≤ (0.0000050676 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2525 : ℝ) (2550 : ℝ) 2 3645 7.7933e-13
    (0.0000050676 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2525_a2_le row2525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2525_2_lt, exp_neg_5050_3_lt,
                   Real.exp_pos (-(2525/2:ℝ)), Real.exp_pos (-(5050/3:ℝ))])


/-- Row 2525 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2525_k3_margin :
    B_8_exact 3 (2525 : ℝ) (2550 : ℝ) ≤ (0.012922 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2525 : ℝ) (2550 : ℝ) 2 3645 7.7933e-13
    (0.012922 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2525_a2_le row2525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2525_2_lt, exp_neg_5050_3_lt,
                   Real.exp_pos (-(2525/2:ℝ)), Real.exp_pos (-(5050/3:ℝ))])


/-- Row 2525 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2525_k4_margin :
    B_8_exact 4 (2525 : ℝ) (2550 : ℝ) ≤ (32.952 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2525 : ℝ) (2550 : ℝ) 2 3645 7.7933e-13
    (32.952 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2525_a2_le row2525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2525_2_lt, exp_neg_5050_3_lt,
                   Real.exp_pos (-(2525/2:ℝ)), Real.exp_pos (-(5050/3:ℝ))])


/-- Row 2525 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2525_k5_margin :
    B_8_exact 5 (2525 : ℝ) (2550 : ℝ) ≤ (84027 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2525 : ℝ) (2550 : ℝ) 2 3645 7.7933e-13
    (84027 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2525_a2_le row2525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2525_2_lt, exp_neg_5050_3_lt,
                   Real.exp_pos (-(2525/2:ℝ)), Real.exp_pos (-(5050/3:ℝ))])


/-- Row 2550 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2550_k1_margin :
    B_8_exact 1 (2550 : ℝ) (2575 : ℝ) ≤ (0.0000000017270 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2550 : ℝ) (2575 : ℝ) 2 3681 6.7069e-13
    (0.0000000017270 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2550_a2_le row2550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1275_lt, exp_neg_1700_lt,
                   Real.exp_pos (-(1275:ℝ)), Real.exp_pos (-(1700:ℝ))])


/-- Row 2550 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2550_k2_margin :
    B_8_exact 2 (2550 : ℝ) (2575 : ℝ) ≤ (0.0000044470 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2550 : ℝ) (2575 : ℝ) 2 3681 6.7069e-13
    (0.0000044470 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2550_a2_le row2550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1275_lt, exp_neg_1700_lt,
                   Real.exp_pos (-(1275:ℝ)), Real.exp_pos (-(1700:ℝ))])


/-- Row 2550 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2550_k3_margin :
    B_8_exact 3 (2550 : ℝ) (2575 : ℝ) ≤ (0.011451 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2550 : ℝ) (2575 : ℝ) 2 3681 6.7069e-13
    (0.011451 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2550_a2_le row2550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1275_lt, exp_neg_1700_lt,
                   Real.exp_pos (-(1275:ℝ)), Real.exp_pos (-(1700:ℝ))])


/-- Row 2550 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2550_k4_margin :
    B_8_exact 4 (2550 : ℝ) (2575 : ℝ) ≤ (29.487 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2550 : ℝ) (2575 : ℝ) 2 3681 6.7069e-13
    (29.487 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2550_a2_le row2550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1275_lt, exp_neg_1700_lt,
                   Real.exp_pos (-(1275:ℝ)), Real.exp_pos (-(1700:ℝ))])


/-- Row 2550 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2550_k5_margin :
    B_8_exact 5 (2550 : ℝ) (2575 : ℝ) ≤ (75928 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2550 : ℝ) (2575 : ℝ) 2 3681 6.7069e-13
    (75928 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2550_a2_le row2550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1275_lt, exp_neg_1700_lt,
                   Real.exp_pos (-(1275:ℝ)), Real.exp_pos (-(1700:ℝ))])


/-- Row 2575 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2575_k1_margin :
    B_8_exact 1 (2575 : ℝ) (2600 : ℝ) ≤ (0.0000000014992 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2575 : ℝ) (2600 : ℝ) 2 3717 5.7662e-13
    (0.0000000014992 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2575_a2_le row2575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2575_2_lt, exp_neg_5150_3_lt,
                   Real.exp_pos (-(2575/2:ℝ)), Real.exp_pos (-(5150/3:ℝ))])


/-- Row 2575 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2575_k2_margin :
    B_8_exact 2 (2575 : ℝ) (2600 : ℝ) ≤ (0.0000038979 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2575 : ℝ) (2600 : ℝ) 2 3717 5.7662e-13
    (0.0000038979 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2575_a2_le row2575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2575_2_lt, exp_neg_5150_3_lt,
                   Real.exp_pos (-(2575/2:ℝ)), Real.exp_pos (-(5150/3:ℝ))])


/-- Row 2575 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2575_k3_margin :
    B_8_exact 3 (2575 : ℝ) (2600 : ℝ) ≤ (0.010135 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2575 : ℝ) (2600 : ℝ) 2 3717 5.7662e-13
    (0.010135 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2575_a2_le row2575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2575_2_lt, exp_neg_5150_3_lt,
                   Real.exp_pos (-(2575/2:ℝ)), Real.exp_pos (-(5150/3:ℝ))])


/-- Row 2575 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2575_k4_margin :
    B_8_exact 4 (2575 : ℝ) (2600 : ℝ) ≤ (26.350 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2575 : ℝ) (2600 : ℝ) 2 3717 5.7662e-13
    (26.350 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2575_a2_le row2575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2575_2_lt, exp_neg_5150_3_lt,
                   Real.exp_pos (-(2575/2:ℝ)), Real.exp_pos (-(5150/3:ℝ))])


/-- Row 2575 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2575_k5_margin :
    B_8_exact 5 (2575 : ℝ) (2600 : ℝ) ≤ (68509 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2575 : ℝ) (2600 : ℝ) 2 3717 5.7662e-13
    (68509 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2575_a2_le row2575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2575_2_lt, exp_neg_5150_3_lt,
                   Real.exp_pos (-(2575/2:ℝ)), Real.exp_pos (-(5150/3:ℝ))])


/-- Row 2600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2600_k1_margin :
    B_8_exact 1 (2600 : ℝ) (2625 : ℝ) ≤ (0.0000000013022 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2600 : ℝ) (2625 : ℝ) 2 3754 4.9610e-13
    (0.0000000013022 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2600_a2_le row2600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1300_lt, exp_neg_5200_3_lt,
                   Real.exp_pos (-(1300:ℝ)), Real.exp_pos (-(5200/3:ℝ))])


/-- Row 2600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2600_k2_margin :
    B_8_exact 2 (2600 : ℝ) (2625 : ℝ) ≤ (0.0000034184 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2600 : ℝ) (2625 : ℝ) 2 3754 4.9610e-13
    (0.0000034184 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2600_a2_le row2600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1300_lt, exp_neg_5200_3_lt,
                   Real.exp_pos (-(1300:ℝ)), Real.exp_pos (-(5200/3:ℝ))])


/-- Row 2600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2600_k3_margin :
    B_8_exact 3 (2600 : ℝ) (2625 : ℝ) ≤ (0.0089732 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2600 : ℝ) (2625 : ℝ) 2 3754 4.9610e-13
    (0.0089732 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2600_a2_le row2600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1300_lt, exp_neg_5200_3_lt,
                   Real.exp_pos (-(1300:ℝ)), Real.exp_pos (-(5200/3:ℝ))])


/-- Row 2600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2600_k4_margin :
    B_8_exact 4 (2600 : ℝ) (2625 : ℝ) ≤ (23.555 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2600 : ℝ) (2625 : ℝ) 2 3754 4.9610e-13
    (23.555 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2600_a2_le row2600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1300_lt, exp_neg_5200_3_lt,
                   Real.exp_pos (-(1300:ℝ)), Real.exp_pos (-(5200/3:ℝ))])


/-- Row 2600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2600_k5_margin :
    B_8_exact 5 (2600 : ℝ) (2625 : ℝ) ≤ (61831 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2600 : ℝ) (2625 : ℝ) 2 3754 4.9610e-13
    (61831 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2600_a2_le row2600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1300_lt, exp_neg_5200_3_lt,
                   Real.exp_pos (-(1300:ℝ)), Real.exp_pos (-(5200/3:ℝ))])


/-- Row 2625 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2625_k1_margin :
    B_8_exact 1 (2625 : ℝ) (2650 : ℝ) ≤ (0.0000000011314 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2625 : ℝ) (2650 : ℝ) 2 3790 4.2694e-13
    (0.0000000011314 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2625_a2_le row2625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2625_2_lt, exp_neg_1750_lt,
                   Real.exp_pos (-(2625/2:ℝ)), Real.exp_pos (-(1750:ℝ))])


/-- Row 2625 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2625_k2_margin :
    B_8_exact 2 (2625 : ℝ) (2650 : ℝ) ≤ (0.0000029981 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2625 : ℝ) (2650 : ℝ) 2 3790 4.2694e-13
    (0.0000029981 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2625_a2_le row2625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2625_2_lt, exp_neg_1750_lt,
                   Real.exp_pos (-(2625/2:ℝ)), Real.exp_pos (-(1750:ℝ))])


/-- Row 2625 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2625_k3_margin :
    B_8_exact 3 (2625 : ℝ) (2650 : ℝ) ≤ (0.0079449 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2625 : ℝ) (2650 : ℝ) 2 3790 4.2694e-13
    (0.0079449 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2625_a2_le row2625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2625_2_lt, exp_neg_1750_lt,
                   Real.exp_pos (-(2625/2:ℝ)), Real.exp_pos (-(1750:ℝ))])


/-- Row 2625 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2625_k4_margin :
    B_8_exact 4 (2625 : ℝ) (2650 : ℝ) ≤ (21.054 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2625 : ℝ) (2650 : ℝ) 2 3790 4.2694e-13
    (21.054 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2625_a2_le row2625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2625_2_lt, exp_neg_1750_lt,
                   Real.exp_pos (-(2625/2:ℝ)), Real.exp_pos (-(1750:ℝ))])


/-- Row 2625 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2625_k5_margin :
    B_8_exact 5 (2625 : ℝ) (2650 : ℝ) ≤ (55793 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2625 : ℝ) (2650 : ℝ) 2 3790 4.2694e-13
    (55793 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2625_a2_le row2625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2625_2_lt, exp_neg_1750_lt,
                   Real.exp_pos (-(2625/2:ℝ)), Real.exp_pos (-(1750:ℝ))])


/-- Row 2650 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2650_k1_margin :
    B_8_exact 1 (2650 : ℝ) (2675 : ℝ) ≤ (0.00000000098296 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2650 : ℝ) (2675 : ℝ) 2 3826 3.6747e-13
    (0.00000000098296 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2650_a2_le row2650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1325_lt, exp_neg_5300_3_lt,
                   Real.exp_pos (-(1325:ℝ)), Real.exp_pos (-(5300/3:ℝ))])


/-- Row 2650 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2650_k2_margin :
    B_8_exact 2 (2650 : ℝ) (2675 : ℝ) ≤ (0.0000026294 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2650 : ℝ) (2675 : ℝ) 2 3826 3.6747e-13
    (0.0000026294 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2650_a2_le row2650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1325_lt, exp_neg_5300_3_lt,
                   Real.exp_pos (-(1325:ℝ)), Real.exp_pos (-(5300/3:ℝ))])


/-- Row 2650 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2650_k3_margin :
    B_8_exact 3 (2650 : ℝ) (2675 : ℝ) ≤ (0.0070337 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2650 : ℝ) (2675 : ℝ) 2 3826 3.6747e-13
    (0.0070337 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2650_a2_le row2650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1325_lt, exp_neg_5300_3_lt,
                   Real.exp_pos (-(1325:ℝ)), Real.exp_pos (-(5300/3:ℝ))])


/-- Row 2650 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2650_k4_margin :
    B_8_exact 4 (2650 : ℝ) (2675 : ℝ) ≤ (18.815 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2650 : ℝ) (2675 : ℝ) 2 3826 3.6747e-13
    (18.815 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2650_a2_le row2650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1325_lt, exp_neg_5300_3_lt,
                   Real.exp_pos (-(1325:ℝ)), Real.exp_pos (-(5300/3:ℝ))])


/-- Row 2650 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2650_k5_margin :
    B_8_exact 5 (2650 : ℝ) (2675 : ℝ) ≤ (50330 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2650 : ℝ) (2675 : ℝ) 2 3826 3.6747e-13
    (50330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2650_a2_le row2650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1325_lt, exp_neg_5300_3_lt,
                   Real.exp_pos (-(1325:ℝ)), Real.exp_pos (-(5300/3:ℝ))])


/-- Row 2675 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2675_k1_margin :
    B_8_exact 1 (2675 : ℝ) (2700 : ℝ) ≤ (0.00000000085431 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2675 : ℝ) (2700 : ℝ) 2 3862 3.1642e-13
    (0.00000000085431 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2675_a2_le row2675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2675_2_lt, exp_neg_5350_3_lt,
                   Real.exp_pos (-(2675/2:ℝ)), Real.exp_pos (-(5350/3:ℝ))])


/-- Row 2675 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2675_k2_margin :
    B_8_exact 2 (2675 : ℝ) (2700 : ℝ) ≤ (0.0000023067 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2675 : ℝ) (2700 : ℝ) 2 3862 3.1642e-13
    (0.0000023067 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2675_a2_le row2675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2675_2_lt, exp_neg_5350_3_lt,
                   Real.exp_pos (-(2675/2:ℝ)), Real.exp_pos (-(5350/3:ℝ))])


/-- Row 2675 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2675_k3_margin :
    B_8_exact 3 (2675 : ℝ) (2700 : ℝ) ≤ (0.0062279 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2675 : ℝ) (2700 : ℝ) 2 3862 3.1642e-13
    (0.0062279 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2675_a2_le row2675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2675_2_lt, exp_neg_5350_3_lt,
                   Real.exp_pos (-(2675/2:ℝ)), Real.exp_pos (-(5350/3:ℝ))])


/-- Row 2675 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2675_k4_margin :
    B_8_exact 4 (2675 : ℝ) (2700 : ℝ) ≤ (16.816 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2675 : ℝ) (2700 : ℝ) 2 3862 3.1642e-13
    (16.816 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2675_a2_le row2675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2675_2_lt, exp_neg_5350_3_lt,
                   Real.exp_pos (-(2675/2:ℝ)), Real.exp_pos (-(5350/3:ℝ))])


/-- Row 2675 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2675_k5_margin :
    B_8_exact 5 (2675 : ℝ) (2700 : ℝ) ≤ (45402 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2675 : ℝ) (2700 : ℝ) 2 3862 3.1642e-13
    (45402 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2675_a2_le row2675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2675_2_lt, exp_neg_5350_3_lt,
                   Real.exp_pos (-(2675/2:ℝ)), Real.exp_pos (-(5350/3:ℝ))])


/-- Row 2700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2700_k1_margin :
    B_8_exact 1 (2700 : ℝ) (2725 : ℝ) ≤ (0.00000000074234 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2700 : ℝ) (2725 : ℝ) 2 3898 2.7243e-13
    (0.00000000074234 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2700_a2_le row2700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1350_lt, exp_neg_1800_lt,
                   Real.exp_pos (-(1350:ℝ)), Real.exp_pos (-(1800:ℝ))])


/-- Row 2700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2700_k2_margin :
    B_8_exact 2 (2700 : ℝ) (2725 : ℝ) ≤ (0.0000020229 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2700 : ℝ) (2725 : ℝ) 2 3898 2.7243e-13
    (0.0000020229 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2700_a2_le row2700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1350_lt, exp_neg_1800_lt,
                   Real.exp_pos (-(1350:ℝ)), Real.exp_pos (-(1800:ℝ))])


/-- Row 2700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2700_k3_margin :
    B_8_exact 3 (2700 : ℝ) (2725 : ℝ) ≤ (0.0055123 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2700 : ℝ) (2725 : ℝ) 2 3898 2.7243e-13
    (0.0055123 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2700_a2_le row2700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1350_lt, exp_neg_1800_lt,
                   Real.exp_pos (-(1350:ℝ)), Real.exp_pos (-(1800:ℝ))])


/-- Row 2700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2700_k4_margin :
    B_8_exact 4 (2700 : ℝ) (2725 : ℝ) ≤ (15.021 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2700 : ℝ) (2725 : ℝ) 2 3898 2.7243e-13
    (15.021 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2700_a2_le row2700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1350_lt, exp_neg_1800_lt,
                   Real.exp_pos (-(1350:ℝ)), Real.exp_pos (-(1800:ℝ))])


/-- Row 2700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2700_k5_margin :
    B_8_exact 5 (2700 : ℝ) (2725 : ℝ) ≤ (40932 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2700 : ℝ) (2725 : ℝ) 2 3898 2.7243e-13
    (40932 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2700_a2_le row2700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1350_lt, exp_neg_1800_lt,
                   Real.exp_pos (-(1350:ℝ)), Real.exp_pos (-(1800:ℝ))])


/-- Row 2725 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2725_k1_margin :
    B_8_exact 1 (2725 : ℝ) (2750 : ℝ) ≤ (0.00000000064498 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2725 : ℝ) (2750 : ℝ) 2 3934 2.3455e-13
    (0.00000000064498 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2725_a2_le row2725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2725_2_lt, exp_neg_5450_3_lt,
                   Real.exp_pos (-(2725/2:ℝ)), Real.exp_pos (-(5450/3:ℝ))])


/-- Row 2725 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2725_k2_margin :
    B_8_exact 2 (2725 : ℝ) (2750 : ℝ) ≤ (0.0000017737 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2725 : ℝ) (2750 : ℝ) 2 3934 2.3455e-13
    (0.0000017737 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2725_a2_le row2725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2725_2_lt, exp_neg_5450_3_lt,
                   Real.exp_pos (-(2725/2:ℝ)), Real.exp_pos (-(5450/3:ℝ))])


/-- Row 2725 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2725_k3_margin :
    B_8_exact 3 (2725 : ℝ) (2750 : ℝ) ≤ (0.0048777 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2725 : ℝ) (2750 : ℝ) 2 3934 2.3455e-13
    (0.0048777 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2725_a2_le row2725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2725_2_lt, exp_neg_5450_3_lt,
                   Real.exp_pos (-(2725/2:ℝ)), Real.exp_pos (-(5450/3:ℝ))])


/-- Row 2725 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2725_k4_margin :
    B_8_exact 4 (2725 : ℝ) (2750 : ℝ) ≤ (13.414 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2725 : ℝ) (2750 : ℝ) 2 3934 2.3455e-13
    (13.414 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2725_a2_le row2725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2725_2_lt, exp_neg_5450_3_lt,
                   Real.exp_pos (-(2725/2:ℝ)), Real.exp_pos (-(5450/3:ℝ))])


/-- Row 2725 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2725_k5_margin :
    B_8_exact 5 (2725 : ℝ) (2750 : ℝ) ≤ (36887 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2725 : ℝ) (2750 : ℝ) 2 3934 2.3455e-13
    (36887 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2725_a2_le row2725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2725_2_lt, exp_neg_5450_3_lt,
                   Real.exp_pos (-(2725/2:ℝ)), Real.exp_pos (-(5450/3:ℝ))])


/-- Row 2750 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2750_k1_margin :
    B_8_exact 1 (2750 : ℝ) (2775 : ℝ) ≤ (0.00000000056071 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2750 : ℝ) (2775 : ℝ) 2 3970 2.0207e-13
    (0.00000000056071 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2750_a2_le row2750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1375_lt, exp_neg_5500_3_lt,
                   Real.exp_pos (-(1375:ℝ)), Real.exp_pos (-(5500/3:ℝ))])


/-- Row 2750 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2750_k2_margin :
    B_8_exact 2 (2750 : ℝ) (2775 : ℝ) ≤ (0.0000015560 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2750 : ℝ) (2775 : ℝ) 2 3970 2.0207e-13
    (0.0000015560 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2750_a2_le row2750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1375_lt, exp_neg_5500_3_lt,
                   Real.exp_pos (-(1375:ℝ)), Real.exp_pos (-(5500/3:ℝ))])


/-- Row 2750 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2750_k3_margin :
    B_8_exact 3 (2750 : ℝ) (2775 : ℝ) ≤ (0.0043178 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2750 : ℝ) (2775 : ℝ) 2 3970 2.0207e-13
    (0.0043178 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2750_a2_le row2750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1375_lt, exp_neg_5500_3_lt,
                   Real.exp_pos (-(1375:ℝ)), Real.exp_pos (-(5500/3:ℝ))])


/-- Row 2750 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2750_k4_margin :
    B_8_exact 4 (2750 : ℝ) (2775 : ℝ) ≤ (11.982 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2750 : ℝ) (2775 : ℝ) 2 3970 2.0207e-13
    (11.982 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2750_a2_le row2750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1375_lt, exp_neg_5500_3_lt,
                   Real.exp_pos (-(1375:ℝ)), Real.exp_pos (-(5500/3:ℝ))])


/-- Row 2750 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2750_k5_margin :
    B_8_exact 5 (2750 : ℝ) (2775 : ℝ) ≤ (33250 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2750 : ℝ) (2775 : ℝ) 2 3970 2.0207e-13
    (33250 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2750_a2_le row2750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1375_lt, exp_neg_5500_3_lt,
                   Real.exp_pos (-(1375:ℝ)), Real.exp_pos (-(5500/3:ℝ))])


/-- Row 2775 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2775_k1_margin :
    B_8_exact 1 (2775 : ℝ) (2800 : ℝ) ≤ (0.00000000048730 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2775 : ℝ) (2800 : ℝ) 2 4006 1.7404e-13
    (0.00000000048730 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2775_a2_le row2775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2775_2_lt, exp_neg_1850_lt,
                   Real.exp_pos (-(2775/2:ℝ)), Real.exp_pos (-(1850:ℝ))])


/-- Row 2775 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2775_k2_margin :
    B_8_exact 2 (2775 : ℝ) (2800 : ℝ) ≤ (0.0000013644 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2775 : ℝ) (2800 : ℝ) 2 4006 1.7404e-13
    (0.0000013644 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2775_a2_le row2775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2775_2_lt, exp_neg_1850_lt,
                   Real.exp_pos (-(2775/2:ℝ)), Real.exp_pos (-(1850:ℝ))])


/-- Row 2775 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2775_k3_margin :
    B_8_exact 3 (2775 : ℝ) (2800 : ℝ) ≤ (0.0038204 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2775 : ℝ) (2800 : ℝ) 2 4006 1.7404e-13
    (0.0038204 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2775_a2_le row2775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2775_2_lt, exp_neg_1850_lt,
                   Real.exp_pos (-(2775/2:ℝ)), Real.exp_pos (-(1850:ℝ))])


/-- Row 2775 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2775_k4_margin :
    B_8_exact 4 (2775 : ℝ) (2800 : ℝ) ≤ (10.697 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2775 : ℝ) (2800 : ℝ) 2 4006 1.7404e-13
    (10.697 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2775_a2_le row2775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2775_2_lt, exp_neg_1850_lt,
                   Real.exp_pos (-(2775/2:ℝ)), Real.exp_pos (-(1850:ℝ))])


/-- Row 2775 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2775_k5_margin :
    B_8_exact 5 (2775 : ℝ) (2800 : ℝ) ≤ (29952 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2775 : ℝ) (2800 : ℝ) 2 4006 1.7404e-13
    (29952 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2775_a2_le row2775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2775_2_lt, exp_neg_1850_lt,
                   Real.exp_pos (-(2775/2:ℝ)), Real.exp_pos (-(1850:ℝ))])


/-- Row 2800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2800_k1_margin :
    B_8_exact 1 (2800 : ℝ) (2825 : ℝ) ≤ (0.00000000042388 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2800 : ℝ) (2825 : ℝ) 2 4042 1.5006e-13
    (0.00000000042388 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2800_a2_le row2800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1400_lt, exp_neg_5600_3_lt,
                   Real.exp_pos (-(1400:ℝ)), Real.exp_pos (-(5600/3:ℝ))])


/-- Row 2800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2800_k2_margin :
    B_8_exact 2 (2800 : ℝ) (2825 : ℝ) ≤ (0.0000011975 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2800 : ℝ) (2825 : ℝ) 2 4042 1.5006e-13
    (0.0000011975 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2800_a2_le row2800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1400_lt, exp_neg_5600_3_lt,
                   Real.exp_pos (-(1400:ℝ)), Real.exp_pos (-(5600/3:ℝ))])


/-- Row 2800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2800_k3_margin :
    B_8_exact 3 (2800 : ℝ) (2825 : ℝ) ≤ (0.0033829 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2800 : ℝ) (2825 : ℝ) 2 4042 1.5006e-13
    (0.0033829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2800_a2_le row2800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1400_lt, exp_neg_5600_3_lt,
                   Real.exp_pos (-(1400:ℝ)), Real.exp_pos (-(5600/3:ℝ))])


/-- Row 2800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2800_k4_margin :
    B_8_exact 4 (2800 : ℝ) (2825 : ℝ) ≤ (9.5565 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2800 : ℝ) (2825 : ℝ) 2 4042 1.5006e-13
    (9.5565 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2800_a2_le row2800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1400_lt, exp_neg_5600_3_lt,
                   Real.exp_pos (-(1400:ℝ)), Real.exp_pos (-(5600/3:ℝ))])


/-- Row 2800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2800_k5_margin :
    B_8_exact 5 (2800 : ℝ) (2825 : ℝ) ≤ (26997 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2800 : ℝ) (2825 : ℝ) 2 4042 1.5006e-13
    (26997 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2800_a2_le row2800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1400_lt, exp_neg_5600_3_lt,
                   Real.exp_pos (-(1400:ℝ)), Real.exp_pos (-(5600/3:ℝ))])


/-- Row 2825 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2825_k1_margin :
    B_8_exact 1 (2825 : ℝ) (2850 : ℝ) ≤ (0.00000000036911 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2825 : ℝ) (2850 : ℝ) 2 4078 1.2952e-13
    (0.00000000036911 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2825_a2_le row2825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2825_2_lt, exp_neg_5650_3_lt,
                   Real.exp_pos (-(2825/2:ℝ)), Real.exp_pos (-(5650/3:ℝ))])


/-- Row 2825 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2825_k2_margin :
    B_8_exact 2 (2825 : ℝ) (2850 : ℝ) ≤ (0.0000010520 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2825 : ℝ) (2850 : ℝ) 2 4078 1.2952e-13
    (0.0000010520 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2825_a2_le row2825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2825_2_lt, exp_neg_5650_3_lt,
                   Real.exp_pos (-(2825/2:ℝ)), Real.exp_pos (-(5650/3:ℝ))])


/-- Row 2825 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2825_k3_margin :
    B_8_exact 3 (2825 : ℝ) (2850 : ℝ) ≤ (0.0029981 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2825 : ℝ) (2850 : ℝ) 2 4078 1.2952e-13
    (0.0029981 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2825_a2_le row2825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2825_2_lt, exp_neg_5650_3_lt,
                   Real.exp_pos (-(2825/2:ℝ)), Real.exp_pos (-(5650/3:ℝ))])


/-- Row 2825 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2825_k4_margin :
    B_8_exact 4 (2825 : ℝ) (2850 : ℝ) ≤ (8.5446 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2825 : ℝ) (2850 : ℝ) 2 4078 1.2952e-13
    (8.5446 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2825_a2_le row2825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2825_2_lt, exp_neg_5650_3_lt,
                   Real.exp_pos (-(2825/2:ℝ)), Real.exp_pos (-(5650/3:ℝ))])


/-- Row 2825 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2825_k5_margin :
    B_8_exact 5 (2825 : ℝ) (2850 : ℝ) ≤ (24352 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2825 : ℝ) (2850 : ℝ) 2 4078 1.2952e-13
    (24352 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2825_a2_le row2825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2825_2_lt, exp_neg_5650_3_lt,
                   Real.exp_pos (-(2825/2:ℝ)), Real.exp_pos (-(5650/3:ℝ))])


/-- Row 2850 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2850_k1_margin :
    B_8_exact 1 (2850 : ℝ) (2875 : ℝ) ≤ (0.00000000032167 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2850 : ℝ) (2875 : ℝ) 2 4114 1.1190e-13
    (0.00000000032167 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2850_a2_le row2850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1425_lt, exp_neg_1900_lt,
                   Real.exp_pos (-(1425:ℝ)), Real.exp_pos (-(1900:ℝ))])


/-- Row 2850 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2850_k2_margin :
    B_8_exact 2 (2850 : ℝ) (2875 : ℝ) ≤ (0.00000092481 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2850 : ℝ) (2875 : ℝ) 2 4114 1.1190e-13
    (0.00000092481 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2850_a2_le row2850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1425_lt, exp_neg_1900_lt,
                   Real.exp_pos (-(1425:ℝ)), Real.exp_pos (-(1900:ℝ))])


/-- Row 2850 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2850_k3_margin :
    B_8_exact 3 (2850 : ℝ) (2875 : ℝ) ≤ (0.0026588 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2850 : ℝ) (2875 : ℝ) 2 4114 1.1190e-13
    (0.0026588 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2850_a2_le row2850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1425_lt, exp_neg_1900_lt,
                   Real.exp_pos (-(1425:ℝ)), Real.exp_pos (-(1900:ℝ))])


/-- Row 2850 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2850_k4_margin :
    B_8_exact 4 (2850 : ℝ) (2875 : ℝ) ≤ (7.6442 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2850 : ℝ) (2875 : ℝ) 2 4114 1.1190e-13
    (7.6442 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2850_a2_le row2850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1425_lt, exp_neg_1900_lt,
                   Real.exp_pos (-(1425:ℝ)), Real.exp_pos (-(1900:ℝ))])


/-- Row 2850 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2850_k5_margin :
    B_8_exact 5 (2850 : ℝ) (2875 : ℝ) ≤ (21977 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2850 : ℝ) (2875 : ℝ) 2 4114 1.1190e-13
    (21977 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2850_a2_le row2850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1425_lt, exp_neg_1900_lt,
                   Real.exp_pos (-(1425:ℝ)), Real.exp_pos (-(1900:ℝ))])


/-- Row 2875 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2875_k1_margin :
    B_8_exact 1 (2875 : ℝ) (2900 : ℝ) ≤ (0.00000000027953 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2875 : ℝ) (2900 : ℝ) 2 4150 9.6389e-14
    (0.00000000027953 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2875_a2_le row2875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2875_2_lt, exp_neg_5750_3_lt,
                   Real.exp_pos (-(2875/2:ℝ)), Real.exp_pos (-(5750/3:ℝ))])


/-- Row 2875 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2875_k2_margin :
    B_8_exact 2 (2875 : ℝ) (2900 : ℝ) ≤ (0.00000081062 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2875 : ℝ) (2900 : ℝ) 2 4150 9.6389e-14
    (0.00000081062 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2875_a2_le row2875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2875_2_lt, exp_neg_5750_3_lt,
                   Real.exp_pos (-(2875/2:ℝ)), Real.exp_pos (-(5750/3:ℝ))])


/-- Row 2875 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2875_k3_margin :
    B_8_exact 3 (2875 : ℝ) (2900 : ℝ) ≤ (0.0023508 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2875 : ℝ) (2900 : ℝ) 2 4150 9.6389e-14
    (0.0023508 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2875_a2_le row2875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2875_2_lt, exp_neg_5750_3_lt,
                   Real.exp_pos (-(2875/2:ℝ)), Real.exp_pos (-(5750/3:ℝ))])


/-- Row 2875 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2875_k4_margin :
    B_8_exact 4 (2875 : ℝ) (2900 : ℝ) ≤ (6.8173 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2875 : ℝ) (2900 : ℝ) 2 4150 9.6389e-14
    (6.8173 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2875_a2_le row2875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2875_2_lt, exp_neg_5750_3_lt,
                   Real.exp_pos (-(2875/2:ℝ)), Real.exp_pos (-(5750/3:ℝ))])


/-- Row 2875 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2875_k5_margin :
    B_8_exact 5 (2875 : ℝ) (2900 : ℝ) ≤ (19770 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2875 : ℝ) (2900 : ℝ) 2 4150 9.6389e-14
    (19770 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2875_a2_le row2875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2875_2_lt, exp_neg_5750_3_lt,
                   Real.exp_pos (-(2875/2:ℝ)), Real.exp_pos (-(5750/3:ℝ))])

end BKLNW
