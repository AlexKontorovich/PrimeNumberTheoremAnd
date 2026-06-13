import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Generated regime-3 pointwise Table 10 margin certificates.

This shard expects `row_bound_pointwise`
to be available from `BKLNW_table10_rows_core.lean`.
-/

namespace BKLNW

open Real Set Finset

/-! ## Cached exp(-x) bounds shared across this file's k-margin theorems. -/

private lemma exp_neg_2450_lt : Real.exp (-(2450 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_4925_2_lt : Real.exp (-(4925/2 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2475_lt : Real.exp (-(2475 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_4975_2_lt : Real.exp (-(4975/2 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2500_lt : Real.exp (-(2500 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2550_lt : Real.exp (-(2550 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2600_lt : Real.exp (-(2600 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2650_lt : Real.exp (-(2650 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2700_lt : Real.exp (-(2700 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2750_lt : Real.exp (-(2750 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2800_lt : Real.exp (-(2800 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2850_lt : Real.exp (-(2850 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2900_lt : Real.exp (-(2900 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_2950_lt : Real.exp (-(2950 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3000_lt : Real.exp (-(3000 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3050_lt : Real.exp (-(3050 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3100_lt : Real.exp (-(3100 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3150_lt : Real.exp (-(3150 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3200_lt : Real.exp (-(3200 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3250_lt : Real.exp (-(3250 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_9800_3_lt : Real.exp (-(9800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_9850_3_lt : Real.exp (-(9850/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3300_lt : Real.exp (-(3300 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_9950_3_lt : Real.exp (-(9950/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_10000_3_lt : Real.exp (-(10000/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3400_lt : Real.exp (-(3400 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_10400_3_lt : Real.exp (-(10400/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_10600_3_lt : Real.exp (-(10600/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3600_lt : Real.exp (-(3600 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_11000_3_lt : Real.exp (-(11000/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_11200_3_lt : Real.exp (-(11200/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_3800_lt : Real.exp (-(3800 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_11600_3_lt : Real.exp (-(11600/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_11800_3_lt : Real.exp (-(11800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_4000_lt : Real.exp (-(4000 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_12200_3_lt : Real.exp (-(12200/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_12400_3_lt : Real.exp (-(12400/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_4200_lt : Real.exp (-(4200 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_12800_3_lt : Real.exp (-(12800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_13000_3_lt : Real.exp (-(13000/3 : ℝ)) < 1e-100 := by interval_decide



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


private lemma row4900_a2_le : Inputs.default.a₂ (4900 : ℝ) ≤ (7072 : ℝ) := by
  have h := a2_crude_le (4900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4900 : ℝ) / log 2⌋₊ : ℝ) ≤ (4900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4900 : ℝ) / log 2 ≤ 7070 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7070 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7072 := by norm_num


private lemma row4925_a2_le : Inputs.default.a₂ (4925 : ℝ) ≤ (7108 : ℝ) := by
  have h := a2_crude_le (4925 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4925 : ℝ) / log 2⌋₊ : ℝ) ≤ (4925 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4925 : ℝ) / log 2 ≤ 7106 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4925 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4925 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7106 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7108 := by norm_num


private lemma row4950_a2_le : Inputs.default.a₂ (4950 : ℝ) ≤ (7144 : ℝ) := by
  have h := a2_crude_le (4950 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4950 : ℝ) / log 2⌋₊ : ℝ) ≤ (4950 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4950 : ℝ) / log 2 ≤ 7142 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4950 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4950 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7142 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7144 := by norm_num


private lemma row4975_a2_le : Inputs.default.a₂ (4975 : ℝ) ≤ (7180 : ℝ) := by
  have h := a2_crude_le (4975 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4975 : ℝ) / log 2⌋₊ : ℝ) ≤ (4975 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4975 : ℝ) / log 2 ≤ 7178 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4975 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4975 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7178 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7180 := by norm_num


private lemma row5000_a2_le : Inputs.default.a₂ (5000 : ℝ) ≤ (7216 : ℝ) := by
  have h := a2_crude_le (5000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5000 : ℝ) / log 2⌋₊ : ℝ) ≤ (5000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5000 : ℝ) / log 2 ≤ 7214 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7214 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7216 := by norm_num


private lemma row5100_a2_le : Inputs.default.a₂ (5100 : ℝ) ≤ (7360 : ℝ) := by
  have h := a2_crude_le (5100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5100 : ℝ) / log 2⌋₊ : ℝ) ≤ (5100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5100 : ℝ) / log 2 ≤ 7358 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7358 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7360 := by norm_num


private lemma row5200_a2_le : Inputs.default.a₂ (5200 : ℝ) ≤ (7505 : ℝ) := by
  have h := a2_crude_le (5200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5200 : ℝ) / log 2⌋₊ : ℝ) ≤ (5200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5200 : ℝ) / log 2 ≤ 7503 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7503 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7505 := by norm_num


private lemma row5300_a2_le : Inputs.default.a₂ (5300 : ℝ) ≤ (7649 : ℝ) := by
  have h := a2_crude_le (5300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5300 : ℝ) / log 2⌋₊ : ℝ) ≤ (5300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5300 : ℝ) / log 2 ≤ 7647 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7647 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7649 := by norm_num


private lemma row5400_a2_le : Inputs.default.a₂ (5400 : ℝ) ≤ (7793 : ℝ) := by
  have h := a2_crude_le (5400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5400 : ℝ) / log 2⌋₊ : ℝ) ≤ (5400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5400 : ℝ) / log 2 ≤ 7791 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7791 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7793 := by norm_num


private lemma row5500_a2_le : Inputs.default.a₂ (5500 : ℝ) ≤ (7937 : ℝ) := by
  have h := a2_crude_le (5500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5500 : ℝ) / log 2⌋₊ : ℝ) ≤ (5500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5500 : ℝ) / log 2 ≤ 7935 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7935 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7937 := by norm_num


private lemma row5600_a2_le : Inputs.default.a₂ (5600 : ℝ) ≤ (8082 : ℝ) := by
  have h := a2_crude_le (5600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5600 : ℝ) / log 2⌋₊ : ℝ) ≤ (5600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5600 : ℝ) / log 2 ≤ 8080 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8080 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8082 := by norm_num


private lemma row5700_a2_le : Inputs.default.a₂ (5700 : ℝ) ≤ (8226 : ℝ) := by
  have h := a2_crude_le (5700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5700 : ℝ) / log 2⌋₊ : ℝ) ≤ (5700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5700 : ℝ) / log 2 ≤ 8224 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8224 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8226 := by norm_num


private lemma row5800_a2_le : Inputs.default.a₂ (5800 : ℝ) ≤ (8370 : ℝ) := by
  have h := a2_crude_le (5800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5800 : ℝ) / log 2⌋₊ : ℝ) ≤ (5800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5800 : ℝ) / log 2 ≤ 8368 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8368 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8370 := by norm_num


private lemma row5900_a2_le : Inputs.default.a₂ (5900 : ℝ) ≤ (8514 : ℝ) := by
  have h := a2_crude_le (5900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(5900 : ℝ) / log 2⌋₊ : ℝ) ≤ (5900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (5900 : ℝ) / log 2 ≤ 8512 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (5900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(5900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8512 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8514 := by norm_num


private lemma row6000_a2_le : Inputs.default.a₂ (6000 : ℝ) ≤ (8659 : ℝ) := by
  have h := a2_crude_le (6000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6000 : ℝ) / log 2⌋₊ : ℝ) ≤ (6000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6000 : ℝ) / log 2 ≤ 8657 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8657 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8659 := by norm_num


private lemma row6100_a2_le : Inputs.default.a₂ (6100 : ℝ) ≤ (8803 : ℝ) := by
  have h := a2_crude_le (6100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6100 : ℝ) / log 2⌋₊ : ℝ) ≤ (6100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6100 : ℝ) / log 2 ≤ 8801 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8801 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8803 := by norm_num


private lemma row6200_a2_le : Inputs.default.a₂ (6200 : ℝ) ≤ (8947 : ℝ) := by
  have h := a2_crude_le (6200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6200 : ℝ) / log 2⌋₊ : ℝ) ≤ (6200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6200 : ℝ) / log 2 ≤ 8945 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (8945 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 8947 := by norm_num


private lemma row6300_a2_le : Inputs.default.a₂ (6300 : ℝ) ≤ (9091 : ℝ) := by
  have h := a2_crude_le (6300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6300 : ℝ) / log 2⌋₊ : ℝ) ≤ (6300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6300 : ℝ) / log 2 ≤ 9089 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9089 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9091 := by norm_num


private lemma row6400_a2_le : Inputs.default.a₂ (6400 : ℝ) ≤ (9236 : ℝ) := by
  have h := a2_crude_le (6400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6400 : ℝ) / log 2⌋₊ : ℝ) ≤ (6400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6400 : ℝ) / log 2 ≤ 9234 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9234 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9236 := by norm_num


private lemma row6500_a2_le : Inputs.default.a₂ (6500 : ℝ) ≤ (9380 : ℝ) := by
  have h := a2_crude_le (6500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6500 : ℝ) / log 2⌋₊ : ℝ) ≤ (6500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6500 : ℝ) / log 2 ≤ 9378 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9378 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9380 := by norm_num


set_option maxRecDepth 10000 in
private lemma row4900_table8_mem : (4900, 9.6895e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4900_eps_le : Inputs.default.ε (4900 : ℝ) ≤ 9.6895e-19 := by
  change BKLNW_app.table_8_ε (4900 : ℝ) ≤ 9.6895e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4900)
    (ε := 9.6895e-19) row4900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4925_table8_mem : (4925, 8.4602e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4925_eps_le : Inputs.default.ε (4925 : ℝ) ≤ 8.4602e-19 := by
  change BKLNW_app.table_8_ε (4925 : ℝ) ≤ 8.4602e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4925)
    (ε := 8.4602e-19) row4925_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4950_table8_mem : (4950, 7.3831e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4950_eps_le : Inputs.default.ε (4950 : ℝ) ≤ 7.3831e-19 := by
  change BKLNW_app.table_8_ε (4950 : ℝ) ≤ 7.3831e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4950)
    (ε := 7.3831e-19) row4950_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4975_table8_mem : (4975, 6.4458e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4975_eps_le : Inputs.default.ε (4975 : ℝ) ≤ 6.4458e-19 := by
  change BKLNW_app.table_8_ε (4975 : ℝ) ≤ 6.4458e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4975)
    (ε := 6.4458e-19) row4975_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5000_table8_mem : (5000, 5.6304e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5000_eps_le : Inputs.default.ε (5000 : ℝ) ≤ 5.6304e-19 := by
  change BKLNW_app.table_8_ε (5000 : ℝ) ≤ 5.6304e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5000)
    (ε := 5.6304e-19) row5000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5100_table8_mem : (5100, 3.2860e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5100_eps_le : Inputs.default.ε (5100 : ℝ) ≤ 3.2860e-19 := by
  change BKLNW_app.table_8_ε (5100 : ℝ) ≤ 3.2860e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5100)
    (ε := 3.2860e-19) row5100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5200_table8_mem : (5200, 1.9218e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5200_eps_le : Inputs.default.ε (5200 : ℝ) ≤ 1.9218e-19 := by
  change BKLNW_app.table_8_ε (5200 : ℝ) ≤ 1.9218e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5200)
    (ε := 1.9218e-19) row5200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5300_table8_mem : (5300, 1.1293e-19) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5300_eps_le : Inputs.default.ε (5300 : ℝ) ≤ 1.1293e-19 := by
  change BKLNW_app.table_8_ε (5300 : ℝ) ≤ 1.1293e-19
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5300)
    (ε := 1.1293e-19) row5300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5400_table8_mem : (5400, 6.6313e-20) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5400_eps_le : Inputs.default.ε (5400 : ℝ) ≤ 6.6313e-20 := by
  change BKLNW_app.table_8_ε (5400 : ℝ) ≤ 6.6313e-20
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5400)
    (ε := 6.6313e-20) row5400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5500_table8_mem : (5500, 3.9136e-20) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5500_eps_le : Inputs.default.ε (5500 : ℝ) ≤ 3.9136e-20 := by
  change BKLNW_app.table_8_ε (5500 : ℝ) ≤ 3.9136e-20
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5500)
    (ε := 3.9136e-20) row5500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5600_table8_mem : (5600, 2.3189e-20) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5600_eps_le : Inputs.default.ε (5600 : ℝ) ≤ 2.3189e-20 := by
  change BKLNW_app.table_8_ε (5600 : ℝ) ≤ 2.3189e-20
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5600)
    (ε := 2.3189e-20) row5600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5700_table8_mem : (5700, 1.3808e-20) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5700_eps_le : Inputs.default.ε (5700 : ℝ) ≤ 1.3808e-20 := by
  change BKLNW_app.table_8_ε (5700 : ℝ) ≤ 1.3808e-20
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5700)
    (ε := 1.3808e-20) row5700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5800_table8_mem : (5800, 8.2235e-21) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5800_eps_le : Inputs.default.ε (5800 : ℝ) ≤ 8.2235e-21 := by
  change BKLNW_app.table_8_ε (5800 : ℝ) ≤ 8.2235e-21
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5800)
    (ε := 8.2235e-21) row5800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row5900_table8_mem : (5900, 4.9138e-21) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row5900_eps_le : Inputs.default.ε (5900 : ℝ) ≤ 4.9138e-21 := by
  change BKLNW_app.table_8_ε (5900 : ℝ) ≤ 4.9138e-21
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 5900)
    (ε := 4.9138e-21) row5900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6000_table8_mem : (6000, 2.9430e-21) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6000_eps_le : Inputs.default.ε (6000 : ℝ) ≤ 2.9430e-21 := by
  change BKLNW_app.table_8_ε (6000 : ℝ) ≤ 2.9430e-21
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6000)
    (ε := 2.9430e-21) row6000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6100_table8_mem : (6100, 1.7722e-21) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6100_eps_le : Inputs.default.ε (6100 : ℝ) ≤ 1.7722e-21 := by
  change BKLNW_app.table_8_ε (6100 : ℝ) ≤ 1.7722e-21
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6100)
    (ε := 1.7722e-21) row6100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6200_table8_mem : (6200, 1.0664e-21) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6200_eps_le : Inputs.default.ε (6200 : ℝ) ≤ 1.0664e-21 := by
  change BKLNW_app.table_8_ε (6200 : ℝ) ≤ 1.0664e-21
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6200)
    (ε := 1.0664e-21) row6200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6300_table8_mem : (6300, 6.4481e-22) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6300_eps_le : Inputs.default.ε (6300 : ℝ) ≤ 6.4481e-22 := by
  change BKLNW_app.table_8_ε (6300 : ℝ) ≤ 6.4481e-22
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6300)
    (ε := 6.4481e-22) row6300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6400_table8_mem : (6400, 3.9202e-22) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6400_eps_le : Inputs.default.ε (6400 : ℝ) ≤ 3.9202e-22 := by
  change BKLNW_app.table_8_ε (6400 : ℝ) ≤ 3.9202e-22
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6400)
    (ε := 3.9202e-22) row6400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6500_table8_mem : (6500, 2.3850e-22) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6500_eps_le : Inputs.default.ε (6500 : ℝ) ≤ 2.3850e-22 := by
  change BKLNW_app.table_8_ε (6500 : ℝ) ≤ 2.3850e-22
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6500)
    (ε := 2.3850e-22) row6500_table8_mem (by norm_num)


/-- Row 4900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4900_k1_margin :
    B_8_exact 1 (4900 : ℝ) (4925 : ℝ) ≤ (0.0000000000000047720 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4900 : ℝ) (4925 : ℝ) 2 7072 9.6895e-19
    (0.0000000000000047720 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4900_a2_le row4900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2450_lt, exp_neg_9800_3_lt,
                   Real.exp_pos (-(2450:ℝ)), Real.exp_pos (-(9800/3:ℝ))])


/-- Row 4900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4900_k2_margin :
    B_8_exact 2 (4900 : ℝ) (4925 : ℝ) ≤ (0.000000000023502 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4900 : ℝ) (4925 : ℝ) 2 7072 9.6895e-19
    (0.000000000023502 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4900_a2_le row4900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2450_lt, exp_neg_9800_3_lt,
                   Real.exp_pos (-(2450:ℝ)), Real.exp_pos (-(9800/3:ℝ))])


/-- Row 4900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4900_k3_margin :
    B_8_exact 3 (4900 : ℝ) (4925 : ℝ) ≤ (0.00000011575 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4900 : ℝ) (4925 : ℝ) 2 7072 9.6895e-19
    (0.00000011575 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4900_a2_le row4900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2450_lt, exp_neg_9800_3_lt,
                   Real.exp_pos (-(2450:ℝ)), Real.exp_pos (-(9800/3:ℝ))])


/-- Row 4900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4900_k4_margin :
    B_8_exact 4 (4900 : ℝ) (4925 : ℝ) ≤ (0.00057006 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4900 : ℝ) (4925 : ℝ) 2 7072 9.6895e-19
    (0.00057006 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4900_a2_le row4900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2450_lt, exp_neg_9800_3_lt,
                   Real.exp_pos (-(2450:ℝ)), Real.exp_pos (-(9800/3:ℝ))])


/-- Row 4900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4900_k5_margin :
    B_8_exact 5 (4900 : ℝ) (4925 : ℝ) ≤ (2.8076 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4900 : ℝ) (4925 : ℝ) 2 7072 9.6895e-19
    (2.8076 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4900_a2_le row4900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2450_lt, exp_neg_9800_3_lt,
                   Real.exp_pos (-(2450:ℝ)), Real.exp_pos (-(9800/3:ℝ))])


/-- Row 4925 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4925_k1_margin :
    B_8_exact 1 (4925 : ℝ) (4950 : ℝ) ≤ (0.0000000000000041878 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4925 : ℝ) (4950 : ℝ) 2 7108 8.4602e-19
    (0.0000000000000041878 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4925_a2_le row4925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4925_2_lt, exp_neg_9850_3_lt,
                   Real.exp_pos (-(4925/2:ℝ)), Real.exp_pos (-(9850/3:ℝ))])


/-- Row 4925 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4925_k2_margin :
    B_8_exact 2 (4925 : ℝ) (4950 : ℝ) ≤ (0.000000000020729 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4925 : ℝ) (4950 : ℝ) 2 7108 8.4602e-19
    (0.000000000020729 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4925_a2_le row4925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4925_2_lt, exp_neg_9850_3_lt,
                   Real.exp_pos (-(4925/2:ℝ)), Real.exp_pos (-(9850/3:ℝ))])


/-- Row 4925 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4925_k3_margin :
    B_8_exact 3 (4925 : ℝ) (4950 : ℝ) ≤ (0.00000010261 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4925 : ℝ) (4950 : ℝ) 2 7108 8.4602e-19
    (0.00000010261 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4925_a2_le row4925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4925_2_lt, exp_neg_9850_3_lt,
                   Real.exp_pos (-(4925/2:ℝ)), Real.exp_pos (-(9850/3:ℝ))])


/-- Row 4925 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4925_k4_margin :
    B_8_exact 4 (4925 : ℝ) (4950 : ℝ) ≤ (0.00050792 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4925 : ℝ) (4950 : ℝ) 2 7108 8.4602e-19
    (0.00050792 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4925_a2_le row4925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4925_2_lt, exp_neg_9850_3_lt,
                   Real.exp_pos (-(4925/2:ℝ)), Real.exp_pos (-(9850/3:ℝ))])


/-- Row 4925 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4925_k5_margin :
    B_8_exact 5 (4925 : ℝ) (4950 : ℝ) ≤ (2.5142 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4925 : ℝ) (4950 : ℝ) 2 7108 8.4602e-19
    (2.5142 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4925_a2_le row4925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4925_2_lt, exp_neg_9850_3_lt,
                   Real.exp_pos (-(4925/2:ℝ)), Real.exp_pos (-(9850/3:ℝ))])


/-- Row 4950 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4950_k1_margin :
    B_8_exact 1 (4950 : ℝ) (4975 : ℝ) ≤ (0.0000000000000036731 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4950 : ℝ) (4975 : ℝ) 2 7144 7.3831e-19
    (0.0000000000000036731 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4950_a2_le row4950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_lt, exp_neg_3300_lt,
                   Real.exp_pos (-(2475:ℝ)), Real.exp_pos (-(3300:ℝ))])


/-- Row 4950 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4950_k2_margin :
    B_8_exact 2 (4950 : ℝ) (4975 : ℝ) ≤ (0.000000000018274 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4950 : ℝ) (4975 : ℝ) 2 7144 7.3831e-19
    (0.000000000018274 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4950_a2_le row4950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_lt, exp_neg_3300_lt,
                   Real.exp_pos (-(2475:ℝ)), Real.exp_pos (-(3300:ℝ))])


/-- Row 4950 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4950_k3_margin :
    B_8_exact 3 (4950 : ℝ) (4975 : ℝ) ≤ (0.000000090911 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4950 : ℝ) (4975 : ℝ) 2 7144 7.3831e-19
    (0.000000090911 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4950_a2_le row4950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_lt, exp_neg_3300_lt,
                   Real.exp_pos (-(2475:ℝ)), Real.exp_pos (-(3300:ℝ))])


/-- Row 4950 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4950_k4_margin :
    B_8_exact 4 (4950 : ℝ) (4975 : ℝ) ≤ (0.00045228 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4950 : ℝ) (4975 : ℝ) 2 7144 7.3831e-19
    (0.00045228 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4950_a2_le row4950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_lt, exp_neg_3300_lt,
                   Real.exp_pos (-(2475:ℝ)), Real.exp_pos (-(3300:ℝ))])


/-- Row 4950 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4950_k5_margin :
    B_8_exact 5 (4950 : ℝ) (4975 : ℝ) ≤ (2.2501 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4950 : ℝ) (4975 : ℝ) 2 7144 7.3831e-19
    (2.2501 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4950_a2_le row4950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2475_lt, exp_neg_3300_lt,
                   Real.exp_pos (-(2475:ℝ)), Real.exp_pos (-(3300:ℝ))])


/-- Row 4975 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4975_k1_margin :
    B_8_exact 1 (4975 : ℝ) (5000 : ℝ) ≤ (0.0000000000000032229 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4975 : ℝ) (5000 : ℝ) 2 7180 6.4458e-19
    (0.0000000000000032229 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4975_a2_le row4975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4975_2_lt, exp_neg_9950_3_lt,
                   Real.exp_pos (-(4975/2:ℝ)), Real.exp_pos (-(9950/3:ℝ))])


/-- Row 4975 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4975_k2_margin :
    B_8_exact 2 (4975 : ℝ) (5000 : ℝ) ≤ (0.000000000016114 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4975 : ℝ) (5000 : ℝ) 2 7180 6.4458e-19
    (0.000000000016114 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4975_a2_le row4975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4975_2_lt, exp_neg_9950_3_lt,
                   Real.exp_pos (-(4975/2:ℝ)), Real.exp_pos (-(9950/3:ℝ))])


/-- Row 4975 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4975_k3_margin :
    B_8_exact 3 (4975 : ℝ) (5000 : ℝ) ≤ (0.000000080571 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4975 : ℝ) (5000 : ℝ) 2 7180 6.4458e-19
    (0.000000080571 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4975_a2_le row4975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4975_2_lt, exp_neg_9950_3_lt,
                   Real.exp_pos (-(4975/2:ℝ)), Real.exp_pos (-(9950/3:ℝ))])


/-- Row 4975 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4975_k4_margin :
    B_8_exact 4 (4975 : ℝ) (5000 : ℝ) ≤ (0.00040286 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4975 : ℝ) (5000 : ℝ) 2 7180 6.4458e-19
    (0.00040286 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4975_a2_le row4975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4975_2_lt, exp_neg_9950_3_lt,
                   Real.exp_pos (-(4975/2:ℝ)), Real.exp_pos (-(9950/3:ℝ))])


/-- Row 4975 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4975_k5_margin :
    B_8_exact 5 (4975 : ℝ) (5000 : ℝ) ≤ (2.0143 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4975 : ℝ) (5000 : ℝ) 2 7180 6.4458e-19
    (2.0143 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4975_a2_le row4975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4975_2_lt, exp_neg_9950_3_lt,
                   Real.exp_pos (-(4975/2:ℝ)), Real.exp_pos (-(9950/3:ℝ))])


/-- Row 5000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5000_k1_margin :
    B_8_exact 1 (5000 : ℝ) (5100 : ℝ) ≤ (0.0000000000000028715 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5000 : ℝ) (5100 : ℝ) 2 7216 5.6304e-19
    (0.0000000000000028715 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5000_a2_le row5000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2500_lt, exp_neg_10000_3_lt,
                   Real.exp_pos (-(2500:ℝ)), Real.exp_pos (-(10000/3:ℝ))])


/-- Row 5000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5000_k2_margin :
    B_8_exact 2 (5000 : ℝ) (5100 : ℝ) ≤ (0.000000000014645 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5000 : ℝ) (5100 : ℝ) 2 7216 5.6304e-19
    (0.000000000014645 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5000_a2_le row5000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2500_lt, exp_neg_10000_3_lt,
                   Real.exp_pos (-(2500:ℝ)), Real.exp_pos (-(10000/3:ℝ))])


/-- Row 5000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5000_k3_margin :
    B_8_exact 3 (5000 : ℝ) (5100 : ℝ) ≤ (0.000000074687 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5000 : ℝ) (5100 : ℝ) 2 7216 5.6304e-19
    (0.000000074687 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5000_a2_le row5000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2500_lt, exp_neg_10000_3_lt,
                   Real.exp_pos (-(2500:ℝ)), Real.exp_pos (-(10000/3:ℝ))])


/-- Row 5000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5000_k4_margin :
    B_8_exact 4 (5000 : ℝ) (5100 : ℝ) ≤ (0.00038090 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5000 : ℝ) (5100 : ℝ) 2 7216 5.6304e-19
    (0.00038090 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5000_a2_le row5000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2500_lt, exp_neg_10000_3_lt,
                   Real.exp_pos (-(2500:ℝ)), Real.exp_pos (-(10000/3:ℝ))])


/-- Row 5000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5000_k5_margin :
    B_8_exact 5 (5000 : ℝ) (5100 : ℝ) ≤ (1.9426 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5000 : ℝ) (5100 : ℝ) 2 7216 5.6304e-19
    (1.9426 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5000_a2_le row5000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2500_lt, exp_neg_10000_3_lt,
                   Real.exp_pos (-(2500:ℝ)), Real.exp_pos (-(10000/3:ℝ))])


/-- Row 5100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5100_k1_margin :
    B_8_exact 1 (5100 : ℝ) (5200 : ℝ) ≤ (0.0000000000000017087 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5100 : ℝ) (5200 : ℝ) 2 7360 3.2860e-19
    (0.0000000000000017087 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5100_a2_le row5100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2550_lt, exp_neg_3400_lt,
                   Real.exp_pos (-(2550:ℝ)), Real.exp_pos (-(3400:ℝ))])


/-- Row 5100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5100_k2_margin :
    B_8_exact 2 (5100 : ℝ) (5200 : ℝ) ≤ (0.0000000000088850 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5100 : ℝ) (5200 : ℝ) 2 7360 3.2860e-19
    (0.0000000000088850 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5100_a2_le row5100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2550_lt, exp_neg_3400_lt,
                   Real.exp_pos (-(2550:ℝ)), Real.exp_pos (-(3400:ℝ))])


/-- Row 5100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5100_k3_margin :
    B_8_exact 3 (5100 : ℝ) (5200 : ℝ) ≤ (0.000000046202 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5100 : ℝ) (5200 : ℝ) 2 7360 3.2860e-19
    (0.000000046202 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5100_a2_le row5100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2550_lt, exp_neg_3400_lt,
                   Real.exp_pos (-(2550:ℝ)), Real.exp_pos (-(3400:ℝ))])


/-- Row 5100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5100_k4_margin :
    B_8_exact 4 (5100 : ℝ) (5200 : ℝ) ≤ (0.00024025 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5100 : ℝ) (5200 : ℝ) 2 7360 3.2860e-19
    (0.00024025 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5100_a2_le row5100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2550_lt, exp_neg_3400_lt,
                   Real.exp_pos (-(2550:ℝ)), Real.exp_pos (-(3400:ℝ))])


/-- Row 5100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5100_k5_margin :
    B_8_exact 5 (5100 : ℝ) (5200 : ℝ) ≤ (1.2493 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5100 : ℝ) (5200 : ℝ) 2 7360 3.2860e-19
    (1.2493 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5100_a2_le row5100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2550_lt, exp_neg_3400_lt,
                   Real.exp_pos (-(2550:ℝ)), Real.exp_pos (-(3400:ℝ))])


/-- Row 5200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5200_k1_margin :
    B_8_exact 1 (5200 : ℝ) (5300 : ℝ) ≤ (0.0000000000000010185 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5200 : ℝ) (5300 : ℝ) 2 7505 1.9218e-19
    (0.0000000000000010185 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5200_a2_le row5200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2600_lt, exp_neg_10400_3_lt,
                   Real.exp_pos (-(2600:ℝ)), Real.exp_pos (-(10400/3:ℝ))])


/-- Row 5200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5200_k2_margin :
    B_8_exact 2 (5200 : ℝ) (5300 : ℝ) ≤ (0.0000000000053980 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5200 : ℝ) (5300 : ℝ) 2 7505 1.9218e-19
    (0.0000000000053980 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5200_a2_le row5200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2600_lt, exp_neg_10400_3_lt,
                   Real.exp_pos (-(2600:ℝ)), Real.exp_pos (-(10400/3:ℝ))])


/-- Row 5200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5200_k3_margin :
    B_8_exact 3 (5200 : ℝ) (5300 : ℝ) ≤ (0.000000028610 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5200 : ℝ) (5300 : ℝ) 2 7505 1.9218e-19
    (0.000000028610 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5200_a2_le row5200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2600_lt, exp_neg_10400_3_lt,
                   Real.exp_pos (-(2600:ℝ)), Real.exp_pos (-(10400/3:ℝ))])


/-- Row 5200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5200_k4_margin :
    B_8_exact 4 (5200 : ℝ) (5300 : ℝ) ≤ (0.00015163 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5200 : ℝ) (5300 : ℝ) 2 7505 1.9218e-19
    (0.00015163 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5200_a2_le row5200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2600_lt, exp_neg_10400_3_lt,
                   Real.exp_pos (-(2600:ℝ)), Real.exp_pos (-(10400/3:ℝ))])


/-- Row 5200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5200_k5_margin :
    B_8_exact 5 (5200 : ℝ) (5300 : ℝ) ≤ (0.80364 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5200 : ℝ) (5300 : ℝ) 2 7505 1.9218e-19
    (0.80364 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5200_a2_le row5200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2600_lt, exp_neg_10400_3_lt,
                   Real.exp_pos (-(2600:ℝ)), Real.exp_pos (-(10400/3:ℝ))])


/-- Row 5300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5300_k1_margin :
    B_8_exact 1 (5300 : ℝ) (5400 : ℝ) ≤ (0.00000000000000060977 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5300 : ℝ) (5400 : ℝ) 2 7649 1.1293e-19
    (0.00000000000000060977 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5300_a2_le row5300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2650_lt, exp_neg_10600_3_lt,
                   Real.exp_pos (-(2650:ℝ)), Real.exp_pos (-(10600/3:ℝ))])


/-- Row 5300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5300_k2_margin :
    B_8_exact 2 (5300 : ℝ) (5400 : ℝ) ≤ (0.0000000000032927 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5300 : ℝ) (5400 : ℝ) 2 7649 1.1293e-19
    (0.0000000000032927 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5300_a2_le row5300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2650_lt, exp_neg_10600_3_lt,
                   Real.exp_pos (-(2650:ℝ)), Real.exp_pos (-(10600/3:ℝ))])


/-- Row 5300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5300_k3_margin :
    B_8_exact 3 (5300 : ℝ) (5400 : ℝ) ≤ (0.000000017781 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5300 : ℝ) (5400 : ℝ) 2 7649 1.1293e-19
    (0.000000017781 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5300_a2_le row5300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2650_lt, exp_neg_10600_3_lt,
                   Real.exp_pos (-(2650:ℝ)), Real.exp_pos (-(10600/3:ℝ))])


/-- Row 5300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5300_k4_margin :
    B_8_exact 4 (5300 : ℝ) (5400 : ℝ) ≤ (0.000096016 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5300 : ℝ) (5400 : ℝ) 2 7649 1.1293e-19
    (0.000096016 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5300_a2_le row5300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2650_lt, exp_neg_10600_3_lt,
                   Real.exp_pos (-(2650:ℝ)), Real.exp_pos (-(10600/3:ℝ))])


/-- Row 5300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5300_k5_margin :
    B_8_exact 5 (5300 : ℝ) (5400 : ℝ) ≤ (0.51849 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5300 : ℝ) (5400 : ℝ) 2 7649 1.1293e-19
    (0.51849 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5300_a2_le row5300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2650_lt, exp_neg_10600_3_lt,
                   Real.exp_pos (-(2650:ℝ)), Real.exp_pos (-(10600/3:ℝ))])


/-- Row 5400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5400_k1_margin :
    B_8_exact 1 (5400 : ℝ) (5500 : ℝ) ≤ (0.00000000000000036472 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5400 : ℝ) (5500 : ℝ) 2 7793 6.6313e-20
    (0.00000000000000036472 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5400_a2_le row5400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2700_lt, exp_neg_3600_lt,
                   Real.exp_pos (-(2700:ℝ)), Real.exp_pos (-(3600:ℝ))])


/-- Row 5400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5400_k2_margin :
    B_8_exact 2 (5400 : ℝ) (5500 : ℝ) ≤ (0.0000000000020059 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5400 : ℝ) (5500 : ℝ) 2 7793 6.6313e-20
    (0.0000000000020059 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5400_a2_le row5400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2700_lt, exp_neg_3600_lt,
                   Real.exp_pos (-(2700:ℝ)), Real.exp_pos (-(3600:ℝ))])


/-- Row 5400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5400_k3_margin :
    B_8_exact 3 (5400 : ℝ) (5500 : ℝ) ≤ (0.000000011033 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5400 : ℝ) (5500 : ℝ) 2 7793 6.6313e-20
    (0.000000011033 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5400_a2_le row5400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2700_lt, exp_neg_3600_lt,
                   Real.exp_pos (-(2700:ℝ)), Real.exp_pos (-(3600:ℝ))])


/-- Row 5400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5400_k4_margin :
    B_8_exact 4 (5400 : ℝ) (5500 : ℝ) ≤ (0.000060679 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5400 : ℝ) (5500 : ℝ) 2 7793 6.6313e-20
    (0.000060679 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5400_a2_le row5400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2700_lt, exp_neg_3600_lt,
                   Real.exp_pos (-(2700:ℝ)), Real.exp_pos (-(3600:ℝ))])


/-- Row 5400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5400_k5_margin :
    B_8_exact 5 (5400 : ℝ) (5500 : ℝ) ≤ (0.33374 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5400 : ℝ) (5500 : ℝ) 2 7793 6.6313e-20
    (0.33374 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5400_a2_le row5400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2700_lt, exp_neg_3600_lt,
                   Real.exp_pos (-(2700:ℝ)), Real.exp_pos (-(3600:ℝ))])


/-- Row 5500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5500_k1_margin :
    B_8_exact 1 (5500 : ℝ) (5600 : ℝ) ≤ (0.00000000000000021916 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5500 : ℝ) (5600 : ℝ) 2 7937 3.9136e-20
    (0.00000000000000021916 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5500_a2_le row5500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2750_lt, exp_neg_11000_3_lt,
                   Real.exp_pos (-(2750:ℝ)), Real.exp_pos (-(11000/3:ℝ))])


/-- Row 5500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5500_k2_margin :
    B_8_exact 2 (5500 : ℝ) (5600 : ℝ) ≤ (0.0000000000012273 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5500 : ℝ) (5600 : ℝ) 2 7937 3.9136e-20
    (0.0000000000012273 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5500_a2_le row5500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2750_lt, exp_neg_11000_3_lt,
                   Real.exp_pos (-(2750:ℝ)), Real.exp_pos (-(11000/3:ℝ))])


/-- Row 5500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5500_k3_margin :
    B_8_exact 3 (5500 : ℝ) (5600 : ℝ) ≤ (0.0000000068727 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5500 : ℝ) (5600 : ℝ) 2 7937 3.9136e-20
    (0.0000000068727 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5500_a2_le row5500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2750_lt, exp_neg_11000_3_lt,
                   Real.exp_pos (-(2750:ℝ)), Real.exp_pos (-(11000/3:ℝ))])


/-- Row 5500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5500_k4_margin :
    B_8_exact 4 (5500 : ℝ) (5600 : ℝ) ≤ (0.000038487 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5500 : ℝ) (5600 : ℝ) 2 7937 3.9136e-20
    (0.000038487 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5500_a2_le row5500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2750_lt, exp_neg_11000_3_lt,
                   Real.exp_pos (-(2750:ℝ)), Real.exp_pos (-(11000/3:ℝ))])


/-- Row 5500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5500_k5_margin :
    B_8_exact 5 (5500 : ℝ) (5600 : ℝ) ≤ (0.21553 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5500 : ℝ) (5600 : ℝ) 2 7937 3.9136e-20
    (0.21553 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5500_a2_le row5500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2750_lt, exp_neg_11000_3_lt,
                   Real.exp_pos (-(2750:ℝ)), Real.exp_pos (-(11000/3:ℝ))])


/-- Row 5600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5600_k1_margin :
    B_8_exact 1 (5600 : ℝ) (5700 : ℝ) ≤ (0.00000000000000013217 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5600 : ℝ) (5700 : ℝ) 2 8082 2.3189e-20
    (0.00000000000000013217 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5600_a2_le row5600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2800_lt, exp_neg_11200_3_lt,
                   Real.exp_pos (-(2800:ℝ)), Real.exp_pos (-(11200/3:ℝ))])


/-- Row 5600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5600_k2_margin :
    B_8_exact 2 (5600 : ℝ) (5700 : ℝ) ≤ (0.00000000000075337 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5600 : ℝ) (5700 : ℝ) 2 8082 2.3189e-20
    (0.00000000000075337 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5600_a2_le row5600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2800_lt, exp_neg_11200_3_lt,
                   Real.exp_pos (-(2800:ℝ)), Real.exp_pos (-(11200/3:ℝ))])


/-- Row 5600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5600_k3_margin :
    B_8_exact 3 (5600 : ℝ) (5700 : ℝ) ≤ (0.0000000042942 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5600 : ℝ) (5700 : ℝ) 2 8082 2.3189e-20
    (0.0000000042942 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5600_a2_le row5600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2800_lt, exp_neg_11200_3_lt,
                   Real.exp_pos (-(2800:ℝ)), Real.exp_pos (-(11200/3:ℝ))])


/-- Row 5600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5600_k4_margin :
    B_8_exact 4 (5600 : ℝ) (5700 : ℝ) ≤ (0.000024477 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5600 : ℝ) (5700 : ℝ) 2 8082 2.3189e-20
    (0.000024477 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5600_a2_le row5600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2800_lt, exp_neg_11200_3_lt,
                   Real.exp_pos (-(2800:ℝ)), Real.exp_pos (-(11200/3:ℝ))])


/-- Row 5600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5600_k5_margin :
    B_8_exact 5 (5600 : ℝ) (5700 : ℝ) ≤ (0.13952 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5600 : ℝ) (5700 : ℝ) 2 8082 2.3189e-20
    (0.13952 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5600_a2_le row5600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2800_lt, exp_neg_11200_3_lt,
                   Real.exp_pos (-(2800:ℝ)), Real.exp_pos (-(11200/3:ℝ))])


/-- Row 5700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5700_k1_margin :
    B_8_exact 1 (5700 : ℝ) (5800 : ℝ) ≤ (0.000000000000000080079 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5700 : ℝ) (5800 : ℝ) 2 8226 1.3808e-20
    (0.000000000000000080079 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5700_a2_le row5700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2850_lt, exp_neg_3800_lt,
                   Real.exp_pos (-(2850:ℝ)), Real.exp_pos (-(3800:ℝ))])


/-- Row 5700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5700_k2_margin :
    B_8_exact 2 (5700 : ℝ) (5800 : ℝ) ≤ (0.00000000000046446 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5700 : ℝ) (5800 : ℝ) 2 8226 1.3808e-20
    (0.00000000000046446 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5700_a2_le row5700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2850_lt, exp_neg_3800_lt,
                   Real.exp_pos (-(2850:ℝ)), Real.exp_pos (-(3800:ℝ))])


/-- Row 5700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5700_k3_margin :
    B_8_exact 3 (5700 : ℝ) (5800 : ℝ) ≤ (0.0000000026938 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5700 : ℝ) (5800 : ℝ) 2 8226 1.3808e-20
    (0.0000000026938 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5700_a2_le row5700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2850_lt, exp_neg_3800_lt,
                   Real.exp_pos (-(2850:ℝ)), Real.exp_pos (-(3800:ℝ))])


/-- Row 5700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5700_k4_margin :
    B_8_exact 4 (5700 : ℝ) (5800 : ℝ) ≤ (0.000015624 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5700 : ℝ) (5800 : ℝ) 2 8226 1.3808e-20
    (0.000015624 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5700_a2_le row5700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2850_lt, exp_neg_3800_lt,
                   Real.exp_pos (-(2850:ℝ)), Real.exp_pos (-(3800:ℝ))])


/-- Row 5700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5700_k5_margin :
    B_8_exact 5 (5700 : ℝ) (5800 : ℝ) ≤ (0.090621 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5700 : ℝ) (5800 : ℝ) 2 8226 1.3808e-20
    (0.090621 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5700_a2_le row5700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2850_lt, exp_neg_3800_lt,
                   Real.exp_pos (-(2850:ℝ)), Real.exp_pos (-(3800:ℝ))])


/-- Row 5800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5800_k1_margin :
    B_8_exact 1 (5800 : ℝ) (5900 : ℝ) ≤ (0.000000000000000048518 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5800 : ℝ) (5900 : ℝ) 2 8370 8.2235e-21
    (0.000000000000000048518 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5800_a2_le row5800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2900_lt, exp_neg_11600_3_lt,
                   Real.exp_pos (-(2900:ℝ)), Real.exp_pos (-(11600/3:ℝ))])


/-- Row 5800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5800_k2_margin :
    B_8_exact 2 (5800 : ℝ) (5900 : ℝ) ≤ (0.00000000000028626 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5800 : ℝ) (5900 : ℝ) 2 8370 8.2235e-21
    (0.00000000000028626 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5800_a2_le row5800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2900_lt, exp_neg_11600_3_lt,
                   Real.exp_pos (-(2900:ℝ)), Real.exp_pos (-(11600/3:ℝ))])


/-- Row 5800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5800_k3_margin :
    B_8_exact 3 (5800 : ℝ) (5900 : ℝ) ≤ (0.0000000016889 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5800 : ℝ) (5900 : ℝ) 2 8370 8.2235e-21
    (0.0000000016889 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5800_a2_le row5800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2900_lt, exp_neg_11600_3_lt,
                   Real.exp_pos (-(2900:ℝ)), Real.exp_pos (-(11600/3:ℝ))])


/-- Row 5800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5800_k4_margin :
    B_8_exact 4 (5800 : ℝ) (5900 : ℝ) ≤ (0.0000099646 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5800 : ℝ) (5900 : ℝ) 2 8370 8.2235e-21
    (0.0000099646 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5800_a2_le row5800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2900_lt, exp_neg_11600_3_lt,
                   Real.exp_pos (-(2900:ℝ)), Real.exp_pos (-(11600/3:ℝ))])


/-- Row 5800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5800_k5_margin :
    B_8_exact 5 (5800 : ℝ) (5900 : ℝ) ≤ (0.058791 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5800 : ℝ) (5900 : ℝ) 2 8370 8.2235e-21
    (0.058791 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5800_a2_le row5800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2900_lt, exp_neg_11600_3_lt,
                   Real.exp_pos (-(2900:ℝ)), Real.exp_pos (-(11600/3:ℝ))])


/-- Row 5900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row5900_k1_margin :
    B_8_exact 1 (5900 : ℝ) (6000 : ℝ) ≤ (0.000000000000000029482 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (5900 : ℝ) (6000 : ℝ) 2 8514 4.9138e-21
    (0.000000000000000029482 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5900_a2_le row5900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2950_lt, exp_neg_11800_3_lt,
                   Real.exp_pos (-(2950:ℝ)), Real.exp_pos (-(11800/3:ℝ))])


/-- Row 5900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row5900_k2_margin :
    B_8_exact 2 (5900 : ℝ) (6000 : ℝ) ≤ (0.00000000000017689 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (5900 : ℝ) (6000 : ℝ) 2 8514 4.9138e-21
    (0.00000000000017689 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5900_a2_le row5900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2950_lt, exp_neg_11800_3_lt,
                   Real.exp_pos (-(2950:ℝ)), Real.exp_pos (-(11800/3:ℝ))])


/-- Row 5900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row5900_k3_margin :
    B_8_exact 3 (5900 : ℝ) (6000 : ℝ) ≤ (0.0000000010614 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (5900 : ℝ) (6000 : ℝ) 2 8514 4.9138e-21
    (0.0000000010614 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5900_a2_le row5900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2950_lt, exp_neg_11800_3_lt,
                   Real.exp_pos (-(2950:ℝ)), Real.exp_pos (-(11800/3:ℝ))])


/-- Row 5900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row5900_k4_margin :
    B_8_exact 4 (5900 : ℝ) (6000 : ℝ) ≤ (0.0000063682 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (5900 : ℝ) (6000 : ℝ) 2 8514 4.9138e-21
    (0.0000063682 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5900_a2_le row5900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2950_lt, exp_neg_11800_3_lt,
                   Real.exp_pos (-(2950:ℝ)), Real.exp_pos (-(11800/3:ℝ))])


/-- Row 5900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row5900_k5_margin :
    B_8_exact 5 (5900 : ℝ) (6000 : ℝ) ≤ (0.038209 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (5900 : ℝ) (6000 : ℝ) 2 8514 4.9138e-21
    (0.038209 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row5900_a2_le row5900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2950_lt, exp_neg_11800_3_lt,
                   Real.exp_pos (-(2950:ℝ)), Real.exp_pos (-(11800/3:ℝ))])


/-- Row 6000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6000_k1_margin :
    B_8_exact 1 (6000 : ℝ) (6100 : ℝ) ≤ (0.000000000000000017952 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6000 : ℝ) (6100 : ℝ) 2 8659 2.9430e-21
    (0.000000000000000017952 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6000_a2_le row6000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3000_lt, exp_neg_4000_lt,
                   Real.exp_pos (-(3000:ℝ)), Real.exp_pos (-(4000:ℝ))])


/-- Row 6000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6000_k2_margin :
    B_8_exact 2 (6000 : ℝ) (6100 : ℝ) ≤ (0.00000000000010951 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6000 : ℝ) (6100 : ℝ) 2 8659 2.9430e-21
    (0.00000000000010951 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6000_a2_le row6000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3000_lt, exp_neg_4000_lt,
                   Real.exp_pos (-(3000:ℝ)), Real.exp_pos (-(4000:ℝ))])


/-- Row 6000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6000_k3_margin :
    B_8_exact 3 (6000 : ℝ) (6100 : ℝ) ≤ (0.00000000066798 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6000 : ℝ) (6100 : ℝ) 2 8659 2.9430e-21
    (0.00000000066798 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6000_a2_le row6000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3000_lt, exp_neg_4000_lt,
                   Real.exp_pos (-(3000:ℝ)), Real.exp_pos (-(4000:ℝ))])


/-- Row 6000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6000_k4_margin :
    B_8_exact 4 (6000 : ℝ) (6100 : ℝ) ≤ (0.0000040747 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6000 : ℝ) (6100 : ℝ) 2 8659 2.9430e-21
    (0.0000040747 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6000_a2_le row6000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3000_lt, exp_neg_4000_lt,
                   Real.exp_pos (-(3000:ℝ)), Real.exp_pos (-(4000:ℝ))])


/-- Row 6000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6000_k5_margin :
    B_8_exact 5 (6000 : ℝ) (6100 : ℝ) ≤ (0.024855 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6000 : ℝ) (6100 : ℝ) 2 8659 2.9430e-21
    (0.024855 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6000_a2_le row6000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3000_lt, exp_neg_4000_lt,
                   Real.exp_pos (-(3000:ℝ)), Real.exp_pos (-(4000:ℝ))])


/-- Row 6100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6100_k1_margin :
    B_8_exact 1 (6100 : ℝ) (6200 : ℝ) ≤ (0.000000000000000010987 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6100 : ℝ) (6200 : ℝ) 2 8803 1.7722e-21
    (0.000000000000000010987 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6100_a2_le row6100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3050_lt, exp_neg_12200_3_lt,
                   Real.exp_pos (-(3050:ℝ)), Real.exp_pos (-(12200/3:ℝ))])


/-- Row 6100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6100_k2_margin :
    B_8_exact 2 (6100 : ℝ) (6200 : ℝ) ≤ (0.000000000000068120 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6100 : ℝ) (6200 : ℝ) 2 8803 1.7722e-21
    (0.000000000000068120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6100_a2_le row6100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3050_lt, exp_neg_12200_3_lt,
                   Real.exp_pos (-(3050:ℝ)), Real.exp_pos (-(12200/3:ℝ))])


/-- Row 6100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6100_k3_margin :
    B_8_exact 3 (6100 : ℝ) (6200 : ℝ) ≤ (0.00000000042234 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6100 : ℝ) (6200 : ℝ) 2 8803 1.7722e-21
    (0.00000000042234 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6100_a2_le row6100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3050_lt, exp_neg_12200_3_lt,
                   Real.exp_pos (-(3050:ℝ)), Real.exp_pos (-(12200/3:ℝ))])


/-- Row 6100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6100_k4_margin :
    B_8_exact 4 (6100 : ℝ) (6200 : ℝ) ≤ (0.0000026185 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6100 : ℝ) (6200 : ℝ) 2 8803 1.7722e-21
    (0.0000026185 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6100_a2_le row6100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3050_lt, exp_neg_12200_3_lt,
                   Real.exp_pos (-(3050:ℝ)), Real.exp_pos (-(12200/3:ℝ))])


/-- Row 6100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6100_k5_margin :
    B_8_exact 5 (6100 : ℝ) (6200 : ℝ) ≤ (0.016235 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6100 : ℝ) (6200 : ℝ) 2 8803 1.7722e-21
    (0.016235 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6100_a2_le row6100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3050_lt, exp_neg_12200_3_lt,
                   Real.exp_pos (-(3050:ℝ)), Real.exp_pos (-(12200/3:ℝ))])


/-- Row 6200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6200_k1_margin :
    B_8_exact 1 (6200 : ℝ) (6300 : ℝ) ≤ (0.0000000000000000067178 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6200 : ℝ) (6300 : ℝ) 2 8947 1.0664e-21
    (0.0000000000000000067178 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6200_a2_le row6200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3100_lt, exp_neg_12400_3_lt,
                   Real.exp_pos (-(3100:ℝ)), Real.exp_pos (-(12400/3:ℝ))])


/-- Row 6200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6200_k2_margin :
    B_8_exact 2 (6200 : ℝ) (6300 : ℝ) ≤ (0.000000000000042322 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6200 : ℝ) (6300 : ℝ) 2 8947 1.0664e-21
    (0.000000000000042322 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6200_a2_le row6200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3100_lt, exp_neg_12400_3_lt,
                   Real.exp_pos (-(3100:ℝ)), Real.exp_pos (-(12400/3:ℝ))])


/-- Row 6200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6200_k3_margin :
    B_8_exact 3 (6200 : ℝ) (6300 : ℝ) ≤ (0.00000000026663 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6200 : ℝ) (6300 : ℝ) 2 8947 1.0664e-21
    (0.00000000026663 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6200_a2_le row6200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3100_lt, exp_neg_12400_3_lt,
                   Real.exp_pos (-(3100:ℝ)), Real.exp_pos (-(12400/3:ℝ))])


/-- Row 6200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6200_k4_margin :
    B_8_exact 4 (6200 : ℝ) (6300 : ℝ) ≤ (0.0000016798 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6200 : ℝ) (6300 : ℝ) 2 8947 1.0664e-21
    (0.0000016798 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6200_a2_le row6200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3100_lt, exp_neg_12400_3_lt,
                   Real.exp_pos (-(3100:ℝ)), Real.exp_pos (-(12400/3:ℝ))])


/-- Row 6200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6200_k5_margin :
    B_8_exact 5 (6200 : ℝ) (6300 : ℝ) ≤ (0.010583 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6200 : ℝ) (6300 : ℝ) 2 8947 1.0664e-21
    (0.010583 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6200_a2_le row6200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3100_lt, exp_neg_12400_3_lt,
                   Real.exp_pos (-(3100:ℝ)), Real.exp_pos (-(12400/3:ℝ))])


/-- Row 6300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6300_k1_margin :
    B_8_exact 1 (6300 : ℝ) (6400 : ℝ) ≤ (0.0000000000000000041267 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6300 : ℝ) (6400 : ℝ) 2 9091 6.4481e-22
    (0.0000000000000000041267 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6300_a2_le row6300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3150_lt, exp_neg_4200_lt,
                   Real.exp_pos (-(3150:ℝ)), Real.exp_pos (-(4200:ℝ))])


/-- Row 6300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6300_k2_margin :
    B_8_exact 2 (6300 : ℝ) (6400 : ℝ) ≤ (0.000000000000026411 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6300 : ℝ) (6400 : ℝ) 2 9091 6.4481e-22
    (0.000000000000026411 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6300_a2_le row6300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3150_lt, exp_neg_4200_lt,
                   Real.exp_pos (-(3150:ℝ)), Real.exp_pos (-(4200:ℝ))])


/-- Row 6300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6300_k3_margin :
    B_8_exact 3 (6300 : ℝ) (6400 : ℝ) ≤ (0.00000000016903 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6300 : ℝ) (6400 : ℝ) 2 9091 6.4481e-22
    (0.00000000016903 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6300_a2_le row6300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3150_lt, exp_neg_4200_lt,
                   Real.exp_pos (-(3150:ℝ)), Real.exp_pos (-(4200:ℝ))])


/-- Row 6300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6300_k4_margin :
    B_8_exact 4 (6300 : ℝ) (6400 : ℝ) ≤ (0.0000010818 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6300 : ℝ) (6400 : ℝ) 2 9091 6.4481e-22
    (0.0000010818 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6300_a2_le row6300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3150_lt, exp_neg_4200_lt,
                   Real.exp_pos (-(3150:ℝ)), Real.exp_pos (-(4200:ℝ))])


/-- Row 6300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6300_k5_margin :
    B_8_exact 5 (6300 : ℝ) (6400 : ℝ) ≤ (0.0069235 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6300 : ℝ) (6400 : ℝ) 2 9091 6.4481e-22
    (0.0069235 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6300_a2_le row6300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3150_lt, exp_neg_4200_lt,
                   Real.exp_pos (-(3150:ℝ)), Real.exp_pos (-(4200:ℝ))])


/-- Row 6400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6400_k1_margin :
    B_8_exact 1 (6400 : ℝ) (6500 : ℝ) ≤ (0.0000000000000000025481 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6400 : ℝ) (6500 : ℝ) 2 9236 3.9202e-22
    (0.0000000000000000025481 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6400_a2_le row6400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3200_lt, exp_neg_12800_3_lt,
                   Real.exp_pos (-(3200:ℝ)), Real.exp_pos (-(12800/3:ℝ))])


/-- Row 6400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6400_k2_margin :
    B_8_exact 2 (6400 : ℝ) (6500 : ℝ) ≤ (0.000000000000016563 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6400 : ℝ) (6500 : ℝ) 2 9236 3.9202e-22
    (0.000000000000016563 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6400_a2_le row6400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3200_lt, exp_neg_12800_3_lt,
                   Real.exp_pos (-(3200:ℝ)), Real.exp_pos (-(12800/3:ℝ))])


/-- Row 6400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6400_k3_margin :
    B_8_exact 3 (6400 : ℝ) (6500 : ℝ) ≤ (0.00000000010766 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6400 : ℝ) (6500 : ℝ) 2 9236 3.9202e-22
    (0.00000000010766 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6400_a2_le row6400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3200_lt, exp_neg_12800_3_lt,
                   Real.exp_pos (-(3200:ℝ)), Real.exp_pos (-(12800/3:ℝ))])


/-- Row 6400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6400_k4_margin :
    B_8_exact 4 (6400 : ℝ) (6500 : ℝ) ≤ (0.00000069977 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6400 : ℝ) (6500 : ℝ) 2 9236 3.9202e-22
    (0.00000069977 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6400_a2_le row6400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3200_lt, exp_neg_12800_3_lt,
                   Real.exp_pos (-(3200:ℝ)), Real.exp_pos (-(12800/3:ℝ))])


/-- Row 6400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6400_k5_margin :
    B_8_exact 5 (6400 : ℝ) (6500 : ℝ) ≤ (0.0045485 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6400 : ℝ) (6500 : ℝ) 2 9236 3.9202e-22
    (0.0045485 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6400_a2_le row6400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3200_lt, exp_neg_12800_3_lt,
                   Real.exp_pos (-(3200:ℝ)), Real.exp_pos (-(12800/3:ℝ))])


/-- Row 6500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6500_k1_margin :
    B_8_exact 1 (6500 : ℝ) (6600 : ℝ) ≤ (0.0000000000000000015741 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6500 : ℝ) (6600 : ℝ) 2 9380 2.3850e-22
    (0.0000000000000000015741 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6500_a2_le row6500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3250_lt, exp_neg_13000_3_lt,
                   Real.exp_pos (-(3250:ℝ)), Real.exp_pos (-(13000/3:ℝ))])


/-- Row 6500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6500_k2_margin :
    B_8_exact 2 (6500 : ℝ) (6600 : ℝ) ≤ (0.000000000000010389 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6500 : ℝ) (6600 : ℝ) 2 9380 2.3850e-22
    (0.000000000000010389 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6500_a2_le row6500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3250_lt, exp_neg_13000_3_lt,
                   Real.exp_pos (-(3250:ℝ)), Real.exp_pos (-(13000/3:ℝ))])


/-- Row 6500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6500_k3_margin :
    B_8_exact 3 (6500 : ℝ) (6600 : ℝ) ≤ (0.000000000068566 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6500 : ℝ) (6600 : ℝ) 2 9380 2.3850e-22
    (0.000000000068566 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6500_a2_le row6500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3250_lt, exp_neg_13000_3_lt,
                   Real.exp_pos (-(3250:ℝ)), Real.exp_pos (-(13000/3:ℝ))])


/-- Row 6500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6500_k4_margin :
    B_8_exact 4 (6500 : ℝ) (6600 : ℝ) ≤ (0.00000045253 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6500 : ℝ) (6600 : ℝ) 2 9380 2.3850e-22
    (0.00000045253 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6500_a2_le row6500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3250_lt, exp_neg_13000_3_lt,
                   Real.exp_pos (-(3250:ℝ)), Real.exp_pos (-(13000/3:ℝ))])


/-- Row 6500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6500_k5_margin :
    B_8_exact 5 (6500 : ℝ) (6600 : ℝ) ≤ (0.0029867 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6500 : ℝ) (6600 : ℝ) 2 9380 2.3850e-22
    (0.0029867 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6500_a2_le row6500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3250_lt, exp_neg_13000_3_lt,
                   Real.exp_pos (-(3250:ℝ)), Real.exp_pos (-(13000/3:ℝ))])

end BKLNW
