import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Generated regime-3 pointwise Table 10 margin certificates.

This shard expects `row_bound_pointwise`
to be available from `BKLNW_table10_rows_core.lean`.
-/

namespace BKLNW

open Real Set Finset

/-! ## Cached exp(-x) bounds shared across this file's k-margin theorems. -/

private lemma exp_neg_1950_lt : Real.exp (-(1950 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_3925_2_lt : Real.exp (-(3925/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_1975_lt : Real.exp (-(1975 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_3975_2_lt : Real.exp (-(3975/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2000_lt : Real.exp (-(2000 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4025_2_lt : Real.exp (-(4025/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2025_lt : Real.exp (-(2025 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4075_2_lt : Real.exp (-(4075/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2050_lt : Real.exp (-(2050 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4125_2_lt : Real.exp (-(4125/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2075_lt : Real.exp (-(2075 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4175_2_lt : Real.exp (-(4175/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2100_lt : Real.exp (-(2100 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4225_2_lt : Real.exp (-(4225/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2125_lt : Real.exp (-(2125 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4275_2_lt : Real.exp (-(4275/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2150_lt : Real.exp (-(2150 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4325_2_lt : Real.exp (-(4325/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2175_lt : Real.exp (-(2175 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_4375_2_lt : Real.exp (-(4375/2 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2600_lt : Real.exp (-(2600 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_7850_3_lt : Real.exp (-(7850/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_7900_3_lt : Real.exp (-(7900/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2650_lt : Real.exp (-(2650 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8000_3_lt : Real.exp (-(8000/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8050_3_lt : Real.exp (-(8050/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2700_lt : Real.exp (-(2700 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8150_3_lt : Real.exp (-(8150/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8200_3_lt : Real.exp (-(8200/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2750_lt : Real.exp (-(2750 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8300_3_lt : Real.exp (-(8300/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8350_3_lt : Real.exp (-(8350/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2800_lt : Real.exp (-(2800 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8450_3_lt : Real.exp (-(8450/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8500_3_lt : Real.exp (-(8500/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2850_lt : Real.exp (-(2850 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8600_3_lt : Real.exp (-(8600/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8650_3_lt : Real.exp (-(8650/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_2900_lt : Real.exp (-(2900 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)
private lemma exp_neg_8750_3_lt : Real.exp (-(8750/3 : ℝ)) < 1e-100 := LogTables.exp_neg_lt_1e_neg_100 (by norm_num)



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


private lemma row3900_a2_le : Inputs.default.a₂ (3900 : ℝ) ≤ (5629 : ℝ) := by
  have h := a2_crude_le (3900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3900 : ℝ) / log 2⌋₊ : ℝ) ≤ (3900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3900 : ℝ) / log 2 ≤ 5627 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5627 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5629 := by norm_num


private lemma row3925_a2_le : Inputs.default.a₂ (3925 : ℝ) ≤ (5665 : ℝ) := by
  have h := a2_crude_le (3925 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3925 : ℝ) / log 2⌋₊ : ℝ) ≤ (3925 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3925 : ℝ) / log 2 ≤ 5663 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3925 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3925 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5663 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5665 := by norm_num


private lemma row3950_a2_le : Inputs.default.a₂ (3950 : ℝ) ≤ (5701 : ℝ) := by
  have h := a2_crude_le (3950 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3950 : ℝ) / log 2⌋₊ : ℝ) ≤ (3950 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3950 : ℝ) / log 2 ≤ 5699 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3950 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3950 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5699 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5701 := by norm_num


private lemma row3975_a2_le : Inputs.default.a₂ (3975 : ℝ) ≤ (5737 : ℝ) := by
  have h := a2_crude_le (3975 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3975 : ℝ) / log 2⌋₊ : ℝ) ≤ (3975 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3975 : ℝ) / log 2 ≤ 5735 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3975 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3975 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5735 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5737 := by norm_num


private lemma row4000_a2_le : Inputs.default.a₂ (4000 : ℝ) ≤ (5773 : ℝ) := by
  have h := a2_crude_le (4000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4000 : ℝ) / log 2⌋₊ : ℝ) ≤ (4000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4000 : ℝ) / log 2 ≤ 5771 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5771 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5773 := by norm_num


private lemma row4025_a2_le : Inputs.default.a₂ (4025 : ℝ) ≤ (5809 : ℝ) := by
  have h := a2_crude_le (4025 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4025 : ℝ) / log 2⌋₊ : ℝ) ≤ (4025 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4025 : ℝ) / log 2 ≤ 5807 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4025 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4025 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5807 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5809 := by norm_num


private lemma row4050_a2_le : Inputs.default.a₂ (4050 : ℝ) ≤ (5845 : ℝ) := by
  have h := a2_crude_le (4050 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4050 : ℝ) / log 2⌋₊ : ℝ) ≤ (4050 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4050 : ℝ) / log 2 ≤ 5843 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4050 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4050 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5843 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5845 := by norm_num


private lemma row4075_a2_le : Inputs.default.a₂ (4075 : ℝ) ≤ (5881 : ℝ) := by
  have h := a2_crude_le (4075 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4075 : ℝ) / log 2⌋₊ : ℝ) ≤ (4075 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4075 : ℝ) / log 2 ≤ 5879 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4075 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4075 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5879 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5881 := by norm_num


private lemma row4100_a2_le : Inputs.default.a₂ (4100 : ℝ) ≤ (5918 : ℝ) := by
  have h := a2_crude_le (4100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4100 : ℝ) / log 2⌋₊ : ℝ) ≤ (4100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4100 : ℝ) / log 2 ≤ 5916 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5916 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5918 := by norm_num


private lemma row4125_a2_le : Inputs.default.a₂ (4125 : ℝ) ≤ (5954 : ℝ) := by
  have h := a2_crude_le (4125 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4125 : ℝ) / log 2⌋₊ : ℝ) ≤ (4125 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4125 : ℝ) / log 2 ≤ 5952 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4125 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4125 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5952 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5954 := by norm_num


private lemma row4150_a2_le : Inputs.default.a₂ (4150 : ℝ) ≤ (5990 : ℝ) := by
  have h := a2_crude_le (4150 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4150 : ℝ) / log 2⌋₊ : ℝ) ≤ (4150 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4150 : ℝ) / log 2 ≤ 5988 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4150 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4150 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5988 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5990 := by norm_num


private lemma row4175_a2_le : Inputs.default.a₂ (4175 : ℝ) ≤ (6026 : ℝ) := by
  have h := a2_crude_le (4175 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4175 : ℝ) / log 2⌋₊ : ℝ) ≤ (4175 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4175 : ℝ) / log 2 ≤ 6024 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4175 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4175 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6024 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6026 := by norm_num


private lemma row4200_a2_le : Inputs.default.a₂ (4200 : ℝ) ≤ (6062 : ℝ) := by
  have h := a2_crude_le (4200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4200 : ℝ) / log 2⌋₊ : ℝ) ≤ (4200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4200 : ℝ) / log 2 ≤ 6060 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6060 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6062 := by norm_num


private lemma row4225_a2_le : Inputs.default.a₂ (4225 : ℝ) ≤ (6098 : ℝ) := by
  have h := a2_crude_le (4225 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4225 : ℝ) / log 2⌋₊ : ℝ) ≤ (4225 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4225 : ℝ) / log 2 ≤ 6096 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4225 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4225 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6096 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6098 := by norm_num


private lemma row4250_a2_le : Inputs.default.a₂ (4250 : ℝ) ≤ (6134 : ℝ) := by
  have h := a2_crude_le (4250 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4250 : ℝ) / log 2⌋₊ : ℝ) ≤ (4250 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4250 : ℝ) / log 2 ≤ 6132 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4250 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4250 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6132 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6134 := by norm_num


private lemma row4275_a2_le : Inputs.default.a₂ (4275 : ℝ) ≤ (6170 : ℝ) := by
  have h := a2_crude_le (4275 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4275 : ℝ) / log 2⌋₊ : ℝ) ≤ (4275 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4275 : ℝ) / log 2 ≤ 6168 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4275 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4275 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6168 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6170 := by norm_num


private lemma row4300_a2_le : Inputs.default.a₂ (4300 : ℝ) ≤ (6206 : ℝ) := by
  have h := a2_crude_le (4300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4300 : ℝ) / log 2⌋₊ : ℝ) ≤ (4300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4300 : ℝ) / log 2 ≤ 6204 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6204 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6206 := by norm_num


private lemma row4325_a2_le : Inputs.default.a₂ (4325 : ℝ) ≤ (6242 : ℝ) := by
  have h := a2_crude_le (4325 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4325 : ℝ) / log 2⌋₊ : ℝ) ≤ (4325 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4325 : ℝ) / log 2 ≤ 6240 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4325 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4325 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6240 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6242 := by norm_num


private lemma row4350_a2_le : Inputs.default.a₂ (4350 : ℝ) ≤ (6278 : ℝ) := by
  have h := a2_crude_le (4350 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4350 : ℝ) / log 2⌋₊ : ℝ) ≤ (4350 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4350 : ℝ) / log 2 ≤ 6276 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4350 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4350 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6276 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6278 := by norm_num


private lemma row4375_a2_le : Inputs.default.a₂ (4375 : ℝ) ≤ (6314 : ℝ) := by
  have h := a2_crude_le (4375 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(4375 : ℝ) / log 2⌋₊ : ℝ) ≤ (4375 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4375 : ℝ) / log 2 ≤ 6312 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4375 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4375 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6312 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6314 := by norm_num


set_option maxRecDepth 10000 in
private lemma row3900_table8_mem : (3900, 2.5173e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3900_eps_le : Inputs.default.ε (3900 : ℝ) ≤ 2.5173e-16 := by
  change BKLNW_app.table_8_ε (3900 : ℝ) ≤ 2.5173e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3900)
    (ε := 2.5173e-16) row3900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3925_table8_mem : (3925, 2.1855e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3925_eps_le : Inputs.default.ε (3925 : ℝ) ≤ 2.1855e-16 := by
  change BKLNW_app.table_8_ε (3925 : ℝ) ≤ 2.1855e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3925)
    (ε := 2.1855e-16) row3925_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3950_table8_mem : (3950, 1.8982e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3950_eps_le : Inputs.default.ε (3950 : ℝ) ≤ 1.8982e-16 := by
  change BKLNW_app.table_8_ε (3950 : ℝ) ≤ 1.8982e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3950)
    (ε := 1.8982e-16) row3950_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3975_table8_mem : (3975, 1.6448e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3975_eps_le : Inputs.default.ε (3975 : ℝ) ≤ 1.6448e-16 := by
  change BKLNW_app.table_8_ε (3975 : ℝ) ≤ 1.6448e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3975)
    (ε := 1.6448e-16) row3975_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4000_table8_mem : (4000, 1.4264e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4000_eps_le : Inputs.default.ε (4000 : ℝ) ≤ 1.4264e-16 := by
  change BKLNW_app.table_8_ε (4000 : ℝ) ≤ 1.4264e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4000)
    (ε := 1.4264e-16) row4000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4025_table8_mem : (4025, 1.2412e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4025_eps_le : Inputs.default.ε (4025 : ℝ) ≤ 1.2412e-16 := by
  change BKLNW_app.table_8_ε (4025 : ℝ) ≤ 1.2412e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4025)
    (ε := 1.2412e-16) row4025_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4050_table8_mem : (4050, 1.0750e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4050_eps_le : Inputs.default.ε (4050 : ℝ) ≤ 1.0750e-16 := by
  change BKLNW_app.table_8_ε (4050 : ℝ) ≤ 1.0750e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4050)
    (ε := 1.0750e-16) row4050_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4075_table8_mem : (4075, 9.3378e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4075_eps_le : Inputs.default.ε (4075 : ℝ) ≤ 9.3378e-17 := by
  change BKLNW_app.table_8_ε (4075 : ℝ) ≤ 9.3378e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4075)
    (ε := 9.3378e-17) row4075_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4100_table8_mem : (4100, 8.1038e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4100_eps_le : Inputs.default.ε (4100 : ℝ) ≤ 8.1038e-17 := by
  change BKLNW_app.table_8_ε (4100 : ℝ) ≤ 8.1038e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4100)
    (ε := 8.1038e-17) row4100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4125_table8_mem : (4125, 7.0376e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4125_eps_le : Inputs.default.ε (4125 : ℝ) ≤ 7.0376e-17 := by
  change BKLNW_app.table_8_ε (4125 : ℝ) ≤ 7.0376e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4125)
    (ε := 7.0376e-17) row4125_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4150_table8_mem : (4150, 6.1237e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4150_eps_le : Inputs.default.ε (4150 : ℝ) ≤ 6.1237e-17 := by
  change BKLNW_app.table_8_ε (4150 : ℝ) ≤ 6.1237e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4150)
    (ε := 6.1237e-17) row4150_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4175_table8_mem : (4175, 5.3118e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4175_eps_le : Inputs.default.ε (4175 : ℝ) ≤ 5.3118e-17 := by
  change BKLNW_app.table_8_ε (4175 : ℝ) ≤ 5.3118e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4175)
    (ε := 5.3118e-17) row4175_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4200_table8_mem : (4200, 4.6145e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4200_eps_le : Inputs.default.ε (4200 : ℝ) ≤ 4.6145e-17 := by
  change BKLNW_app.table_8_ε (4200 : ℝ) ≤ 4.6145e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4200)
    (ε := 4.6145e-17) row4200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4225_table8_mem : (4225, 4.0111e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4225_eps_le : Inputs.default.ε (4225 : ℝ) ≤ 4.0111e-17 := by
  change BKLNW_app.table_8_ε (4225 : ℝ) ≤ 4.0111e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4225)
    (ε := 4.0111e-17) row4225_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4250_table8_mem : (4250, 3.4884e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4250_eps_le : Inputs.default.ε (4250 : ℝ) ≤ 3.4884e-17 := by
  change BKLNW_app.table_8_ε (4250 : ℝ) ≤ 3.4884e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4250)
    (ε := 3.4884e-17) row4250_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4275_table8_mem : (4275, 3.0318e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4275_eps_le : Inputs.default.ε (4275 : ℝ) ≤ 3.0318e-17 := by
  change BKLNW_app.table_8_ε (4275 : ℝ) ≤ 3.0318e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4275)
    (ε := 3.0318e-17) row4275_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4300_table8_mem : (4300, 2.6350e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4300_eps_le : Inputs.default.ε (4300 : ℝ) ≤ 2.6350e-17 := by
  change BKLNW_app.table_8_ε (4300 : ℝ) ≤ 2.6350e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4300)
    (ε := 2.6350e-17) row4300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4325_table8_mem : (4325, 2.2914e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4325_eps_le : Inputs.default.ε (4325 : ℝ) ≤ 2.2914e-17 := by
  change BKLNW_app.table_8_ε (4325 : ℝ) ≤ 2.2914e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4325)
    (ε := 2.2914e-17) row4325_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4350_table8_mem : (4350, 1.9935e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4350_eps_le : Inputs.default.ε (4350 : ℝ) ≤ 1.9935e-17 := by
  change BKLNW_app.table_8_ε (4350 : ℝ) ≤ 1.9935e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4350)
    (ε := 1.9935e-17) row4350_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4375_table8_mem : (4375, 1.7336e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4375_eps_le : Inputs.default.ε (4375 : ℝ) ≤ 1.7336e-17 := by
  change BKLNW_app.table_8_ε (4375 : ℝ) ≤ 1.7336e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4375)
    (ε := 1.7336e-17) row4375_table8_mem (by norm_num)


/-- Row 3900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3900_k1_margin :
    B_8_exact 1 (3900 : ℝ) (3925 : ℝ) ≤ (0.00000000000098800 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3900 : ℝ) (3925 : ℝ) 2 5629 2.5173e-16
    (0.00000000000098800 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3900_a2_le row3900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1950_lt, exp_neg_2600_lt,
                   Real.exp_pos (-(1950:ℝ)), Real.exp_pos (-(2600:ℝ))])


/-- Row 3900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3900_k2_margin :
    B_8_exact 2 (3900 : ℝ) (3925 : ℝ) ≤ (0.0000000038779 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3900 : ℝ) (3925 : ℝ) 2 5629 2.5173e-16
    (0.0000000038779 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3900_a2_le row3900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1950_lt, exp_neg_2600_lt,
                   Real.exp_pos (-(1950:ℝ)), Real.exp_pos (-(2600:ℝ))])


/-- Row 3900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3900_k3_margin :
    B_8_exact 3 (3900 : ℝ) (3925 : ℝ) ≤ (0.000015221 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3900 : ℝ) (3925 : ℝ) 2 5629 2.5173e-16
    (0.000015221 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3900_a2_le row3900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1950_lt, exp_neg_2600_lt,
                   Real.exp_pos (-(1950:ℝ)), Real.exp_pos (-(2600:ℝ))])


/-- Row 3900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3900_k4_margin :
    B_8_exact 4 (3900 : ℝ) (3925 : ℝ) ≤ (0.059741 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3900 : ℝ) (3925 : ℝ) 2 5629 2.5173e-16
    (0.059741 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3900_a2_le row3900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1950_lt, exp_neg_2600_lt,
                   Real.exp_pos (-(1950:ℝ)), Real.exp_pos (-(2600:ℝ))])


/-- Row 3900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3900_k5_margin :
    B_8_exact 5 (3900 : ℝ) (3925 : ℝ) ≤ (234.49 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3900 : ℝ) (3925 : ℝ) 2 5629 2.5173e-16
    (234.49 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3900_a2_le row3900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1950_lt, exp_neg_2600_lt,
                   Real.exp_pos (-(1950:ℝ)), Real.exp_pos (-(2600:ℝ))])


/-- Row 3925 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3925_k1_margin :
    B_8_exact 1 (3925 : ℝ) (3950 : ℝ) ≤ (0.00000000000086323 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3925 : ℝ) (3950 : ℝ) 2 5665 2.1855e-16
    (0.00000000000086323 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3925_a2_le row3925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3925_2_lt, exp_neg_7850_3_lt,
                   Real.exp_pos (-(3925/2:ℝ)), Real.exp_pos (-(7850/3:ℝ))])


/-- Row 3925 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3925_k2_margin :
    B_8_exact 2 (3925 : ℝ) (3950 : ℝ) ≤ (0.0000000034098 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3925 : ℝ) (3950 : ℝ) 2 5665 2.1855e-16
    (0.0000000034098 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3925_a2_le row3925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3925_2_lt, exp_neg_7850_3_lt,
                   Real.exp_pos (-(3925/2:ℝ)), Real.exp_pos (-(7850/3:ℝ))])


/-- Row 3925 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3925_k3_margin :
    B_8_exact 3 (3925 : ℝ) (3950 : ℝ) ≤ (0.000013469 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3925 : ℝ) (3950 : ℝ) 2 5665 2.1855e-16
    (0.000013469 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3925_a2_le row3925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3925_2_lt, exp_neg_7850_3_lt,
                   Real.exp_pos (-(3925/2:ℝ)), Real.exp_pos (-(7850/3:ℝ))])


/-- Row 3925 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3925_k4_margin :
    B_8_exact 4 (3925 : ℝ) (3950 : ℝ) ≤ (0.053201 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3925 : ℝ) (3950 : ℝ) 2 5665 2.1855e-16
    (0.053201 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3925_a2_le row3925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3925_2_lt, exp_neg_7850_3_lt,
                   Real.exp_pos (-(3925/2:ℝ)), Real.exp_pos (-(7850/3:ℝ))])


/-- Row 3925 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3925_k5_margin :
    B_8_exact 5 (3925 : ℝ) (3950 : ℝ) ≤ (210.14 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3925 : ℝ) (3950 : ℝ) 2 5665 2.1855e-16
    (210.14 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3925_a2_le row3925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3925_2_lt, exp_neg_7850_3_lt,
                   Real.exp_pos (-(3925/2:ℝ)), Real.exp_pos (-(7850/3:ℝ))])


/-- Row 3950 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3950_k1_margin :
    B_8_exact 1 (3950 : ℝ) (3975 : ℝ) ≤ (0.00000000000075449 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3950 : ℝ) (3975 : ℝ) 2 5701 1.8982e-16
    (0.00000000000075449 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3950_a2_le row3950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1975_lt, exp_neg_7900_3_lt,
                   Real.exp_pos (-(1975:ℝ)), Real.exp_pos (-(7900/3:ℝ))])


/-- Row 3950 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3950_k2_margin :
    B_8_exact 2 (3950 : ℝ) (3975 : ℝ) ≤ (0.0000000029991 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3950 : ℝ) (3975 : ℝ) 2 5701 1.8982e-16
    (0.0000000029991 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3950_a2_le row3950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1975_lt, exp_neg_7900_3_lt,
                   Real.exp_pos (-(1975:ℝ)), Real.exp_pos (-(7900/3:ℝ))])


/-- Row 3950 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3950_k3_margin :
    B_8_exact 3 (3950 : ℝ) (3975 : ℝ) ≤ (0.000011922 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3950 : ℝ) (3975 : ℝ) 2 5701 1.8982e-16
    (0.000011922 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3950_a2_le row3950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1975_lt, exp_neg_7900_3_lt,
                   Real.exp_pos (-(1975:ℝ)), Real.exp_pos (-(7900/3:ℝ))])


/-- Row 3950 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3950_k4_margin :
    B_8_exact 4 (3950 : ℝ) (3975 : ℝ) ≤ (0.047388 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3950 : ℝ) (3975 : ℝ) 2 5701 1.8982e-16
    (0.047388 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3950_a2_le row3950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1975_lt, exp_neg_7900_3_lt,
                   Real.exp_pos (-(1975:ℝ)), Real.exp_pos (-(7900/3:ℝ))])


/-- Row 3950 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3950_k5_margin :
    B_8_exact 5 (3950 : ℝ) (3975 : ℝ) ≤ (188.37 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3950 : ℝ) (3975 : ℝ) 2 5701 1.8982e-16
    (188.37 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3950_a2_le row3950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_1975_lt, exp_neg_7900_3_lt,
                   Real.exp_pos (-(1975:ℝ)), Real.exp_pos (-(7900/3:ℝ))])


/-- Row 3975 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3975_k1_margin :
    B_8_exact 1 (3975 : ℝ) (4000 : ℝ) ≤ (0.00000000000065788 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3975 : ℝ) (4000 : ℝ) 2 5737 1.6448e-16
    (0.00000000000065788 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3975_a2_le row3975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3975_2_lt, exp_neg_2650_lt,
                   Real.exp_pos (-(3975/2:ℝ)), Real.exp_pos (-(2650:ℝ))])


/-- Row 3975 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3975_k2_margin :
    B_8_exact 2 (3975 : ℝ) (4000 : ℝ) ≤ (0.0000000026315 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3975 : ℝ) (4000 : ℝ) 2 5737 1.6448e-16
    (0.0000000026315 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3975_a2_le row3975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3975_2_lt, exp_neg_2650_lt,
                   Real.exp_pos (-(3975/2:ℝ)), Real.exp_pos (-(2650:ℝ))])


/-- Row 3975 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3975_k3_margin :
    B_8_exact 3 (3975 : ℝ) (4000 : ℝ) ≤ (0.000010526 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3975 : ℝ) (4000 : ℝ) 2 5737 1.6448e-16
    (0.000010526 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3975_a2_le row3975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3975_2_lt, exp_neg_2650_lt,
                   Real.exp_pos (-(3975/2:ℝ)), Real.exp_pos (-(2650:ℝ))])


/-- Row 3975 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3975_k4_margin :
    B_8_exact 4 (3975 : ℝ) (4000 : ℝ) ≤ (0.042104 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3975 : ℝ) (4000 : ℝ) 2 5737 1.6448e-16
    (0.042104 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3975_a2_le row3975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3975_2_lt, exp_neg_2650_lt,
                   Real.exp_pos (-(3975/2:ℝ)), Real.exp_pos (-(2650:ℝ))])


/-- Row 3975 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3975_k5_margin :
    B_8_exact 5 (3975 : ℝ) (4000 : ℝ) ≤ (168.42 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3975 : ℝ) (4000 : ℝ) 2 5737 1.6448e-16
    (168.42 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3975_a2_le row3975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_3975_2_lt, exp_neg_2650_lt,
                   Real.exp_pos (-(3975/2:ℝ)), Real.exp_pos (-(2650:ℝ))])


/-- Row 4000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4000_k1_margin :
    B_8_exact 1 (4000 : ℝ) (4025 : ℝ) ≤ (0.00000000000057409 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4000 : ℝ) (4025 : ℝ) 2 5773 1.4264e-16
    (0.00000000000057409 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4000_a2_le row4000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2000_lt, exp_neg_8000_3_lt,
                   Real.exp_pos (-(2000:ℝ)), Real.exp_pos (-(8000/3:ℝ))])


/-- Row 4000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4000_k2_margin :
    B_8_exact 2 (4000 : ℝ) (4025 : ℝ) ≤ (0.0000000023107 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4000 : ℝ) (4025 : ℝ) 2 5773 1.4264e-16
    (0.0000000023107 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4000_a2_le row4000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2000_lt, exp_neg_8000_3_lt,
                   Real.exp_pos (-(2000:ℝ)), Real.exp_pos (-(8000/3:ℝ))])


/-- Row 4000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4000_k3_margin :
    B_8_exact 3 (4000 : ℝ) (4025 : ℝ) ≤ (0.0000093007 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4000 : ℝ) (4025 : ℝ) 2 5773 1.4264e-16
    (0.0000093007 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4000_a2_le row4000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2000_lt, exp_neg_8000_3_lt,
                   Real.exp_pos (-(2000:ℝ)), Real.exp_pos (-(8000/3:ℝ))])


/-- Row 4000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4000_k4_margin :
    B_8_exact 4 (4000 : ℝ) (4025 : ℝ) ≤ (0.037435 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4000 : ℝ) (4025 : ℝ) 2 5773 1.4264e-16
    (0.037435 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4000_a2_le row4000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2000_lt, exp_neg_8000_3_lt,
                   Real.exp_pos (-(2000:ℝ)), Real.exp_pos (-(8000/3:ℝ))])


/-- Row 4000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4000_k5_margin :
    B_8_exact 5 (4000 : ℝ) (4025 : ℝ) ≤ (150.68 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4000 : ℝ) (4025 : ℝ) 2 5773 1.4264e-16
    (150.68 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4000_a2_le row4000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2000_lt, exp_neg_8000_3_lt,
                   Real.exp_pos (-(2000:ℝ)), Real.exp_pos (-(8000/3:ℝ))])


/-- Row 4025 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4025_k1_margin :
    B_8_exact 1 (4025 : ℝ) (4050 : ℝ) ≤ (0.00000000000050264 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4025 : ℝ) (4050 : ℝ) 2 5809 1.2412e-16
    (0.00000000000050264 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4025_a2_le row4025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4025_2_lt, exp_neg_8050_3_lt,
                   Real.exp_pos (-(4025/2:ℝ)), Real.exp_pos (-(8050/3:ℝ))])


/-- Row 4025 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4025_k2_margin :
    B_8_exact 2 (4025 : ℝ) (4050 : ℝ) ≤ (0.0000000020357 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4025 : ℝ) (4050 : ℝ) 2 5809 1.2412e-16
    (0.0000000020357 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4025_a2_le row4025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4025_2_lt, exp_neg_8050_3_lt,
                   Real.exp_pos (-(4025/2:ℝ)), Real.exp_pos (-(8050/3:ℝ))])


/-- Row 4025 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4025_k3_margin :
    B_8_exact 3 (4025 : ℝ) (4050 : ℝ) ≤ (0.0000082446 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4025 : ℝ) (4050 : ℝ) 2 5809 1.2412e-16
    (0.0000082446 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4025_a2_le row4025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4025_2_lt, exp_neg_8050_3_lt,
                   Real.exp_pos (-(4025/2:ℝ)), Real.exp_pos (-(8050/3:ℝ))])


/-- Row 4025 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4025_k4_margin :
    B_8_exact 4 (4025 : ℝ) (4050 : ℝ) ≤ (0.033391 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4025 : ℝ) (4050 : ℝ) 2 5809 1.2412e-16
    (0.033391 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4025_a2_le row4025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4025_2_lt, exp_neg_8050_3_lt,
                   Real.exp_pos (-(4025/2:ℝ)), Real.exp_pos (-(8050/3:ℝ))])


/-- Row 4025 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4025_k5_margin :
    B_8_exact 5 (4025 : ℝ) (4050 : ℝ) ≤ (135.23 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4025 : ℝ) (4050 : ℝ) 2 5809 1.2412e-16
    (135.23 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4025_a2_le row4025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4025_2_lt, exp_neg_8050_3_lt,
                   Real.exp_pos (-(4025/2:ℝ)), Real.exp_pos (-(8050/3:ℝ))])


/-- Row 4050 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4050_k1_margin :
    B_8_exact 1 (4050 : ℝ) (4075 : ℝ) ≤ (0.00000000000043803 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4050 : ℝ) (4075 : ℝ) 2 5845 1.0750e-16
    (0.00000000000043803 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4050_a2_le row4050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2025_lt, exp_neg_2700_lt,
                   Real.exp_pos (-(2025:ℝ)), Real.exp_pos (-(2700:ℝ))])


/-- Row 4050 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4050_k2_margin :
    B_8_exact 2 (4050 : ℝ) (4075 : ℝ) ≤ (0.0000000017850 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4050 : ℝ) (4075 : ℝ) 2 5845 1.0750e-16
    (0.0000000017850 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4050_a2_le row4050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2025_lt, exp_neg_2700_lt,
                   Real.exp_pos (-(2025:ℝ)), Real.exp_pos (-(2700:ℝ))])


/-- Row 4050 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4050_k3_margin :
    B_8_exact 3 (4050 : ℝ) (4075 : ℝ) ≤ (0.0000072737 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4050 : ℝ) (4075 : ℝ) 2 5845 1.0750e-16
    (0.0000072737 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4050_a2_le row4050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2025_lt, exp_neg_2700_lt,
                   Real.exp_pos (-(2025:ℝ)), Real.exp_pos (-(2700:ℝ))])


/-- Row 4050 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4050_k4_margin :
    B_8_exact 4 (4050 : ℝ) (4075 : ℝ) ≤ (0.029640 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4050 : ℝ) (4075 : ℝ) 2 5845 1.0750e-16
    (0.029640 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4050_a2_le row4050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2025_lt, exp_neg_2700_lt,
                   Real.exp_pos (-(2025:ℝ)), Real.exp_pos (-(2700:ℝ))])


/-- Row 4050 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4050_k5_margin :
    B_8_exact 5 (4050 : ℝ) (4075 : ℝ) ≤ (120.78 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4050 : ℝ) (4075 : ℝ) 2 5845 1.0750e-16
    (120.78 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4050_a2_le row4050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2025_lt, exp_neg_2700_lt,
                   Real.exp_pos (-(2025:ℝ)), Real.exp_pos (-(2700:ℝ))])


/-- Row 4075 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4075_k1_margin :
    B_8_exact 1 (4075 : ℝ) (4100 : ℝ) ≤ (0.00000000000038285 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4075 : ℝ) (4100 : ℝ) 2 5881 9.3378e-17
    (0.00000000000038285 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4075_a2_le row4075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4075_2_lt, exp_neg_8150_3_lt,
                   Real.exp_pos (-(4075/2:ℝ)), Real.exp_pos (-(8150/3:ℝ))])


/-- Row 4075 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4075_k2_margin :
    B_8_exact 2 (4075 : ℝ) (4100 : ℝ) ≤ (0.0000000015697 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4075 : ℝ) (4100 : ℝ) 2 5881 9.3378e-17
    (0.0000000015697 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4075_a2_le row4075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4075_2_lt, exp_neg_8150_3_lt,
                   Real.exp_pos (-(4075/2:ℝ)), Real.exp_pos (-(8150/3:ℝ))])


/-- Row 4075 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4075_k3_margin :
    B_8_exact 3 (4075 : ℝ) (4100 : ℝ) ≤ (0.0000064356 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4075 : ℝ) (4100 : ℝ) 2 5881 9.3378e-17
    (0.0000064356 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4075_a2_le row4075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4075_2_lt, exp_neg_8150_3_lt,
                   Real.exp_pos (-(4075/2:ℝ)), Real.exp_pos (-(8150/3:ℝ))])


/-- Row 4075 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4075_k4_margin :
    B_8_exact 4 (4075 : ℝ) (4100 : ℝ) ≤ (0.026386 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4075 : ℝ) (4100 : ℝ) 2 5881 9.3378e-17
    (0.026386 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4075_a2_le row4075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4075_2_lt, exp_neg_8150_3_lt,
                   Real.exp_pos (-(4075/2:ℝ)), Real.exp_pos (-(8150/3:ℝ))])


/-- Row 4075 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4075_k5_margin :
    B_8_exact 5 (4075 : ℝ) (4100 : ℝ) ≤ (108.18 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4075 : ℝ) (4100 : ℝ) 2 5881 9.3378e-17
    (108.18 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4075_a2_le row4075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4075_2_lt, exp_neg_8150_3_lt,
                   Real.exp_pos (-(4075/2:ℝ)), Real.exp_pos (-(8150/3:ℝ))])


/-- Row 4100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4100_k1_margin :
    B_8_exact 1 (4100 : ℝ) (4125 : ℝ) ≤ (0.00000000000033428 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4100 : ℝ) (4125 : ℝ) 2 5918 8.1038e-17
    (0.00000000000033428 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4100_a2_le row4100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2050_lt, exp_neg_8200_3_lt,
                   Real.exp_pos (-(2050:ℝ)), Real.exp_pos (-(8200/3:ℝ))])


/-- Row 4100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4100_k2_margin :
    B_8_exact 2 (4100 : ℝ) (4125 : ℝ) ≤ (0.0000000013789 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4100 : ℝ) (4125 : ℝ) 2 5918 8.1038e-17
    (0.0000000013789 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4100_a2_le row4100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2050_lt, exp_neg_8200_3_lt,
                   Real.exp_pos (-(2050:ℝ)), Real.exp_pos (-(8200/3:ℝ))])


/-- Row 4100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4100_k3_margin :
    B_8_exact 3 (4100 : ℝ) (4125 : ℝ) ≤ (0.0000056879 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4100 : ℝ) (4125 : ℝ) 2 5918 8.1038e-17
    (0.0000056879 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4100_a2_le row4100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2050_lt, exp_neg_8200_3_lt,
                   Real.exp_pos (-(2050:ℝ)), Real.exp_pos (-(8200/3:ℝ))])


/-- Row 4100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4100_k4_margin :
    B_8_exact 4 (4100 : ℝ) (4125 : ℝ) ≤ (0.023463 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4100 : ℝ) (4125 : ℝ) 2 5918 8.1038e-17
    (0.023463 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4100_a2_le row4100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2050_lt, exp_neg_8200_3_lt,
                   Real.exp_pos (-(2050:ℝ)), Real.exp_pos (-(8200/3:ℝ))])


/-- Row 4100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4100_k5_margin :
    B_8_exact 5 (4100 : ℝ) (4125 : ℝ) ≤ (96.783 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4100 : ℝ) (4125 : ℝ) 2 5918 8.1038e-17
    (96.783 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4100_a2_le row4100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2050_lt, exp_neg_8200_3_lt,
                   Real.exp_pos (-(2050:ℝ)), Real.exp_pos (-(8200/3:ℝ))])


/-- Row 4125 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4125_k1_margin :
    B_8_exact 1 (4125 : ℝ) (4150 : ℝ) ≤ (0.00000000000029206 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4125 : ℝ) (4150 : ℝ) 2 5954 7.0376e-17
    (0.00000000000029206 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4125_a2_le row4125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4125_2_lt, exp_neg_2750_lt,
                   Real.exp_pos (-(4125/2:ℝ)), Real.exp_pos (-(2750:ℝ))])


/-- Row 4125 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4125_k2_margin :
    B_8_exact 2 (4125 : ℝ) (4150 : ℝ) ≤ (0.0000000012120 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4125 : ℝ) (4150 : ℝ) 2 5954 7.0376e-17
    (0.0000000012120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4125_a2_le row4125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4125_2_lt, exp_neg_2750_lt,
                   Real.exp_pos (-(4125/2:ℝ)), Real.exp_pos (-(2750:ℝ))])


/-- Row 4125 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4125_k3_margin :
    B_8_exact 3 (4125 : ℝ) (4150 : ℝ) ≤ (0.0000050299 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4125 : ℝ) (4150 : ℝ) 2 5954 7.0376e-17
    (0.0000050299 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4125_a2_le row4125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4125_2_lt, exp_neg_2750_lt,
                   Real.exp_pos (-(4125/2:ℝ)), Real.exp_pos (-(2750:ℝ))])


/-- Row 4125 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4125_k4_margin :
    B_8_exact 4 (4125 : ℝ) (4150 : ℝ) ≤ (0.020874 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4125 : ℝ) (4150 : ℝ) 2 5954 7.0376e-17
    (0.020874 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4125_a2_le row4125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4125_2_lt, exp_neg_2750_lt,
                   Real.exp_pos (-(4125/2:ℝ)), Real.exp_pos (-(2750:ℝ))])


/-- Row 4125 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4125_k5_margin :
    B_8_exact 5 (4125 : ℝ) (4150 : ℝ) ≤ (86.628 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4125 : ℝ) (4150 : ℝ) 2 5954 7.0376e-17
    (86.628 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4125_a2_le row4125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4125_2_lt, exp_neg_2750_lt,
                   Real.exp_pos (-(4125/2:ℝ)), Real.exp_pos (-(2750:ℝ))])


/-- Row 4150 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4150_k1_margin :
    B_8_exact 1 (4150 : ℝ) (4175 : ℝ) ≤ (0.00000000000025566 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4150 : ℝ) (4175 : ℝ) 2 5990 6.1237e-17
    (0.00000000000025566 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4150_a2_le row4150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2075_lt, exp_neg_8300_3_lt,
                   Real.exp_pos (-(2075:ℝ)), Real.exp_pos (-(8300/3:ℝ))])


/-- Row 4150 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4150_k2_margin :
    B_8_exact 2 (4150 : ℝ) (4175 : ℝ) ≤ (0.0000000010674 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4150 : ℝ) (4175 : ℝ) 2 5990 6.1237e-17
    (0.0000000010674 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4150_a2_le row4150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2075_lt, exp_neg_8300_3_lt,
                   Real.exp_pos (-(2075:ℝ)), Real.exp_pos (-(8300/3:ℝ))])


/-- Row 4150 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4150_k3_margin :
    B_8_exact 3 (4150 : ℝ) (4175 : ℝ) ≤ (0.0000044563 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4150 : ℝ) (4175 : ℝ) 2 5990 6.1237e-17
    (0.0000044563 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4150_a2_le row4150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2075_lt, exp_neg_8300_3_lt,
                   Real.exp_pos (-(2075:ℝ)), Real.exp_pos (-(8300/3:ℝ))])


/-- Row 4150 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4150_k4_margin :
    B_8_exact 4 (4150 : ℝ) (4175 : ℝ) ≤ (0.018605 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4150 : ℝ) (4175 : ℝ) 2 5990 6.1237e-17
    (0.018605 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4150_a2_le row4150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2075_lt, exp_neg_8300_3_lt,
                   Real.exp_pos (-(2075:ℝ)), Real.exp_pos (-(8300/3:ℝ))])


/-- Row 4150 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4150_k5_margin :
    B_8_exact 5 (4150 : ℝ) (4175 : ℝ) ≤ (77.676 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4150 : ℝ) (4175 : ℝ) 2 5990 6.1237e-17
    (77.676 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4150_a2_le row4150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2075_lt, exp_neg_8300_3_lt,
                   Real.exp_pos (-(2075:ℝ)), Real.exp_pos (-(8300/3:ℝ))])


/-- Row 4175 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4175_k1_margin :
    B_8_exact 1 (4175 : ℝ) (4200 : ℝ) ≤ (0.00000000000022309 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4175 : ℝ) (4200 : ℝ) 2 6026 5.3118e-17
    (0.00000000000022309 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4175_a2_le row4175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4175_2_lt, exp_neg_8350_3_lt,
                   Real.exp_pos (-(4175/2:ℝ)), Real.exp_pos (-(8350/3:ℝ))])


/-- Row 4175 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4175_k2_margin :
    B_8_exact 2 (4175 : ℝ) (4200 : ℝ) ≤ (0.00000000093698 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4175 : ℝ) (4200 : ℝ) 2 6026 5.3118e-17
    (0.00000000093698 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4175_a2_le row4175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4175_2_lt, exp_neg_8350_3_lt,
                   Real.exp_pos (-(4175/2:ℝ)), Real.exp_pos (-(8350/3:ℝ))])


/-- Row 4175 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4175_k3_margin :
    B_8_exact 3 (4175 : ℝ) (4200 : ℝ) ≤ (0.0000039353 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4175 : ℝ) (4200 : ℝ) 2 6026 5.3118e-17
    (0.0000039353 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4175_a2_le row4175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4175_2_lt, exp_neg_8350_3_lt,
                   Real.exp_pos (-(4175/2:ℝ)), Real.exp_pos (-(8350/3:ℝ))])


/-- Row 4175 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4175_k4_margin :
    B_8_exact 4 (4175 : ℝ) (4200 : ℝ) ≤ (0.016528 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4175 : ℝ) (4200 : ℝ) 2 6026 5.3118e-17
    (0.016528 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4175_a2_le row4175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4175_2_lt, exp_neg_8350_3_lt,
                   Real.exp_pos (-(4175/2:ℝ)), Real.exp_pos (-(8350/3:ℝ))])


/-- Row 4175 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4175_k5_margin :
    B_8_exact 5 (4175 : ℝ) (4200 : ℝ) ≤ (69.419 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4175 : ℝ) (4200 : ℝ) 2 6026 5.3118e-17
    (69.419 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4175_a2_le row4175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4175_2_lt, exp_neg_8350_3_lt,
                   Real.exp_pos (-(4175/2:ℝ)), Real.exp_pos (-(8350/3:ℝ))])


/-- Row 4200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4200_k1_margin :
    B_8_exact 1 (4200 : ℝ) (4225 : ℝ) ≤ (0.00000000000019496 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4200 : ℝ) (4225 : ℝ) 2 6062 4.6145e-17
    (0.00000000000019496 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4200_a2_le row4200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2100_lt, exp_neg_2800_lt,
                   Real.exp_pos (-(2100:ℝ)), Real.exp_pos (-(2800:ℝ))])


/-- Row 4200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4200_k2_margin :
    B_8_exact 2 (4200 : ℝ) (4225 : ℝ) ≤ (0.00000000082370 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4200 : ℝ) (4225 : ℝ) 2 6062 4.6145e-17
    (0.00000000082370 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4200_a2_le row4200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2100_lt, exp_neg_2800_lt,
                   Real.exp_pos (-(2100:ℝ)), Real.exp_pos (-(2800:ℝ))])


/-- Row 4200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4200_k3_margin :
    B_8_exact 3 (4200 : ℝ) (4225 : ℝ) ≤ (0.0000034801 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4200 : ℝ) (4225 : ℝ) 2 6062 4.6145e-17
    (0.0000034801 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4200_a2_le row4200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2100_lt, exp_neg_2800_lt,
                   Real.exp_pos (-(2100:ℝ)), Real.exp_pos (-(2800:ℝ))])


/-- Row 4200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4200_k4_margin :
    B_8_exact 4 (4200 : ℝ) (4225 : ℝ) ≤ (0.014704 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4200 : ℝ) (4225 : ℝ) 2 6062 4.6145e-17
    (0.014704 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4200_a2_le row4200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2100_lt, exp_neg_2800_lt,
                   Real.exp_pos (-(2100:ℝ)), Real.exp_pos (-(2800:ℝ))])


/-- Row 4200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4200_k5_margin :
    B_8_exact 5 (4200 : ℝ) (4225 : ℝ) ≤ (62.122 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4200 : ℝ) (4225 : ℝ) 2 6062 4.6145e-17
    (62.122 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4200_a2_le row4200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2100_lt, exp_neg_2800_lt,
                   Real.exp_pos (-(2100:ℝ)), Real.exp_pos (-(2800:ℝ))])


/-- Row 4225 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4225_k1_margin :
    B_8_exact 1 (4225 : ℝ) (4250 : ℝ) ≤ (0.00000000000017047 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4225 : ℝ) (4250 : ℝ) 2 6098 4.0111e-17
    (0.00000000000017047 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4225_a2_le row4225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4225_2_lt, exp_neg_8450_3_lt,
                   Real.exp_pos (-(4225/2:ℝ)), Real.exp_pos (-(8450/3:ℝ))])


/-- Row 4225 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4225_k2_margin :
    B_8_exact 2 (4225 : ℝ) (4250 : ℝ) ≤ (0.00000000072449 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4225 : ℝ) (4250 : ℝ) 2 6098 4.0111e-17
    (0.00000000072449 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4225_a2_le row4225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4225_2_lt, exp_neg_8450_3_lt,
                   Real.exp_pos (-(4225/2:ℝ)), Real.exp_pos (-(8450/3:ℝ))])


/-- Row 4225 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4225_k3_margin :
    B_8_exact 3 (4225 : ℝ) (4250 : ℝ) ≤ (0.0000030791 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4225 : ℝ) (4250 : ℝ) 2 6098 4.0111e-17
    (0.0000030791 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4225_a2_le row4225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4225_2_lt, exp_neg_8450_3_lt,
                   Real.exp_pos (-(4225/2:ℝ)), Real.exp_pos (-(8450/3:ℝ))])


/-- Row 4225 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4225_k4_margin :
    B_8_exact 4 (4225 : ℝ) (4250 : ℝ) ≤ (0.013086 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4225 : ℝ) (4250 : ℝ) 2 6098 4.0111e-17
    (0.013086 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4225_a2_le row4225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4225_2_lt, exp_neg_8450_3_lt,
                   Real.exp_pos (-(4225/2:ℝ)), Real.exp_pos (-(8450/3:ℝ))])


/-- Row 4225 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4225_k5_margin :
    B_8_exact 5 (4225 : ℝ) (4250 : ℝ) ≤ (55.616 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4225 : ℝ) (4250 : ℝ) 2 6098 4.0111e-17
    (55.616 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4225_a2_le row4225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4225_2_lt, exp_neg_8450_3_lt,
                   Real.exp_pos (-(4225/2:ℝ)), Real.exp_pos (-(8450/3:ℝ))])


/-- Row 4250 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4250_k1_margin :
    B_8_exact 1 (4250 : ℝ) (4275 : ℝ) ≤ (0.00000000000014913 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4250 : ℝ) (4275 : ℝ) 2 6134 3.4884e-17
    (0.00000000000014913 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4250_a2_le row4250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2125_lt, exp_neg_8500_3_lt,
                   Real.exp_pos (-(2125:ℝ)), Real.exp_pos (-(8500/3:ℝ))])


/-- Row 4250 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4250_k2_margin :
    B_8_exact 2 (4250 : ℝ) (4275 : ℝ) ≤ (0.00000000063751 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4250 : ℝ) (4275 : ℝ) 2 6134 3.4884e-17
    (0.00000000063751 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4250_a2_le row4250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2125_lt, exp_neg_8500_3_lt,
                   Real.exp_pos (-(2125:ℝ)), Real.exp_pos (-(8500/3:ℝ))])


/-- Row 4250 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4250_k3_margin :
    B_8_exact 3 (4250 : ℝ) (4275 : ℝ) ≤ (0.0000027254 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4250 : ℝ) (4275 : ℝ) 2 6134 3.4884e-17
    (0.0000027254 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4250_a2_le row4250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2125_lt, exp_neg_8500_3_lt,
                   Real.exp_pos (-(2125:ℝ)), Real.exp_pos (-(8500/3:ℝ))])


/-- Row 4250 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4250_k4_margin :
    B_8_exact 4 (4250 : ℝ) (4275 : ℝ) ≤ (0.011651 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4250 : ℝ) (4275 : ℝ) 2 6134 3.4884e-17
    (0.011651 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4250_a2_le row4250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2125_lt, exp_neg_8500_3_lt,
                   Real.exp_pos (-(2125:ℝ)), Real.exp_pos (-(8500/3:ℝ))])


/-- Row 4250 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4250_k5_margin :
    B_8_exact 5 (4250 : ℝ) (4275 : ℝ) ≤ (49.808 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4250 : ℝ) (4275 : ℝ) 2 6134 3.4884e-17
    (49.808 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4250_a2_le row4250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2125_lt, exp_neg_8500_3_lt,
                   Real.exp_pos (-(2125:ℝ)), Real.exp_pos (-(8500/3:ℝ))])


/-- Row 4275 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4275_k1_margin :
    B_8_exact 1 (4275 : ℝ) (4300 : ℝ) ≤ (0.00000000000013036 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4275 : ℝ) (4300 : ℝ) 2 6170 3.0318e-17
    (0.00000000000013036 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4275_a2_le row4275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4275_2_lt, exp_neg_2850_lt,
                   Real.exp_pos (-(4275/2:ℝ)), Real.exp_pos (-(2850:ℝ))])


/-- Row 4275 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4275_k2_margin :
    B_8_exact 2 (4275 : ℝ) (4300 : ℝ) ≤ (0.00000000056056 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4275 : ℝ) (4300 : ℝ) 2 6170 3.0318e-17
    (0.00000000056056 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4275_a2_le row4275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4275_2_lt, exp_neg_2850_lt,
                   Real.exp_pos (-(4275/2:ℝ)), Real.exp_pos (-(2850:ℝ))])


/-- Row 4275 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4275_k3_margin :
    B_8_exact 3 (4275 : ℝ) (4300 : ℝ) ≤ (0.0000024104 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4275 : ℝ) (4300 : ℝ) 2 6170 3.0318e-17
    (0.0000024104 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4275_a2_le row4275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4275_2_lt, exp_neg_2850_lt,
                   Real.exp_pos (-(4275/2:ℝ)), Real.exp_pos (-(2850:ℝ))])


/-- Row 4275 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4275_k4_margin :
    B_8_exact 4 (4275 : ℝ) (4300 : ℝ) ≤ (0.010365 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4275 : ℝ) (4300 : ℝ) 2 6170 3.0318e-17
    (0.010365 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4275_a2_le row4275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4275_2_lt, exp_neg_2850_lt,
                   Real.exp_pos (-(4275/2:ℝ)), Real.exp_pos (-(2850:ℝ))])


/-- Row 4275 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4275_k5_margin :
    B_8_exact 5 (4275 : ℝ) (4300 : ℝ) ≤ (44.568 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4275 : ℝ) (4300 : ℝ) 2 6170 3.0318e-17
    (44.568 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4275_a2_le row4275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4275_2_lt, exp_neg_2850_lt,
                   Real.exp_pos (-(4275/2:ℝ)), Real.exp_pos (-(2850:ℝ))])


/-- Row 4300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4300_k1_margin :
    B_8_exact 1 (4300 : ℝ) (4325 : ℝ) ≤ (0.00000000000011396 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4300 : ℝ) (4325 : ℝ) 2 6206 2.6350e-17
    (0.00000000000011396 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4300_a2_le row4300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2150_lt, exp_neg_8600_3_lt,
                   Real.exp_pos (-(2150:ℝ)), Real.exp_pos (-(8600/3:ℝ))])


/-- Row 4300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4300_k2_margin :
    B_8_exact 2 (4300 : ℝ) (4325 : ℝ) ≤ (0.00000000049288 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4300 : ℝ) (4325 : ℝ) 2 6206 2.6350e-17
    (0.00000000049288 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4300_a2_le row4300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2150_lt, exp_neg_8600_3_lt,
                   Real.exp_pos (-(2150:ℝ)), Real.exp_pos (-(8600/3:ℝ))])


/-- Row 4300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4300_k3_margin :
    B_8_exact 3 (4300 : ℝ) (4325 : ℝ) ≤ (0.0000021317 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4300 : ℝ) (4325 : ℝ) 2 6206 2.6350e-17
    (0.0000021317 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4300_a2_le row4300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2150_lt, exp_neg_8600_3_lt,
                   Real.exp_pos (-(2150:ℝ)), Real.exp_pos (-(8600/3:ℝ))])


/-- Row 4300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4300_k4_margin :
    B_8_exact 4 (4300 : ℝ) (4325 : ℝ) ≤ (0.0092195 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4300 : ℝ) (4325 : ℝ) 2 6206 2.6350e-17
    (0.0092195 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4300_a2_le row4300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2150_lt, exp_neg_8600_3_lt,
                   Real.exp_pos (-(2150:ℝ)), Real.exp_pos (-(8600/3:ℝ))])


/-- Row 4300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4300_k5_margin :
    B_8_exact 5 (4300 : ℝ) (4325 : ℝ) ≤ (39.875 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4300 : ℝ) (4325 : ℝ) 2 6206 2.6350e-17
    (39.875 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4300_a2_le row4300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2150_lt, exp_neg_8600_3_lt,
                   Real.exp_pos (-(2150:ℝ)), Real.exp_pos (-(8600/3:ℝ))])


/-- Row 4325 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4325_k1_margin :
    B_8_exact 1 (4325 : ℝ) (4350 : ℝ) ≤ (0.000000000000099670 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4325 : ℝ) (4350 : ℝ) 2 6242 2.2914e-17
    (0.000000000000099670 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4325_a2_le row4325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4325_2_lt, exp_neg_8650_3_lt,
                   Real.exp_pos (-(4325/2:ℝ)), Real.exp_pos (-(8650/3:ℝ))])


/-- Row 4325 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4325_k2_margin :
    B_8_exact 2 (4325 : ℝ) (4350 : ℝ) ≤ (0.00000000043356 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4325 : ℝ) (4350 : ℝ) 2 6242 2.2914e-17
    (0.00000000043356 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4325_a2_le row4325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4325_2_lt, exp_neg_8650_3_lt,
                   Real.exp_pos (-(4325/2:ℝ)), Real.exp_pos (-(8650/3:ℝ))])


/-- Row 4325 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4325_k3_margin :
    B_8_exact 3 (4325 : ℝ) (4350 : ℝ) ≤ (0.0000018860 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4325 : ℝ) (4350 : ℝ) 2 6242 2.2914e-17
    (0.0000018860 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4325_a2_le row4325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4325_2_lt, exp_neg_8650_3_lt,
                   Real.exp_pos (-(4325/2:ℝ)), Real.exp_pos (-(8650/3:ℝ))])


/-- Row 4325 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4325_k4_margin :
    B_8_exact 4 (4325 : ℝ) (4350 : ℝ) ≤ (0.0082041 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4325 : ℝ) (4350 : ℝ) 2 6242 2.2914e-17
    (0.0082041 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4325_a2_le row4325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4325_2_lt, exp_neg_8650_3_lt,
                   Real.exp_pos (-(4325/2:ℝ)), Real.exp_pos (-(8650/3:ℝ))])


/-- Row 4325 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4325_k5_margin :
    B_8_exact 5 (4325 : ℝ) (4350 : ℝ) ≤ (35.688 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4325 : ℝ) (4350 : ℝ) 2 6242 2.2914e-17
    (35.688 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4325_a2_le row4325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4325_2_lt, exp_neg_8650_3_lt,
                   Real.exp_pos (-(4325/2:ℝ)), Real.exp_pos (-(8650/3:ℝ))])


/-- Row 4350 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4350_k1_margin :
    B_8_exact 1 (4350 : ℝ) (4375 : ℝ) ≤ (0.000000000000087210 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4350 : ℝ) (4375 : ℝ) 2 6278 1.9935e-17
    (0.000000000000087210 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4350_a2_le row4350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2175_lt, exp_neg_2900_lt,
                   Real.exp_pos (-(2175:ℝ)), Real.exp_pos (-(2900:ℝ))])


/-- Row 4350 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4350_k2_margin :
    B_8_exact 2 (4350 : ℝ) (4375 : ℝ) ≤ (0.00000000038154 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4350 : ℝ) (4375 : ℝ) 2 6278 1.9935e-17
    (0.00000000038154 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4350_a2_le row4350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2175_lt, exp_neg_2900_lt,
                   Real.exp_pos (-(2175:ℝ)), Real.exp_pos (-(2900:ℝ))])


/-- Row 4350 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4350_k3_margin :
    B_8_exact 3 (4350 : ℝ) (4375 : ℝ) ≤ (0.0000016693 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4350 : ℝ) (4375 : ℝ) 2 6278 1.9935e-17
    (0.0000016693 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4350_a2_le row4350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2175_lt, exp_neg_2900_lt,
                   Real.exp_pos (-(2175:ℝ)), Real.exp_pos (-(2900:ℝ))])


/-- Row 4350 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4350_k4_margin :
    B_8_exact 4 (4350 : ℝ) (4375 : ℝ) ≤ (0.0073030 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4350 : ℝ) (4375 : ℝ) 2 6278 1.9935e-17
    (0.0073030 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4350_a2_le row4350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2175_lt, exp_neg_2900_lt,
                   Real.exp_pos (-(2175:ℝ)), Real.exp_pos (-(2900:ℝ))])


/-- Row 4350 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4350_k5_margin :
    B_8_exact 5 (4350 : ℝ) (4375 : ℝ) ≤ (31.951 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4350 : ℝ) (4375 : ℝ) 2 6278 1.9935e-17
    (31.951 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4350_a2_le row4350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_2175_lt, exp_neg_2900_lt,
                   Real.exp_pos (-(2175:ℝ)), Real.exp_pos (-(2900:ℝ))])


/-- Row 4375 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4375_k1_margin :
    B_8_exact 1 (4375 : ℝ) (4400 : ℝ) ≤ (0.000000000000076274 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4375 : ℝ) (4400 : ℝ) 2 6314 1.7336e-17
    (0.000000000000076274 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4375_a2_le row4375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4375_2_lt, exp_neg_8750_3_lt,
                   Real.exp_pos (-(4375/2:ℝ)), Real.exp_pos (-(8750/3:ℝ))])


/-- Row 4375 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4375_k2_margin :
    B_8_exact 2 (4375 : ℝ) (4400 : ℝ) ≤ (0.00000000033561 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4375 : ℝ) (4400 : ℝ) 2 6314 1.7336e-17
    (0.00000000033561 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4375_a2_le row4375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4375_2_lt, exp_neg_8750_3_lt,
                   Real.exp_pos (-(4375/2:ℝ)), Real.exp_pos (-(8750/3:ℝ))])


/-- Row 4375 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4375_k3_margin :
    B_8_exact 3 (4375 : ℝ) (4400 : ℝ) ≤ (0.0000014767 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4375 : ℝ) (4400 : ℝ) 2 6314 1.7336e-17
    (0.0000014767 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4375_a2_le row4375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4375_2_lt, exp_neg_8750_3_lt,
                   Real.exp_pos (-(4375/2:ℝ)), Real.exp_pos (-(8750/3:ℝ))])


/-- Row 4375 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4375_k4_margin :
    B_8_exact 4 (4375 : ℝ) (4400 : ℝ) ≤ (0.0064973 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4375 : ℝ) (4400 : ℝ) 2 6314 1.7336e-17
    (0.0064973 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4375_a2_le row4375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4375_2_lt, exp_neg_8750_3_lt,
                   Real.exp_pos (-(4375/2:ℝ)), Real.exp_pos (-(8750/3:ℝ))])


/-- Row 4375 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4375_k5_margin :
    B_8_exact 5 (4375 : ℝ) (4400 : ℝ) ≤ (28.588 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4375 : ℝ) (4400 : ℝ) 2 6314 1.7336e-17
    (28.588 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4375_a2_le row4375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_4375_2_lt, exp_neg_8750_3_lt,
                   Real.exp_pos (-(4375/2:ℝ)), Real.exp_pos (-(8750/3:ℝ))])

end BKLNW
