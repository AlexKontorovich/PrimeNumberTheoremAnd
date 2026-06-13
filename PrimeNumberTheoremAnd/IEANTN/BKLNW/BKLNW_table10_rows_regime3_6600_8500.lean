import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Generated regime-3 pointwise Table 10 margin certificates.

This shard expects `row_bound_pointwise`
to be available from `BKLNW_table10_rows_core.lean`.
-/

namespace BKLNW

open Real Set Finset


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


private lemma row6600_a2_le : Inputs.default.a₂ (6600 : ℝ) ≤ (9524 : ℝ) := by
  have h := a2_crude_le (6600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6600 : ℝ) / log 2⌋₊ : ℝ) ≤ (6600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6600 : ℝ) / log 2 ≤ 9522 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9522 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9524 := by norm_num


private lemma row6700_a2_le : Inputs.default.a₂ (6700 : ℝ) ≤ (9669 : ℝ) := by
  have h := a2_crude_le (6700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6700 : ℝ) / log 2⌋₊ : ℝ) ≤ (6700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6700 : ℝ) / log 2 ≤ 9667 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9667 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9669 := by norm_num


private lemma row6800_a2_le : Inputs.default.a₂ (6800 : ℝ) ≤ (9813 : ℝ) := by
  have h := a2_crude_le (6800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6800 : ℝ) / log 2⌋₊ : ℝ) ≤ (6800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6800 : ℝ) / log 2 ≤ 9811 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9811 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9813 := by norm_num


private lemma row6900_a2_le : Inputs.default.a₂ (6900 : ℝ) ≤ (9957 : ℝ) := by
  have h := a2_crude_le (6900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(6900 : ℝ) / log 2⌋₊ : ℝ) ≤ (6900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (6900 : ℝ) / log 2 ≤ 9955 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (6900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(6900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (9955 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 9957 := by norm_num


private lemma row7000_a2_le : Inputs.default.a₂ (7000 : ℝ) ≤ (10101 : ℝ) := by
  have h := a2_crude_le (7000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7000 : ℝ) / log 2⌋₊ : ℝ) ≤ (7000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7000 : ℝ) / log 2 ≤ 10099 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10099 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10101 := by norm_num


private lemma row7100_a2_le : Inputs.default.a₂ (7100 : ℝ) ≤ (10246 : ℝ) := by
  have h := a2_crude_le (7100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7100 : ℝ) / log 2⌋₊ : ℝ) ≤ (7100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7100 : ℝ) / log 2 ≤ 10244 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10244 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10246 := by norm_num


private lemma row7200_a2_le : Inputs.default.a₂ (7200 : ℝ) ≤ (10390 : ℝ) := by
  have h := a2_crude_le (7200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7200 : ℝ) / log 2⌋₊ : ℝ) ≤ (7200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7200 : ℝ) / log 2 ≤ 10388 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10388 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10390 := by norm_num


private lemma row7300_a2_le : Inputs.default.a₂ (7300 : ℝ) ≤ (10534 : ℝ) := by
  have h := a2_crude_le (7300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7300 : ℝ) / log 2⌋₊ : ℝ) ≤ (7300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7300 : ℝ) / log 2 ≤ 10532 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10532 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10534 := by norm_num


private lemma row7400_a2_le : Inputs.default.a₂ (7400 : ℝ) ≤ (10678 : ℝ) := by
  have h := a2_crude_le (7400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7400 : ℝ) / log 2⌋₊ : ℝ) ≤ (7400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7400 : ℝ) / log 2 ≤ 10676 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10676 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10678 := by norm_num


private lemma row7500_a2_le : Inputs.default.a₂ (7500 : ℝ) ≤ (10823 : ℝ) := by
  have h := a2_crude_le (7500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7500 : ℝ) / log 2⌋₊ : ℝ) ≤ (7500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7500 : ℝ) / log 2 ≤ 10821 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10821 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10823 := by norm_num


private lemma row7600_a2_le : Inputs.default.a₂ (7600 : ℝ) ≤ (10967 : ℝ) := by
  have h := a2_crude_le (7600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7600 : ℝ) / log 2⌋₊ : ℝ) ≤ (7600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7600 : ℝ) / log 2 ≤ 10965 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (10965 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 10967 := by norm_num


private lemma row7700_a2_le : Inputs.default.a₂ (7700 : ℝ) ≤ (11111 : ℝ) := by
  have h := a2_crude_le (7700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7700 : ℝ) / log 2⌋₊ : ℝ) ≤ (7700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7700 : ℝ) / log 2 ≤ 11109 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11109 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11111 := by norm_num


private lemma row7800_a2_le : Inputs.default.a₂ (7800 : ℝ) ≤ (11256 : ℝ) := by
  have h := a2_crude_le (7800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7800 : ℝ) / log 2⌋₊ : ℝ) ≤ (7800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7800 : ℝ) / log 2 ≤ 11254 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11254 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11256 := by norm_num


private lemma row7900_a2_le : Inputs.default.a₂ (7900 : ℝ) ≤ (11400 : ℝ) := by
  have h := a2_crude_le (7900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(7900 : ℝ) / log 2⌋₊ : ℝ) ≤ (7900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (7900 : ℝ) / log 2 ≤ 11398 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (7900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(7900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11398 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11400 := by norm_num


private lemma row8000_a2_le : Inputs.default.a₂ (8000 : ℝ) ≤ (11544 : ℝ) := by
  have h := a2_crude_le (8000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8000 : ℝ) / log 2⌋₊ : ℝ) ≤ (8000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8000 : ℝ) / log 2 ≤ 11542 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11542 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11544 := by norm_num


private lemma row8100_a2_le : Inputs.default.a₂ (8100 : ℝ) ≤ (11688 : ℝ) := by
  have h := a2_crude_le (8100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8100 : ℝ) / log 2⌋₊ : ℝ) ≤ (8100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8100 : ℝ) / log 2 ≤ 11686 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11686 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11688 := by norm_num


private lemma row8200_a2_le : Inputs.default.a₂ (8200 : ℝ) ≤ (11833 : ℝ) := by
  have h := a2_crude_le (8200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8200 : ℝ) / log 2⌋₊ : ℝ) ≤ (8200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8200 : ℝ) / log 2 ≤ 11831 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11831 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11833 := by norm_num


private lemma row8300_a2_le : Inputs.default.a₂ (8300 : ℝ) ≤ (11977 : ℝ) := by
  have h := a2_crude_le (8300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8300 : ℝ) / log 2⌋₊ : ℝ) ≤ (8300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8300 : ℝ) / log 2 ≤ 11975 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (11975 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 11977 := by norm_num


private lemma row8400_a2_le : Inputs.default.a₂ (8400 : ℝ) ≤ (12121 : ℝ) := by
  have h := a2_crude_le (8400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8400 : ℝ) / log 2⌋₊ : ℝ) ≤ (8400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8400 : ℝ) / log 2 ≤ 12119 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12119 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12121 := by norm_num


private lemma row8500_a2_le : Inputs.default.a₂ (8500 : ℝ) ≤ (12265 : ℝ) := by
  have h := a2_crude_le (8500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8500 : ℝ) / log 2⌋₊ : ℝ) ≤ (8500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8500 : ℝ) / log 2 ≤ 12263 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12263 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12265 := by norm_num


set_option maxRecDepth 10000 in
private lemma row6600_table8_mem : (6600, 1.4521e-22) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6600_eps_le : Inputs.default.ε (6600 : ℝ) ≤ 1.4521e-22 := by
  change BKLNW_app.table_8_ε (6600 : ℝ) ≤ 1.4521e-22
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6600)
    (ε := 1.4521e-22) row6600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6700_table8_mem : (6700, 8.8894e-23) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6700_eps_le : Inputs.default.ε (6700 : ℝ) ≤ 8.8894e-23 := by
  change BKLNW_app.table_8_ε (6700 : ℝ) ≤ 8.8894e-23
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6700)
    (ε := 8.8894e-23) row6700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6800_table8_mem : (6800, 5.4568e-23) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6800_eps_le : Inputs.default.ε (6800 : ℝ) ≤ 5.4568e-23 := by
  change BKLNW_app.table_8_ε (6800 : ℝ) ≤ 5.4568e-23
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6800)
    (ε := 5.4568e-23) row6800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row6900_table8_mem : (6900, 3.3650e-23) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row6900_eps_le : Inputs.default.ε (6900 : ℝ) ≤ 3.3650e-23 := by
  change BKLNW_app.table_8_ε (6900 : ℝ) ≤ 3.3650e-23
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 6900)
    (ε := 3.3650e-23) row6900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7000_table8_mem : (7000, 2.0766e-23) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7000_eps_le : Inputs.default.ε (7000 : ℝ) ≤ 2.0766e-23 := by
  change BKLNW_app.table_8_ε (7000 : ℝ) ≤ 2.0766e-23
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7000)
    (ε := 2.0766e-23) row7000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7100_table8_mem : (7100, 1.2893e-23) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7100_eps_le : Inputs.default.ε (7100 : ℝ) ≤ 1.2893e-23 := by
  change BKLNW_app.table_8_ε (7100 : ℝ) ≤ 1.2893e-23
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7100)
    (ε := 1.2893e-23) row7100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7200_table8_mem : (7200, 8.0276e-24) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7200_eps_le : Inputs.default.ε (7200 : ℝ) ≤ 8.0276e-24 := by
  change BKLNW_app.table_8_ε (7200 : ℝ) ≤ 8.0276e-24
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7200)
    (ε := 8.0276e-24) row7200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7300_table8_mem : (7300, 5.0020e-24) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7300_eps_le : Inputs.default.ε (7300 : ℝ) ≤ 5.0020e-24 := by
  change BKLNW_app.table_8_ε (7300 : ℝ) ≤ 5.0020e-24
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7300)
    (ε := 5.0020e-24) row7300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7400_table8_mem : (7400, 3.1319e-24) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7400_eps_le : Inputs.default.ε (7400 : ℝ) ≤ 3.1319e-24 := by
  change BKLNW_app.table_8_ε (7400 : ℝ) ≤ 3.1319e-24
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7400)
    (ε := 3.1319e-24) row7400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7500_table8_mem : (7500, 1.9616e-24) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7500_eps_le : Inputs.default.ε (7500 : ℝ) ≤ 1.9616e-24 := by
  change BKLNW_app.table_8_ε (7500 : ℝ) ≤ 1.9616e-24
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7500)
    (ε := 1.9616e-24) row7500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7600_table8_mem : (7600, 1.2315e-24) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7600_eps_le : Inputs.default.ε (7600 : ℝ) ≤ 1.2315e-24 := by
  change BKLNW_app.table_8_ε (7600 : ℝ) ≤ 1.2315e-24
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7600)
    (ε := 1.2315e-24) row7600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7700_table8_mem : (7700, 7.7664e-25) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7700_eps_le : Inputs.default.ε (7700 : ℝ) ≤ 7.7664e-25 := by
  change BKLNW_app.table_8_ε (7700 : ℝ) ≤ 7.7664e-25
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7700)
    (ε := 7.7664e-25) row7700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7800_table8_mem : (7800, 4.9129e-25) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7800_eps_le : Inputs.default.ε (7800 : ℝ) ≤ 4.9129e-25 := by
  change BKLNW_app.table_8_ε (7800 : ℝ) ≤ 4.9129e-25
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7800)
    (ε := 4.9129e-25) row7800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row7900_table8_mem : (7900, 3.1161e-25) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row7900_eps_le : Inputs.default.ε (7900 : ℝ) ≤ 3.1161e-25 := by
  change BKLNW_app.table_8_ε (7900 : ℝ) ≤ 3.1161e-25
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 7900)
    (ε := 3.1161e-25) row7900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8000_table8_mem : (8000, 1.9762e-25) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8000_eps_le : Inputs.default.ε (8000 : ℝ) ≤ 1.9762e-25 := by
  change BKLNW_app.table_8_ε (8000 : ℝ) ≤ 1.9762e-25
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8000)
    (ε := 1.9762e-25) row8000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8100_table8_mem : (8100, 1.2594e-25) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8100_eps_le : Inputs.default.ε (8100 : ℝ) ≤ 1.2594e-25 := by
  change BKLNW_app.table_8_ε (8100 : ℝ) ≤ 1.2594e-25
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8100)
    (ε := 1.2594e-25) row8100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8200_table8_mem : (8200, 8.0517e-26) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8200_eps_le : Inputs.default.ε (8200 : ℝ) ≤ 8.0517e-26 := by
  change BKLNW_app.table_8_ε (8200 : ℝ) ≤ 8.0517e-26
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8200)
    (ε := 8.0517e-26) row8200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8300_table8_mem : (8300, 5.1497e-26) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8300_eps_le : Inputs.default.ε (8300 : ℝ) ≤ 5.1497e-26 := by
  change BKLNW_app.table_8_ε (8300 : ℝ) ≤ 5.1497e-26
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8300)
    (ε := 5.1497e-26) row8300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8400_table8_mem : (8400, 3.3065e-26) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8400_eps_le : Inputs.default.ε (8400 : ℝ) ≤ 3.3065e-26 := by
  change BKLNW_app.table_8_ε (8400 : ℝ) ≤ 3.3065e-26
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8400)
    (ε := 3.3065e-26) row8400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row8500_table8_mem : (8500, 2.1298e-26) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8500_eps_le : Inputs.default.ε (8500 : ℝ) ≤ 2.1298e-26 := by
  change BKLNW_app.table_8_ε (8500 : ℝ) ≤ 2.1298e-26
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8500)
    (ε := 2.1298e-26) row8500_table8_mem (by norm_num)


/-- Row 6600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6600_k1_margin :
    B_8_exact 1 (6600 : ℝ) (6700 : ℝ) ≤ (0.00000000000000000097287 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6600 : ℝ) (6700 : ℝ) 2 9524 1.4521e-22
    (0.00000000000000000097287 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6600_a2_le row6600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6600_k2_margin :
    B_8_exact 2 (6600 : ℝ) (6700 : ℝ) ≤ (0.0000000000000065182 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6600 : ℝ) (6700 : ℝ) 2 9524 1.4521e-22
    (0.0000000000000065182 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6600_a2_le row6600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6600_k3_margin :
    B_8_exact 3 (6600 : ℝ) (6700 : ℝ) ≤ (0.000000000043672 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6600 : ℝ) (6700 : ℝ) 2 9524 1.4521e-22
    (0.000000000043672 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6600_a2_le row6600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6600_k4_margin :
    B_8_exact 4 (6600 : ℝ) (6700 : ℝ) ≤ (0.00000029260 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6600 : ℝ) (6700 : ℝ) 2 9524 1.4521e-22
    (0.00000029260 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6600_a2_le row6600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6600_k5_margin :
    B_8_exact 5 (6600 : ℝ) (6700 : ℝ) ≤ (0.0019604 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6600 : ℝ) (6700 : ℝ) 2 9524 1.4521e-22
    (0.0019604 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6600_a2_le row6600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6700_k1_margin :
    B_8_exact 1 (6700 : ℝ) (6800 : ℝ) ≤ (0.00000000000000000060447 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6700 : ℝ) (6800 : ℝ) 2 9669 8.8894e-23
    (0.00000000000000000060447 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6700_a2_le row6700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6700_k2_margin :
    B_8_exact 2 (6700 : ℝ) (6800 : ℝ) ≤ (0.0000000000000041104 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6700 : ℝ) (6800 : ℝ) 2 9669 8.8894e-23
    (0.0000000000000041104 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6700_a2_le row6700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6700_k3_margin :
    B_8_exact 3 (6700 : ℝ) (6800 : ℝ) ≤ (0.000000000027951 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6700 : ℝ) (6800 : ℝ) 2 9669 8.8894e-23
    (0.000000000027951 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6700_a2_le row6700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6700_k4_margin :
    B_8_exact 4 (6700 : ℝ) (6800 : ℝ) ≤ (0.00000019007 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6700 : ℝ) (6800 : ℝ) 2 9669 8.8894e-23
    (0.00000019007 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6700_a2_le row6700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6700_k5_margin :
    B_8_exact 5 (6700 : ℝ) (6800 : ℝ) ≤ (0.0012924 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6700 : ℝ) (6800 : ℝ) 2 9669 8.8894e-23
    (0.0012924 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6700_a2_le row6700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6800_k1_margin :
    B_8_exact 1 (6800 : ℝ) (6900 : ℝ) ≤ (0.00000000000000000037651 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6800 : ℝ) (6900 : ℝ) 2 9813 5.4568e-23
    (0.00000000000000000037651 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6800_a2_le row6800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6800_k2_margin :
    B_8_exact 2 (6800 : ℝ) (6900 : ℝ) ≤ (0.0000000000000025979 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6800 : ℝ) (6900 : ℝ) 2 9813 5.4568e-23
    (0.0000000000000025979 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6800_a2_le row6800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6800_k3_margin :
    B_8_exact 3 (6800 : ℝ) (6900 : ℝ) ≤ (0.000000000017926 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6800 : ℝ) (6900 : ℝ) 2 9813 5.4568e-23
    (0.000000000017926 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6800_a2_le row6800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6800_k4_margin :
    B_8_exact 4 (6800 : ℝ) (6900 : ℝ) ≤ (0.00000012369 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6800 : ℝ) (6900 : ℝ) 2 9813 5.4568e-23
    (0.00000012369 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6800_a2_le row6800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6800_k5_margin :
    B_8_exact 5 (6800 : ℝ) (6900 : ℝ) ≤ (0.00085344 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6800 : ℝ) (6900 : ℝ) 2 9813 5.4568e-23
    (0.00085344 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6800_a2_le row6800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row6900_k1_margin :
    B_8_exact 1 (6900 : ℝ) (7000 : ℝ) ≤ (0.00000000000000000023554 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (6900 : ℝ) (7000 : ℝ) 2 9957 3.3650e-23
    (0.00000000000000000023554 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6900_a2_le row6900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row6900_k2_margin :
    B_8_exact 2 (6900 : ℝ) (7000 : ℝ) ≤ (0.0000000000000016488 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (6900 : ℝ) (7000 : ℝ) 2 9957 3.3650e-23
    (0.0000000000000016488 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6900_a2_le row6900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row6900_k3_margin :
    B_8_exact 3 (6900 : ℝ) (7000 : ℝ) ≤ (0.000000000011542 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (6900 : ℝ) (7000 : ℝ) 2 9957 3.3650e-23
    (0.000000000011542 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6900_a2_le row6900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row6900_k4_margin :
    B_8_exact 4 (6900 : ℝ) (7000 : ℝ) ≤ (0.000000080791 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (6900 : ℝ) (7000 : ℝ) 2 9957 3.3650e-23
    (0.000000080791 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6900_a2_le row6900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 6900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row6900_k5_margin :
    B_8_exact 5 (6900 : ℝ) (7000 : ℝ) ≤ (0.00056554 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (6900 : ℝ) (7000 : ℝ) 2 9957 3.3650e-23
    (0.00056554 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row6900_a2_le row6900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7000_k1_margin :
    B_8_exact 1 (7000 : ℝ) (7100 : ℝ) ≤ (0.00000000000000000014744 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7000 : ℝ) (7100 : ℝ) 2 10101 2.0766e-23
    (0.00000000000000000014744 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7000_a2_le row7000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7000_k2_margin :
    B_8_exact 2 (7000 : ℝ) (7100 : ℝ) ≤ (0.0000000000000010468 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7000 : ℝ) (7100 : ℝ) 2 10101 2.0766e-23
    (0.0000000000000010468 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7000_a2_le row7000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7000_k3_margin :
    B_8_exact 3 (7000 : ℝ) (7100 : ℝ) ≤ (0.0000000000074322 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7000 : ℝ) (7100 : ℝ) 2 10101 2.0766e-23
    (0.0000000000074322 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7000_a2_le row7000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7000_k4_margin :
    B_8_exact 4 (7000 : ℝ) (7100 : ℝ) ≤ (0.000000052769 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7000 : ℝ) (7100 : ℝ) 2 10101 2.0766e-23
    (0.000000052769 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7000_a2_le row7000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7000_k5_margin :
    B_8_exact 5 (7000 : ℝ) (7100 : ℝ) ≤ (0.00037466 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7000 : ℝ) (7100 : ℝ) 2 10101 2.0766e-23
    (0.00037466 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7000_a2_le row7000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7100_k1_margin :
    B_8_exact 1 (7100 : ℝ) (7200 : ℝ) ≤ (0.000000000000000000092826 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7100 : ℝ) (7200 : ℝ) 2 10246 1.2893e-23
    (0.000000000000000000092826 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7100_a2_le row7100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7100_k2_margin :
    B_8_exact 2 (7100 : ℝ) (7200 : ℝ) ≤ (0.00000000000000066834 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7100 : ℝ) (7200 : ℝ) 2 10246 1.2893e-23
    (0.00000000000000066834 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7100_a2_le row7100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7100_k3_margin :
    B_8_exact 3 (7100 : ℝ) (7200 : ℝ) ≤ (0.0000000000048121 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7100 : ℝ) (7200 : ℝ) 2 10246 1.2893e-23
    (0.0000000000048121 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7100_a2_le row7100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7100_k4_margin :
    B_8_exact 4 (7100 : ℝ) (7200 : ℝ) ≤ (0.000000034647 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7100 : ℝ) (7200 : ℝ) 2 10246 1.2893e-23
    (0.000000034647 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7100_a2_le row7100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7100_k5_margin :
    B_8_exact 5 (7100 : ℝ) (7200 : ℝ) ≤ (0.00024946 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7100 : ℝ) (7200 : ℝ) 2 10246 1.2893e-23
    (0.00024946 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7100_a2_le row7100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7200_k1_margin :
    B_8_exact 1 (7200 : ℝ) (7300 : ℝ) ≤ (0.000000000000000000058601 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7200 : ℝ) (7300 : ℝ) 2 10390 8.0276e-24
    (0.000000000000000000058601 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7200_a2_le row7200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7200_k2_margin :
    B_8_exact 2 (7200 : ℝ) (7300 : ℝ) ≤ (0.00000000000000042779 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7200 : ℝ) (7300 : ℝ) 2 10390 8.0276e-24
    (0.00000000000000042779 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7200_a2_le row7200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7200_k3_margin :
    B_8_exact 3 (7200 : ℝ) (7300 : ℝ) ≤ (0.0000000000031229 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7200 : ℝ) (7300 : ℝ) 2 10390 8.0276e-24
    (0.0000000000031229 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7200_a2_le row7200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7200_k4_margin :
    B_8_exact 4 (7200 : ℝ) (7300 : ℝ) ≤ (0.000000022797 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7200 : ℝ) (7300 : ℝ) 2 10390 8.0276e-24
    (0.000000022797 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7200_a2_le row7200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7200_k5_margin :
    B_8_exact 5 (7200 : ℝ) (7300 : ℝ) ≤ (0.00016642 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7200 : ℝ) (7300 : ℝ) 2 10390 8.0276e-24
    (0.00016642 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7200_a2_le row7200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7300_k1_margin :
    B_8_exact 1 (7300 : ℝ) (7400 : ℝ) ≤ (0.000000000000000000037014 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7300 : ℝ) (7400 : ℝ) 2 10534 5.0020e-24
    (0.000000000000000000037014 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7300_a2_le row7300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7300_k2_margin :
    B_8_exact 2 (7300 : ℝ) (7400 : ℝ) ≤ (0.00000000000000027390 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7300 : ℝ) (7400 : ℝ) 2 10534 5.0020e-24
    (0.00000000000000027390 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7300_a2_le row7300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7300_k3_margin :
    B_8_exact 3 (7300 : ℝ) (7400 : ℝ) ≤ (0.0000000000020269 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7300 : ℝ) (7400 : ℝ) 2 10534 5.0020e-24
    (0.0000000000020269 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7300_a2_le row7300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7300_k4_margin :
    B_8_exact 4 (7300 : ℝ) (7400 : ℝ) ≤ (0.000000014999 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7300 : ℝ) (7400 : ℝ) 2 10534 5.0020e-24
    (0.000000014999 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7300_a2_le row7300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7300_k5_margin :
    B_8_exact 5 (7300 : ℝ) (7400 : ℝ) ≤ (0.00011099 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7300 : ℝ) (7400 : ℝ) 2 10534 5.0020e-24
    (0.00011099 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7300_a2_le row7300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7400_k1_margin :
    B_8_exact 1 (7400 : ℝ) (7500 : ℝ) ≤ (0.000000000000000000023488 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7400 : ℝ) (7500 : ℝ) 2 10678 3.1319e-24
    (0.000000000000000000023488 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7400_a2_le row7400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7400_k2_margin :
    B_8_exact 2 (7400 : ℝ) (7500 : ℝ) ≤ (0.00000000000000017616 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7400 : ℝ) (7500 : ℝ) 2 10678 3.1319e-24
    (0.00000000000000017616 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7400_a2_le row7400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7400_k3_margin :
    B_8_exact 3 (7400 : ℝ) (7500 : ℝ) ≤ (0.0000000000013212 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7400 : ℝ) (7500 : ℝ) 2 10678 3.1319e-24
    (0.0000000000013212 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7400_a2_le row7400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7400_k4_margin :
    B_8_exact 4 (7400 : ℝ) (7500 : ℝ) ≤ (0.0000000099091 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7400 : ℝ) (7500 : ℝ) 2 10678 3.1319e-24
    (0.0000000099091 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7400_a2_le row7400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7400_k5_margin :
    B_8_exact 5 (7400 : ℝ) (7500 : ℝ) ≤ (0.000074318 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7400 : ℝ) (7500 : ℝ) 2 10678 3.1319e-24
    (0.000074318 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7400_a2_le row7400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7500_k1_margin :
    B_8_exact 1 (7500 : ℝ) (7600 : ℝ) ≤ (0.000000000000000000014907 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7500 : ℝ) (7600 : ℝ) 2 10823 1.9616e-24
    (0.000000000000000000014907 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7500_a2_le row7500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7500_k2_margin :
    B_8_exact 2 (7500 : ℝ) (7600 : ℝ) ≤ (0.00000000000000011330 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7500 : ℝ) (7600 : ℝ) 2 10823 1.9616e-24
    (0.00000000000000011330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7500_a2_le row7500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7500_k3_margin :
    B_8_exact 3 (7500 : ℝ) (7600 : ℝ) ≤ (0.00000000000086105 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7500 : ℝ) (7600 : ℝ) 2 10823 1.9616e-24
    (0.00000000000086105 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7500_a2_le row7500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7500_k4_margin :
    B_8_exact 4 (7500 : ℝ) (7600 : ℝ) ≤ (0.0000000065440 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7500 : ℝ) (7600 : ℝ) 2 10823 1.9616e-24
    (0.0000000065440 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7500_a2_le row7500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7500_k5_margin :
    B_8_exact 5 (7500 : ℝ) (7600 : ℝ) ≤ (0.000049734 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7500 : ℝ) (7600 : ℝ) 2 10823 1.9616e-24
    (0.000049734 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7500_a2_le row7500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7600_k1_margin :
    B_8_exact 1 (7600 : ℝ) (7700 : ℝ) ≤ (0.0000000000000000000094822 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7600 : ℝ) (7700 : ℝ) 2 10967 1.2315e-24
    (0.0000000000000000000094822 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7600_a2_le row7600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7600_k2_margin :
    B_8_exact 2 (7600 : ℝ) (7700 : ℝ) ≤ (0.000000000000000073013 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7600 : ℝ) (7700 : ℝ) 2 10967 1.2315e-24
    (0.000000000000000073013 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7600_a2_le row7600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7600_k3_margin :
    B_8_exact 3 (7600 : ℝ) (7700 : ℝ) ≤ (0.00000000000056220 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7600 : ℝ) (7700 : ℝ) 2 10967 1.2315e-24
    (0.00000000000056220 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7600_a2_le row7600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7600_k4_margin :
    B_8_exact 4 (7600 : ℝ) (7700 : ℝ) ≤ (0.0000000043289 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7600 : ℝ) (7700 : ℝ) 2 10967 1.2315e-24
    (0.0000000043289 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7600_a2_le row7600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7600_k5_margin :
    B_8_exact 5 (7600 : ℝ) (7700 : ℝ) ≤ (0.000033333 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7600 : ℝ) (7700 : ℝ) 2 10967 1.2315e-24
    (0.000033333 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7600_a2_le row7600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7700_k1_margin :
    B_8_exact 1 (7700 : ℝ) (7800 : ℝ) ≤ (0.0000000000000000000060569 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7700 : ℝ) (7800 : ℝ) 2 11111 7.7664e-25
    (0.0000000000000000000060569 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7700_a2_le row7700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7700_k2_margin :
    B_8_exact 2 (7700 : ℝ) (7800 : ℝ) ≤ (0.000000000000000047244 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7700 : ℝ) (7800 : ℝ) 2 11111 7.7664e-25
    (0.000000000000000047244 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7700_a2_le row7700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7700_k3_margin :
    B_8_exact 3 (7700 : ℝ) (7800 : ℝ) ≤ (0.00000000000036850 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7700 : ℝ) (7800 : ℝ) 2 11111 7.7664e-25
    (0.00000000000036850 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7700_a2_le row7700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7700_k4_margin :
    B_8_exact 4 (7700 : ℝ) (7800 : ℝ) ≤ (0.0000000028743 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7700 : ℝ) (7800 : ℝ) 2 11111 7.7664e-25
    (0.0000000028743 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7700_a2_le row7700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7700_k5_margin :
    B_8_exact 5 (7700 : ℝ) (7800 : ℝ) ≤ (0.000022420 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7700 : ℝ) (7800 : ℝ) 2 11111 7.7664e-25
    (0.000022420 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7700_a2_le row7700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7800_k1_margin :
    B_8_exact 1 (7800 : ℝ) (7900 : ℝ) ≤ (0.0000000000000000000038811 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7800 : ℝ) (7900 : ℝ) 2 11256 4.9129e-25
    (0.0000000000000000000038811 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7800_a2_le row7800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7800_k2_margin :
    B_8_exact 2 (7800 : ℝ) (7900 : ℝ) ≤ (0.000000000000000030661 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7800 : ℝ) (7900 : ℝ) 2 11256 4.9129e-25
    (0.000000000000000030661 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7800_a2_le row7800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7800_k3_margin :
    B_8_exact 3 (7800 : ℝ) (7900 : ℝ) ≤ (0.00000000000024222 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7800 : ℝ) (7900 : ℝ) 2 11256 4.9129e-25
    (0.00000000000024222 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7800_a2_le row7800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7800_k4_margin :
    B_8_exact 4 (7800 : ℝ) (7900 : ℝ) ≤ (0.0000000019136 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7800 : ℝ) (7900 : ℝ) 2 11256 4.9129e-25
    (0.0000000019136 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7800_a2_le row7800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7800_k5_margin :
    B_8_exact 5 (7800 : ℝ) (7900 : ℝ) ≤ (0.000015117 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7800 : ℝ) (7900 : ℝ) 2 11256 4.9129e-25
    (0.000015117 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7800_a2_le row7800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row7900_k1_margin :
    B_8_exact 1 (7900 : ℝ) (8000 : ℝ) ≤ (0.0000000000000000000024928 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (7900 : ℝ) (8000 : ℝ) 2 11400 3.1161e-25
    (0.0000000000000000000024928 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7900_a2_le row7900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row7900_k2_margin :
    B_8_exact 2 (7900 : ℝ) (8000 : ℝ) ≤ (0.000000000000000019942 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (7900 : ℝ) (8000 : ℝ) 2 11400 3.1161e-25
    (0.000000000000000019942 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7900_a2_le row7900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row7900_k3_margin :
    B_8_exact 3 (7900 : ℝ) (8000 : ℝ) ≤ (0.00000000000015954 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (7900 : ℝ) (8000 : ℝ) 2 11400 3.1161e-25
    (0.00000000000015954 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7900_a2_le row7900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row7900_k4_margin :
    B_8_exact 4 (7900 : ℝ) (8000 : ℝ) ≤ (0.0000000012763 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (7900 : ℝ) (8000 : ℝ) 2 11400 3.1161e-25
    (0.0000000012763 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7900_a2_le row7900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 7900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row7900_k5_margin :
    B_8_exact 5 (7900 : ℝ) (8000 : ℝ) ≤ (0.000010211 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (7900 : ℝ) (8000 : ℝ) 2 11400 3.1161e-25
    (0.000010211 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row7900_a2_le row7900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8000_k1_margin :
    B_8_exact 1 (8000 : ℝ) (8100 : ℝ) ≤ (0.0000000000000000000016007 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8000 : ℝ) (8100 : ℝ) 2 11544 1.9762e-25
    (0.0000000000000000000016007 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8000_a2_le row8000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8000_k2_margin :
    B_8_exact 2 (8000 : ℝ) (8100 : ℝ) ≤ (0.000000000000000012965 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8000 : ℝ) (8100 : ℝ) 2 11544 1.9762e-25
    (0.000000000000000012965 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8000_a2_le row8000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8000_k3_margin :
    B_8_exact 3 (8000 : ℝ) (8100 : ℝ) ≤ (0.00000000000010502 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8000 : ℝ) (8100 : ℝ) 2 11544 1.9762e-25
    (0.00000000000010502 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8000_a2_le row8000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8000_k4_margin :
    B_8_exact 4 (8000 : ℝ) (8100 : ℝ) ≤ (0.00000000085065 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8000 : ℝ) (8100 : ℝ) 2 11544 1.9762e-25
    (0.00000000085065 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8000_a2_le row8000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8000_k5_margin :
    B_8_exact 5 (8000 : ℝ) (8100 : ℝ) ≤ (0.0000068903 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8000 : ℝ) (8100 : ℝ) 2 11544 1.9762e-25
    (0.0000068903 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8000_a2_le row8000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8100_k1_margin :
    B_8_exact 1 (8100 : ℝ) (8200 : ℝ) ≤ (0.0000000000000000000010326 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8100 : ℝ) (8200 : ℝ) 2 11688 1.2594e-25
    (0.0000000000000000000010326 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8100_a2_le row8100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8100_k2_margin :
    B_8_exact 2 (8100 : ℝ) (8200 : ℝ) ≤ (0.0000000000000000084674 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8100 : ℝ) (8200 : ℝ) 2 11688 1.2594e-25
    (0.0000000000000000084674 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8100_a2_le row8100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8100_k3_margin :
    B_8_exact 3 (8100 : ℝ) (8200 : ℝ) ≤ (0.000000000000069433 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8100 : ℝ) (8200 : ℝ) 2 11688 1.2594e-25
    (0.000000000000069433 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8100_a2_le row8100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8100_k4_margin :
    B_8_exact 4 (8100 : ℝ) (8200 : ℝ) ≤ (0.00000000056935 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8100 : ℝ) (8200 : ℝ) 2 11688 1.2594e-25
    (0.00000000056935 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8100_a2_le row8100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8100_k5_margin :
    B_8_exact 5 (8100 : ℝ) (8200 : ℝ) ≤ (0.0000046687 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8100 : ℝ) (8200 : ℝ) 2 11688 1.2594e-25
    (0.0000046687 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8100_a2_le row8100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8200_k1_margin :
    B_8_exact 1 (8200 : ℝ) (8300 : ℝ) ≤ (0.00000000000000000000066828 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8200 : ℝ) (8300 : ℝ) 2 11833 8.0517e-26
    (0.00000000000000000000066828 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8200_a2_le row8200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8200_k2_margin :
    B_8_exact 2 (8200 : ℝ) (8300 : ℝ) ≤ (0.0000000000000000055467 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8200 : ℝ) (8300 : ℝ) 2 11833 8.0517e-26
    (0.0000000000000000055467 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8200_a2_le row8200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8200_k3_margin :
    B_8_exact 3 (8200 : ℝ) (8300 : ℝ) ≤ (0.000000000000046038 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8200 : ℝ) (8300 : ℝ) 2 11833 8.0517e-26
    (0.000000000000046038 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8200_a2_le row8200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8200_k4_margin :
    B_8_exact 4 (8200 : ℝ) (8300 : ℝ) ≤ (0.00000000038212 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8200 : ℝ) (8300 : ℝ) 2 11833 8.0517e-26
    (0.00000000038212 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8200_a2_le row8200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8200_k5_margin :
    B_8_exact 5 (8200 : ℝ) (8300 : ℝ) ≤ (0.0000031716 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8200 : ℝ) (8300 : ℝ) 2 11833 8.0517e-26
    (0.0000031716 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8200_a2_le row8200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8300_k1_margin :
    B_8_exact 1 (8300 : ℝ) (8400 : ℝ) ≤ (0.00000000000000000000043257 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8300 : ℝ) (8400 : ℝ) 2 11977 5.1497e-26
    (0.00000000000000000000043257 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8300_a2_le row8300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8300_k2_margin :
    B_8_exact 2 (8300 : ℝ) (8400 : ℝ) ≤ (0.0000000000000000036336 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8300 : ℝ) (8400 : ℝ) 2 11977 5.1497e-26
    (0.0000000000000000036336 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8300_a2_le row8300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8300_k3_margin :
    B_8_exact 3 (8300 : ℝ) (8400 : ℝ) ≤ (0.000000000000030522 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8300 : ℝ) (8400 : ℝ) 2 11977 5.1497e-26
    (0.000000000000030522 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8300_a2_le row8300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8300_k4_margin :
    B_8_exact 4 (8300 : ℝ) (8400 : ℝ) ≤ (0.00000000025639 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8300 : ℝ) (8400 : ℝ) 2 11977 5.1497e-26
    (0.00000000025639 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8300_a2_le row8300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8300_k5_margin :
    B_8_exact 5 (8300 : ℝ) (8400 : ℝ) ≤ (0.0000021536 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8300 : ℝ) (8400 : ℝ) 2 11977 5.1497e-26
    (0.0000021536 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8300_a2_le row8300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8400_k1_margin :
    B_8_exact 1 (8400 : ℝ) (8500 : ℝ) ≤ (0.00000000000000000000028105 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8400 : ℝ) (8500 : ℝ) 2 12121 3.3065e-26
    (0.00000000000000000000028105 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8400_a2_le row8400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8400_k2_margin :
    B_8_exact 2 (8400 : ℝ) (8500 : ℝ) ≤ (0.0000000000000000023889 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8400 : ℝ) (8500 : ℝ) 2 12121 3.3065e-26
    (0.0000000000000000023889 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8400_a2_le row8400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8400_k3_margin :
    B_8_exact 3 (8400 : ℝ) (8500 : ℝ) ≤ (0.000000000000020306 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8400 : ℝ) (8500 : ℝ) 2 12121 3.3065e-26
    (0.000000000000020306 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8400_a2_le row8400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8400_k4_margin :
    B_8_exact 4 (8400 : ℝ) (8500 : ℝ) ≤ (0.00000000017260 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8400 : ℝ) (8500 : ℝ) 2 12121 3.3065e-26
    (0.00000000017260 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8400_a2_le row8400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8400_k5_margin :
    B_8_exact 5 (8400 : ℝ) (8500 : ℝ) ≤ (0.0000014671 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8400 : ℝ) (8500 : ℝ) 2 12121 3.3065e-26
    (0.0000014671 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8400_a2_le row8400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8500_k1_margin :
    B_8_exact 1 (8500 : ℝ) (8600 : ℝ) ≤ (0.00000000000000000000018315 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8500 : ℝ) (8600 : ℝ) 2 12265 2.1298e-26
    (0.00000000000000000000018315 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8500_a2_le row8500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8500_k2_margin :
    B_8_exact 2 (8500 : ℝ) (8600 : ℝ) ≤ (0.0000000000000000015751 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8500 : ℝ) (8600 : ℝ) 2 12265 2.1298e-26
    (0.0000000000000000015751 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8500_a2_le row8500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8500_k3_margin :
    B_8_exact 3 (8500 : ℝ) (8600 : ℝ) ≤ (0.000000000000013546 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8500 : ℝ) (8600 : ℝ) 2 12265 2.1298e-26
    (0.000000000000013546 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8500_a2_le row8500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8500_k4_margin :
    B_8_exact 4 (8500 : ℝ) (8600 : ℝ) ≤ (0.00000000011650 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8500 : ℝ) (8600 : ℝ) 2 12265 2.1298e-26
    (0.00000000011650 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8500_a2_le row8500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 8500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8500_k5_margin :
    B_8_exact 5 (8500 : ℝ) (8600 : ℝ) ≤ (0.0000010019 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8500 : ℝ) (8600 : ℝ) 2 12265 2.1298e-26
    (0.0000010019 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8500_a2_le row8500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
