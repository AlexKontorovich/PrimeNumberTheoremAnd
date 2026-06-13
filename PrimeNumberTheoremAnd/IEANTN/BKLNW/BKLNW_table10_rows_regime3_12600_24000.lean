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

private lemma row12600_a2_le : Inputs.default.a₂ (12600 : ℝ) ≤ (18180 : ℝ) := by
  have h := a2_crude_le (12600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12600 : ℝ) / log 2⌋₊ : ℝ) ≤ (12600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12600 : ℝ) / log 2 ≤ 18178 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18178 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18180 := by norm_num

private lemma row12700_a2_le : Inputs.default.a₂ (12700 : ℝ) ≤ (18325 : ℝ) := by
  have h := a2_crude_le (12700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12700 : ℝ) / log 2⌋₊ : ℝ) ≤ (12700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12700 : ℝ) / log 2 ≤ 18323 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18323 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18325 := by norm_num

private lemma row12800_a2_le : Inputs.default.a₂ (12800 : ℝ) ≤ (18469 : ℝ) := by
  have h := a2_crude_le (12800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12800 : ℝ) / log 2⌋₊ : ℝ) ≤ (12800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12800 : ℝ) / log 2 ≤ 18467 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18467 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18469 := by norm_num

private lemma row12900_a2_le : Inputs.default.a₂ (12900 : ℝ) ≤ (18613 : ℝ) := by
  have h := a2_crude_le (12900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12900 : ℝ) / log 2⌋₊ : ℝ) ≤ (12900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12900 : ℝ) / log 2 ≤ 18611 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18611 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18613 := by norm_num

private lemma row13000_a2_le : Inputs.default.a₂ (13000 : ℝ) ≤ (18758 : ℝ) := by
  have h := a2_crude_le (13000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(13000 : ℝ) / log 2⌋₊ : ℝ) ≤ (13000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (13000 : ℝ) / log 2 ≤ 18756 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (13000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(13000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18756 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18758 := by norm_num

private lemma row13500_a2_le : Inputs.default.a₂ (13500 : ℝ) ≤ (19479 : ℝ) := by
  have h := a2_crude_le (13500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(13500 : ℝ) / log 2⌋₊ : ℝ) ≤ (13500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (13500 : ℝ) / log 2 ≤ 19477 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (13500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(13500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (19477 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 19479 := by norm_num

private lemma row13800_7464_a2_le : Inputs.default.a₂ (13800.7464 : ℝ) ≤ (19913 : ℝ) := by
  have h := a2_crude_le (13800.7464 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(13800.7464 : ℝ) / log 2⌋₊ : ℝ) ≤ (13800.7464 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (13800.7464 : ℝ) / log 2 ≤ 19911 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (13800.7464 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(13800.7464 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (19911 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 19913 := by norm_num

private lemma row14000_a2_le : Inputs.default.a₂ (14000 : ℝ) ≤ (20200 : ℝ) := by
  have h := a2_crude_le (14000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(14000 : ℝ) / log 2⌋₊ : ℝ) ≤ (14000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (14000 : ℝ) / log 2 ≤ 20198 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (14000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(14000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (20198 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 20200 := by norm_num

private lemma row15000_a2_le : Inputs.default.a₂ (15000 : ℝ) ≤ (21643 : ℝ) := by
  have h := a2_crude_le (15000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(15000 : ℝ) / log 2⌋₊ : ℝ) ≤ (15000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (15000 : ℝ) / log 2 ≤ 21641 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (15000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(15000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (21641 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 21643 := by norm_num

private lemma row16000_a2_le : Inputs.default.a₂ (16000 : ℝ) ≤ (23086 : ℝ) := by
  have h := a2_crude_le (16000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(16000 : ℝ) / log 2⌋₊ : ℝ) ≤ (16000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (16000 : ℝ) / log 2 ≤ 23084 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (16000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(16000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (23084 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 23086 := by norm_num

private lemma row17000_a2_le : Inputs.default.a₂ (17000 : ℝ) ≤ (24528 : ℝ) := by
  have h := a2_crude_le (17000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(17000 : ℝ) / log 2⌋₊ : ℝ) ≤ (17000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (17000 : ℝ) / log 2 ≤ 24526 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (17000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(17000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (24526 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 24528 := by norm_num

private lemma row18000_a2_le : Inputs.default.a₂ (18000 : ℝ) ≤ (25971 : ℝ) := by
  have h := a2_crude_le (18000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(18000 : ℝ) / log 2⌋₊ : ℝ) ≤ (18000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (18000 : ℝ) / log 2 ≤ 25969 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (18000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(18000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (25969 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 25971 := by norm_num

private lemma row19000_a2_le : Inputs.default.a₂ (19000 : ℝ) ≤ (27414 : ℝ) := by
  have h := a2_crude_le (19000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(19000 : ℝ) / log 2⌋₊ : ℝ) ≤ (19000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (19000 : ℝ) / log 2 ≤ 27412 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (19000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(19000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (27412 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 27414 := by norm_num

private lemma row20000_a2_le : Inputs.default.a₂ (20000 : ℝ) ≤ (28856 : ℝ) := by
  have h := a2_crude_le (20000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(20000 : ℝ) / log 2⌋₊ : ℝ) ≤ (20000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (20000 : ℝ) / log 2 ≤ 28854 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (20000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(20000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (28854 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 28856 := by norm_num

private lemma row21000_a2_le : Inputs.default.a₂ (21000 : ℝ) ≤ (30299 : ℝ) := by
  have h := a2_crude_le (21000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(21000 : ℝ) / log 2⌋₊ : ℝ) ≤ (21000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (21000 : ℝ) / log 2 ≤ 30297 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (21000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(21000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (30297 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 30299 := by norm_num

private lemma row22000_a2_le : Inputs.default.a₂ (22000 : ℝ) ≤ (31742 : ℝ) := by
  have h := a2_crude_le (22000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(22000 : ℝ) / log 2⌋₊ : ℝ) ≤ (22000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (22000 : ℝ) / log 2 ≤ 31740 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (22000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(22000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (31740 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 31742 := by norm_num

private lemma row23000_a2_le : Inputs.default.a₂ (23000 : ℝ) ≤ (33184 : ℝ) := by
  have h := a2_crude_le (23000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(23000 : ℝ) / log 2⌋₊ : ℝ) ≤ (23000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (23000 : ℝ) / log 2 ≤ 33182 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (23000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(23000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (33182 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 33184 := by norm_num

private lemma row24000_a2_le : Inputs.default.a₂ (24000 : ℝ) ≤ (34627 : ℝ) := by
  have h := a2_crude_le (24000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(24000 : ℝ) / log 2⌋₊ : ℝ) ≤ (24000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (24000 : ℝ) / log 2 ≤ 34625 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (24000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(24000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (34625 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 34627 := by norm_num

set_option maxRecDepth 10000 in
private lemma row12600_table8_mem : (12600, 1.7565e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12600_eps_le : Inputs.default.ε (12600 : ℝ) ≤ 1.7565e-33 := by
  change BKLNW_app.table_8_ε (12600 : ℝ) ≤ 1.7565e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12600)
    (ε := 1.7565e-33) row12600_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row12700_table8_mem : (12700, 1.2188e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12700_eps_le : Inputs.default.ε (12700 : ℝ) ≤ 1.2188e-33 := by
  change BKLNW_app.table_8_ε (12700 : ℝ) ≤ 1.2188e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12700)
    (ε := 1.2188e-33) row12700_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row12800_table8_mem : (12800, 8.4803e-34) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12800_eps_le : Inputs.default.ε (12800 : ℝ) ≤ 8.4803e-34 := by
  change BKLNW_app.table_8_ε (12800 : ℝ) ≤ 8.4803e-34
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12800)
    (ε := 8.4803e-34) row12800_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row12900_table8_mem : (12900, 5.9154e-34) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12900_eps_le : Inputs.default.ε (12900 : ℝ) ≤ 5.9154e-34 := by
  change BKLNW_app.table_8_ε (12900 : ℝ) ≤ 5.9154e-34
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12900)
    (ε := 5.9154e-34) row12900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row13000_table8_mem : (13000, 4.1356e-34) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row13000_eps_le : Inputs.default.ε (13000 : ℝ) ≤ 4.1356e-34 := by
  change BKLNW_app.table_8_ε (13000 : ℝ) ≤ 4.1356e-34
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 13000)
    (ε := 4.1356e-34) row13000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row13500_table8_mem : (13500, 7.2154e-35) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row13500_eps_le : Inputs.default.ε (13500 : ℝ) ≤ 7.2154e-35 := by
  change BKLNW_app.table_8_ε (13500 : ℝ) ≤ 7.2154e-35
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 13500)
    (ε := 7.2154e-35) row13500_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row13800_7464_table8_mem : (13800, 2.5423e-35) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row13800_7464_eps_le : Inputs.default.ε (13800.7464 : ℝ) ≤ 2.5423e-35 := by
  change BKLNW_app.table_8_ε (13800.7464 : ℝ) ≤ 2.5423e-35
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 13800)
    (ε := 2.5423e-35) row13800_7464_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row14000_table8_mem : (14000, 1.2266e-35) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row14000_eps_le : Inputs.default.ε (14000 : ℝ) ≤ 1.2266e-35 := by
  change BKLNW_app.table_8_ε (14000 : ℝ) ≤ 1.2266e-35
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 14000)
    (ε := 1.2266e-35) row14000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row15000_table8_mem : (15000, 4.1071e-37) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row15000_eps_le : Inputs.default.ε (15000 : ℝ) ≤ 4.1071e-37 := by
  change BKLNW_app.table_8_ε (15000 : ℝ) ≤ 4.1071e-37
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 15000)
    (ε := 4.1071e-37) row15000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row16000_table8_mem : (16000, 1.5141e-38) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row16000_eps_le : Inputs.default.ε (16000 : ℝ) ≤ 1.5141e-38 := by
  change BKLNW_app.table_8_ε (16000 : ℝ) ≤ 1.5141e-38
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 16000)
    (ε := 1.5141e-38) row16000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row17000_table8_mem : (17000, 6.2041e-40) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row17000_eps_le : Inputs.default.ε (17000 : ℝ) ≤ 6.2041e-40 := by
  change BKLNW_app.table_8_ε (17000 : ℝ) ≤ 6.2041e-40
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 17000)
    (ε := 6.2041e-40) row17000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row18000_table8_mem : (18000, 2.8284e-41) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row18000_eps_le : Inputs.default.ε (18000 : ℝ) ≤ 2.8284e-41 := by
  change BKLNW_app.table_8_ε (18000 : ℝ) ≤ 2.8284e-41
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 18000)
    (ε := 2.8284e-41) row18000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row19000_table8_mem : (19000, 1.3679e-42) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row19000_eps_le : Inputs.default.ε (19000 : ℝ) ≤ 1.3679e-42 := by
  change BKLNW_app.table_8_ε (19000 : ℝ) ≤ 1.3679e-42
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 19000)
    (ε := 1.3679e-42) row19000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row20000_table8_mem : (20000, 7.1622e-44) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row20000_eps_le : Inputs.default.ε (20000 : ℝ) ≤ 7.1622e-44 := by
  change BKLNW_app.table_8_ε (20000 : ℝ) ≤ 7.1622e-44
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 20000)
    (ε := 7.1622e-44) row20000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row21000_table8_mem : (21000, 4.1185e-45) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row21000_eps_le : Inputs.default.ε (21000 : ℝ) ≤ 4.1185e-45 := by
  change BKLNW_app.table_8_ε (21000 : ℝ) ≤ 4.1185e-45
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 21000)
    (ε := 4.1185e-45) row21000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row22000_table8_mem : (22000, 2.4393e-46) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row22000_eps_le : Inputs.default.ε (22000 : ℝ) ≤ 2.4393e-46 := by
  change BKLNW_app.table_8_ε (22000 : ℝ) ≤ 2.4393e-46
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 22000)
    (ε := 2.4393e-46) row22000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row23000_table8_mem : (23000, 1.5648e-47) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row23000_eps_le : Inputs.default.ε (23000 : ℝ) ≤ 1.5648e-47 := by
  change BKLNW_app.table_8_ε (23000 : ℝ) ≤ 1.5648e-47
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 23000)
    (ε := 1.5648e-47) row23000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row24000_table8_mem : (24000, 1.0703e-48) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row24000_eps_le : Inputs.default.ε (24000 : ℝ) ≤ 1.0703e-48 := by
  change BKLNW_app.table_8_ε (24000 : ℝ) ≤ 1.0703e-48
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 24000)
    (ε := 1.0703e-48) row24000_table8_mem (by norm_num)

/-- Row 12600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12600_k1_margin :
    B_8_exact 1 (12600 : ℝ) (12700 : ℝ) ≤ (0.000000000000000000000000000022307 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12600 : ℝ) (12700 : ℝ) 2 18180 1.7565e-33
    (0.000000000000000000000000000022307 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12600_a2_le row12600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6300_lt, LogTables.exp_neg_8400_lt,
                   Real.exp_pos (-(6300:ℝ)), Real.exp_pos (-(8400:ℝ))])

/-- Row 12600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12600_k2_margin :
    B_8_exact 2 (12600 : ℝ) (12700 : ℝ) ≤ (0.00000000000000000000000028330 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12600 : ℝ) (12700 : ℝ) 2 18180 1.7565e-33
    (0.00000000000000000000000028330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12600_a2_le row12600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6300_lt, LogTables.exp_neg_8400_lt,
                   Real.exp_pos (-(6300:ℝ)), Real.exp_pos (-(8400:ℝ))])

/-- Row 12600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12600_k3_margin :
    B_8_exact 3 (12600 : ℝ) (12700 : ℝ) ≤ (0.0000000000000000000035979 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12600 : ℝ) (12700 : ℝ) 2 18180 1.7565e-33
    (0.0000000000000000000035979 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12600_a2_le row12600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6300_lt, LogTables.exp_neg_8400_lt,
                   Real.exp_pos (-(6300:ℝ)), Real.exp_pos (-(8400:ℝ))])

/-- Row 12600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12600_k4_margin :
    B_8_exact 4 (12600 : ℝ) (12700 : ℝ) ≤ (0.000000000000000045693 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12600 : ℝ) (12700 : ℝ) 2 18180 1.7565e-33
    (0.000000000000000045693 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12600_a2_le row12600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6300_lt, LogTables.exp_neg_8400_lt,
                   Real.exp_pos (-(6300:ℝ)), Real.exp_pos (-(8400:ℝ))])

/-- Row 12600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12600_k5_margin :
    B_8_exact 5 (12600 : ℝ) (12700 : ℝ) ≤ (0.00000000000058030 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12600 : ℝ) (12700 : ℝ) 2 18180 1.7565e-33
    (0.00000000000058030 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12600_a2_le row12600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6300_lt, LogTables.exp_neg_8400_lt,
                   Real.exp_pos (-(6300:ℝ)), Real.exp_pos (-(8400:ℝ))])

/-- Row 12700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12700_k1_margin :
    B_8_exact 1 (12700 : ℝ) (12800 : ℝ) ≤ (0.000000000000000000000000000015599 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12700 : ℝ) (12800 : ℝ) 2 18325 1.2188e-33
    (0.000000000000000000000000000015599 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12700_a2_le row12700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6350_lt, LogTables.exp_neg_25400_3_lt,
                   Real.exp_pos (-(6350:ℝ)), Real.exp_pos (-(25400/3:ℝ))])

/-- Row 12700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12700_k2_margin :
    B_8_exact 2 (12700 : ℝ) (12800 : ℝ) ≤ (0.00000000000000000000000019967 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12700 : ℝ) (12800 : ℝ) 2 18325 1.2188e-33
    (0.00000000000000000000000019967 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12700_a2_le row12700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6350_lt, LogTables.exp_neg_25400_3_lt,
                   Real.exp_pos (-(6350:ℝ)), Real.exp_pos (-(25400/3:ℝ))])

/-- Row 12700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12700_k3_margin :
    B_8_exact 3 (12700 : ℝ) (12800 : ℝ) ≤ (0.0000000000000000000025558 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12700 : ℝ) (12800 : ℝ) 2 18325 1.2188e-33
    (0.0000000000000000000025558 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12700_a2_le row12700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6350_lt, LogTables.exp_neg_25400_3_lt,
                   Real.exp_pos (-(6350:ℝ)), Real.exp_pos (-(25400/3:ℝ))])

/-- Row 12700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12700_k4_margin :
    B_8_exact 4 (12700 : ℝ) (12800 : ℝ) ≤ (0.000000000000000032714 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12700 : ℝ) (12800 : ℝ) 2 18325 1.2188e-33
    (0.000000000000000032714 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12700_a2_le row12700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6350_lt, LogTables.exp_neg_25400_3_lt,
                   Real.exp_pos (-(6350:ℝ)), Real.exp_pos (-(25400/3:ℝ))])

/-- Row 12700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12700_k5_margin :
    B_8_exact 5 (12700 : ℝ) (12800 : ℝ) ≤ (0.00000000000041873 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12700 : ℝ) (12800 : ℝ) 2 18325 1.2188e-33
    (0.00000000000041873 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12700_a2_le row12700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6350_lt, LogTables.exp_neg_25400_3_lt,
                   Real.exp_pos (-(6350:ℝ)), Real.exp_pos (-(25400/3:ℝ))])

/-- Row 12800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12800_k1_margin :
    B_8_exact 1 (12800 : ℝ) (12900 : ℝ) ≤ (0.000000000000000000000000000010940 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12800 : ℝ) (12900 : ℝ) 2 18469 8.4803e-34
    (0.000000000000000000000000000010940 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12800_a2_le row12800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6400_lt, LogTables.exp_neg_25600_3_lt,
                   Real.exp_pos (-(6400:ℝ)), Real.exp_pos (-(25600/3:ℝ))])

/-- Row 12800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12800_k2_margin :
    B_8_exact 2 (12800 : ℝ) (12900 : ℝ) ≤ (0.00000000000000000000000014112 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12800 : ℝ) (12900 : ℝ) 2 18469 8.4803e-34
    (0.00000000000000000000000014112 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12800_a2_le row12800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6400_lt, LogTables.exp_neg_25600_3_lt,
                   Real.exp_pos (-(6400:ℝ)), Real.exp_pos (-(25600/3:ℝ))])

/-- Row 12800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12800_k3_margin :
    B_8_exact 3 (12800 : ℝ) (12900 : ℝ) ≤ (0.0000000000000000000018205 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12800 : ℝ) (12900 : ℝ) 2 18469 8.4803e-34
    (0.0000000000000000000018205 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12800_a2_le row12800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6400_lt, LogTables.exp_neg_25600_3_lt,
                   Real.exp_pos (-(6400:ℝ)), Real.exp_pos (-(25600/3:ℝ))])

/-- Row 12800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12800_k4_margin :
    B_8_exact 4 (12800 : ℝ) (12900 : ℝ) ≤ (0.000000000000000023484 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12800 : ℝ) (12900 : ℝ) 2 18469 8.4803e-34
    (0.000000000000000023484 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12800_a2_le row12800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6400_lt, LogTables.exp_neg_25600_3_lt,
                   Real.exp_pos (-(6400:ℝ)), Real.exp_pos (-(25600/3:ℝ))])

/-- Row 12800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12800_k5_margin :
    B_8_exact 5 (12800 : ℝ) (12900 : ℝ) ≤ (0.00000000000030294 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12800 : ℝ) (12900 : ℝ) 2 18469 8.4803e-34
    (0.00000000000030294 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12800_a2_le row12800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6400_lt, LogTables.exp_neg_25600_3_lt,
                   Real.exp_pos (-(6400:ℝ)), Real.exp_pos (-(25600/3:ℝ))])

/-- Row 12900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12900_k1_margin :
    B_8_exact 1 (12900 : ℝ) (13000 : ℝ) ≤ (0.0000000000000000000000000000076899 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12900 : ℝ) (13000 : ℝ) 2 18613 5.9154e-34
    (0.0000000000000000000000000000076899 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12900_a2_le row12900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6450_lt, LogTables.exp_neg_8600_lt,
                   Real.exp_pos (-(6450:ℝ)), Real.exp_pos (-(8600:ℝ))])

/-- Row 12900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12900_k2_margin :
    B_8_exact 2 (12900 : ℝ) (13000 : ℝ) ≤ (0.000000000000000000000000099969 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12900 : ℝ) (13000 : ℝ) 2 18613 5.9154e-34
    (0.000000000000000000000000099969 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12900_a2_le row12900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6450_lt, LogTables.exp_neg_8600_lt,
                   Real.exp_pos (-(6450:ℝ)), Real.exp_pos (-(8600:ℝ))])

/-- Row 12900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12900_k3_margin :
    B_8_exact 3 (12900 : ℝ) (13000 : ℝ) ≤ (0.0000000000000000000012996 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12900 : ℝ) (13000 : ℝ) 2 18613 5.9154e-34
    (0.0000000000000000000012996 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12900_a2_le row12900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6450_lt, LogTables.exp_neg_8600_lt,
                   Real.exp_pos (-(6450:ℝ)), Real.exp_pos (-(8600:ℝ))])

/-- Row 12900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12900_k4_margin :
    B_8_exact 4 (12900 : ℝ) (13000 : ℝ) ≤ (0.000000000000000016895 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12900 : ℝ) (13000 : ℝ) 2 18613 5.9154e-34
    (0.000000000000000016895 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12900_a2_le row12900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6450_lt, LogTables.exp_neg_8600_lt,
                   Real.exp_pos (-(6450:ℝ)), Real.exp_pos (-(8600:ℝ))])

/-- Row 12900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12900_k5_margin :
    B_8_exact 5 (12900 : ℝ) (13000 : ℝ) ≤ (0.00000000000021963 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12900 : ℝ) (13000 : ℝ) 2 18613 5.9154e-34
    (0.00000000000021963 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12900_a2_le row12900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6450_lt, LogTables.exp_neg_8600_lt,
                   Real.exp_pos (-(6450:ℝ)), Real.exp_pos (-(8600:ℝ))])

/-- Row 13000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row13000_k1_margin :
    B_8_exact 1 (13000 : ℝ) (13500 : ℝ) ≤ (0.0000000000000000000000000000055830 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (13000 : ℝ) (13500 : ℝ) 2 18758 4.1356e-34
    (0.0000000000000000000000000000055830 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13000_a2_le row13000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6500_lt, LogTables.exp_neg_26000_3_lt,
                   Real.exp_pos (-(6500:ℝ)), Real.exp_pos (-(26000/3:ℝ))])

/-- Row 13000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row13000_k2_margin :
    B_8_exact 2 (13000 : ℝ) (13500 : ℝ) ≤ (0.000000000000000000000000075370 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (13000 : ℝ) (13500 : ℝ) 2 18758 4.1356e-34
    (0.000000000000000000000000075370 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13000_a2_le row13000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6500_lt, LogTables.exp_neg_26000_3_lt,
                   Real.exp_pos (-(6500:ℝ)), Real.exp_pos (-(26000/3:ℝ))])

/-- Row 13000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row13000_k3_margin :
    B_8_exact 3 (13000 : ℝ) (13500 : ℝ) ≤ (0.0000000000000000000010175 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (13000 : ℝ) (13500 : ℝ) 2 18758 4.1356e-34
    (0.0000000000000000000010175 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13000_a2_le row13000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6500_lt, LogTables.exp_neg_26000_3_lt,
                   Real.exp_pos (-(6500:ℝ)), Real.exp_pos (-(26000/3:ℝ))])

/-- Row 13000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row13000_k4_margin :
    B_8_exact 4 (13000 : ℝ) (13500 : ℝ) ≤ (0.000000000000000013736 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (13000 : ℝ) (13500 : ℝ) 2 18758 4.1356e-34
    (0.000000000000000013736 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13000_a2_le row13000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6500_lt, LogTables.exp_neg_26000_3_lt,
                   Real.exp_pos (-(6500:ℝ)), Real.exp_pos (-(26000/3:ℝ))])

/-- Row 13000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row13000_k5_margin :
    B_8_exact 5 (13000 : ℝ) (13500 : ℝ) ≤ (0.00000000000018544 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (13000 : ℝ) (13500 : ℝ) 2 18758 4.1356e-34
    (0.00000000000018544 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13000_a2_le row13000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6500_lt, LogTables.exp_neg_26000_3_lt,
                   Real.exp_pos (-(6500:ℝ)), Real.exp_pos (-(26000/3:ℝ))])

/-- Row 13500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row13500_k1_margin :
    B_8_exact 1 (13500 : ℝ) (13800.7464 : ℝ) ≤ (0.00000000000000000000000000000099578 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (13500 : ℝ) (13800.7464 : ℝ) 2 19479 7.2154e-35
    (0.00000000000000000000000000000099578 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13500_a2_le row13500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6750_lt, LogTables.exp_neg_9000_lt,
                   Real.exp_pos (-(6750:ℝ)), Real.exp_pos (-(9000:ℝ))])

/-- Row 13500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row13500_k2_margin :
    B_8_exact 2 (13500 : ℝ) (13800.7464 : ℝ) ≤ (0.000000000000000000000000013743 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (13500 : ℝ) (13800.7464 : ℝ) 2 19479 7.2154e-35
    (0.000000000000000000000000013743 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13500_a2_le row13500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6750_lt, LogTables.exp_neg_9000_lt,
                   Real.exp_pos (-(6750:ℝ)), Real.exp_pos (-(9000:ℝ))])

/-- Row 13500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row13500_k3_margin :
    B_8_exact 3 (13500 : ℝ) (13800.7464 : ℝ) ≤ (0.00000000000000000000018966 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (13500 : ℝ) (13800.7464 : ℝ) 2 19479 7.2154e-35
    (0.00000000000000000000018966 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13500_a2_le row13500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6750_lt, LogTables.exp_neg_9000_lt,
                   Real.exp_pos (-(6750:ℝ)), Real.exp_pos (-(9000:ℝ))])

/-- Row 13500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row13500_k4_margin :
    B_8_exact 4 (13500 : ℝ) (13800.7464 : ℝ) ≤ (0.0000000000000000026174 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (13500 : ℝ) (13800.7464 : ℝ) 2 19479 7.2154e-35
    (0.0000000000000000026174 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13500_a2_le row13500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6750_lt, LogTables.exp_neg_9000_lt,
                   Real.exp_pos (-(6750:ℝ)), Real.exp_pos (-(9000:ℝ))])

/-- Row 13500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row13500_k5_margin :
    B_8_exact 5 (13500 : ℝ) (13800.7464 : ℝ) ≤ (0.000000000000036122 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (13500 : ℝ) (13800.7464 : ℝ) 2 19479 7.2154e-35
    (0.000000000000036122 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13500_a2_le row13500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_6750_lt, LogTables.exp_neg_9000_lt,
                   Real.exp_pos (-(6750:ℝ)), Real.exp_pos (-(9000:ℝ))])

/-- Row 13800.7464 (k = 1), exact Table-10 margin target. -/
theorem table_10_row13800_7464_k1_margin :
    B_8_exact 1 (13800.7464 : ℝ) (14000 : ℝ) ≤ (0.00000000000000000000000000000035592 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (13800.7464 : ℝ) (14000 : ℝ) 2 19913 2.5423e-35
    (0.00000000000000000000000000000035592 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13800_7464_a2_le row13800_7464_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 13800.7464 (k = 2), exact Table-10 margin target. -/
theorem table_10_row13800_7464_k2_margin :
    B_8_exact 2 (13800.7464 : ℝ) (14000 : ℝ) ≤ (0.0000000000000000000000000049829 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (13800.7464 : ℝ) (14000 : ℝ) 2 19913 2.5423e-35
    (0.0000000000000000000000000049829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13800_7464_a2_le row13800_7464_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 13800.7464 (k = 3), exact Table-10 margin target. -/
theorem table_10_row13800_7464_k3_margin :
    B_8_exact 3 (13800.7464 : ℝ) (14000 : ℝ) ≤ (0.000000000000000000000069761 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (13800.7464 : ℝ) (14000 : ℝ) 2 19913 2.5423e-35
    (0.000000000000000000000069761 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13800_7464_a2_le row13800_7464_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 13800.7464 (k = 4), exact Table-10 margin target. -/
theorem table_10_row13800_7464_k4_margin :
    B_8_exact 4 (13800.7464 : ℝ) (14000 : ℝ) ≤ (0.00000000000000000097665 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (13800.7464 : ℝ) (14000 : ℝ) 2 19913 2.5423e-35
    (0.00000000000000000097665 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13800_7464_a2_le row13800_7464_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 13800.7464 (k = 5), exact Table-10 margin target. -/
theorem table_10_row13800_7464_k5_margin :
    B_8_exact 5 (13800.7464 : ℝ) (14000 : ℝ) ≤ (0.000000000000013673 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (13800.7464 : ℝ) (14000 : ℝ) 2 19913 2.5423e-35
    (0.000000000000013673 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row13800_7464_a2_le row13800_7464_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 14000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row14000_k1_margin :
    B_8_exact 1 (14000 : ℝ) (15000 : ℝ) ≤ (0.00000000000000000000000000000018398 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (14000 : ℝ) (15000 : ℝ) 2 20200 1.2266e-35
    (0.00000000000000000000000000000018398 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row14000_a2_le row14000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7000_lt, LogTables.exp_neg_28000_3_lt,
                   Real.exp_pos (-(7000:ℝ)), Real.exp_pos (-(28000/3:ℝ))])

/-- Row 14000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row14000_k2_margin :
    B_8_exact 2 (14000 : ℝ) (15000 : ℝ) ≤ (0.0000000000000000000000000027597 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (14000 : ℝ) (15000 : ℝ) 2 20200 1.2266e-35
    (0.0000000000000000000000000027597 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row14000_a2_le row14000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7000_lt, LogTables.exp_neg_28000_3_lt,
                   Real.exp_pos (-(7000:ℝ)), Real.exp_pos (-(28000/3:ℝ))])

/-- Row 14000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row14000_k3_margin :
    B_8_exact 3 (14000 : ℝ) (15000 : ℝ) ≤ (0.000000000000000000000041396 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (14000 : ℝ) (15000 : ℝ) 2 20200 1.2266e-35
    (0.000000000000000000000041396 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row14000_a2_le row14000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7000_lt, LogTables.exp_neg_28000_3_lt,
                   Real.exp_pos (-(7000:ℝ)), Real.exp_pos (-(28000/3:ℝ))])

/-- Row 14000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row14000_k4_margin :
    B_8_exact 4 (14000 : ℝ) (15000 : ℝ) ≤ (0.00000000000000000062094 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (14000 : ℝ) (15000 : ℝ) 2 20200 1.2266e-35
    (0.00000000000000000062094 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row14000_a2_le row14000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7000_lt, LogTables.exp_neg_28000_3_lt,
                   Real.exp_pos (-(7000:ℝ)), Real.exp_pos (-(28000/3:ℝ))])

/-- Row 14000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row14000_k5_margin :
    B_8_exact 5 (14000 : ℝ) (15000 : ℝ) ≤ (0.0000000000000093141 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (14000 : ℝ) (15000 : ℝ) 2 20200 1.2266e-35
    (0.0000000000000093141 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row14000_a2_le row14000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7000_lt, LogTables.exp_neg_28000_3_lt,
                   Real.exp_pos (-(7000:ℝ)), Real.exp_pos (-(28000/3:ℝ))])

/-- Row 15000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row15000_k1_margin :
    B_8_exact 1 (15000 : ℝ) (16000 : ℝ) ≤ (0.0000000000000000000000000000000065711 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (15000 : ℝ) (16000 : ℝ) 2 21643 4.1071e-37
    (0.0000000000000000000000000000000065711 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row15000_a2_le row15000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7500_lt, LogTables.exp_neg_10000_lt,
                   Real.exp_pos (-(7500:ℝ)), Real.exp_pos (-(10000:ℝ))])

/-- Row 15000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row15000_k2_margin :
    B_8_exact 2 (15000 : ℝ) (16000 : ℝ) ≤ (0.00000000000000000000000000010514 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (15000 : ℝ) (16000 : ℝ) 2 21643 4.1071e-37
    (0.00000000000000000000000000010514 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row15000_a2_le row15000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7500_lt, LogTables.exp_neg_10000_lt,
                   Real.exp_pos (-(7500:ℝ)), Real.exp_pos (-(10000:ℝ))])

/-- Row 15000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row15000_k3_margin :
    B_8_exact 3 (15000 : ℝ) (16000 : ℝ) ≤ (0.0000000000000000000000016822 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (15000 : ℝ) (16000 : ℝ) 2 21643 4.1071e-37
    (0.0000000000000000000000016822 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row15000_a2_le row15000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7500_lt, LogTables.exp_neg_10000_lt,
                   Real.exp_pos (-(7500:ℝ)), Real.exp_pos (-(10000:ℝ))])

/-- Row 15000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row15000_k4_margin :
    B_8_exact 4 (15000 : ℝ) (16000 : ℝ) ≤ (0.000000000000000000026915 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (15000 : ℝ) (16000 : ℝ) 2 21643 4.1071e-37
    (0.000000000000000000026915 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row15000_a2_le row15000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7500_lt, LogTables.exp_neg_10000_lt,
                   Real.exp_pos (-(7500:ℝ)), Real.exp_pos (-(10000:ℝ))])

/-- Row 15000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row15000_k5_margin :
    B_8_exact 5 (15000 : ℝ) (16000 : ℝ) ≤ (0.00000000000000043065 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (15000 : ℝ) (16000 : ℝ) 2 21643 4.1071e-37
    (0.00000000000000043065 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row15000_a2_le row15000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_7500_lt, LogTables.exp_neg_10000_lt,
                   Real.exp_pos (-(7500:ℝ)), Real.exp_pos (-(10000:ℝ))])

/-- Row 16000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row16000_k1_margin :
    B_8_exact 1 (16000 : ℝ) (17000 : ℝ) ≤ (0.00000000000000000000000000000000025738 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (16000 : ℝ) (17000 : ℝ) 2 23086 1.5141e-38
    (0.00000000000000000000000000000000025738 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row16000_a2_le row16000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8000_lt, LogTables.exp_neg_32000_3_lt,
                   Real.exp_pos (-(8000:ℝ)), Real.exp_pos (-(32000/3:ℝ))])

/-- Row 16000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row16000_k2_margin :
    B_8_exact 2 (16000 : ℝ) (17000 : ℝ) ≤ (0.0000000000000000000000000000043755 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (16000 : ℝ) (17000 : ℝ) 2 23086 1.5141e-38
    (0.0000000000000000000000000000043755 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row16000_a2_le row16000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8000_lt, LogTables.exp_neg_32000_3_lt,
                   Real.exp_pos (-(8000:ℝ)), Real.exp_pos (-(32000/3:ℝ))])

/-- Row 16000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row16000_k3_margin :
    B_8_exact 3 (16000 : ℝ) (17000 : ℝ) ≤ (0.000000000000000000000000074384 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (16000 : ℝ) (17000 : ℝ) 2 23086 1.5141e-38
    (0.000000000000000000000000074384 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row16000_a2_le row16000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8000_lt, LogTables.exp_neg_32000_3_lt,
                   Real.exp_pos (-(8000:ℝ)), Real.exp_pos (-(32000/3:ℝ))])

/-- Row 16000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row16000_k4_margin :
    B_8_exact 4 (16000 : ℝ) (17000 : ℝ) ≤ (0.0000000000000000000012645 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (16000 : ℝ) (17000 : ℝ) 2 23086 1.5141e-38
    (0.0000000000000000000012645 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row16000_a2_le row16000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8000_lt, LogTables.exp_neg_32000_3_lt,
                   Real.exp_pos (-(8000:ℝ)), Real.exp_pos (-(32000/3:ℝ))])

/-- Row 16000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row16000_k5_margin :
    B_8_exact 5 (16000 : ℝ) (17000 : ℝ) ≤ (0.000000000000000021497 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (16000 : ℝ) (17000 : ℝ) 2 23086 1.5141e-38
    (0.000000000000000021497 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row16000_a2_le row16000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8000_lt, LogTables.exp_neg_32000_3_lt,
                   Real.exp_pos (-(8000:ℝ)), Real.exp_pos (-(32000/3:ℝ))])

/-- Row 17000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row17000_k1_margin :
    B_8_exact 1 (17000 : ℝ) (18000 : ℝ) ≤ (0.000000000000000000000000000000000011167 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (17000 : ℝ) (18000 : ℝ) 2 24528 6.2041e-40
    (0.000000000000000000000000000000000011167 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row17000_a2_le row17000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8500_lt, LogTables.exp_neg_34000_3_lt,
                   Real.exp_pos (-(8500:ℝ)), Real.exp_pos (-(34000/3:ℝ))])

/-- Row 17000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row17000_k2_margin :
    B_8_exact 2 (17000 : ℝ) (18000 : ℝ) ≤ (0.00000000000000000000000000000020101 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (17000 : ℝ) (18000 : ℝ) 2 24528 6.2041e-40
    (0.00000000000000000000000000000020101 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row17000_a2_le row17000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8500_lt, LogTables.exp_neg_34000_3_lt,
                   Real.exp_pos (-(8500:ℝ)), Real.exp_pos (-(34000/3:ℝ))])

/-- Row 17000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row17000_k3_margin :
    B_8_exact 3 (17000 : ℝ) (18000 : ℝ) ≤ (0.0000000000000000000000000036182 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (17000 : ℝ) (18000 : ℝ) 2 24528 6.2041e-40
    (0.0000000000000000000000000036182 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row17000_a2_le row17000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8500_lt, LogTables.exp_neg_34000_3_lt,
                   Real.exp_pos (-(8500:ℝ)), Real.exp_pos (-(34000/3:ℝ))])

/-- Row 17000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row17000_k4_margin :
    B_8_exact 4 (17000 : ℝ) (18000 : ℝ) ≤ (0.000000000000000000000065127 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (17000 : ℝ) (18000 : ℝ) 2 24528 6.2041e-40
    (0.000000000000000000000065127 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row17000_a2_le row17000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8500_lt, LogTables.exp_neg_34000_3_lt,
                   Real.exp_pos (-(8500:ℝ)), Real.exp_pos (-(34000/3:ℝ))])

/-- Row 17000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row17000_k5_margin :
    B_8_exact 5 (17000 : ℝ) (18000 : ℝ) ≤ (0.0000000000000000011723 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (17000 : ℝ) (18000 : ℝ) 2 24528 6.2041e-40
    (0.0000000000000000011723 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row17000_a2_le row17000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_8500_lt, LogTables.exp_neg_34000_3_lt,
                   Real.exp_pos (-(8500:ℝ)), Real.exp_pos (-(34000/3:ℝ))])

/-- Row 18000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row18000_k1_margin :
    B_8_exact 1 (18000 : ℝ) (19000 : ℝ) ≤ (0.00000000000000000000000000000000000053738 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (18000 : ℝ) (19000 : ℝ) 2 25971 2.8284e-41
    (0.00000000000000000000000000000000000053738 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row18000_a2_le row18000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9000_lt, LogTables.exp_neg_12000_lt,
                   Real.exp_pos (-(9000:ℝ)), Real.exp_pos (-(12000:ℝ))])

/-- Row 18000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row18000_k2_margin :
    B_8_exact 2 (18000 : ℝ) (19000 : ℝ) ≤ (0.000000000000000000000000000000010210 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (18000 : ℝ) (19000 : ℝ) 2 25971 2.8284e-41
    (0.000000000000000000000000000000010210 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row18000_a2_le row18000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9000_lt, LogTables.exp_neg_12000_lt,
                   Real.exp_pos (-(9000:ℝ)), Real.exp_pos (-(12000:ℝ))])

/-- Row 18000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row18000_k3_margin :
    B_8_exact 3 (18000 : ℝ) (19000 : ℝ) ≤ (0.00000000000000000000000000019400 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (18000 : ℝ) (19000 : ℝ) 2 25971 2.8284e-41
    (0.00000000000000000000000000019400 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row18000_a2_le row18000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9000_lt, LogTables.exp_neg_12000_lt,
                   Real.exp_pos (-(9000:ℝ)), Real.exp_pos (-(12000:ℝ))])

/-- Row 18000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row18000_k4_margin :
    B_8_exact 4 (18000 : ℝ) (19000 : ℝ) ≤ (0.0000000000000000000000036859 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (18000 : ℝ) (19000 : ℝ) 2 25971 2.8284e-41
    (0.0000000000000000000000036859 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row18000_a2_le row18000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9000_lt, LogTables.exp_neg_12000_lt,
                   Real.exp_pos (-(9000:ℝ)), Real.exp_pos (-(12000:ℝ))])

/-- Row 18000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row18000_k5_margin :
    B_8_exact 5 (18000 : ℝ) (19000 : ℝ) ≤ (0.000000000000000000070032 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (18000 : ℝ) (19000 : ℝ) 2 25971 2.8284e-41
    (0.000000000000000000070032 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row18000_a2_le row18000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9000_lt, LogTables.exp_neg_12000_lt,
                   Real.exp_pos (-(9000:ℝ)), Real.exp_pos (-(12000:ℝ))])

/-- Row 19000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row19000_k1_margin :
    B_8_exact 1 (19000 : ℝ) (20000 : ℝ) ≤ (0.000000000000000000000000000000000000027357 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (19000 : ℝ) (20000 : ℝ) 2 27414 1.3679e-42
    (0.000000000000000000000000000000000000027357 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row19000_a2_le row19000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9500_lt, LogTables.exp_neg_38000_3_lt,
                   Real.exp_pos (-(9500:ℝ)), Real.exp_pos (-(38000/3:ℝ))])

/-- Row 19000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row19000_k2_margin :
    B_8_exact 2 (19000 : ℝ) (20000 : ℝ) ≤ (0.00000000000000000000000000000000054714 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (19000 : ℝ) (20000 : ℝ) 2 27414 1.3679e-42
    (0.00000000000000000000000000000000054714 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row19000_a2_le row19000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9500_lt, LogTables.exp_neg_38000_3_lt,
                   Real.exp_pos (-(9500:ℝ)), Real.exp_pos (-(38000/3:ℝ))])

/-- Row 19000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row19000_k3_margin :
    B_8_exact 3 (19000 : ℝ) (20000 : ℝ) ≤ (0.000000000000000000000000000010943 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (19000 : ℝ) (20000 : ℝ) 2 27414 1.3679e-42
    (0.000000000000000000000000000010943 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row19000_a2_le row19000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9500_lt, LogTables.exp_neg_38000_3_lt,
                   Real.exp_pos (-(9500:ℝ)), Real.exp_pos (-(38000/3:ℝ))])

/-- Row 19000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row19000_k4_margin :
    B_8_exact 4 (19000 : ℝ) (20000 : ℝ) ≤ (0.00000000000000000000000021886 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (19000 : ℝ) (20000 : ℝ) 2 27414 1.3679e-42
    (0.00000000000000000000000021886 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row19000_a2_le row19000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9500_lt, LogTables.exp_neg_38000_3_lt,
                   Real.exp_pos (-(9500:ℝ)), Real.exp_pos (-(38000/3:ℝ))])

/-- Row 19000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row19000_k5_margin :
    B_8_exact 5 (19000 : ℝ) (20000 : ℝ) ≤ (0.0000000000000000000043771 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (19000 : ℝ) (20000 : ℝ) 2 27414 1.3679e-42
    (0.0000000000000000000043771 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row19000_a2_le row19000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_9500_lt, LogTables.exp_neg_38000_3_lt,
                   Real.exp_pos (-(9500:ℝ)), Real.exp_pos (-(38000/3:ℝ))])

/-- Row 20000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row20000_k1_margin :
    B_8_exact 1 (20000 : ℝ) (21000 : ℝ) ≤ (0.0000000000000000000000000000000000000015040 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (20000 : ℝ) (21000 : ℝ) 2 28856 7.1622e-44
    (0.0000000000000000000000000000000000000015040 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row20000_a2_le row20000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10000_lt, LogTables.exp_neg_40000_3_lt,
                   Real.exp_pos (-(10000:ℝ)), Real.exp_pos (-(40000/3:ℝ))])

/-- Row 20000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row20000_k2_margin :
    B_8_exact 2 (20000 : ℝ) (21000 : ℝ) ≤ (0.000000000000000000000000000000000031585 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (20000 : ℝ) (21000 : ℝ) 2 28856 7.1622e-44
    (0.000000000000000000000000000000000031585 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row20000_a2_le row20000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10000_lt, LogTables.exp_neg_40000_3_lt,
                   Real.exp_pos (-(10000:ℝ)), Real.exp_pos (-(40000/3:ℝ))])

/-- Row 20000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row20000_k3_margin :
    B_8_exact 3 (20000 : ℝ) (21000 : ℝ) ≤ (0.00000000000000000000000000000066328 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (20000 : ℝ) (21000 : ℝ) 2 28856 7.1622e-44
    (0.00000000000000000000000000000066328 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row20000_a2_le row20000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10000_lt, LogTables.exp_neg_40000_3_lt,
                   Real.exp_pos (-(10000:ℝ)), Real.exp_pos (-(40000/3:ℝ))])

/-- Row 20000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row20000_k4_margin :
    B_8_exact 4 (20000 : ℝ) (21000 : ℝ) ≤ (0.000000000000000000000000013929 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (20000 : ℝ) (21000 : ℝ) 2 28856 7.1622e-44
    (0.000000000000000000000000013929 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row20000_a2_le row20000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10000_lt, LogTables.exp_neg_40000_3_lt,
                   Real.exp_pos (-(10000:ℝ)), Real.exp_pos (-(40000/3:ℝ))])

/-- Row 20000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row20000_k5_margin :
    B_8_exact 5 (20000 : ℝ) (21000 : ℝ) ≤ (0.00000000000000000000029251 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (20000 : ℝ) (21000 : ℝ) 2 28856 7.1622e-44
    (0.00000000000000000000029251 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row20000_a2_le row20000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10000_lt, LogTables.exp_neg_40000_3_lt,
                   Real.exp_pos (-(10000:ℝ)), Real.exp_pos (-(40000/3:ℝ))])

/-- Row 21000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row21000_k1_margin :
    B_8_exact 1 (21000 : ℝ) (22000 : ℝ) ≤ (0.000000000000000000000000000000000000000090605 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (21000 : ℝ) (22000 : ℝ) 2 30299 4.1185e-45
    (0.000000000000000000000000000000000000000090605 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row21000_a2_le row21000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10500_lt, LogTables.exp_neg_14000_lt,
                   Real.exp_pos (-(10500:ℝ)), Real.exp_pos (-(14000:ℝ))])

/-- Row 21000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row21000_k2_margin :
    B_8_exact 2 (21000 : ℝ) (22000 : ℝ) ≤ (0.0000000000000000000000000000000000019933 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (21000 : ℝ) (22000 : ℝ) 2 30299 4.1185e-45
    (0.0000000000000000000000000000000000019933 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row21000_a2_le row21000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10500_lt, LogTables.exp_neg_14000_lt,
                   Real.exp_pos (-(10500:ℝ)), Real.exp_pos (-(14000:ℝ))])

/-- Row 21000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row21000_k3_margin :
    B_8_exact 3 (21000 : ℝ) (22000 : ℝ) ≤ (0.000000000000000000000000000000043853 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (21000 : ℝ) (22000 : ℝ) 2 30299 4.1185e-45
    (0.000000000000000000000000000000043853 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row21000_a2_le row21000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10500_lt, LogTables.exp_neg_14000_lt,
                   Real.exp_pos (-(10500:ℝ)), Real.exp_pos (-(14000:ℝ))])

/-- Row 21000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row21000_k4_margin :
    B_8_exact 4 (21000 : ℝ) (22000 : ℝ) ≤ (0.00000000000000000000000000096476 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (21000 : ℝ) (22000 : ℝ) 2 30299 4.1185e-45
    (0.00000000000000000000000000096476 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row21000_a2_le row21000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10500_lt, LogTables.exp_neg_14000_lt,
                   Real.exp_pos (-(10500:ℝ)), Real.exp_pos (-(14000:ℝ))])

/-- Row 21000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row21000_k5_margin :
    B_8_exact 5 (21000 : ℝ) (22000 : ℝ) ≤ (0.000000000000000000000021225 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (21000 : ℝ) (22000 : ℝ) 2 30299 4.1185e-45
    (0.000000000000000000000021225 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row21000_a2_le row21000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_10500_lt, LogTables.exp_neg_14000_lt,
                   Real.exp_pos (-(10500:ℝ)), Real.exp_pos (-(14000:ℝ))])

/-- Row 22000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row22000_k1_margin :
    B_8_exact 1 (22000 : ℝ) (23000 : ℝ) ≤ (0.0000000000000000000000000000000000000000056101 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (22000 : ℝ) (23000 : ℝ) 2 31742 2.4393e-46
    (0.0000000000000000000000000000000000000000056101 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row22000_a2_le row22000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11000_lt, LogTables.exp_neg_44000_3_lt,
                   Real.exp_pos (-(11000:ℝ)), Real.exp_pos (-(44000/3:ℝ))])

/-- Row 22000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row22000_k2_margin :
    B_8_exact 2 (22000 : ℝ) (23000 : ℝ) ≤ (0.00000000000000000000000000000000000012903 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (22000 : ℝ) (23000 : ℝ) 2 31742 2.4393e-46
    (0.00000000000000000000000000000000000012903 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row22000_a2_le row22000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11000_lt, LogTables.exp_neg_44000_3_lt,
                   Real.exp_pos (-(11000:ℝ)), Real.exp_pos (-(44000/3:ℝ))])

/-- Row 22000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row22000_k3_margin :
    B_8_exact 3 (22000 : ℝ) (23000 : ℝ) ≤ (0.0000000000000000000000000000000029677 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (22000 : ℝ) (23000 : ℝ) 2 31742 2.4393e-46
    (0.0000000000000000000000000000000029677 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row22000_a2_le row22000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11000_lt, LogTables.exp_neg_44000_3_lt,
                   Real.exp_pos (-(11000:ℝ)), Real.exp_pos (-(44000/3:ℝ))])

/-- Row 22000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row22000_k4_margin :
    B_8_exact 4 (22000 : ℝ) (23000 : ℝ) ≤ (0.000000000000000000000000000068258 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (22000 : ℝ) (23000 : ℝ) 2 31742 2.4393e-46
    (0.000000000000000000000000000068258 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row22000_a2_le row22000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11000_lt, LogTables.exp_neg_44000_3_lt,
                   Real.exp_pos (-(11000:ℝ)), Real.exp_pos (-(44000/3:ℝ))])

/-- Row 22000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row22000_k5_margin :
    B_8_exact 5 (22000 : ℝ) (23000 : ℝ) ≤ (0.0000000000000000000000015699 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (22000 : ℝ) (23000 : ℝ) 2 31742 2.4393e-46
    (0.0000000000000000000000015699 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row22000_a2_le row22000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11000_lt, LogTables.exp_neg_44000_3_lt,
                   Real.exp_pos (-(11000:ℝ)), Real.exp_pos (-(44000/3:ℝ))])

/-- Row 23000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row23000_k1_margin :
    B_8_exact 1 (23000 : ℝ) (24000 : ℝ) ≤ (0.00000000000000000000000000000000000000000037554 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (23000 : ℝ) (24000 : ℝ) 2 33184 1.5648e-47
    (0.00000000000000000000000000000000000000000037554 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row23000_a2_le row23000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11500_lt, LogTables.exp_neg_46000_3_lt,
                   Real.exp_pos (-(11500:ℝ)), Real.exp_pos (-(46000/3:ℝ))])

/-- Row 23000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row23000_k2_margin :
    B_8_exact 2 (23000 : ℝ) (24000 : ℝ) ≤ (0.0000000000000000000000000000000000000090129 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (23000 : ℝ) (24000 : ℝ) 2 33184 1.5648e-47
    (0.0000000000000000000000000000000000000090129 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row23000_a2_le row23000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11500_lt, LogTables.exp_neg_46000_3_lt,
                   Real.exp_pos (-(11500:ℝ)), Real.exp_pos (-(46000/3:ℝ))])

/-- Row 23000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row23000_k3_margin :
    B_8_exact 3 (23000 : ℝ) (24000 : ℝ) ≤ (0.00000000000000000000000000000000021631 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (23000 : ℝ) (24000 : ℝ) 2 33184 1.5648e-47
    (0.00000000000000000000000000000000021631 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row23000_a2_le row23000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11500_lt, LogTables.exp_neg_46000_3_lt,
                   Real.exp_pos (-(11500:ℝ)), Real.exp_pos (-(46000/3:ℝ))])

/-- Row 23000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row23000_k4_margin :
    B_8_exact 4 (23000 : ℝ) (24000 : ℝ) ≤ (0.0000000000000000000000000000051914 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (23000 : ℝ) (24000 : ℝ) 2 33184 1.5648e-47
    (0.0000000000000000000000000000051914 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row23000_a2_le row23000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11500_lt, LogTables.exp_neg_46000_3_lt,
                   Real.exp_pos (-(11500:ℝ)), Real.exp_pos (-(46000/3:ℝ))])

/-- Row 23000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row23000_k5_margin :
    B_8_exact 5 (23000 : ℝ) (24000 : ℝ) ≤ (0.00000000000000000000000012460 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (23000 : ℝ) (24000 : ℝ) 2 33184 1.5648e-47
    (0.00000000000000000000000012460 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row23000_a2_le row23000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_11500_lt, LogTables.exp_neg_46000_3_lt,
                   Real.exp_pos (-(11500:ℝ)), Real.exp_pos (-(46000/3:ℝ))])

/-- Row 24000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row24000_k1_margin :
    B_8_exact 1 (24000 : ℝ) (25000 : ℝ) ≤ (0.000000000000000000000000000000000000000000026755 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (24000 : ℝ) (25000 : ℝ) 2 34627 1.0703e-48
    (0.000000000000000000000000000000000000000000026755 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row24000_a2_le row24000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_12000_lt, LogTables.exp_neg_16000_lt,
                   Real.exp_pos (-(12000:ℝ)), Real.exp_pos (-(16000:ℝ))])

/-- Row 24000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row24000_k2_margin :
    B_8_exact 2 (24000 : ℝ) (25000 : ℝ) ≤ (0.00000000000000000000000000000000000000066888 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (24000 : ℝ) (25000 : ℝ) 2 34627 1.0703e-48
    (0.00000000000000000000000000000000000000066888 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row24000_a2_le row24000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_12000_lt, LogTables.exp_neg_16000_lt,
                   Real.exp_pos (-(12000:ℝ)), Real.exp_pos (-(16000:ℝ))])

/-- Row 24000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row24000_k3_margin :
    B_8_exact 3 (24000 : ℝ) (25000 : ℝ) ≤ (0.000000000000000000000000000000000016722 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (24000 : ℝ) (25000 : ℝ) 2 34627 1.0703e-48
    (0.000000000000000000000000000000000016722 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row24000_a2_le row24000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_12000_lt, LogTables.exp_neg_16000_lt,
                   Real.exp_pos (-(12000:ℝ)), Real.exp_pos (-(16000:ℝ))])

/-- Row 24000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row24000_k4_margin :
    B_8_exact 4 (24000 : ℝ) (25000 : ℝ) ≤ (0.00000000000000000000000000000041805 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (24000 : ℝ) (25000 : ℝ) 2 34627 1.0703e-48
    (0.00000000000000000000000000000041805 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row24000_a2_le row24000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_12000_lt, LogTables.exp_neg_16000_lt,
                   Real.exp_pos (-(12000:ℝ)), Real.exp_pos (-(16000:ℝ))])

/-- Row 24000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row24000_k5_margin :
    B_8_exact 5 (24000 : ℝ) (25000 : ℝ) ≤ (0.000000000000000000000000010451 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (24000 : ℝ) (25000 : ℝ) 2 34627 1.0703e-48
    (0.000000000000000000000000010451 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row24000_a2_le row24000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_12000_lt, LogTables.exp_neg_16000_lt,
                   Real.exp_pos (-(12000:ℝ)), Real.exp_pos (-(16000:ℝ))])

end BKLNW
