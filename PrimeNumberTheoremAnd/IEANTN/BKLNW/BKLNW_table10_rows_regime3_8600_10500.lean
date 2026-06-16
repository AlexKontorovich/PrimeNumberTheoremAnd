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

private lemma row8600_a2_le : Inputs.default.a₂ (8600 : ℝ) ≤ (12410 : ℝ) := by
  have h := a2_crude_le (8600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8600 : ℝ) / log 2⌋₊ : ℝ) ≤ (8600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8600 : ℝ) / log 2 ≤ 12408 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12408 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12410 := by norm_num

private lemma row8700_a2_le : Inputs.default.a₂ (8700 : ℝ) ≤ (12554 : ℝ) := by
  have h := a2_crude_le (8700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8700 : ℝ) / log 2⌋₊ : ℝ) ≤ (8700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8700 : ℝ) / log 2 ≤ 12552 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12552 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12554 := by norm_num

private lemma row8800_a2_le : Inputs.default.a₂ (8800 : ℝ) ≤ (12698 : ℝ) := by
  have h := a2_crude_le (8800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8800 : ℝ) / log 2⌋₊ : ℝ) ≤ (8800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8800 : ℝ) / log 2 ≤ 12696 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12696 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12698 := by norm_num

private lemma row8900_a2_le : Inputs.default.a₂ (8900 : ℝ) ≤ (12842 : ℝ) := by
  have h := a2_crude_le (8900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(8900 : ℝ) / log 2⌋₊ : ℝ) ≤ (8900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (8900 : ℝ) / log 2 ≤ 12840 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (8900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(8900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12840 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12842 := by norm_num

private lemma row9000_a2_le : Inputs.default.a₂ (9000 : ℝ) ≤ (12987 : ℝ) := by
  have h := a2_crude_le (9000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9000 : ℝ) / log 2⌋₊ : ℝ) ≤ (9000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9000 : ℝ) / log 2 ≤ 12985 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (12985 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 12987 := by norm_num

private lemma row9100_a2_le : Inputs.default.a₂ (9100 : ℝ) ≤ (13131 : ℝ) := by
  have h := a2_crude_le (9100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9100 : ℝ) / log 2⌋₊ : ℝ) ≤ (9100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9100 : ℝ) / log 2 ≤ 13129 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13129 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13131 := by norm_num

private lemma row9200_a2_le : Inputs.default.a₂ (9200 : ℝ) ≤ (13275 : ℝ) := by
  have h := a2_crude_le (9200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9200 : ℝ) / log 2⌋₊ : ℝ) ≤ (9200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9200 : ℝ) / log 2 ≤ 13273 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13273 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13275 := by norm_num

private lemma row9300_a2_le : Inputs.default.a₂ (9300 : ℝ) ≤ (13420 : ℝ) := by
  have h := a2_crude_le (9300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9300 : ℝ) / log 2⌋₊ : ℝ) ≤ (9300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9300 : ℝ) / log 2 ≤ 13418 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13418 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13420 := by norm_num

private lemma row9400_a2_le : Inputs.default.a₂ (9400 : ℝ) ≤ (13564 : ℝ) := by
  have h := a2_crude_le (9400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9400 : ℝ) / log 2⌋₊ : ℝ) ≤ (9400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9400 : ℝ) / log 2 ≤ 13562 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13562 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13564 := by norm_num

private lemma row9500_a2_le : Inputs.default.a₂ (9500 : ℝ) ≤ (13708 : ℝ) := by
  have h := a2_crude_le (9500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9500 : ℝ) / log 2⌋₊ : ℝ) ≤ (9500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9500 : ℝ) / log 2 ≤ 13706 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13706 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13708 := by norm_num

private lemma row9600_a2_le : Inputs.default.a₂ (9600 : ℝ) ≤ (13852 : ℝ) := by
  have h := a2_crude_le (9600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9600 : ℝ) / log 2⌋₊ : ℝ) ≤ (9600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9600 : ℝ) / log 2 ≤ 13850 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13850 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13852 := by norm_num

private lemma row9700_a2_le : Inputs.default.a₂ (9700 : ℝ) ≤ (13997 : ℝ) := by
  have h := a2_crude_le (9700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9700 : ℝ) / log 2⌋₊ : ℝ) ≤ (9700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9700 : ℝ) / log 2 ≤ 13995 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (13995 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 13997 := by norm_num

private lemma row9800_a2_le : Inputs.default.a₂ (9800 : ℝ) ≤ (14141 : ℝ) := by
  have h := a2_crude_le (9800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9800 : ℝ) / log 2⌋₊ : ℝ) ≤ (9800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9800 : ℝ) / log 2 ≤ 14139 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14139 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14141 := by norm_num

private lemma row9900_a2_le : Inputs.default.a₂ (9900 : ℝ) ≤ (14285 : ℝ) := by
  have h := a2_crude_le (9900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(9900 : ℝ) / log 2⌋₊ : ℝ) ≤ (9900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (9900 : ℝ) / log 2 ≤ 14283 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (9900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(9900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14283 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14285 := by norm_num

private lemma row10000_a2_le : Inputs.default.a₂ (10000 : ℝ) ≤ (14429 : ℝ) := by
  have h := a2_crude_le (10000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10000 : ℝ) / log 2⌋₊ : ℝ) ≤ (10000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10000 : ℝ) / log 2 ≤ 14427 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14427 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14429 := by norm_num

private lemma row10100_a2_le : Inputs.default.a₂ (10100 : ℝ) ≤ (14574 : ℝ) := by
  have h := a2_crude_le (10100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10100 : ℝ) / log 2⌋₊ : ℝ) ≤ (10100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10100 : ℝ) / log 2 ≤ 14572 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14572 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14574 := by norm_num

private lemma row10200_a2_le : Inputs.default.a₂ (10200 : ℝ) ≤ (14718 : ℝ) := by
  have h := a2_crude_le (10200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10200 : ℝ) / log 2⌋₊ : ℝ) ≤ (10200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10200 : ℝ) / log 2 ≤ 14716 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14716 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14718 := by norm_num

private lemma row10300_a2_le : Inputs.default.a₂ (10300 : ℝ) ≤ (14862 : ℝ) := by
  have h := a2_crude_le (10300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10300 : ℝ) / log 2⌋₊ : ℝ) ≤ (10300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10300 : ℝ) / log 2 ≤ 14860 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (14860 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 14862 := by norm_num

private lemma row10400_a2_le : Inputs.default.a₂ (10400 : ℝ) ≤ (15007 : ℝ) := by
  have h := a2_crude_le (10400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10400 : ℝ) / log 2⌋₊ : ℝ) ≤ (10400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10400 : ℝ) / log 2 ≤ 15005 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15005 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15007 := by norm_num

private lemma row10500_a2_le : Inputs.default.a₂ (10500 : ℝ) ≤ (15151 : ℝ) := by
  have h := a2_crude_le (10500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10500 : ℝ) / log 2⌋₊ : ℝ) ≤ (10500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10500 : ℝ) / log 2 ≤ 15149 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15149 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15151 := by norm_num

set_option maxRecDepth 10000 in
private lemma row8600_table8_mem : (8600, 1.3772e-26) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8600_eps_le : Inputs.default.ε (8600 : ℝ) ≤ 1.3772e-26 := by
  change BKLNW_app.table_8_ε (8600 : ℝ) ≤ 1.3772e-26
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8600)
    (ε := 1.3772e-26) row8600_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row8700_table8_mem : (8700, 8.8888e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8700_eps_le : Inputs.default.ε (8700 : ℝ) ≤ 8.8888e-27 := by
  change BKLNW_app.table_8_ε (8700 : ℝ) ≤ 8.8888e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8700)
    (ε := 8.8888e-27) row8700_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row8800_table8_mem : (8800, 5.7961e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8800_eps_le : Inputs.default.ε (8800 : ℝ) ≤ 5.7961e-27 := by
  change BKLNW_app.table_8_ε (8800 : ℝ) ≤ 5.7961e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8800)
    (ε := 5.7961e-27) row8800_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row8900_table8_mem : (8900, 3.7648e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row8900_eps_le : Inputs.default.ε (8900 : ℝ) ≤ 3.7648e-27 := by
  change BKLNW_app.table_8_ε (8900 : ℝ) ≤ 3.7648e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 8900)
    (ε := 3.7648e-27) row8900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9000_table8_mem : (9000, 2.4454e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9000_eps_le : Inputs.default.ε (9000 : ℝ) ≤ 2.4454e-27 := by
  change BKLNW_app.table_8_ε (9000 : ℝ) ≤ 2.4454e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9000)
    (ε := 2.4454e-27) row9000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9100_table8_mem : (9100, 1.5915e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9100_eps_le : Inputs.default.ε (9100 : ℝ) ≤ 1.5915e-27 := by
  change BKLNW_app.table_8_ε (9100 : ℝ) ≤ 1.5915e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9100)
    (ε := 1.5915e-27) row9100_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9200_table8_mem : (9200, 1.0407e-27) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9200_eps_le : Inputs.default.ε (9200 : ℝ) ≤ 1.0407e-27 := by
  change BKLNW_app.table_8_ε (9200 : ℝ) ≤ 1.0407e-27
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9200)
    (ε := 1.0407e-27) row9200_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9300_table8_mem : (9300, 6.8293e-28) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9300_eps_le : Inputs.default.ε (9300 : ℝ) ≤ 6.8293e-28 := by
  change BKLNW_app.table_8_ε (9300 : ℝ) ≤ 6.8293e-28
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9300)
    (ε := 6.8293e-28) row9300_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9400_table8_mem : (9400, 4.5234e-28) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9400_eps_le : Inputs.default.ε (9400 : ℝ) ≤ 4.5234e-28 := by
  change BKLNW_app.table_8_ε (9400 : ℝ) ≤ 4.5234e-28
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9400)
    (ε := 4.5234e-28) row9400_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9500_table8_mem : (9500, 2.9701e-28) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9500_eps_le : Inputs.default.ε (9500 : ℝ) ≤ 2.9701e-28 := by
  change BKLNW_app.table_8_ε (9500 : ℝ) ≤ 2.9701e-28
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9500)
    (ε := 2.9701e-28) row9500_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9600_table8_mem : (9600, 1.9649e-28) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9600_eps_le : Inputs.default.ε (9600 : ℝ) ≤ 1.9649e-28 := by
  change BKLNW_app.table_8_ε (9600 : ℝ) ≤ 1.9649e-28
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9600)
    (ε := 1.9649e-28) row9600_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9700_table8_mem : (9700, 1.2949e-28) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9700_eps_le : Inputs.default.ε (9700 : ℝ) ≤ 1.2949e-28 := by
  change BKLNW_app.table_8_ε (9700 : ℝ) ≤ 1.2949e-28
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9700)
    (ε := 1.2949e-28) row9700_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9800_table8_mem : (9800, 8.5698e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9800_eps_le : Inputs.default.ε (9800 : ℝ) ≤ 8.5698e-29 := by
  change BKLNW_app.table_8_ε (9800 : ℝ) ≤ 8.5698e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9800)
    (ε := 8.5698e-29) row9800_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row9900_table8_mem : (9900, 5.7396e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row9900_eps_le : Inputs.default.ε (9900 : ℝ) ≤ 5.7396e-29 := by
  change BKLNW_app.table_8_ε (9900 : ℝ) ≤ 5.7396e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 9900)
    (ε := 5.7396e-29) row9900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10000_table8_mem : (10000, 3.7850e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10000_eps_le : Inputs.default.ε (10000 : ℝ) ≤ 3.7850e-29 := by
  change BKLNW_app.table_8_ε (10000 : ℝ) ≤ 3.7850e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10000)
    (ε := 3.7850e-29) row10000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10100_table8_mem : (10100, 2.5241e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10100_eps_le : Inputs.default.ε (10100 : ℝ) ≤ 2.5241e-29 := by
  change BKLNW_app.table_8_ε (10100 : ℝ) ≤ 2.5241e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10100)
    (ε := 2.5241e-29) row10100_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10200_table8_mem : (10200, 1.6883e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10200_eps_le : Inputs.default.ε (10200 : ℝ) ≤ 1.6883e-29 := by
  change BKLNW_app.table_8_ε (10200 : ℝ) ≤ 1.6883e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10200)
    (ε := 1.6883e-29) row10200_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10300_table8_mem : (10300, 1.1283e-29) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10300_eps_le : Inputs.default.ε (10300 : ℝ) ≤ 1.1283e-29 := by
  change BKLNW_app.table_8_ε (10300 : ℝ) ≤ 1.1283e-29
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10300)
    (ε := 1.1283e-29) row10300_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10400_table8_mem : (10400, 7.5768e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10400_eps_le : Inputs.default.ε (10400 : ℝ) ≤ 7.5768e-30 := by
  change BKLNW_app.table_8_ε (10400 : ℝ) ≤ 7.5768e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10400)
    (ε := 7.5768e-30) row10400_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row10500_table8_mem : (10500, 5.1016e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10500_eps_le : Inputs.default.ε (10500 : ℝ) ≤ 5.1016e-30 := by
  change BKLNW_app.table_8_ε (10500 : ℝ) ≤ 5.1016e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10500)
    (ε := 5.1016e-30) row10500_table8_mem (by norm_num)

/-- Row 8600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8600_k1_margin :
    B_8_exact 1 (8600 : ℝ) (8700 : ℝ) ≤ (0.00000000000000000000011981 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8600 : ℝ) (8700 : ℝ) 2 12410 1.3772e-26
    (0.00000000000000000000011981 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8600_a2_le row8600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4300_lt, LogTables.exp_neg_17200_3_lt,
                   Real.exp_pos (-(4300:ℝ)), Real.exp_pos (-(17200/3:ℝ))])

/-- Row 8600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8600_k2_margin :
    B_8_exact 2 (8600 : ℝ) (8700 : ℝ) ≤ (0.0000000000000000010423 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8600 : ℝ) (8700 : ℝ) 2 12410 1.3772e-26
    (0.0000000000000000010423 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8600_a2_le row8600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4300_lt, LogTables.exp_neg_17200_3_lt,
                   Real.exp_pos (-(4300:ℝ)), Real.exp_pos (-(17200/3:ℝ))])

/-- Row 8600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8600_k3_margin :
    B_8_exact 3 (8600 : ℝ) (8700 : ℝ) ≤ (0.0000000000000090682 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8600 : ℝ) (8700 : ℝ) 2 12410 1.3772e-26
    (0.0000000000000090682 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8600_a2_le row8600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4300_lt, LogTables.exp_neg_17200_3_lt,
                   Real.exp_pos (-(4300:ℝ)), Real.exp_pos (-(17200/3:ℝ))])

/-- Row 8600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8600_k4_margin :
    B_8_exact 4 (8600 : ℝ) (8700 : ℝ) ≤ (0.000000000078893 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8600 : ℝ) (8700 : ℝ) 2 12410 1.3772e-26
    (0.000000000078893 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8600_a2_le row8600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4300_lt, LogTables.exp_neg_17200_3_lt,
                   Real.exp_pos (-(4300:ℝ)), Real.exp_pos (-(17200/3:ℝ))])

/-- Row 8600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8600_k5_margin :
    B_8_exact 5 (8600 : ℝ) (8700 : ℝ) ≤ (0.00000068637 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8600 : ℝ) (8700 : ℝ) 2 12410 1.3772e-26
    (0.00000068637 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8600_a2_le row8600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4300_lt, LogTables.exp_neg_17200_3_lt,
                   Real.exp_pos (-(4300:ℝ)), Real.exp_pos (-(17200/3:ℝ))])

/-- Row 8700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8700_k1_margin :
    B_8_exact 1 (8700 : ℝ) (8800 : ℝ) ≤ (0.000000000000000000000078220 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8700 : ℝ) (8800 : ℝ) 2 12554 8.8888e-27
    (0.000000000000000000000078220 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8700_a2_le row8700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4350_lt, LogTables.exp_neg_5800_lt,
                   Real.exp_pos (-(4350:ℝ)), Real.exp_pos (-(5800:ℝ))])

/-- Row 8700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8700_k2_margin :
    B_8_exact 2 (8700 : ℝ) (8800 : ℝ) ≤ (0.00000000000000000068834 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8700 : ℝ) (8800 : ℝ) 2 12554 8.8888e-27
    (0.00000000000000000068834 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8700_a2_le row8700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4350_lt, LogTables.exp_neg_5800_lt,
                   Real.exp_pos (-(4350:ℝ)), Real.exp_pos (-(5800:ℝ))])

/-- Row 8700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8700_k3_margin :
    B_8_exact 3 (8700 : ℝ) (8800 : ℝ) ≤ (0.0000000000000060574 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8700 : ℝ) (8800 : ℝ) 2 12554 8.8888e-27
    (0.0000000000000060574 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8700_a2_le row8700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4350_lt, LogTables.exp_neg_5800_lt,
                   Real.exp_pos (-(4350:ℝ)), Real.exp_pos (-(5800:ℝ))])

/-- Row 8700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8700_k4_margin :
    B_8_exact 4 (8700 : ℝ) (8800 : ℝ) ≤ (0.000000000053305 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8700 : ℝ) (8800 : ℝ) 2 12554 8.8888e-27
    (0.000000000053305 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8700_a2_le row8700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4350_lt, LogTables.exp_neg_5800_lt,
                   Real.exp_pos (-(4350:ℝ)), Real.exp_pos (-(5800:ℝ))])

/-- Row 8700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8700_k5_margin :
    B_8_exact 5 (8700 : ℝ) (8800 : ℝ) ≤ (0.00000046908 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8700 : ℝ) (8800 : ℝ) 2 12554 8.8888e-27
    (0.00000046908 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8700_a2_le row8700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4350_lt, LogTables.exp_neg_5800_lt,
                   Real.exp_pos (-(4350:ℝ)), Real.exp_pos (-(5800:ℝ))])

/-- Row 8800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8800_k1_margin :
    B_8_exact 1 (8800 : ℝ) (8900 : ℝ) ≤ (0.000000000000000000000051585 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8800 : ℝ) (8900 : ℝ) 2 12698 5.7961e-27
    (0.000000000000000000000051585 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8800_a2_le row8800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4400_lt, LogTables.exp_neg_17600_3_lt,
                   Real.exp_pos (-(4400:ℝ)), Real.exp_pos (-(17600/3:ℝ))])

/-- Row 8800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8800_k2_margin :
    B_8_exact 2 (8800 : ℝ) (8900 : ℝ) ≤ (0.00000000000000000045910 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8800 : ℝ) (8900 : ℝ) 2 12698 5.7961e-27
    (0.00000000000000000045910 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8800_a2_le row8800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4400_lt, LogTables.exp_neg_17600_3_lt,
                   Real.exp_pos (-(4400:ℝ)), Real.exp_pos (-(17600/3:ℝ))])

/-- Row 8800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8800_k3_margin :
    B_8_exact 3 (8800 : ℝ) (8900 : ℝ) ≤ (0.0000000000000040860 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8800 : ℝ) (8900 : ℝ) 2 12698 5.7961e-27
    (0.0000000000000040860 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8800_a2_le row8800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4400_lt, LogTables.exp_neg_17600_3_lt,
                   Real.exp_pos (-(4400:ℝ)), Real.exp_pos (-(17600/3:ℝ))])

/-- Row 8800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8800_k4_margin :
    B_8_exact 4 (8800 : ℝ) (8900 : ℝ) ≤ (0.000000000036366 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8800 : ℝ) (8900 : ℝ) 2 12698 5.7961e-27
    (0.000000000036366 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8800_a2_le row8800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4400_lt, LogTables.exp_neg_17600_3_lt,
                   Real.exp_pos (-(4400:ℝ)), Real.exp_pos (-(17600/3:ℝ))])

/-- Row 8800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8800_k5_margin :
    B_8_exact 5 (8800 : ℝ) (8900 : ℝ) ≤ (0.00000032365 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8800 : ℝ) (8900 : ℝ) 2 12698 5.7961e-27
    (0.00000032365 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8800_a2_le row8800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4400_lt, LogTables.exp_neg_17600_3_lt,
                   Real.exp_pos (-(4400:ℝ)), Real.exp_pos (-(17600/3:ℝ))])

/-- Row 8900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row8900_k1_margin :
    B_8_exact 1 (8900 : ℝ) (9000 : ℝ) ≤ (0.000000000000000000000033882 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (8900 : ℝ) (9000 : ℝ) 2 12842 3.7648e-27
    (0.000000000000000000000033882 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8900_a2_le row8900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4450_lt, LogTables.exp_neg_17800_3_lt,
                   Real.exp_pos (-(4450:ℝ)), Real.exp_pos (-(17800/3:ℝ))])

/-- Row 8900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row8900_k2_margin :
    B_8_exact 2 (8900 : ℝ) (9000 : ℝ) ≤ (0.00000000000000000030494 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (8900 : ℝ) (9000 : ℝ) 2 12842 3.7648e-27
    (0.00000000000000000030494 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8900_a2_le row8900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4450_lt, LogTables.exp_neg_17800_3_lt,
                   Real.exp_pos (-(4450:ℝ)), Real.exp_pos (-(17800/3:ℝ))])

/-- Row 8900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row8900_k3_margin :
    B_8_exact 3 (8900 : ℝ) (9000 : ℝ) ≤ (0.0000000000000027445 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (8900 : ℝ) (9000 : ℝ) 2 12842 3.7648e-27
    (0.0000000000000027445 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8900_a2_le row8900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4450_lt, LogTables.exp_neg_17800_3_lt,
                   Real.exp_pos (-(4450:ℝ)), Real.exp_pos (-(17800/3:ℝ))])

/-- Row 8900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row8900_k4_margin :
    B_8_exact 4 (8900 : ℝ) (9000 : ℝ) ≤ (0.000000000024700 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (8900 : ℝ) (9000 : ℝ) 2 12842 3.7648e-27
    (0.000000000024700 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8900_a2_le row8900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4450_lt, LogTables.exp_neg_17800_3_lt,
                   Real.exp_pos (-(4450:ℝ)), Real.exp_pos (-(17800/3:ℝ))])

/-- Row 8900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row8900_k5_margin :
    B_8_exact 5 (8900 : ℝ) (9000 : ℝ) ≤ (0.00000022230 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (8900 : ℝ) (9000 : ℝ) 2 12842 3.7648e-27
    (0.00000022230 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row8900_a2_le row8900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4450_lt, LogTables.exp_neg_17800_3_lt,
                   Real.exp_pos (-(4450:ℝ)), Real.exp_pos (-(17800/3:ℝ))])

/-- Row 9000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9000_k1_margin :
    B_8_exact 1 (9000 : ℝ) (9100 : ℝ) ≤ (0.000000000000000000000022252 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9000 : ℝ) (9100 : ℝ) 2 12987 2.4454e-27
    (0.000000000000000000000022252 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9000_a2_le row9000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4500_lt, LogTables.exp_neg_6000_lt,
                   Real.exp_pos (-(4500:ℝ)), Real.exp_pos (-(6000:ℝ))])

/-- Row 9000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9000_k2_margin :
    B_8_exact 2 (9000 : ℝ) (9100 : ℝ) ≤ (0.00000000000000000020250 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9000 : ℝ) (9100 : ℝ) 2 12987 2.4454e-27
    (0.00000000000000000020250 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9000_a2_le row9000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4500_lt, LogTables.exp_neg_6000_lt,
                   Real.exp_pos (-(4500:ℝ)), Real.exp_pos (-(6000:ℝ))])

/-- Row 9000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9000_k3_margin :
    B_8_exact 3 (9000 : ℝ) (9100 : ℝ) ≤ (0.0000000000000018427 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9000 : ℝ) (9100 : ℝ) 2 12987 2.4454e-27
    (0.0000000000000018427 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9000_a2_le row9000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4500_lt, LogTables.exp_neg_6000_lt,
                   Real.exp_pos (-(4500:ℝ)), Real.exp_pos (-(6000:ℝ))])

/-- Row 9000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9000_k4_margin :
    B_8_exact 4 (9000 : ℝ) (9100 : ℝ) ≤ (0.000000000016769 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9000 : ℝ) (9100 : ℝ) 2 12987 2.4454e-27
    (0.000000000016769 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9000_a2_le row9000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4500_lt, LogTables.exp_neg_6000_lt,
                   Real.exp_pos (-(4500:ℝ)), Real.exp_pos (-(6000:ℝ))])

/-- Row 9000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9000_k5_margin :
    B_8_exact 5 (9000 : ℝ) (9100 : ℝ) ≤ (0.00000015260 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9000 : ℝ) (9100 : ℝ) 2 12987 2.4454e-27
    (0.00000015260 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9000_a2_le row9000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4500_lt, LogTables.exp_neg_6000_lt,
                   Real.exp_pos (-(4500:ℝ)), Real.exp_pos (-(6000:ℝ))])

/-- Row 9100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9100_k1_margin :
    B_8_exact 1 (9100 : ℝ) (9200 : ℝ) ≤ (0.000000000000000000000014641 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9100 : ℝ) (9200 : ℝ) 2 13131 1.5915e-27
    (0.000000000000000000000014641 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9100_a2_le row9100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4550_lt, LogTables.exp_neg_18200_3_lt,
                   Real.exp_pos (-(4550:ℝ)), Real.exp_pos (-(18200/3:ℝ))])

/-- Row 9100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9100_k2_margin :
    B_8_exact 2 (9100 : ℝ) (9200 : ℝ) ≤ (0.00000000000000000013470 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9100 : ℝ) (9200 : ℝ) 2 13131 1.5915e-27
    (0.00000000000000000013470 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9100_a2_le row9100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4550_lt, LogTables.exp_neg_18200_3_lt,
                   Real.exp_pos (-(4550:ℝ)), Real.exp_pos (-(18200/3:ℝ))])

/-- Row 9100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9100_k3_margin :
    B_8_exact 3 (9100 : ℝ) (9200 : ℝ) ≤ (0.0000000000000012392 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9100 : ℝ) (9200 : ℝ) 2 13131 1.5915e-27
    (0.0000000000000012392 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9100_a2_le row9100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4550_lt, LogTables.exp_neg_18200_3_lt,
                   Real.exp_pos (-(4550:ℝ)), Real.exp_pos (-(18200/3:ℝ))])

/-- Row 9100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9100_k4_margin :
    B_8_exact 4 (9100 : ℝ) (9200 : ℝ) ≤ (0.000000000011401 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9100 : ℝ) (9200 : ℝ) 2 13131 1.5915e-27
    (0.000000000011401 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9100_a2_le row9100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4550_lt, LogTables.exp_neg_18200_3_lt,
                   Real.exp_pos (-(4550:ℝ)), Real.exp_pos (-(18200/3:ℝ))])

/-- Row 9100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9100_k5_margin :
    B_8_exact 5 (9100 : ℝ) (9200 : ℝ) ≤ (0.00000010489 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9100 : ℝ) (9200 : ℝ) 2 13131 1.5915e-27
    (0.00000010489 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9100_a2_le row9100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4550_lt, LogTables.exp_neg_18200_3_lt,
                   Real.exp_pos (-(4550:ℝ)), Real.exp_pos (-(18200/3:ℝ))])

/-- Row 9200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9200_k1_margin :
    B_8_exact 1 (9200 : ℝ) (9300 : ℝ) ≤ (0.0000000000000000000000096777 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9200 : ℝ) (9300 : ℝ) 2 13275 1.0407e-27
    (0.0000000000000000000000096777 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9200_a2_le row9200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4600_lt, LogTables.exp_neg_18400_3_lt,
                   Real.exp_pos (-(4600:ℝ)), Real.exp_pos (-(18400/3:ℝ))])

/-- Row 9200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9200_k2_margin :
    B_8_exact 2 (9200 : ℝ) (9300 : ℝ) ≤ (0.000000000000000000090003 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9200 : ℝ) (9300 : ℝ) 2 13275 1.0407e-27
    (0.000000000000000000090003 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9200_a2_le row9200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4600_lt, LogTables.exp_neg_18400_3_lt,
                   Real.exp_pos (-(4600:ℝ)), Real.exp_pos (-(18400/3:ℝ))])

/-- Row 9200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9200_k3_margin :
    B_8_exact 3 (9200 : ℝ) (9300 : ℝ) ≤ (0.00000000000000083703 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9200 : ℝ) (9300 : ℝ) 2 13275 1.0407e-27
    (0.00000000000000083703 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9200_a2_le row9200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4600_lt, LogTables.exp_neg_18400_3_lt,
                   Real.exp_pos (-(4600:ℝ)), Real.exp_pos (-(18400/3:ℝ))])

/-- Row 9200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9200_k4_margin :
    B_8_exact 4 (9200 : ℝ) (9300 : ℝ) ≤ (0.0000000000077844 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9200 : ℝ) (9300 : ℝ) 2 13275 1.0407e-27
    (0.0000000000077844 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9200_a2_le row9200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4600_lt, LogTables.exp_neg_18400_3_lt,
                   Real.exp_pos (-(4600:ℝ)), Real.exp_pos (-(18400/3:ℝ))])

/-- Row 9200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9200_k5_margin :
    B_8_exact 5 (9200 : ℝ) (9300 : ℝ) ≤ (0.000000072395 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9200 : ℝ) (9300 : ℝ) 2 13275 1.0407e-27
    (0.000000072395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9200_a2_le row9200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4600_lt, LogTables.exp_neg_18400_3_lt,
                   Real.exp_pos (-(4600:ℝ)), Real.exp_pos (-(18400/3:ℝ))])

/-- Row 9300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9300_k1_margin :
    B_8_exact 1 (9300 : ℝ) (9400 : ℝ) ≤ (0.0000000000000000000000064195 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9300 : ℝ) (9400 : ℝ) 2 13420 6.8293e-28
    (0.0000000000000000000000064195 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9300_a2_le row9300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4650_lt, LogTables.exp_neg_6200_lt,
                   Real.exp_pos (-(4650:ℝ)), Real.exp_pos (-(6200:ℝ))])

/-- Row 9300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9300_k2_margin :
    B_8_exact 2 (9300 : ℝ) (9400 : ℝ) ≤ (0.000000000000000000060343 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9300 : ℝ) (9400 : ℝ) 2 13420 6.8293e-28
    (0.000000000000000000060343 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9300_a2_le row9300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4650_lt, LogTables.exp_neg_6200_lt,
                   Real.exp_pos (-(4650:ℝ)), Real.exp_pos (-(6200:ℝ))])

/-- Row 9300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9300_k3_margin :
    B_8_exact 3 (9300 : ℝ) (9400 : ℝ) ≤ (0.00000000000000056723 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9300 : ℝ) (9400 : ℝ) 2 13420 6.8293e-28
    (0.00000000000000056723 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9300_a2_le row9300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4650_lt, LogTables.exp_neg_6200_lt,
                   Real.exp_pos (-(4650:ℝ)), Real.exp_pos (-(6200:ℝ))])

/-- Row 9300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9300_k4_margin :
    B_8_exact 4 (9300 : ℝ) (9400 : ℝ) ≤ (0.0000000000053319 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9300 : ℝ) (9400 : ℝ) 2 13420 6.8293e-28
    (0.0000000000053319 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9300_a2_le row9300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4650_lt, LogTables.exp_neg_6200_lt,
                   Real.exp_pos (-(4650:ℝ)), Real.exp_pos (-(6200:ℝ))])

/-- Row 9300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9300_k5_margin :
    B_8_exact 5 (9300 : ℝ) (9400 : ℝ) ≤ (0.000000050120 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9300 : ℝ) (9400 : ℝ) 2 13420 6.8293e-28
    (0.000000050120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9300_a2_le row9300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4650_lt, LogTables.exp_neg_6200_lt,
                   Real.exp_pos (-(4650:ℝ)), Real.exp_pos (-(6200:ℝ))])

/-- Row 9400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9400_k1_margin :
    B_8_exact 1 (9400 : ℝ) (9500 : ℝ) ≤ (0.0000000000000000000000042972 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9400 : ℝ) (9500 : ℝ) 2 13564 4.5234e-28
    (0.0000000000000000000000042972 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9400_a2_le row9400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4700_lt, LogTables.exp_neg_18800_3_lt,
                   Real.exp_pos (-(4700:ℝ)), Real.exp_pos (-(18800/3:ℝ))])

/-- Row 9400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9400_k2_margin :
    B_8_exact 2 (9400 : ℝ) (9500 : ℝ) ≤ (0.000000000000000000040823 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9400 : ℝ) (9500 : ℝ) 2 13564 4.5234e-28
    (0.000000000000000000040823 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9400_a2_le row9400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4700_lt, LogTables.exp_neg_18800_3_lt,
                   Real.exp_pos (-(4700:ℝ)), Real.exp_pos (-(18800/3:ℝ))])

/-- Row 9400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9400_k3_margin :
    B_8_exact 3 (9400 : ℝ) (9500 : ℝ) ≤ (0.00000000000000038782 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9400 : ℝ) (9500 : ℝ) 2 13564 4.5234e-28
    (0.00000000000000038782 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9400_a2_le row9400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4700_lt, LogTables.exp_neg_18800_3_lt,
                   Real.exp_pos (-(4700:ℝ)), Real.exp_pos (-(18800/3:ℝ))])

/-- Row 9400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9400_k4_margin :
    B_8_exact 4 (9400 : ℝ) (9500 : ℝ) ≤ (0.0000000000036843 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9400 : ℝ) (9500 : ℝ) 2 13564 4.5234e-28
    (0.0000000000036843 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9400_a2_le row9400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4700_lt, LogTables.exp_neg_18800_3_lt,
                   Real.exp_pos (-(4700:ℝ)), Real.exp_pos (-(18800/3:ℝ))])

/-- Row 9400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9400_k5_margin :
    B_8_exact 5 (9400 : ℝ) (9500 : ℝ) ≤ (0.000000035001 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9400 : ℝ) (9500 : ℝ) 2 13564 4.5234e-28
    (0.000000035001 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9400_a2_le row9400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4700_lt, LogTables.exp_neg_18800_3_lt,
                   Real.exp_pos (-(4700:ℝ)), Real.exp_pos (-(18800/3:ℝ))])

/-- Row 9500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9500_k1_margin :
    B_8_exact 1 (9500 : ℝ) (9600 : ℝ) ≤ (0.0000000000000000000000028512 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9500 : ℝ) (9600 : ℝ) 2 13708 2.9701e-28
    (0.0000000000000000000000028512 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9500_a2_le row9500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4750_lt, LogTables.exp_neg_19000_3_lt,
                   Real.exp_pos (-(4750:ℝ)), Real.exp_pos (-(19000/3:ℝ))])

/-- Row 9500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9500_k2_margin :
    B_8_exact 2 (9500 : ℝ) (9600 : ℝ) ≤ (0.000000000000000000027372 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9500 : ℝ) (9600 : ℝ) 2 13708 2.9701e-28
    (0.000000000000000000027372 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9500_a2_le row9500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4750_lt, LogTables.exp_neg_19000_3_lt,
                   Real.exp_pos (-(4750:ℝ)), Real.exp_pos (-(19000/3:ℝ))])

/-- Row 9500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9500_k3_margin :
    B_8_exact 3 (9500 : ℝ) (9600 : ℝ) ≤ (0.00000000000000026277 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9500 : ℝ) (9600 : ℝ) 2 13708 2.9701e-28
    (0.00000000000000026277 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9500_a2_le row9500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4750_lt, LogTables.exp_neg_19000_3_lt,
                   Real.exp_pos (-(4750:ℝ)), Real.exp_pos (-(19000/3:ℝ))])

/-- Row 9500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9500_k4_margin :
    B_8_exact 4 (9500 : ℝ) (9600 : ℝ) ≤ (0.0000000000025226 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9500 : ℝ) (9600 : ℝ) 2 13708 2.9701e-28
    (0.0000000000025226 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9500_a2_le row9500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4750_lt, LogTables.exp_neg_19000_3_lt,
                   Real.exp_pos (-(4750:ℝ)), Real.exp_pos (-(19000/3:ℝ))])

/-- Row 9500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9500_k5_margin :
    B_8_exact 5 (9500 : ℝ) (9600 : ℝ) ≤ (0.000000024217 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9500 : ℝ) (9600 : ℝ) 2 13708 2.9701e-28
    (0.000000024217 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9500_a2_le row9500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4750_lt, LogTables.exp_neg_19000_3_lt,
                   Real.exp_pos (-(4750:ℝ)), Real.exp_pos (-(19000/3:ℝ))])

/-- Row 9600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9600_k1_margin :
    B_8_exact 1 (9600 : ℝ) (9700 : ℝ) ≤ (0.0000000000000000000000019059 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9600 : ℝ) (9700 : ℝ) 2 13852 1.9649e-28
    (0.0000000000000000000000019059 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9600_a2_le row9600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4800_lt, LogTables.exp_neg_6400_lt,
                   Real.exp_pos (-(4800:ℝ)), Real.exp_pos (-(6400:ℝ))])

/-- Row 9600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9600_k2_margin :
    B_8_exact 2 (9600 : ℝ) (9700 : ℝ) ≤ (0.000000000000000000018487 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9600 : ℝ) (9700 : ℝ) 2 13852 1.9649e-28
    (0.000000000000000000018487 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9600_a2_le row9600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4800_lt, LogTables.exp_neg_6400_lt,
                   Real.exp_pos (-(4800:ℝ)), Real.exp_pos (-(6400:ℝ))])

/-- Row 9600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9600_k3_margin :
    B_8_exact 3 (9600 : ℝ) (9700 : ℝ) ≤ (0.00000000000000017932 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9600 : ℝ) (9700 : ℝ) 2 13852 1.9649e-28
    (0.00000000000000017932 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9600_a2_le row9600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4800_lt, LogTables.exp_neg_6400_lt,
                   Real.exp_pos (-(4800:ℝ)), Real.exp_pos (-(6400:ℝ))])

/-- Row 9600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9600_k4_margin :
    B_8_exact 4 (9600 : ℝ) (9700 : ℝ) ≤ (0.0000000000017395 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9600 : ℝ) (9700 : ℝ) 2 13852 1.9649e-28
    (0.0000000000017395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9600_a2_le row9600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4800_lt, LogTables.exp_neg_6400_lt,
                   Real.exp_pos (-(4800:ℝ)), Real.exp_pos (-(6400:ℝ))])

/-- Row 9600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9600_k5_margin :
    B_8_exact 5 (9600 : ℝ) (9700 : ℝ) ≤ (0.000000016873 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9600 : ℝ) (9700 : ℝ) 2 13852 1.9649e-28
    (0.000000016873 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9600_a2_le row9600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4800_lt, LogTables.exp_neg_6400_lt,
                   Real.exp_pos (-(4800:ℝ)), Real.exp_pos (-(6400:ℝ))])

/-- Row 9700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9700_k1_margin :
    B_8_exact 1 (9700 : ℝ) (9800 : ℝ) ≤ (0.0000000000000000000000012689 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9700 : ℝ) (9800 : ℝ) 2 13997 1.2949e-28
    (0.0000000000000000000000012689 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9700_a2_le row9700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4850_lt, LogTables.exp_neg_19400_3_lt,
                   Real.exp_pos (-(4850:ℝ)), Real.exp_pos (-(19400/3:ℝ))])

/-- Row 9700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9700_k2_margin :
    B_8_exact 2 (9700 : ℝ) (9800 : ℝ) ≤ (0.000000000000000000012435 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9700 : ℝ) (9800 : ℝ) 2 13997 1.2949e-28
    (0.000000000000000000012435 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9700_a2_le row9700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4850_lt, LogTables.exp_neg_19400_3_lt,
                   Real.exp_pos (-(4850:ℝ)), Real.exp_pos (-(19400/3:ℝ))])

/-- Row 9700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9700_k3_margin :
    B_8_exact 3 (9700 : ℝ) (9800 : ℝ) ≤ (0.00000000000000012187 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9700 : ℝ) (9800 : ℝ) 2 13997 1.2949e-28
    (0.00000000000000012187 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9700_a2_le row9700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4850_lt, LogTables.exp_neg_19400_3_lt,
                   Real.exp_pos (-(4850:ℝ)), Real.exp_pos (-(19400/3:ℝ))])

/-- Row 9700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9700_k4_margin :
    B_8_exact 4 (9700 : ℝ) (9800 : ℝ) ≤ (0.0000000000011943 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9700 : ℝ) (9800 : ℝ) 2 13997 1.2949e-28
    (0.0000000000011943 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9700_a2_le row9700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4850_lt, LogTables.exp_neg_19400_3_lt,
                   Real.exp_pos (-(4850:ℝ)), Real.exp_pos (-(19400/3:ℝ))])

/-- Row 9700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9700_k5_margin :
    B_8_exact 5 (9700 : ℝ) (9800 : ℝ) ≤ (0.000000011704 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9700 : ℝ) (9800 : ℝ) 2 13997 1.2949e-28
    (0.000000011704 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9700_a2_le row9700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4850_lt, LogTables.exp_neg_19400_3_lt,
                   Real.exp_pos (-(4850:ℝ)), Real.exp_pos (-(19400/3:ℝ))])

/-- Row 9800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9800_k1_margin :
    B_8_exact 1 (9800 : ℝ) (9900 : ℝ) ≤ (0.00000000000000000000000084841 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9800 : ℝ) (9900 : ℝ) 2 14141 8.5698e-29
    (0.00000000000000000000000084841 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9800_a2_le row9800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4900_lt, LogTables.exp_neg_19600_3_lt,
                   Real.exp_pos (-(4900:ℝ)), Real.exp_pos (-(19600/3:ℝ))])

/-- Row 9800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9800_k2_margin :
    B_8_exact 2 (9800 : ℝ) (9900 : ℝ) ≤ (0.0000000000000000000083992 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9800 : ℝ) (9900 : ℝ) 2 14141 8.5698e-29
    (0.0000000000000000000083992 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9800_a2_le row9800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4900_lt, LogTables.exp_neg_19600_3_lt,
                   Real.exp_pos (-(4900:ℝ)), Real.exp_pos (-(19600/3:ℝ))])

/-- Row 9800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9800_k3_margin :
    B_8_exact 3 (9800 : ℝ) (9900 : ℝ) ≤ (0.000000000000000083152 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9800 : ℝ) (9900 : ℝ) 2 14141 8.5698e-29
    (0.000000000000000083152 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9800_a2_le row9800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4900_lt, LogTables.exp_neg_19600_3_lt,
                   Real.exp_pos (-(4900:ℝ)), Real.exp_pos (-(19600/3:ℝ))])

/-- Row 9800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9800_k4_margin :
    B_8_exact 4 (9800 : ℝ) (9900 : ℝ) ≤ (0.00000000000082321 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9800 : ℝ) (9900 : ℝ) 2 14141 8.5698e-29
    (0.00000000000082321 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9800_a2_le row9800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4900_lt, LogTables.exp_neg_19600_3_lt,
                   Real.exp_pos (-(4900:ℝ)), Real.exp_pos (-(19600/3:ℝ))])

/-- Row 9800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9800_k5_margin :
    B_8_exact 5 (9800 : ℝ) (9900 : ℝ) ≤ (0.0000000081497 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9800 : ℝ) (9900 : ℝ) 2 14141 8.5698e-29
    (0.0000000081497 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9800_a2_le row9800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4900_lt, LogTables.exp_neg_19600_3_lt,
                   Real.exp_pos (-(4900:ℝ)), Real.exp_pos (-(19600/3:ℝ))])

/-- Row 9900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row9900_k1_margin :
    B_8_exact 1 (9900 : ℝ) (10000 : ℝ) ≤ (0.00000000000000000000000057395 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (9900 : ℝ) (10000 : ℝ) 2 14285 5.7396e-29
    (0.00000000000000000000000057395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9900_a2_le row9900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4950_lt, LogTables.exp_neg_6600_lt,
                   Real.exp_pos (-(4950:ℝ)), Real.exp_pos (-(6600:ℝ))])

/-- Row 9900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row9900_k2_margin :
    B_8_exact 2 (9900 : ℝ) (10000 : ℝ) ≤ (0.0000000000000000000057395 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (9900 : ℝ) (10000 : ℝ) 2 14285 5.7396e-29
    (0.0000000000000000000057395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9900_a2_le row9900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4950_lt, LogTables.exp_neg_6600_lt,
                   Real.exp_pos (-(4950:ℝ)), Real.exp_pos (-(6600:ℝ))])

/-- Row 9900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row9900_k3_margin :
    B_8_exact 3 (9900 : ℝ) (10000 : ℝ) ≤ (0.000000000000000057395 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (9900 : ℝ) (10000 : ℝ) 2 14285 5.7396e-29
    (0.000000000000000057395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9900_a2_le row9900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4950_lt, LogTables.exp_neg_6600_lt,
                   Real.exp_pos (-(4950:ℝ)), Real.exp_pos (-(6600:ℝ))])

/-- Row 9900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row9900_k4_margin :
    B_8_exact 4 (9900 : ℝ) (10000 : ℝ) ≤ (0.00000000000057395 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (9900 : ℝ) (10000 : ℝ) 2 14285 5.7396e-29
    (0.00000000000057395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9900_a2_le row9900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4950_lt, LogTables.exp_neg_6600_lt,
                   Real.exp_pos (-(4950:ℝ)), Real.exp_pos (-(6600:ℝ))])

/-- Row 9900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row9900_k5_margin :
    B_8_exact 5 (9900 : ℝ) (10000 : ℝ) ≤ (0.0000000057395 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (9900 : ℝ) (10000 : ℝ) 2 14285 5.7396e-29
    (0.0000000057395 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row9900_a2_le row9900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_4950_lt, LogTables.exp_neg_6600_lt,
                   Real.exp_pos (-(4950:ℝ)), Real.exp_pos (-(6600:ℝ))])

/-- Row 10000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10000_k1_margin :
    B_8_exact 1 (10000 : ℝ) (10100 : ℝ) ≤ (0.00000000000000000000000038228 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10000 : ℝ) (10100 : ℝ) 2 14429 3.7850e-29
    (0.00000000000000000000000038228 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10000_a2_le row10000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5000_lt, LogTables.exp_neg_20000_3_lt,
                   Real.exp_pos (-(5000:ℝ)), Real.exp_pos (-(20000/3:ℝ))])

/-- Row 10000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10000_k2_margin :
    B_8_exact 2 (10000 : ℝ) (10100 : ℝ) ≤ (0.0000000000000000000038610 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10000 : ℝ) (10100 : ℝ) 2 14429 3.7850e-29
    (0.0000000000000000000038610 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10000_a2_le row10000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5000_lt, LogTables.exp_neg_20000_3_lt,
                   Real.exp_pos (-(5000:ℝ)), Real.exp_pos (-(20000/3:ℝ))])

/-- Row 10000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10000_k3_margin :
    B_8_exact 3 (10000 : ℝ) (10100 : ℝ) ≤ (0.000000000000000038996 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10000 : ℝ) (10100 : ℝ) 2 14429 3.7850e-29
    (0.000000000000000038996 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10000_a2_le row10000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5000_lt, LogTables.exp_neg_20000_3_lt,
                   Real.exp_pos (-(5000:ℝ)), Real.exp_pos (-(20000/3:ℝ))])

/-- Row 10000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10000_k4_margin :
    B_8_exact 4 (10000 : ℝ) (10100 : ℝ) ≤ (0.00000000000039386 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10000 : ℝ) (10100 : ℝ) 2 14429 3.7850e-29
    (0.00000000000039386 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10000_a2_le row10000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5000_lt, LogTables.exp_neg_20000_3_lt,
                   Real.exp_pos (-(5000:ℝ)), Real.exp_pos (-(20000/3:ℝ))])

/-- Row 10000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10000_k5_margin :
    B_8_exact 5 (10000 : ℝ) (10100 : ℝ) ≤ (0.0000000039780 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10000 : ℝ) (10100 : ℝ) 2 14429 3.7850e-29
    (0.0000000039780 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10000_a2_le row10000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5000_lt, LogTables.exp_neg_20000_3_lt,
                   Real.exp_pos (-(5000:ℝ)), Real.exp_pos (-(20000/3:ℝ))])

/-- Row 10100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10100_k1_margin :
    B_8_exact 1 (10100 : ℝ) (10200 : ℝ) ≤ (0.00000000000000000000000025745 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10100 : ℝ) (10200 : ℝ) 2 14574 2.5241e-29
    (0.00000000000000000000000025745 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10100_a2_le row10100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5050_lt, LogTables.exp_neg_20200_3_lt,
                   Real.exp_pos (-(5050:ℝ)), Real.exp_pos (-(20200/3:ℝ))])

/-- Row 10100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10100_k2_margin :
    B_8_exact 2 (10100 : ℝ) (10200 : ℝ) ≤ (0.0000000000000000000026260 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10100 : ℝ) (10200 : ℝ) 2 14574 2.5241e-29
    (0.0000000000000000000026260 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10100_a2_le row10100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5050_lt, LogTables.exp_neg_20200_3_lt,
                   Real.exp_pos (-(5050:ℝ)), Real.exp_pos (-(20200/3:ℝ))])

/-- Row 10100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10100_k3_margin :
    B_8_exact 3 (10100 : ℝ) (10200 : ℝ) ≤ (0.000000000000000026785 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10100 : ℝ) (10200 : ℝ) 2 14574 2.5241e-29
    (0.000000000000000026785 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10100_a2_le row10100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5050_lt, LogTables.exp_neg_20200_3_lt,
                   Real.exp_pos (-(5050:ℝ)), Real.exp_pos (-(20200/3:ℝ))])

/-- Row 10100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10100_k4_margin :
    B_8_exact 4 (10100 : ℝ) (10200 : ℝ) ≤ (0.00000000000027321 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10100 : ℝ) (10200 : ℝ) 2 14574 2.5241e-29
    (0.00000000000027321 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10100_a2_le row10100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5050_lt, LogTables.exp_neg_20200_3_lt,
                   Real.exp_pos (-(5050:ℝ)), Real.exp_pos (-(20200/3:ℝ))])

/-- Row 10100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10100_k5_margin :
    B_8_exact 5 (10100 : ℝ) (10200 : ℝ) ≤ (0.0000000027867 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10100 : ℝ) (10200 : ℝ) 2 14574 2.5241e-29
    (0.0000000027867 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10100_a2_le row10100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5050_lt, LogTables.exp_neg_20200_3_lt,
                   Real.exp_pos (-(5050:ℝ)), Real.exp_pos (-(20200/3:ℝ))])

/-- Row 10200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10200_k1_margin :
    B_8_exact 1 (10200 : ℝ) (10300 : ℝ) ≤ (0.00000000000000000000000017389 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10200 : ℝ) (10300 : ℝ) 2 14718 1.6883e-29
    (0.00000000000000000000000017389 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10200_a2_le row10200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5100_lt, LogTables.exp_neg_6800_lt,
                   Real.exp_pos (-(5100:ℝ)), Real.exp_pos (-(6800:ℝ))])

/-- Row 10200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10200_k2_margin :
    B_8_exact 2 (10200 : ℝ) (10300 : ℝ) ≤ (0.0000000000000000000017911 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10200 : ℝ) (10300 : ℝ) 2 14718 1.6883e-29
    (0.0000000000000000000017911 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10200_a2_le row10200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5100_lt, LogTables.exp_neg_6800_lt,
                   Real.exp_pos (-(5100:ℝ)), Real.exp_pos (-(6800:ℝ))])

/-- Row 10200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10200_k3_margin :
    B_8_exact 3 (10200 : ℝ) (10300 : ℝ) ≤ (0.000000000000000018448 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10200 : ℝ) (10300 : ℝ) 2 14718 1.6883e-29
    (0.000000000000000018448 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10200_a2_le row10200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5100_lt, LogTables.exp_neg_6800_lt,
                   Real.exp_pos (-(5100:ℝ)), Real.exp_pos (-(6800:ℝ))])

/-- Row 10200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10200_k4_margin :
    B_8_exact 4 (10200 : ℝ) (10300 : ℝ) ≤ (0.00000000000019001 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10200 : ℝ) (10300 : ℝ) 2 14718 1.6883e-29
    (0.00000000000019001 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10200_a2_le row10200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5100_lt, LogTables.exp_neg_6800_lt,
                   Real.exp_pos (-(5100:ℝ)), Real.exp_pos (-(6800:ℝ))])

/-- Row 10200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10200_k5_margin :
    B_8_exact 5 (10200 : ℝ) (10300 : ℝ) ≤ (0.0000000019571 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10200 : ℝ) (10300 : ℝ) 2 14718 1.6883e-29
    (0.0000000019571 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10200_a2_le row10200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5100_lt, LogTables.exp_neg_6800_lt,
                   Real.exp_pos (-(5100:ℝ)), Real.exp_pos (-(6800:ℝ))])

/-- Row 10300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10300_k1_margin :
    B_8_exact 1 (10300 : ℝ) (10400 : ℝ) ≤ (0.00000000000000000000000011734 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10300 : ℝ) (10400 : ℝ) 2 14862 1.1283e-29
    (0.00000000000000000000000011734 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10300_a2_le row10300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5150_lt, LogTables.exp_neg_20600_3_lt,
                   Real.exp_pos (-(5150:ℝ)), Real.exp_pos (-(20600/3:ℝ))])

/-- Row 10300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10300_k2_margin :
    B_8_exact 2 (10300 : ℝ) (10400 : ℝ) ≤ (0.0000000000000000000012203 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10300 : ℝ) (10400 : ℝ) 2 14862 1.1283e-29
    (0.0000000000000000000012203 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10300_a2_le row10300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5150_lt, LogTables.exp_neg_20600_3_lt,
                   Real.exp_pos (-(5150:ℝ)), Real.exp_pos (-(20600/3:ℝ))])

/-- Row 10300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10300_k3_margin :
    B_8_exact 3 (10300 : ℝ) (10400 : ℝ) ≤ (0.000000000000000012691 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10300 : ℝ) (10400 : ℝ) 2 14862 1.1283e-29
    (0.000000000000000012691 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10300_a2_le row10300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5150_lt, LogTables.exp_neg_20600_3_lt,
                   Real.exp_pos (-(5150:ℝ)), Real.exp_pos (-(20600/3:ℝ))])

/-- Row 10300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10300_k4_margin :
    B_8_exact 4 (10300 : ℝ) (10400 : ℝ) ≤ (0.00000000000013199 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10300 : ℝ) (10400 : ℝ) 2 14862 1.1283e-29
    (0.00000000000013199 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10300_a2_le row10300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5150_lt, LogTables.exp_neg_20600_3_lt,
                   Real.exp_pos (-(5150:ℝ)), Real.exp_pos (-(20600/3:ℝ))])

/-- Row 10300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10300_k5_margin :
    B_8_exact 5 (10300 : ℝ) (10400 : ℝ) ≤ (0.0000000013727 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10300 : ℝ) (10400 : ℝ) 2 14862 1.1283e-29
    (0.0000000013727 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10300_a2_le row10300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5150_lt, LogTables.exp_neg_20600_3_lt,
                   Real.exp_pos (-(5150:ℝ)), Real.exp_pos (-(20600/3:ℝ))])

/-- Row 10400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10400_k1_margin :
    B_8_exact 1 (10400 : ℝ) (10500 : ℝ) ≤ (0.000000000000000000000000079556 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10400 : ℝ) (10500 : ℝ) 2 15007 7.5768e-30
    (0.000000000000000000000000079556 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10400_a2_le row10400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5200_lt, LogTables.exp_neg_20800_3_lt,
                   Real.exp_pos (-(5200:ℝ)), Real.exp_pos (-(20800/3:ℝ))])

/-- Row 10400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10400_k2_margin :
    B_8_exact 2 (10400 : ℝ) (10500 : ℝ) ≤ (0.00000000000000000000083534 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10400 : ℝ) (10500 : ℝ) 2 15007 7.5768e-30
    (0.00000000000000000000083534 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10400_a2_le row10400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5200_lt, LogTables.exp_neg_20800_3_lt,
                   Real.exp_pos (-(5200:ℝ)), Real.exp_pos (-(20800/3:ℝ))])

/-- Row 10400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10400_k3_margin :
    B_8_exact 3 (10400 : ℝ) (10500 : ℝ) ≤ (0.0000000000000000087710 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10400 : ℝ) (10500 : ℝ) 2 15007 7.5768e-30
    (0.0000000000000000087710 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10400_a2_le row10400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5200_lt, LogTables.exp_neg_20800_3_lt,
                   Real.exp_pos (-(5200:ℝ)), Real.exp_pos (-(20800/3:ℝ))])

/-- Row 10400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10400_k4_margin :
    B_8_exact 4 (10400 : ℝ) (10500 : ℝ) ≤ (0.000000000000092096 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10400 : ℝ) (10500 : ℝ) 2 15007 7.5768e-30
    (0.000000000000092096 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10400_a2_le row10400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5200_lt, LogTables.exp_neg_20800_3_lt,
                   Real.exp_pos (-(5200:ℝ)), Real.exp_pos (-(20800/3:ℝ))])

/-- Row 10400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10400_k5_margin :
    B_8_exact 5 (10400 : ℝ) (10500 : ℝ) ≤ (0.00000000096701 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10400 : ℝ) (10500 : ℝ) 2 15007 7.5768e-30
    (0.00000000096701 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10400_a2_le row10400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5200_lt, LogTables.exp_neg_20800_3_lt,
                   Real.exp_pos (-(5200:ℝ)), Real.exp_pos (-(20800/3:ℝ))])

/-- Row 10500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10500_k1_margin :
    B_8_exact 1 (10500 : ℝ) (10600 : ℝ) ≤ (0.000000000000000000000000054076 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10500 : ℝ) (10600 : ℝ) 2 15151 5.1016e-30
    (0.000000000000000000000000054076 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10500_a2_le row10500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5250_lt, LogTables.exp_neg_7000_lt,
                   Real.exp_pos (-(5250:ℝ)), Real.exp_pos (-(7000:ℝ))])

/-- Row 10500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10500_k2_margin :
    B_8_exact 2 (10500 : ℝ) (10600 : ℝ) ≤ (0.00000000000000000000057321 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10500 : ℝ) (10600 : ℝ) 2 15151 5.1016e-30
    (0.00000000000000000000057321 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10500_a2_le row10500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5250_lt, LogTables.exp_neg_7000_lt,
                   Real.exp_pos (-(5250:ℝ)), Real.exp_pos (-(7000:ℝ))])

/-- Row 10500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10500_k3_margin :
    B_8_exact 3 (10500 : ℝ) (10600 : ℝ) ≤ (0.0000000000000000060760 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10500 : ℝ) (10600 : ℝ) 2 15151 5.1016e-30
    (0.0000000000000000060760 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10500_a2_le row10500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5250_lt, LogTables.exp_neg_7000_lt,
                   Real.exp_pos (-(5250:ℝ)), Real.exp_pos (-(7000:ℝ))])

/-- Row 10500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10500_k4_margin :
    B_8_exact 4 (10500 : ℝ) (10600 : ℝ) ≤ (0.000000000000064406 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10500 : ℝ) (10600 : ℝ) 2 15151 5.1016e-30
    (0.000000000000064406 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10500_a2_le row10500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5250_lt, LogTables.exp_neg_7000_lt,
                   Real.exp_pos (-(5250:ℝ)), Real.exp_pos (-(7000:ℝ))])

/-- Row 10500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10500_k5_margin :
    B_8_exact 5 (10500 : ℝ) (10600 : ℝ) ≤ (0.00000000068270 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10500 : ℝ) (10600 : ℝ) 2 15151 5.1016e-30
    (0.00000000068270 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10500_a2_le row10500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_5250_lt, LogTables.exp_neg_7000_lt,
                   Real.exp_pos (-(5250:ℝ)), Real.exp_pos (-(7000:ℝ))])

end BKLNW
