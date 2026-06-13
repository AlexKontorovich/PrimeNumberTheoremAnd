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

private lemma row100_a2_le : Inputs.default.a₂ (100 : ℝ) ≤ (147 : ℝ) := by
  have h := a2_crude_le (100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(100 : ℝ) / log 2⌋₊ : ℝ) ≤ (100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (100 : ℝ) / log 2 ≤ 145 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (145 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 147 := by norm_num

private lemma row200_a2_le : Inputs.default.a₂ (200 : ℝ) ≤ (291 : ℝ) := by
  have h := a2_crude_le (200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(200 : ℝ) / log 2⌋₊ : ℝ) ≤ (200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (200 : ℝ) / log 2 ≤ 289 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (289 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 291 := by norm_num

private lemma row300_a2_le : Inputs.default.a₂ (300 : ℝ) ≤ (435 : ℝ) := by
  have h := a2_crude_le (300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(300 : ℝ) / log 2⌋₊ : ℝ) ≤ (300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (300 : ℝ) / log 2 ≤ 433 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (433 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 435 := by norm_num

private lemma row400_a2_le : Inputs.default.a₂ (400 : ℝ) ≤ (580 : ℝ) := by
  have h := a2_crude_le (400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(400 : ℝ) / log 2⌋₊ : ℝ) ≤ (400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (400 : ℝ) / log 2 ≤ 578 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (578 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 580 := by norm_num

private lemma row500_a2_le : Inputs.default.a₂ (500 : ℝ) ≤ (724 : ℝ) := by
  have h := a2_crude_le (500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(500 : ℝ) / log 2⌋₊ : ℝ) ≤ (500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (500 : ℝ) / log 2 ≤ 722 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (722 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 724 := by norm_num

private lemma row600_a2_le : Inputs.default.a₂ (600 : ℝ) ≤ (868 : ℝ) := by
  have h := a2_crude_le (600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(600 : ℝ) / log 2⌋₊ : ℝ) ≤ (600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (600 : ℝ) / log 2 ≤ 866 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (866 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 868 := by norm_num

private lemma row700_a2_le : Inputs.default.a₂ (700 : ℝ) ≤ (1012 : ℝ) := by
  have h := a2_crude_le (700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(700 : ℝ) / log 2⌋₊ : ℝ) ≤ (700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (700 : ℝ) / log 2 ≤ 1010 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (1010 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 1012 := by norm_num

private lemma row800_a2_le : Inputs.default.a₂ (800 : ℝ) ≤ (1157 : ℝ) := by
  have h := a2_crude_le (800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(800 : ℝ) / log 2⌋₊ : ℝ) ≤ (800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (800 : ℝ) / log 2 ≤ 1155 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (1155 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 1157 := by norm_num

private lemma row900_a2_le : Inputs.default.a₂ (900 : ℝ) ≤ (1301 : ℝ) := by
  have h := a2_crude_le (900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(900 : ℝ) / log 2⌋₊ : ℝ) ≤ (900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (900 : ℝ) / log 2 ≤ 1299 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (1299 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 1301 := by norm_num

private lemma row1000_a2_le : Inputs.default.a₂ (1000 : ℝ) ≤ (1445 : ℝ) := by
  have h := a2_crude_le (1000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1000 : ℝ) / log 2⌋₊ : ℝ) ≤ (1000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1000 : ℝ) / log 2 ≤ 1443 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (1443 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 1445 := by norm_num

private lemma row1500_a2_le : Inputs.default.a₂ (1500 : ℝ) ≤ (2167 : ℝ) := by
  have h := a2_crude_le (1500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1500 : ℝ) / log 2⌋₊ : ℝ) ≤ (1500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1500 : ℝ) / log 2 ≤ 2165 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2165 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2167 := by norm_num

private lemma row1600_a2_le : Inputs.default.a₂ (1600 : ℝ) ≤ (2311 : ℝ) := by
  have h := a2_crude_le (1600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1600 : ℝ) / log 2⌋₊ : ℝ) ≤ (1600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1600 : ℝ) / log 2 ≤ 2309 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2309 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2311 := by norm_num

private lemma row1700_a2_le : Inputs.default.a₂ (1700 : ℝ) ≤ (2455 : ℝ) := by
  have h := a2_crude_le (1700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1700 : ℝ) / log 2⌋₊ : ℝ) ≤ (1700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1700 : ℝ) / log 2 ≤ 2453 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2453 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2455 := by norm_num

private lemma row1725_a2_le : Inputs.default.a₂ (1725 : ℝ) ≤ (2491 : ℝ) := by
  have h := a2_crude_le (1725 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1725 : ℝ) / log 2⌋₊ : ℝ) ≤ (1725 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1725 : ℝ) / log 2 ≤ 2489 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1725 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1725 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2489 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2491 := by norm_num

private lemma row1750_a2_le : Inputs.default.a₂ (1750 : ℝ) ≤ (2527 : ℝ) := by
  have h := a2_crude_le (1750 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1750 : ℝ) / log 2⌋₊ : ℝ) ≤ (1750 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1750 : ℝ) / log 2 ≤ 2525 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1750 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1750 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2525 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2527 := by norm_num

private lemma row1775_a2_le : Inputs.default.a₂ (1775 : ℝ) ≤ (2563 : ℝ) := by
  have h := a2_crude_le (1775 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1775 : ℝ) / log 2⌋₊ : ℝ) ≤ (1775 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1775 : ℝ) / log 2 ≤ 2561 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1775 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1775 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2561 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2563 := by norm_num

private lemma row1800_a2_le : Inputs.default.a₂ (1800 : ℝ) ≤ (2599 : ℝ) := by
  have h := a2_crude_le (1800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1800 : ℝ) / log 2⌋₊ : ℝ) ≤ (1800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1800 : ℝ) / log 2 ≤ 2597 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2597 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2599 := by norm_num

private lemma row1825_a2_le : Inputs.default.a₂ (1825 : ℝ) ≤ (2635 : ℝ) := by
  have h := a2_crude_le (1825 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1825 : ℝ) / log 2⌋₊ : ℝ) ≤ (1825 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1825 : ℝ) / log 2 ≤ 2633 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1825 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1825 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2633 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2635 := by norm_num

private lemma row1850_a2_le : Inputs.default.a₂ (1850 : ℝ) ≤ (2671 : ℝ) := by
  have h := a2_crude_le (1850 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1850 : ℝ) / log 2⌋₊ : ℝ) ≤ (1850 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1850 : ℝ) / log 2 ≤ 2669 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1850 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1850 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2669 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2671 := by norm_num

private lemma row1875_a2_le : Inputs.default.a₂ (1875 : ℝ) ≤ (2708 : ℝ) := by
  have h := a2_crude_le (1875 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1875 : ℝ) / log 2⌋₊ : ℝ) ≤ (1875 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1875 : ℝ) / log 2 ≤ 2706 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1875 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1875 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2706 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2708 := by norm_num

set_option maxRecDepth 10000 in
private lemma row100_table8_mem : (100, 2.4531e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row100_eps_le : Inputs.default.ε (100 : ℝ) ≤ 2.4531e-12 := by
  change BKLNW_app.table_8_ε (100 : ℝ) ≤ 2.4531e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 100)
    (ε := 2.4531e-12) row100_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row200_table8_mem : (200, 2.1816e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row200_eps_le : Inputs.default.ε (200 : ℝ) ≤ 2.1816e-12 := by
  change BKLNW_app.table_8_ε (200 : ℝ) ≤ 2.1816e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 200)
    (ε := 2.1816e-12) row200_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row300_table8_mem : (300, 2.0903e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row300_eps_le : Inputs.default.ε (300 : ℝ) ≤ 2.0903e-12 := by
  change BKLNW_app.table_8_ε (300 : ℝ) ≤ 2.0903e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 300)
    (ε := 2.0903e-12) row300_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row400_table8_mem : (400, 2.0399e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row400_eps_le : Inputs.default.ε (400 : ℝ) ≤ 2.0399e-12 := by
  change BKLNW_app.table_8_ε (400 : ℝ) ≤ 2.0399e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 400)
    (ε := 2.0399e-12) row400_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row500_table8_mem : (500, 1.9999e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row500_eps_le : Inputs.default.ε (500 : ℝ) ≤ 1.9999e-12 := by
  change BKLNW_app.table_8_ε (500 : ℝ) ≤ 1.9999e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 500)
    (ε := 1.9999e-12) row500_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row600_table8_mem : (600, 1.9890e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row600_eps_le : Inputs.default.ε (600 : ℝ) ≤ 1.9890e-12 := by
  change BKLNW_app.table_8_ε (600 : ℝ) ≤ 1.9890e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 600)
    (ε := 1.9890e-12) row600_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row700_table8_mem : (700, 1.9765e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row700_eps_le : Inputs.default.ε (700 : ℝ) ≤ 1.9765e-12 := by
  change BKLNW_app.table_8_ε (700 : ℝ) ≤ 1.9765e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 700)
    (ε := 1.9765e-12) row700_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row800_table8_mem : (800, 1.9672e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row800_eps_le : Inputs.default.ε (800 : ℝ) ≤ 1.9672e-12 := by
  change BKLNW_app.table_8_ε (800 : ℝ) ≤ 1.9672e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 800)
    (ε := 1.9672e-12) row800_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row900_table8_mem : (900, 1.9600e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row900_eps_le : Inputs.default.ε (900 : ℝ) ≤ 1.9600e-12 := by
  change BKLNW_app.table_8_ε (900 : ℝ) ≤ 1.9600e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 900)
    (ε := 1.9600e-12) row900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1000_table8_mem : (1000, 1.9476e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1000_eps_le : Inputs.default.ε (1000 : ℝ) ≤ 1.9476e-12 := by
  change BKLNW_app.table_8_ε (1000 : ℝ) ≤ 1.9476e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1000)
    (ε := 1.9476e-12) row1000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1500_table8_mem : (1500, 1.9369e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1500_eps_le : Inputs.default.ε (1500 : ℝ) ≤ 1.9369e-12 := by
  change BKLNW_app.table_8_ε (1500 : ℝ) ≤ 1.9369e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1500)
    (ε := 1.9369e-12) row1500_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1600_table8_mem : (1600, 1.9293e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1600_eps_le : Inputs.default.ε (1600 : ℝ) ≤ 1.9293e-12 := by
  change BKLNW_app.table_8_ε (1600 : ℝ) ≤ 1.9293e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1600)
    (ε := 1.9293e-12) row1600_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1700_table8_mem : (1700, 1.9274e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1700_eps_le : Inputs.default.ε (1700 : ℝ) ≤ 1.9274e-12 := by
  change BKLNW_app.table_8_ε (1700 : ℝ) ≤ 1.9274e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1700)
    (ε := 1.9274e-12) row1700_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1725_table8_mem : (1725, 1.9270e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1725_eps_le : Inputs.default.ε (1725 : ℝ) ≤ 1.9270e-12 := by
  change BKLNW_app.table_8_ε (1725 : ℝ) ≤ 1.9270e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1725)
    (ε := 1.9270e-12) row1725_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1750_table8_mem : (1750, 1.9266e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1750_eps_le : Inputs.default.ε (1750 : ℝ) ≤ 1.9266e-12 := by
  change BKLNW_app.table_8_ε (1750 : ℝ) ≤ 1.9266e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1750)
    (ε := 1.9266e-12) row1750_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1775_table8_mem : (1775, 1.9261e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1775_eps_le : Inputs.default.ε (1775 : ℝ) ≤ 1.9261e-12 := by
  change BKLNW_app.table_8_ε (1775 : ℝ) ≤ 1.9261e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1775)
    (ε := 1.9261e-12) row1775_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1800_table8_mem : (1800, 1.9257e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1800_eps_le : Inputs.default.ε (1800 : ℝ) ≤ 1.9257e-12 := by
  change BKLNW_app.table_8_ε (1800 : ℝ) ≤ 1.9257e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1800)
    (ε := 1.9257e-12) row1800_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1825_table8_mem : (1825, 1.9254e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1825_eps_le : Inputs.default.ε (1825 : ℝ) ≤ 1.9254e-12 := by
  change BKLNW_app.table_8_ε (1825 : ℝ) ≤ 1.9254e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1825)
    (ε := 1.9254e-12) row1825_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1850_table8_mem : (1850, 1.9250e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1850_eps_le : Inputs.default.ε (1850 : ℝ) ≤ 1.9250e-12 := by
  change BKLNW_app.table_8_ε (1850 : ℝ) ≤ 1.9250e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1850)
    (ε := 1.9250e-12) row1850_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1875_table8_mem : (1875, 1.9246e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1875_eps_le : Inputs.default.ε (1875 : ℝ) ≤ 1.9246e-12 := by
  change BKLNW_app.table_8_ε (1875 : ℝ) ≤ 1.9246e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1875)
    (ε := 1.9246e-12) row1875_table8_mem (by norm_num)

/-- Row 100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row100_k1_margin :
    B_8_exact 1 (100 : ℝ) (200 : ℝ) ≤ (0.00000000049060 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (100 : ℝ) (200 : ℝ) 2 147 2.4531e-12
    (0.00000000049060 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row100_a2_le row100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_50_lt, LogTables.exp_neg_200_3_lt,
                   Real.exp_pos (-(50:ℝ)), Real.exp_pos (-(200/3:ℝ))])

/-- Row 100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row100_k2_margin :
    B_8_exact 2 (100 : ℝ) (200 : ℝ) ≤ (0.000000098120 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (100 : ℝ) (200 : ℝ) 2 147 2.4531e-12
    (0.000000098120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row100_a2_le row100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_50_lt, LogTables.exp_neg_200_3_lt,
                   Real.exp_pos (-(50:ℝ)), Real.exp_pos (-(200/3:ℝ))])

/-- Row 100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row100_k3_margin :
    B_8_exact 3 (100 : ℝ) (200 : ℝ) ≤ (0.000019624 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (100 : ℝ) (200 : ℝ) 2 147 2.4531e-12
    (0.000019624 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row100_a2_le row100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_50_lt, LogTables.exp_neg_200_3_lt,
                   Real.exp_pos (-(50:ℝ)), Real.exp_pos (-(200/3:ℝ))])

/-- Row 100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row100_k4_margin :
    B_8_exact 4 (100 : ℝ) (200 : ℝ) ≤ (0.0039248 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (100 : ℝ) (200 : ℝ) 2 147 2.4531e-12
    (0.0039248 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row100_a2_le row100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_50_lt, LogTables.exp_neg_200_3_lt,
                   Real.exp_pos (-(50:ℝ)), Real.exp_pos (-(200/3:ℝ))])

/-- Row 100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row100_k5_margin :
    B_8_exact 5 (100 : ℝ) (200 : ℝ) ≤ (0.78496 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (100 : ℝ) (200 : ℝ) 2 147 2.4531e-12
    (0.78496 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row100_a2_le row100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_50_lt, LogTables.exp_neg_200_3_lt,
                   Real.exp_pos (-(50:ℝ)), Real.exp_pos (-(200/3:ℝ))])

/-- Row 200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row200_k1_margin :
    B_8_exact 1 (200 : ℝ) (300 : ℝ) ≤ (0.00000000065446 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (200 : ℝ) (300 : ℝ) 2 291 2.1816e-12
    (0.00000000065446 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row200_a2_le row200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_100_lt, LogTables.exp_neg_400_3_lt,
                   Real.exp_pos (-(100:ℝ)), Real.exp_pos (-(400/3:ℝ))])

/-- Row 200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row200_k2_margin :
    B_8_exact 2 (200 : ℝ) (300 : ℝ) ≤ (0.00000019634 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (200 : ℝ) (300 : ℝ) 2 291 2.1816e-12
    (0.00000019634 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row200_a2_le row200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_100_lt, LogTables.exp_neg_400_3_lt,
                   Real.exp_pos (-(100:ℝ)), Real.exp_pos (-(400/3:ℝ))])

/-- Row 200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row200_k3_margin :
    B_8_exact 3 (200 : ℝ) (300 : ℝ) ≤ (0.000058902 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (200 : ℝ) (300 : ℝ) 2 291 2.1816e-12
    (0.000058902 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row200_a2_le row200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_100_lt, LogTables.exp_neg_400_3_lt,
                   Real.exp_pos (-(100:ℝ)), Real.exp_pos (-(400/3:ℝ))])

/-- Row 200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row200_k4_margin :
    B_8_exact 4 (200 : ℝ) (300 : ℝ) ≤ (0.017671 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (200 : ℝ) (300 : ℝ) 2 291 2.1816e-12
    (0.017671 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row200_a2_le row200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_100_lt, LogTables.exp_neg_400_3_lt,
                   Real.exp_pos (-(100:ℝ)), Real.exp_pos (-(400/3:ℝ))])

/-- Row 200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row200_k5_margin :
    B_8_exact 5 (200 : ℝ) (300 : ℝ) ≤ (5.3012 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (200 : ℝ) (300 : ℝ) 2 291 2.1816e-12
    (5.3012 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row200_a2_le row200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_100_lt, LogTables.exp_neg_400_3_lt,
                   Real.exp_pos (-(100:ℝ)), Real.exp_pos (-(400/3:ℝ))])

/-- Row 300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row300_k1_margin :
    B_8_exact 1 (300 : ℝ) (400 : ℝ) ≤ (0.00000000083609 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (300 : ℝ) (400 : ℝ) 2 435 2.0903e-12
    (0.00000000083609 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row300_a2_le row300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_150_lt, LogTables.exp_neg_200_lt,
                   Real.exp_pos (-(150:ℝ)), Real.exp_pos (-(200:ℝ))])

/-- Row 300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row300_k2_margin :
    B_8_exact 2 (300 : ℝ) (400 : ℝ) ≤ (0.00000033444 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (300 : ℝ) (400 : ℝ) 2 435 2.0903e-12
    (0.00000033444 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row300_a2_le row300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_150_lt, LogTables.exp_neg_200_lt,
                   Real.exp_pos (-(150:ℝ)), Real.exp_pos (-(200:ℝ))])

/-- Row 300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row300_k3_margin :
    B_8_exact 3 (300 : ℝ) (400 : ℝ) ≤ (0.00013378 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (300 : ℝ) (400 : ℝ) 2 435 2.0903e-12
    (0.00013378 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row300_a2_le row300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_150_lt, LogTables.exp_neg_200_lt,
                   Real.exp_pos (-(150:ℝ)), Real.exp_pos (-(200:ℝ))])

/-- Row 300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row300_k4_margin :
    B_8_exact 4 (300 : ℝ) (400 : ℝ) ≤ (0.053510 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (300 : ℝ) (400 : ℝ) 2 435 2.0903e-12
    (0.053510 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row300_a2_le row300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_150_lt, LogTables.exp_neg_200_lt,
                   Real.exp_pos (-(150:ℝ)), Real.exp_pos (-(200:ℝ))])

/-- Row 300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row300_k5_margin :
    B_8_exact 5 (300 : ℝ) (400 : ℝ) ≤ (21.404 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (300 : ℝ) (400 : ℝ) 2 435 2.0903e-12
    (21.404 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row300_a2_le row300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_150_lt, LogTables.exp_neg_200_lt,
                   Real.exp_pos (-(150:ℝ)), Real.exp_pos (-(200:ℝ))])

/-- Row 400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row400_k1_margin :
    B_8_exact 1 (400 : ℝ) (500 : ℝ) ≤ (0.0000000010199 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (400 : ℝ) (500 : ℝ) 2 580 2.0399e-12
    (0.0000000010199 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row400_a2_le row400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_200_lt, LogTables.exp_neg_800_3_lt,
                   Real.exp_pos (-(200:ℝ)), Real.exp_pos (-(800/3:ℝ))])

/-- Row 400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row400_k2_margin :
    B_8_exact 2 (400 : ℝ) (500 : ℝ) ≤ (0.00000050995 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (400 : ℝ) (500 : ℝ) 2 580 2.0399e-12
    (0.00000050995 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row400_a2_le row400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_200_lt, LogTables.exp_neg_800_3_lt,
                   Real.exp_pos (-(200:ℝ)), Real.exp_pos (-(800/3:ℝ))])

/-- Row 400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row400_k3_margin :
    B_8_exact 3 (400 : ℝ) (500 : ℝ) ≤ (0.00025498 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (400 : ℝ) (500 : ℝ) 2 580 2.0399e-12
    (0.00025498 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row400_a2_le row400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_200_lt, LogTables.exp_neg_800_3_lt,
                   Real.exp_pos (-(200:ℝ)), Real.exp_pos (-(800/3:ℝ))])

/-- Row 400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row400_k4_margin :
    B_8_exact 4 (400 : ℝ) (500 : ℝ) ≤ (0.12749 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (400 : ℝ) (500 : ℝ) 2 580 2.0399e-12
    (0.12749 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row400_a2_le row400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_200_lt, LogTables.exp_neg_800_3_lt,
                   Real.exp_pos (-(200:ℝ)), Real.exp_pos (-(800/3:ℝ))])

/-- Row 400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row400_k5_margin :
    B_8_exact 5 (400 : ℝ) (500 : ℝ) ≤ (63.744 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (400 : ℝ) (500 : ℝ) 2 580 2.0399e-12
    (63.744 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row400_a2_le row400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_200_lt, LogTables.exp_neg_800_3_lt,
                   Real.exp_pos (-(200:ℝ)), Real.exp_pos (-(800/3:ℝ))])

/-- Row 500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row500_k1_margin :
    B_8_exact 1 (500 : ℝ) (600 : ℝ) ≤ (0.0000000011999 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (500 : ℝ) (600 : ℝ) 2 724 1.9999e-12
    (0.0000000011999 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row500_a2_le row500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_250_lt, LogTables.exp_neg_1000_3_lt,
                   Real.exp_pos (-(250:ℝ)), Real.exp_pos (-(1000/3:ℝ))])

/-- Row 500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row500_k2_margin :
    B_8_exact 2 (500 : ℝ) (600 : ℝ) ≤ (0.00000071995 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (500 : ℝ) (600 : ℝ) 2 724 1.9999e-12
    (0.00000071995 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row500_a2_le row500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_250_lt, LogTables.exp_neg_1000_3_lt,
                   Real.exp_pos (-(250:ℝ)), Real.exp_pos (-(1000/3:ℝ))])

/-- Row 500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row500_k3_margin :
    B_8_exact 3 (500 : ℝ) (600 : ℝ) ≤ (0.00043197 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (500 : ℝ) (600 : ℝ) 2 724 1.9999e-12
    (0.00043197 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row500_a2_le row500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_250_lt, LogTables.exp_neg_1000_3_lt,
                   Real.exp_pos (-(250:ℝ)), Real.exp_pos (-(1000/3:ℝ))])

/-- Row 500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row500_k4_margin :
    B_8_exact 4 (500 : ℝ) (600 : ℝ) ≤ (0.25918 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (500 : ℝ) (600 : ℝ) 2 724 1.9999e-12
    (0.25918 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row500_a2_le row500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_250_lt, LogTables.exp_neg_1000_3_lt,
                   Real.exp_pos (-(250:ℝ)), Real.exp_pos (-(1000/3:ℝ))])

/-- Row 500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row500_k5_margin :
    B_8_exact 5 (500 : ℝ) (600 : ℝ) ≤ (155.51 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (500 : ℝ) (600 : ℝ) 2 724 1.9999e-12
    (155.51 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row500_a2_le row500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_250_lt, LogTables.exp_neg_1000_3_lt,
                   Real.exp_pos (-(250:ℝ)), Real.exp_pos (-(1000/3:ℝ))])

/-- Row 600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row600_k1_margin :
    B_8_exact 1 (600 : ℝ) (700 : ℝ) ≤ (0.0000000013923 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (600 : ℝ) (700 : ℝ) 2 868 1.9890e-12
    (0.0000000013923 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row600_a2_le row600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_300_lt, LogTables.exp_neg_400_lt,
                   Real.exp_pos (-(300:ℝ)), Real.exp_pos (-(400:ℝ))])

/-- Row 600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row600_k2_margin :
    B_8_exact 2 (600 : ℝ) (700 : ℝ) ≤ (0.00000097458 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (600 : ℝ) (700 : ℝ) 2 868 1.9890e-12
    (0.00000097458 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row600_a2_le row600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_300_lt, LogTables.exp_neg_400_lt,
                   Real.exp_pos (-(300:ℝ)), Real.exp_pos (-(400:ℝ))])

/-- Row 600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row600_k3_margin :
    B_8_exact 3 (600 : ℝ) (700 : ℝ) ≤ (0.00068221 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (600 : ℝ) (700 : ℝ) 2 868 1.9890e-12
    (0.00068221 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row600_a2_le row600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_300_lt, LogTables.exp_neg_400_lt,
                   Real.exp_pos (-(300:ℝ)), Real.exp_pos (-(400:ℝ))])

/-- Row 600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row600_k4_margin :
    B_8_exact 4 (600 : ℝ) (700 : ℝ) ≤ (0.47755 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (600 : ℝ) (700 : ℝ) 2 868 1.9890e-12
    (0.47755 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row600_a2_le row600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_300_lt, LogTables.exp_neg_400_lt,
                   Real.exp_pos (-(300:ℝ)), Real.exp_pos (-(400:ℝ))])

/-- Row 600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row600_k5_margin :
    B_8_exact 5 (600 : ℝ) (700 : ℝ) ≤ (334.28 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (600 : ℝ) (700 : ℝ) 2 868 1.9890e-12
    (334.28 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row600_a2_le row600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_300_lt, LogTables.exp_neg_400_lt,
                   Real.exp_pos (-(300:ℝ)), Real.exp_pos (-(400:ℝ))])

/-- Row 700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row700_k1_margin :
    B_8_exact 1 (700 : ℝ) (800 : ℝ) ≤ (0.0000000015812 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (700 : ℝ) (800 : ℝ) 2 1012 1.9765e-12
    (0.0000000015812 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row700_a2_le row700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_350_lt, LogTables.exp_neg_1400_3_lt,
                   Real.exp_pos (-(350:ℝ)), Real.exp_pos (-(1400/3:ℝ))])

/-- Row 700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row700_k2_margin :
    B_8_exact 2 (700 : ℝ) (800 : ℝ) ≤ (0.0000012649 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (700 : ℝ) (800 : ℝ) 2 1012 1.9765e-12
    (0.0000012649 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row700_a2_le row700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_350_lt, LogTables.exp_neg_1400_3_lt,
                   Real.exp_pos (-(350:ℝ)), Real.exp_pos (-(1400/3:ℝ))])

/-- Row 700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row700_k3_margin :
    B_8_exact 3 (700 : ℝ) (800 : ℝ) ≤ (0.0010119 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (700 : ℝ) (800 : ℝ) 2 1012 1.9765e-12
    (0.0010119 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row700_a2_le row700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_350_lt, LogTables.exp_neg_1400_3_lt,
                   Real.exp_pos (-(350:ℝ)), Real.exp_pos (-(1400/3:ℝ))])

/-- Row 700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row700_k4_margin :
    B_8_exact 4 (700 : ℝ) (800 : ℝ) ≤ (0.80955 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (700 : ℝ) (800 : ℝ) 2 1012 1.9765e-12
    (0.80955 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row700_a2_le row700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_350_lt, LogTables.exp_neg_1400_3_lt,
                   Real.exp_pos (-(350:ℝ)), Real.exp_pos (-(1400/3:ℝ))])

/-- Row 700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row700_k5_margin :
    B_8_exact 5 (700 : ℝ) (800 : ℝ) ≤ (647.64 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (700 : ℝ) (800 : ℝ) 2 1012 1.9765e-12
    (647.64 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row700_a2_le row700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_350_lt, LogTables.exp_neg_1400_3_lt,
                   Real.exp_pos (-(350:ℝ)), Real.exp_pos (-(1400/3:ℝ))])

/-- Row 800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row800_k1_margin :
    B_8_exact 1 (800 : ℝ) (900 : ℝ) ≤ (0.0000000017704 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (800 : ℝ) (900 : ℝ) 2 1157 1.9672e-12
    (0.0000000017704 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row800_a2_le row800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_400_lt, LogTables.exp_neg_1600_3_lt,
                   Real.exp_pos (-(400:ℝ)), Real.exp_pos (-(1600/3:ℝ))])

/-- Row 800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row800_k2_margin :
    B_8_exact 2 (800 : ℝ) (900 : ℝ) ≤ (0.0000015934 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (800 : ℝ) (900 : ℝ) 2 1157 1.9672e-12
    (0.0000015934 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row800_a2_le row800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_400_lt, LogTables.exp_neg_1600_3_lt,
                   Real.exp_pos (-(400:ℝ)), Real.exp_pos (-(1600/3:ℝ))])

/-- Row 800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row800_k3_margin :
    B_8_exact 3 (800 : ℝ) (900 : ℝ) ≤ (0.0014340 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (800 : ℝ) (900 : ℝ) 2 1157 1.9672e-12
    (0.0014340 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row800_a2_le row800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_400_lt, LogTables.exp_neg_1600_3_lt,
                   Real.exp_pos (-(400:ℝ)), Real.exp_pos (-(1600/3:ℝ))])

/-- Row 800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row800_k4_margin :
    B_8_exact 4 (800 : ℝ) (900 : ℝ) ≤ (1.2906 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (800 : ℝ) (900 : ℝ) 2 1157 1.9672e-12
    (1.2906 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row800_a2_le row800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_400_lt, LogTables.exp_neg_1600_3_lt,
                   Real.exp_pos (-(400:ℝ)), Real.exp_pos (-(1600/3:ℝ))])

/-- Row 800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row800_k5_margin :
    B_8_exact 5 (800 : ℝ) (900 : ℝ) ≤ (1161.6 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (800 : ℝ) (900 : ℝ) 2 1157 1.9672e-12
    (1161.6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row800_a2_le row800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_400_lt, LogTables.exp_neg_1600_3_lt,
                   Real.exp_pos (-(400:ℝ)), Real.exp_pos (-(1600/3:ℝ))])

/-- Row 900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row900_k1_margin :
    B_8_exact 1 (900 : ℝ) (1000 : ℝ) ≤ (0.0000000019599 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (900 : ℝ) (1000 : ℝ) 2 1301 1.9600e-12
    (0.0000000019599 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row900_a2_le row900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_450_lt, LogTables.exp_neg_600_lt,
                   Real.exp_pos (-(450:ℝ)), Real.exp_pos (-(600:ℝ))])

/-- Row 900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row900_k2_margin :
    B_8_exact 2 (900 : ℝ) (1000 : ℝ) ≤ (0.0000019599 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (900 : ℝ) (1000 : ℝ) 2 1301 1.9600e-12
    (0.0000019599 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row900_a2_le row900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_450_lt, LogTables.exp_neg_600_lt,
                   Real.exp_pos (-(450:ℝ)), Real.exp_pos (-(600:ℝ))])

/-- Row 900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row900_k3_margin :
    B_8_exact 3 (900 : ℝ) (1000 : ℝ) ≤ (0.0019599 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (900 : ℝ) (1000 : ℝ) 2 1301 1.9600e-12
    (0.0019599 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row900_a2_le row900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_450_lt, LogTables.exp_neg_600_lt,
                   Real.exp_pos (-(450:ℝ)), Real.exp_pos (-(600:ℝ))])

/-- Row 900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row900_k4_margin :
    B_8_exact 4 (900 : ℝ) (1000 : ℝ) ≤ (1.9599 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (900 : ℝ) (1000 : ℝ) 2 1301 1.9600e-12
    (1.9599 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row900_a2_le row900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_450_lt, LogTables.exp_neg_600_lt,
                   Real.exp_pos (-(450:ℝ)), Real.exp_pos (-(600:ℝ))])

/-- Row 900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row900_k5_margin :
    B_8_exact 5 (900 : ℝ) (1000 : ℝ) ≤ (1959.9 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (900 : ℝ) (1000 : ℝ) 2 1301 1.9600e-12
    (1959.9 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row900_a2_le row900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_450_lt, LogTables.exp_neg_600_lt,
                   Real.exp_pos (-(450:ℝ)), Real.exp_pos (-(600:ℝ))])

/-- Row 1000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1000_k1_margin :
    B_8_exact 1 (1000 : ℝ) (1500 : ℝ) ≤ (0.0000000029213 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1000 : ℝ) (1500 : ℝ) 2 1445 1.9476e-12
    (0.0000000029213 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1000_a2_le row1000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_500_lt, LogTables.exp_neg_2000_3_lt,
                   Real.exp_pos (-(500:ℝ)), Real.exp_pos (-(2000/3:ℝ))])

/-- Row 1000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1000_k2_margin :
    B_8_exact 2 (1000 : ℝ) (1500 : ℝ) ≤ (0.0000043819 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1000 : ℝ) (1500 : ℝ) 2 1445 1.9476e-12
    (0.0000043819 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1000_a2_le row1000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_500_lt, LogTables.exp_neg_2000_3_lt,
                   Real.exp_pos (-(500:ℝ)), Real.exp_pos (-(2000/3:ℝ))])

/-- Row 1000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1000_k3_margin :
    B_8_exact 3 (1000 : ℝ) (1500 : ℝ) ≤ (0.0065729 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1000 : ℝ) (1500 : ℝ) 2 1445 1.9476e-12
    (0.0065729 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1000_a2_le row1000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_500_lt, LogTables.exp_neg_2000_3_lt,
                   Real.exp_pos (-(500:ℝ)), Real.exp_pos (-(2000/3:ℝ))])

/-- Row 1000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1000_k4_margin :
    B_8_exact 4 (1000 : ℝ) (1500 : ℝ) ≤ (9.8593 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1000 : ℝ) (1500 : ℝ) 2 1445 1.9476e-12
    (9.8593 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1000_a2_le row1000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_500_lt, LogTables.exp_neg_2000_3_lt,
                   Real.exp_pos (-(500:ℝ)), Real.exp_pos (-(2000/3:ℝ))])

/-- Row 1000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1000_k5_margin :
    B_8_exact 5 (1000 : ℝ) (1500 : ℝ) ≤ (14789 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1000 : ℝ) (1500 : ℝ) 2 1445 1.9476e-12
    (14789 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1000_a2_le row1000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_500_lt, LogTables.exp_neg_2000_3_lt,
                   Real.exp_pos (-(500:ℝ)), Real.exp_pos (-(2000/3:ℝ))])

/-- Row 1500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1500_k1_margin :
    B_8_exact 1 (1500 : ℝ) (1600 : ℝ) ≤ (0.0000000030988 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1500 : ℝ) (1600 : ℝ) 2 2167 1.9369e-12
    (0.0000000030988 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1500_a2_le row1500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_750_lt, LogTables.exp_neg_1000_lt,
                   Real.exp_pos (-(750:ℝ)), Real.exp_pos (-(1000:ℝ))])

/-- Row 1500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1500_k2_margin :
    B_8_exact 2 (1500 : ℝ) (1600 : ℝ) ≤ (0.0000049581 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1500 : ℝ) (1600 : ℝ) 2 2167 1.9369e-12
    (0.0000049581 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1500_a2_le row1500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_750_lt, LogTables.exp_neg_1000_lt,
                   Real.exp_pos (-(750:ℝ)), Real.exp_pos (-(1000:ℝ))])

/-- Row 1500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1500_k3_margin :
    B_8_exact 3 (1500 : ℝ) (1600 : ℝ) ≤ (0.0079330 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1500 : ℝ) (1600 : ℝ) 2 2167 1.9369e-12
    (0.0079330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1500_a2_le row1500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_750_lt, LogTables.exp_neg_1000_lt,
                   Real.exp_pos (-(750:ℝ)), Real.exp_pos (-(1000:ℝ))])

/-- Row 1500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1500_k4_margin :
    B_8_exact 4 (1500 : ℝ) (1600 : ℝ) ≤ (12.693 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1500 : ℝ) (1600 : ℝ) 2 2167 1.9369e-12
    (12.693 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1500_a2_le row1500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_750_lt, LogTables.exp_neg_1000_lt,
                   Real.exp_pos (-(750:ℝ)), Real.exp_pos (-(1000:ℝ))])

/-- Row 1500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1500_k5_margin :
    B_8_exact 5 (1500 : ℝ) (1600 : ℝ) ≤ (20309 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1500 : ℝ) (1600 : ℝ) 2 2167 1.9369e-12
    (20309 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1500_a2_le row1500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_750_lt, LogTables.exp_neg_1000_lt,
                   Real.exp_pos (-(750:ℝ)), Real.exp_pos (-(1000:ℝ))])

/-- Row 1600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1600_k1_margin :
    B_8_exact 1 (1600 : ℝ) (1700 : ℝ) ≤ (0.0000000032797 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1600 : ℝ) (1700 : ℝ) 2 2311 1.9293e-12
    (0.0000000032797 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1600_a2_le row1600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_800_lt, LogTables.exp_neg_3200_3_lt,
                   Real.exp_pos (-(800:ℝ)), Real.exp_pos (-(3200/3:ℝ))])

/-- Row 1600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1600_k2_margin :
    B_8_exact 2 (1600 : ℝ) (1700 : ℝ) ≤ (0.0000055755 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1600 : ℝ) (1700 : ℝ) 2 2311 1.9293e-12
    (0.0000055755 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1600_a2_le row1600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_800_lt, LogTables.exp_neg_3200_3_lt,
                   Real.exp_pos (-(800:ℝ)), Real.exp_pos (-(3200/3:ℝ))])

/-- Row 1600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1600_k3_margin :
    B_8_exact 3 (1600 : ℝ) (1700 : ℝ) ≤ (0.0094783 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1600 : ℝ) (1700 : ℝ) 2 2311 1.9293e-12
    (0.0094783 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1600_a2_le row1600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_800_lt, LogTables.exp_neg_3200_3_lt,
                   Real.exp_pos (-(800:ℝ)), Real.exp_pos (-(3200/3:ℝ))])

/-- Row 1600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1600_k4_margin :
    B_8_exact 4 (1600 : ℝ) (1700 : ℝ) ≤ (16.113 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1600 : ℝ) (1700 : ℝ) 2 2311 1.9293e-12
    (16.113 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1600_a2_le row1600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_800_lt, LogTables.exp_neg_3200_3_lt,
                   Real.exp_pos (-(800:ℝ)), Real.exp_pos (-(3200/3:ℝ))])

/-- Row 1600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1600_k5_margin :
    B_8_exact 5 (1600 : ℝ) (1700 : ℝ) ≤ (27392 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1600 : ℝ) (1700 : ℝ) 2 2311 1.9293e-12
    (27392 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1600_a2_le row1600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_800_lt, LogTables.exp_neg_3200_3_lt,
                   Real.exp_pos (-(800:ℝ)), Real.exp_pos (-(3200/3:ℝ))])

/-- Row 1700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1700_k1_margin :
    B_8_exact 1 (1700 : ℝ) (1725 : ℝ) ≤ (0.0000000033247 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1700 : ℝ) (1725 : ℝ) 2 2455 1.9274e-12
    (0.0000000033247 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1700_a2_le row1700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_850_lt, LogTables.exp_neg_3400_3_lt,
                   Real.exp_pos (-(850:ℝ)), Real.exp_pos (-(3400/3:ℝ))])

/-- Row 1700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1700_k2_margin :
    B_8_exact 2 (1700 : ℝ) (1725 : ℝ) ≤ (0.0000057350 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1700 : ℝ) (1725 : ℝ) 2 2455 1.9274e-12
    (0.0000057350 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1700_a2_le row1700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_850_lt, LogTables.exp_neg_3400_3_lt,
                   Real.exp_pos (-(850:ℝ)), Real.exp_pos (-(3400/3:ℝ))])

/-- Row 1700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1700_k3_margin :
    B_8_exact 3 (1700 : ℝ) (1725 : ℝ) ≤ (0.0098929 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1700 : ℝ) (1725 : ℝ) 2 2455 1.9274e-12
    (0.0098929 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1700_a2_le row1700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_850_lt, LogTables.exp_neg_3400_3_lt,
                   Real.exp_pos (-(850:ℝ)), Real.exp_pos (-(3400/3:ℝ))])

/-- Row 1700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1700_k4_margin :
    B_8_exact 4 (1700 : ℝ) (1725 : ℝ) ≤ (17.065 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1700 : ℝ) (1725 : ℝ) 2 2455 1.9274e-12
    (17.065 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1700_a2_le row1700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_850_lt, LogTables.exp_neg_3400_3_lt,
                   Real.exp_pos (-(850:ℝ)), Real.exp_pos (-(3400/3:ℝ))])

/-- Row 1700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1700_k5_margin :
    B_8_exact 5 (1700 : ℝ) (1725 : ℝ) ≤ (29438 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1700 : ℝ) (1725 : ℝ) 2 2455 1.9274e-12
    (29438 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1700_a2_le row1700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_850_lt, LogTables.exp_neg_3400_3_lt,
                   Real.exp_pos (-(850:ℝ)), Real.exp_pos (-(3400/3:ℝ))])

/-- Row 1725 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1725_k1_margin :
    B_8_exact 1 (1725 : ℝ) (1750 : ℝ) ≤ (0.0000000033721 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1725 : ℝ) (1750 : ℝ) 2 2491 1.9270e-12
    (0.0000000033721 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1725_a2_le row1725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1725_2_lt, LogTables.exp_neg_1150_lt,
                   Real.exp_pos (-(1725/2:ℝ)), Real.exp_pos (-(1150:ℝ))])

/-- Row 1725 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1725_k2_margin :
    B_8_exact 2 (1725 : ℝ) (1750 : ℝ) ≤ (0.0000059011 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1725 : ℝ) (1750 : ℝ) 2 2491 1.9270e-12
    (0.0000059011 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1725_a2_le row1725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1725_2_lt, LogTables.exp_neg_1150_lt,
                   Real.exp_pos (-(1725/2:ℝ)), Real.exp_pos (-(1150:ℝ))])

/-- Row 1725 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1725_k3_margin :
    B_8_exact 3 (1725 : ℝ) (1750 : ℝ) ≤ (0.010327 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1725 : ℝ) (1750 : ℝ) 2 2491 1.9270e-12
    (0.010327 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1725_a2_le row1725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1725_2_lt, LogTables.exp_neg_1150_lt,
                   Real.exp_pos (-(1725/2:ℝ)), Real.exp_pos (-(1150:ℝ))])

/-- Row 1725 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1725_k4_margin :
    B_8_exact 4 (1725 : ℝ) (1750 : ℝ) ≤ (18.072 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1725 : ℝ) (1750 : ℝ) 2 2491 1.9270e-12
    (18.072 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1725_a2_le row1725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1725_2_lt, LogTables.exp_neg_1150_lt,
                   Real.exp_pos (-(1725/2:ℝ)), Real.exp_pos (-(1150:ℝ))])

/-- Row 1725 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1725_k5_margin :
    B_8_exact 5 (1725 : ℝ) (1750 : ℝ) ≤ (31626 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1725 : ℝ) (1750 : ℝ) 2 2491 1.9270e-12
    (31626 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1725_a2_le row1725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1725_2_lt, LogTables.exp_neg_1150_lt,
                   Real.exp_pos (-(1725/2:ℝ)), Real.exp_pos (-(1150:ℝ))])

/-- Row 1750 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1750_k1_margin :
    B_8_exact 1 (1750 : ℝ) (1775 : ℝ) ≤ (0.0000000034195 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1750 : ℝ) (1775 : ℝ) 2 2527 1.9266e-12
    (0.0000000034195 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1750_a2_le row1750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_875_lt, LogTables.exp_neg_3500_3_lt,
                   Real.exp_pos (-(875:ℝ)), Real.exp_pos (-(3500/3:ℝ))])

/-- Row 1750 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1750_k2_margin :
    B_8_exact 2 (1750 : ℝ) (1775 : ℝ) ≤ (0.0000060696 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1750 : ℝ) (1775 : ℝ) 2 2527 1.9266e-12
    (0.0000060696 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1750_a2_le row1750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_875_lt, LogTables.exp_neg_3500_3_lt,
                   Real.exp_pos (-(875:ℝ)), Real.exp_pos (-(3500/3:ℝ))])

/-- Row 1750 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1750_k3_margin :
    B_8_exact 3 (1750 : ℝ) (1775 : ℝ) ≤ (0.010774 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1750 : ℝ) (1775 : ℝ) 2 2527 1.9266e-12
    (0.010774 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1750_a2_le row1750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_875_lt, LogTables.exp_neg_3500_3_lt,
                   Real.exp_pos (-(875:ℝ)), Real.exp_pos (-(3500/3:ℝ))])

/-- Row 1750 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1750_k4_margin :
    B_8_exact 4 (1750 : ℝ) (1775 : ℝ) ≤ (19.123 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1750 : ℝ) (1775 : ℝ) 2 2527 1.9266e-12
    (19.123 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1750_a2_le row1750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_875_lt, LogTables.exp_neg_3500_3_lt,
                   Real.exp_pos (-(875:ℝ)), Real.exp_pos (-(3500/3:ℝ))])

/-- Row 1750 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1750_k5_margin :
    B_8_exact 5 (1750 : ℝ) (1775 : ℝ) ≤ (33943 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1750 : ℝ) (1775 : ℝ) 2 2527 1.9266e-12
    (33943 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1750_a2_le row1750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_875_lt, LogTables.exp_neg_3500_3_lt,
                   Real.exp_pos (-(875:ℝ)), Real.exp_pos (-(3500/3:ℝ))])

/-- Row 1775 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1775_k1_margin :
    B_8_exact 1 (1775 : ℝ) (1800 : ℝ) ≤ (0.0000000034669 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1775 : ℝ) (1800 : ℝ) 2 2563 1.9261e-12
    (0.0000000034669 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1775_a2_le row1775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1775_2_lt, LogTables.exp_neg_3550_3_lt,
                   Real.exp_pos (-(1775/2:ℝ)), Real.exp_pos (-(3550/3:ℝ))])

/-- Row 1775 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1775_k2_margin :
    B_8_exact 2 (1775 : ℝ) (1800 : ℝ) ≤ (0.0000062404 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1775 : ℝ) (1800 : ℝ) 2 2563 1.9261e-12
    (0.0000062404 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1775_a2_le row1775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1775_2_lt, LogTables.exp_neg_3550_3_lt,
                   Real.exp_pos (-(1775/2:ℝ)), Real.exp_pos (-(3550/3:ℝ))])

/-- Row 1775 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1775_k3_margin :
    B_8_exact 3 (1775 : ℝ) (1800 : ℝ) ≤ (0.011233 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1775 : ℝ) (1800 : ℝ) 2 2563 1.9261e-12
    (0.011233 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1775_a2_le row1775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1775_2_lt, LogTables.exp_neg_3550_3_lt,
                   Real.exp_pos (-(1775/2:ℝ)), Real.exp_pos (-(3550/3:ℝ))])

/-- Row 1775 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1775_k4_margin :
    B_8_exact 4 (1775 : ℝ) (1800 : ℝ) ≤ (20.219 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1775 : ℝ) (1800 : ℝ) 2 2563 1.9261e-12
    (20.219 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1775_a2_le row1775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1775_2_lt, LogTables.exp_neg_3550_3_lt,
                   Real.exp_pos (-(1775/2:ℝ)), Real.exp_pos (-(3550/3:ℝ))])

/-- Row 1775 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1775_k5_margin :
    B_8_exact 5 (1775 : ℝ) (1800 : ℝ) ≤ (36394 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1775 : ℝ) (1800 : ℝ) 2 2563 1.9261e-12
    (36394 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1775_a2_le row1775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1775_2_lt, LogTables.exp_neg_3550_3_lt,
                   Real.exp_pos (-(1775/2:ℝ)), Real.exp_pos (-(3550/3:ℝ))])

/-- Row 1800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1800_k1_margin :
    B_8_exact 1 (1800 : ℝ) (1825 : ℝ) ≤ (0.0000000035143 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1800 : ℝ) (1825 : ℝ) 2 2599 1.9257e-12
    (0.0000000035143 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1800_a2_le row1800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_900_lt, LogTables.exp_neg_1200_lt,
                   Real.exp_pos (-(900:ℝ)), Real.exp_pos (-(1200:ℝ))])

/-- Row 1800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1800_k2_margin :
    B_8_exact 2 (1800 : ℝ) (1825 : ℝ) ≤ (0.0000064136 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1800 : ℝ) (1825 : ℝ) 2 2599 1.9257e-12
    (0.0000064136 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1800_a2_le row1800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_900_lt, LogTables.exp_neg_1200_lt,
                   Real.exp_pos (-(900:ℝ)), Real.exp_pos (-(1200:ℝ))])

/-- Row 1800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1800_k3_margin :
    B_8_exact 3 (1800 : ℝ) (1825 : ℝ) ≤ (0.011705 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1800 : ℝ) (1825 : ℝ) 2 2599 1.9257e-12
    (0.011705 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1800_a2_le row1800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_900_lt, LogTables.exp_neg_1200_lt,
                   Real.exp_pos (-(900:ℝ)), Real.exp_pos (-(1200:ℝ))])

/-- Row 1800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1800_k4_margin :
    B_8_exact 4 (1800 : ℝ) (1825 : ℝ) ≤ (21.361 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1800 : ℝ) (1825 : ℝ) 2 2599 1.9257e-12
    (21.361 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1800_a2_le row1800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_900_lt, LogTables.exp_neg_1200_lt,
                   Real.exp_pos (-(900:ℝ)), Real.exp_pos (-(1200:ℝ))])

/-- Row 1800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1800_k5_margin :
    B_8_exact 5 (1800 : ℝ) (1825 : ℝ) ≤ (38984 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1800 : ℝ) (1825 : ℝ) 2 2599 1.9257e-12
    (38984 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1800_a2_le row1800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_900_lt, LogTables.exp_neg_1200_lt,
                   Real.exp_pos (-(900:ℝ)), Real.exp_pos (-(1200:ℝ))])

/-- Row 1825 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1825_k1_margin :
    B_8_exact 1 (1825 : ℝ) (1850 : ℝ) ≤ (0.0000000035617 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1825 : ℝ) (1850 : ℝ) 2 2635 1.9254e-12
    (0.0000000035617 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1825_a2_le row1825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1825_2_lt, LogTables.exp_neg_3650_3_lt,
                   Real.exp_pos (-(1825/2:ℝ)), Real.exp_pos (-(3650/3:ℝ))])

/-- Row 1825 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1825_k2_margin :
    B_8_exact 2 (1825 : ℝ) (1850 : ℝ) ≤ (0.0000065892 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1825 : ℝ) (1850 : ℝ) 2 2635 1.9254e-12
    (0.0000065892 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1825_a2_le row1825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1825_2_lt, LogTables.exp_neg_3650_3_lt,
                   Real.exp_pos (-(1825/2:ℝ)), Real.exp_pos (-(3650/3:ℝ))])

/-- Row 1825 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1825_k3_margin :
    B_8_exact 3 (1825 : ℝ) (1850 : ℝ) ≤ (0.012190 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1825 : ℝ) (1850 : ℝ) 2 2635 1.9254e-12
    (0.012190 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1825_a2_le row1825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1825_2_lt, LogTables.exp_neg_3650_3_lt,
                   Real.exp_pos (-(1825/2:ℝ)), Real.exp_pos (-(3650/3:ℝ))])

/-- Row 1825 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1825_k4_margin :
    B_8_exact 4 (1825 : ℝ) (1850 : ℝ) ≤ (22.552 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1825 : ℝ) (1850 : ℝ) 2 2635 1.9254e-12
    (22.552 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1825_a2_le row1825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1825_2_lt, LogTables.exp_neg_3650_3_lt,
                   Real.exp_pos (-(1825/2:ℝ)), Real.exp_pos (-(3650/3:ℝ))])

/-- Row 1825 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1825_k5_margin :
    B_8_exact 5 (1825 : ℝ) (1850 : ℝ) ≤ (41720 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1825 : ℝ) (1850 : ℝ) 2 2635 1.9254e-12
    (41720 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1825_a2_le row1825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1825_2_lt, LogTables.exp_neg_3650_3_lt,
                   Real.exp_pos (-(1825/2:ℝ)), Real.exp_pos (-(3650/3:ℝ))])

/-- Row 1850 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1850_k1_margin :
    B_8_exact 1 (1850 : ℝ) (1875 : ℝ) ≤ (0.0000000036091 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1850 : ℝ) (1875 : ℝ) 2 2671 1.9250e-12
    (0.0000000036091 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1850_a2_le row1850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_925_lt, LogTables.exp_neg_3700_3_lt,
                   Real.exp_pos (-(925:ℝ)), Real.exp_pos (-(3700/3:ℝ))])

/-- Row 1850 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1850_k2_margin :
    B_8_exact 2 (1850 : ℝ) (1875 : ℝ) ≤ (0.0000067671 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1850 : ℝ) (1875 : ℝ) 2 2671 1.9250e-12
    (0.0000067671 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1850_a2_le row1850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_925_lt, LogTables.exp_neg_3700_3_lt,
                   Real.exp_pos (-(925:ℝ)), Real.exp_pos (-(3700/3:ℝ))])

/-- Row 1850 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1850_k3_margin :
    B_8_exact 3 (1850 : ℝ) (1875 : ℝ) ≤ (0.012688 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1850 : ℝ) (1875 : ℝ) 2 2671 1.9250e-12
    (0.012688 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1850_a2_le row1850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_925_lt, LogTables.exp_neg_3700_3_lt,
                   Real.exp_pos (-(925:ℝ)), Real.exp_pos (-(3700/3:ℝ))])

/-- Row 1850 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1850_k4_margin :
    B_8_exact 4 (1850 : ℝ) (1875 : ℝ) ≤ (23.791 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1850 : ℝ) (1875 : ℝ) 2 2671 1.9250e-12
    (23.791 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1850_a2_le row1850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_925_lt, LogTables.exp_neg_3700_3_lt,
                   Real.exp_pos (-(925:ℝ)), Real.exp_pos (-(3700/3:ℝ))])

/-- Row 1850 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1850_k5_margin :
    B_8_exact 5 (1850 : ℝ) (1875 : ℝ) ≤ (44608 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1850 : ℝ) (1875 : ℝ) 2 2671 1.9250e-12
    (44608 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1850_a2_le row1850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_925_lt, LogTables.exp_neg_3700_3_lt,
                   Real.exp_pos (-(925:ℝ)), Real.exp_pos (-(3700/3:ℝ))])

/-- Row 1875 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1875_k1_margin :
    B_8_exact 1 (1875 : ℝ) (1900 : ℝ) ≤ (0.0000000036566 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1875 : ℝ) (1900 : ℝ) 2 2708 1.9246e-12
    (0.0000000036566 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1875_a2_le row1875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1875_2_lt, LogTables.exp_neg_1250_lt,
                   Real.exp_pos (-(1875/2:ℝ)), Real.exp_pos (-(1250:ℝ))])

/-- Row 1875 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1875_k2_margin :
    B_8_exact 2 (1875 : ℝ) (1900 : ℝ) ≤ (0.0000069475 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1875 : ℝ) (1900 : ℝ) 2 2708 1.9246e-12
    (0.0000069475 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1875_a2_le row1875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1875_2_lt, LogTables.exp_neg_1250_lt,
                   Real.exp_pos (-(1875/2:ℝ)), Real.exp_pos (-(1250:ℝ))])

/-- Row 1875 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1875_k3_margin :
    B_8_exact 3 (1875 : ℝ) (1900 : ℝ) ≤ (0.013200 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1875 : ℝ) (1900 : ℝ) 2 2708 1.9246e-12
    (0.013200 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1875_a2_le row1875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1875_2_lt, LogTables.exp_neg_1250_lt,
                   Real.exp_pos (-(1875/2:ℝ)), Real.exp_pos (-(1250:ℝ))])

/-- Row 1875 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1875_k4_margin :
    B_8_exact 4 (1875 : ℝ) (1900 : ℝ) ≤ (25.080 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1875 : ℝ) (1900 : ℝ) 2 2708 1.9246e-12
    (25.080 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1875_a2_le row1875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1875_2_lt, LogTables.exp_neg_1250_lt,
                   Real.exp_pos (-(1875/2:ℝ)), Real.exp_pos (-(1250:ℝ))])

/-- Row 1875 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1875_k5_margin :
    B_8_exact 5 (1875 : ℝ) (1900 : ℝ) ≤ (47653 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1875 : ℝ) (1900 : ℝ) 2 2708 1.9246e-12
    (47653 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1875_a2_le row1875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1875_2_lt, LogTables.exp_neg_1250_lt,
                   Real.exp_pos (-(1875/2:ℝ)), Real.exp_pos (-(1250:ℝ))])

end BKLNW
