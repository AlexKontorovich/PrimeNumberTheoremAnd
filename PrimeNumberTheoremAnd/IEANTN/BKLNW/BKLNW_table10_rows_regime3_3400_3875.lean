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


private lemma row3400_a2_le : Inputs.default.a₂ (3400 : ℝ) ≤ (4908 : ℝ) := by
  have h := a2_crude_le (3400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3400 : ℝ) / log 2⌋₊ : ℝ) ≤ (3400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3400 : ℝ) / log 2 ≤ 4906 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4906 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4908 := by norm_num


private lemma row3425_a2_le : Inputs.default.a₂ (3425 : ℝ) ≤ (4944 : ℝ) := by
  have h := a2_crude_le (3425 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3425 : ℝ) / log 2⌋₊ : ℝ) ≤ (3425 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3425 : ℝ) / log 2 ≤ 4942 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3425 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3425 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4942 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4944 := by norm_num


private lemma row3450_a2_le : Inputs.default.a₂ (3450 : ℝ) ≤ (4980 : ℝ) := by
  have h := a2_crude_le (3450 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3450 : ℝ) / log 2⌋₊ : ℝ) ≤ (3450 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3450 : ℝ) / log 2 ≤ 4978 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3450 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3450 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4978 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4980 := by norm_num


private lemma row3475_a2_le : Inputs.default.a₂ (3475 : ℝ) ≤ (5016 : ℝ) := by
  have h := a2_crude_le (3475 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3475 : ℝ) / log 2⌋₊ : ℝ) ≤ (3475 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3475 : ℝ) / log 2 ≤ 5014 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3475 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3475 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5014 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5016 := by norm_num


private lemma row3500_a2_le : Inputs.default.a₂ (3500 : ℝ) ≤ (5052 : ℝ) := by
  have h := a2_crude_le (3500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3500 : ℝ) / log 2⌋₊ : ℝ) ≤ (3500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3500 : ℝ) / log 2 ≤ 5050 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5050 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5052 := by norm_num


private lemma row3525_a2_le : Inputs.default.a₂ (3525 : ℝ) ≤ (5088 : ℝ) := by
  have h := a2_crude_le (3525 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3525 : ℝ) / log 2⌋₊ : ℝ) ≤ (3525 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3525 : ℝ) / log 2 ≤ 5086 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3525 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3525 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5086 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5088 := by norm_num


private lemma row3550_a2_le : Inputs.default.a₂ (3550 : ℝ) ≤ (5124 : ℝ) := by
  have h := a2_crude_le (3550 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3550 : ℝ) / log 2⌋₊ : ℝ) ≤ (3550 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3550 : ℝ) / log 2 ≤ 5122 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3550 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3550 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5122 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5124 := by norm_num


private lemma row3575_a2_le : Inputs.default.a₂ (3575 : ℝ) ≤ (5160 : ℝ) := by
  have h := a2_crude_le (3575 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3575 : ℝ) / log 2⌋₊ : ℝ) ≤ (3575 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3575 : ℝ) / log 2 ≤ 5158 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3575 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3575 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5158 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5160 := by norm_num


private lemma row3600_a2_le : Inputs.default.a₂ (3600 : ℝ) ≤ (5196 : ℝ) := by
  have h := a2_crude_le (3600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3600 : ℝ) / log 2⌋₊ : ℝ) ≤ (3600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3600 : ℝ) / log 2 ≤ 5194 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5194 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5196 := by norm_num


private lemma row3625_a2_le : Inputs.default.a₂ (3625 : ℝ) ≤ (5232 : ℝ) := by
  have h := a2_crude_le (3625 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3625 : ℝ) / log 2⌋₊ : ℝ) ≤ (3625 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3625 : ℝ) / log 2 ≤ 5230 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3625 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3625 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5230 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5232 := by norm_num


private lemma row3650_a2_le : Inputs.default.a₂ (3650 : ℝ) ≤ (5268 : ℝ) := by
  have h := a2_crude_le (3650 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3650 : ℝ) / log 2⌋₊ : ℝ) ≤ (3650 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3650 : ℝ) / log 2 ≤ 5266 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3650 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3650 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5266 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5268 := by norm_num


private lemma row3675_a2_le : Inputs.default.a₂ (3675 : ℝ) ≤ (5304 : ℝ) := by
  have h := a2_crude_le (3675 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3675 : ℝ) / log 2⌋₊ : ℝ) ≤ (3675 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3675 : ℝ) / log 2 ≤ 5302 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3675 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3675 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5302 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5304 := by norm_num


private lemma row3700_a2_le : Inputs.default.a₂ (3700 : ℝ) ≤ (5340 : ℝ) := by
  have h := a2_crude_le (3700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3700 : ℝ) / log 2⌋₊ : ℝ) ≤ (3700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3700 : ℝ) / log 2 ≤ 5338 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5338 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5340 := by norm_num


private lemma row3725_a2_le : Inputs.default.a₂ (3725 : ℝ) ≤ (5377 : ℝ) := by
  have h := a2_crude_le (3725 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3725 : ℝ) / log 2⌋₊ : ℝ) ≤ (3725 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3725 : ℝ) / log 2 ≤ 5375 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3725 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3725 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5375 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5377 := by norm_num


private lemma row3750_a2_le : Inputs.default.a₂ (3750 : ℝ) ≤ (5413 : ℝ) := by
  have h := a2_crude_le (3750 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3750 : ℝ) / log 2⌋₊ : ℝ) ≤ (3750 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3750 : ℝ) / log 2 ≤ 5411 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3750 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3750 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5411 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5413 := by norm_num


private lemma row3775_a2_le : Inputs.default.a₂ (3775 : ℝ) ≤ (5449 : ℝ) := by
  have h := a2_crude_le (3775 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3775 : ℝ) / log 2⌋₊ : ℝ) ≤ (3775 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3775 : ℝ) / log 2 ≤ 5447 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3775 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3775 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5447 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5449 := by norm_num


private lemma row3800_a2_le : Inputs.default.a₂ (3800 : ℝ) ≤ (5485 : ℝ) := by
  have h := a2_crude_le (3800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3800 : ℝ) / log 2⌋₊ : ℝ) ≤ (3800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3800 : ℝ) / log 2 ≤ 5483 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5483 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5485 := by norm_num


private lemma row3825_a2_le : Inputs.default.a₂ (3825 : ℝ) ≤ (5521 : ℝ) := by
  have h := a2_crude_le (3825 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3825 : ℝ) / log 2⌋₊ : ℝ) ≤ (3825 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3825 : ℝ) / log 2 ≤ 5519 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3825 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3825 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5519 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5521 := by norm_num


private lemma row3850_a2_le : Inputs.default.a₂ (3850 : ℝ) ≤ (5557 : ℝ) := by
  have h := a2_crude_le (3850 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3850 : ℝ) / log 2⌋₊ : ℝ) ≤ (3850 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3850 : ℝ) / log 2 ≤ 5555 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3850 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3850 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5555 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5557 := by norm_num


private lemma row3875_a2_le : Inputs.default.a₂ (3875 : ℝ) ≤ (5593 : ℝ) := by
  have h := a2_crude_le (3875 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3875 : ℝ) / log 2⌋₊ : ℝ) ≤ (3875 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3875 : ℝ) / log 2 ≤ 5591 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3875 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3875 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (5591 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 5593 := by norm_num


set_option maxRecDepth 10000 in
private lemma row3400_table8_mem : (3400, 4.4414e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3400_eps_le : Inputs.default.ε (3400 : ℝ) ≤ 4.4414e-15 := by
  change BKLNW_app.table_8_ε (3400 : ℝ) ≤ 4.4414e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3400)
    (ε := 4.4414e-15) row3400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3425_table8_mem : (3425, 3.8454e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3425_eps_le : Inputs.default.ε (3425 : ℝ) ≤ 3.8454e-15 := by
  change BKLNW_app.table_8_ε (3425 : ℝ) ≤ 3.8454e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3425)
    (ε := 3.8454e-15) row3425_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3450_table8_mem : (3450, 3.3251e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3450_eps_le : Inputs.default.ε (3450 : ℝ) ≤ 3.3251e-15 := by
  change BKLNW_app.table_8_ε (3450 : ℝ) ≤ 3.3251e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3450)
    (ε := 3.3251e-15) row3450_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3475_table8_mem : (3475, 2.8741e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3475_eps_le : Inputs.default.ε (3475 : ℝ) ≤ 2.8741e-15 := by
  change BKLNW_app.table_8_ε (3475 : ℝ) ≤ 2.8741e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3475)
    (ε := 2.8741e-15) row3475_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3500_table8_mem : (3500, 2.4865e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3500_eps_le : Inputs.default.ε (3500 : ℝ) ≤ 2.4865e-15 := by
  change BKLNW_app.table_8_ε (3500 : ℝ) ≤ 2.4865e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3500)
    (ε := 2.4865e-15) row3500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3525_table8_mem : (3525, 2.1523e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3525_eps_le : Inputs.default.ε (3525 : ℝ) ≤ 2.1523e-15 := by
  change BKLNW_app.table_8_ε (3525 : ℝ) ≤ 2.1523e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3525)
    (ε := 2.1523e-15) row3525_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3550_table8_mem : (3550, 1.8633e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3550_eps_le : Inputs.default.ε (3550 : ℝ) ≤ 1.8633e-15 := by
  change BKLNW_app.table_8_ε (3550 : ℝ) ≤ 1.8633e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3550)
    (ε := 1.8633e-15) row3550_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3575_table8_mem : (3575, 1.6124e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3575_eps_le : Inputs.default.ε (3575 : ℝ) ≤ 1.6124e-15 := by
  change BKLNW_app.table_8_ε (3575 : ℝ) ≤ 1.6124e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3575)
    (ε := 1.6124e-15) row3575_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3600_table8_mem : (3600, 1.3966e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3600_eps_le : Inputs.default.ε (3600 : ℝ) ≤ 1.3966e-15 := by
  change BKLNW_app.table_8_ε (3600 : ℝ) ≤ 1.3966e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3600)
    (ε := 1.3966e-15) row3600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3625_table8_mem : (3625, 1.2101e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3625_eps_le : Inputs.default.ε (3625 : ℝ) ≤ 1.2101e-15 := by
  change BKLNW_app.table_8_ε (3625 : ℝ) ≤ 1.2101e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3625)
    (ε := 1.2101e-15) row3625_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3650_table8_mem : (3650, 1.0470e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3650_eps_le : Inputs.default.ε (3650 : ℝ) ≤ 1.0470e-15 := by
  change BKLNW_app.table_8_ε (3650 : ℝ) ≤ 1.0470e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3650)
    (ε := 1.0470e-15) row3650_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3675_table8_mem : (3675, 9.0704e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3675_eps_le : Inputs.default.ε (3675 : ℝ) ≤ 9.0704e-16 := by
  change BKLNW_app.table_8_ε (3675 : ℝ) ≤ 9.0704e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3675)
    (ε := 9.0704e-16) row3675_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3700_table8_mem : (3700, 7.8647e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3700_eps_le : Inputs.default.ε (3700 : ℝ) ≤ 7.8647e-16 := by
  change BKLNW_app.table_8_ε (3700 : ℝ) ≤ 7.8647e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3700)
    (ε := 7.8647e-16) row3700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3725_table8_mem : (3725, 6.8213e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3725_eps_le : Inputs.default.ε (3725 : ℝ) ≤ 6.8213e-16 := by
  change BKLNW_app.table_8_ε (3725 : ℝ) ≤ 6.8213e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3725)
    (ε := 6.8213e-16) row3725_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3750_table8_mem : (3750, 5.9196e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3750_eps_le : Inputs.default.ε (3750 : ℝ) ≤ 5.9196e-16 := by
  change BKLNW_app.table_8_ε (3750 : ℝ) ≤ 5.9196e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3750)
    (ε := 5.9196e-16) row3750_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3775_table8_mem : (3775, 5.1352e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3775_eps_le : Inputs.default.ε (3775 : ℝ) ≤ 5.1352e-16 := by
  change BKLNW_app.table_8_ε (3775 : ℝ) ≤ 5.1352e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3775)
    (ε := 5.1352e-16) row3775_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3800_table8_mem : (3800, 4.4496e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3800_eps_le : Inputs.default.ε (3800 : ℝ) ≤ 4.4496e-16 := by
  change BKLNW_app.table_8_ε (3800 : ℝ) ≤ 4.4496e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3800)
    (ε := 4.4496e-16) row3800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3825_table8_mem : (3825, 3.8583e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3825_eps_le : Inputs.default.ε (3825 : ℝ) ≤ 3.8583e-16 := by
  change BKLNW_app.table_8_ε (3825 : ℝ) ≤ 3.8583e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3825)
    (ε := 3.8583e-16) row3825_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3850_table8_mem : (3850, 3.3477e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3850_eps_le : Inputs.default.ε (3850 : ℝ) ≤ 3.3477e-16 := by
  change BKLNW_app.table_8_ε (3850 : ℝ) ≤ 3.3477e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3850)
    (ε := 3.3477e-16) row3850_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row3875_table8_mem : (3875, 2.9011e-16) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3875_eps_le : Inputs.default.ε (3875 : ℝ) ≤ 2.9011e-16 := by
  change BKLNW_app.table_8_ε (3875 : ℝ) ≤ 2.9011e-16
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3875)
    (ε := 2.9011e-16) row3875_table8_mem (by norm_num)


/-- Row 3400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3400_k1_margin :
    B_8_exact 1 (3400 : ℝ) (3425 : ℝ) ≤ (0.000000000015212 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3400 : ℝ) (3425 : ℝ) 2 4908 4.4414e-15
    (0.000000000015212 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3400_a2_le row3400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3400_k2_margin :
    B_8_exact 2 (3400 : ℝ) (3425 : ℝ) ≤ (0.000000052099 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3400 : ℝ) (3425 : ℝ) 2 4908 4.4414e-15
    (0.000000052099 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3400_a2_le row3400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3400_k3_margin :
    B_8_exact 3 (3400 : ℝ) (3425 : ℝ) ≤ (0.00017844 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3400 : ℝ) (3425 : ℝ) 2 4908 4.4414e-15
    (0.00017844 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3400_a2_le row3400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3400_k4_margin :
    B_8_exact 4 (3400 : ℝ) (3425 : ℝ) ≤ (0.61116 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3400 : ℝ) (3425 : ℝ) 2 4908 4.4414e-15
    (0.61116 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3400_a2_le row3400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3400_k5_margin :
    B_8_exact 5 (3400 : ℝ) (3425 : ℝ) ≤ (2093.2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3400 : ℝ) (3425 : ℝ) 2 4908 4.4414e-15
    (2093.2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3400_a2_le row3400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3425 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3425_k1_margin :
    B_8_exact 1 (3425 : ℝ) (3450 : ℝ) ≤ (0.000000000013266 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3425 : ℝ) (3450 : ℝ) 2 4944 3.8454e-15
    (0.000000000013266 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3425_a2_le row3425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3425 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3425_k2_margin :
    B_8_exact 2 (3425 : ℝ) (3450 : ℝ) ≤ (0.000000045768 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3425 : ℝ) (3450 : ℝ) 2 4944 3.8454e-15
    (0.000000045768 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3425_a2_le row3425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3425 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3425_k3_margin :
    B_8_exact 3 (3425 : ℝ) (3450 : ℝ) ≤ (0.00015790 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3425 : ℝ) (3450 : ℝ) 2 4944 3.8454e-15
    (0.00015790 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3425_a2_le row3425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3425 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3425_k4_margin :
    B_8_exact 4 (3425 : ℝ) (3450 : ℝ) ≤ (0.54476 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3425 : ℝ) (3450 : ℝ) 2 4944 3.8454e-15
    (0.54476 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3425_a2_le row3425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3425 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3425_k5_margin :
    B_8_exact 5 (3425 : ℝ) (3450 : ℝ) ≤ (1879.4 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3425 : ℝ) (3450 : ℝ) 2 4944 3.8454e-15
    (1879.4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3425_a2_le row3425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3450 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3450_k1_margin :
    B_8_exact 1 (3450 : ℝ) (3475 : ℝ) ≤ (0.000000000011554 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3450 : ℝ) (3475 : ℝ) 2 4980 3.3251e-15
    (0.000000000011554 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3450_a2_le row3450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3450 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3450_k2_margin :
    B_8_exact 2 (3450 : ℝ) (3475 : ℝ) ≤ (0.000000040151 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3450 : ℝ) (3475 : ℝ) 2 4980 3.3251e-15
    (0.000000040151 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3450_a2_le row3450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3450 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3450_k3_margin :
    B_8_exact 3 (3450 : ℝ) (3475 : ℝ) ≤ (0.00013953 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3450 : ℝ) (3475 : ℝ) 2 4980 3.3251e-15
    (0.00013953 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3450_a2_le row3450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3450 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3450_k4_margin :
    B_8_exact 4 (3450 : ℝ) (3475 : ℝ) ≤ (0.48485 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3450 : ℝ) (3475 : ℝ) 2 4980 3.3251e-15
    (0.48485 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3450_a2_le row3450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3450 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3450_k5_margin :
    B_8_exact 5 (3450 : ℝ) (3475 : ℝ) ≤ (1684.9 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3450 : ℝ) (3475 : ℝ) 2 4980 3.3251e-15
    (1684.9 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3450_a2_le row3450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3475 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3475_k1_margin :
    B_8_exact 1 (3475 : ℝ) (3500 : ℝ) ≤ (0.000000000010059 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3475 : ℝ) (3500 : ℝ) 2 5016 2.8741e-15
    (0.000000000010059 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3475_a2_le row3475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3475 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3475_k2_margin :
    B_8_exact 2 (3475 : ℝ) (3500 : ℝ) ≤ (0.000000035206 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3475 : ℝ) (3500 : ℝ) 2 5016 2.8741e-15
    (0.000000035206 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3475_a2_le row3475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3475 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3475_k3_margin :
    B_8_exact 3 (3475 : ℝ) (3500 : ℝ) ≤ (0.00012322 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3475 : ℝ) (3500 : ℝ) 2 5016 2.8741e-15
    (0.00012322 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3475_a2_le row3475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3475 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3475_k4_margin :
    B_8_exact 4 (3475 : ℝ) (3500 : ℝ) ≤ (0.43127 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3475 : ℝ) (3500 : ℝ) 2 5016 2.8741e-15
    (0.43127 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3475_a2_le row3475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3475 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3475_k5_margin :
    B_8_exact 5 (3475 : ℝ) (3500 : ℝ) ≤ (1509.5 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3475 : ℝ) (3500 : ℝ) 2 5016 2.8741e-15
    (1509.5 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3475_a2_le row3475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3500_k1_margin :
    B_8_exact 1 (3500 : ℝ) (3525 : ℝ) ≤ (0.0000000000087646 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3500 : ℝ) (3525 : ℝ) 2 5052 2.4865e-15
    (0.0000000000087646 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3500_a2_le row3500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3500_k2_margin :
    B_8_exact 2 (3500 : ℝ) (3525 : ℝ) ≤ (0.000000030895 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3500 : ℝ) (3525 : ℝ) 2 5052 2.4865e-15
    (0.000000030895 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3500_a2_le row3500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3500_k3_margin :
    B_8_exact 3 (3500 : ℝ) (3525 : ℝ) ≤ (0.00010891 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3500 : ℝ) (3525 : ℝ) 2 5052 2.4865e-15
    (0.00010891 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3500_a2_le row3500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3500_k4_margin :
    B_8_exact 4 (3500 : ℝ) (3525 : ℝ) ≤ (0.38389 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3500 : ℝ) (3525 : ℝ) 2 5052 2.4865e-15
    (0.38389 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3500_a2_le row3500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3500_k5_margin :
    B_8_exact 5 (3500 : ℝ) (3525 : ℝ) ≤ (1353.2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3500 : ℝ) (3525 : ℝ) 2 5052 2.4865e-15
    (1353.2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3500_a2_le row3500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3525 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3525_k1_margin :
    B_8_exact 1 (3525 : ℝ) (3550 : ℝ) ≤ (0.0000000000076403 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3525 : ℝ) (3550 : ℝ) 2 5088 2.1523e-15
    (0.0000000000076403 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3525_a2_le row3525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3525 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3525_k2_margin :
    B_8_exact 2 (3525 : ℝ) (3550 : ℝ) ≤ (0.000000027123 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3525 : ℝ) (3550 : ℝ) 2 5088 2.1523e-15
    (0.000000027123 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3525_a2_le row3525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3525 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3525_k3_margin :
    B_8_exact 3 (3525 : ℝ) (3550 : ℝ) ≤ (0.000096287 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3525 : ℝ) (3550 : ℝ) 2 5088 2.1523e-15
    (0.000096287 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3525_a2_le row3525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3525 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3525_k4_margin :
    B_8_exact 4 (3525 : ℝ) (3550 : ℝ) ≤ (0.34182 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3525 : ℝ) (3550 : ℝ) 2 5088 2.1523e-15
    (0.34182 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3525_a2_le row3525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3525 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3525_k5_margin :
    B_8_exact 5 (3525 : ℝ) (3550 : ℝ) ≤ (1213.5 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3525 : ℝ) (3550 : ℝ) 2 5088 2.1523e-15
    (1213.5 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3525_a2_le row3525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3550 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3550_k1_margin :
    B_8_exact 1 (3550 : ℝ) (3575 : ℝ) ≤ (0.0000000000066608 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3550 : ℝ) (3575 : ℝ) 2 5124 1.8633e-15
    (0.0000000000066608 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3550_a2_le row3550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3550 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3550_k2_margin :
    B_8_exact 2 (3550 : ℝ) (3575 : ℝ) ≤ (0.000000023812 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3550 : ℝ) (3575 : ℝ) 2 5124 1.8633e-15
    (0.000000023812 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3550_a2_le row3550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3550 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3550_k3_margin :
    B_8_exact 3 (3550 : ℝ) (3575 : ℝ) ≤ (0.000085129 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3550 : ℝ) (3575 : ℝ) 2 5124 1.8633e-15
    (0.000085129 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3550_a2_le row3550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3550 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3550_k4_margin :
    B_8_exact 4 (3550 : ℝ) (3575 : ℝ) ≤ (0.30434 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3550 : ℝ) (3575 : ℝ) 2 5124 1.8633e-15
    (0.30434 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3550_a2_le row3550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3550 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3550_k5_margin :
    B_8_exact 5 (3550 : ℝ) (3575 : ℝ) ≤ (1088.0 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3550 : ℝ) (3575 : ℝ) 2 5124 1.8633e-15
    (1088.0 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3550_a2_le row3550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3575 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3575_k1_margin :
    B_8_exact 1 (3575 : ℝ) (3600 : ℝ) ≤ (0.0000000000058042 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3575 : ℝ) (3600 : ℝ) 2 5160 1.6124e-15
    (0.0000000000058042 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3575_a2_le row3575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3575 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3575_k2_margin :
    B_8_exact 2 (3575 : ℝ) (3600 : ℝ) ≤ (0.000000020895 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3575 : ℝ) (3600 : ℝ) 2 5160 1.6124e-15
    (0.000000020895 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3575_a2_le row3575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3575 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3575_k3_margin :
    B_8_exact 3 (3575 : ℝ) (3600 : ℝ) ≤ (0.000075222 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3575 : ℝ) (3600 : ℝ) 2 5160 1.6124e-15
    (0.000075222 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3575_a2_le row3575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3575 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3575_k4_margin :
    B_8_exact 4 (3575 : ℝ) (3600 : ℝ) ≤ (0.27080 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3575 : ℝ) (3600 : ℝ) 2 5160 1.6124e-15
    (0.27080 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3575_a2_le row3575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3575 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3575_k5_margin :
    B_8_exact 5 (3575 : ℝ) (3600 : ℝ) ≤ (974.88 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3575 : ℝ) (3600 : ℝ) 2 5160 1.6124e-15
    (974.88 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3575_a2_le row3575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3600_k1_margin :
    B_8_exact 1 (3600 : ℝ) (3625 : ℝ) ≤ (0.0000000000050621 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3600 : ℝ) (3625 : ℝ) 2 5196 1.3966e-15
    (0.0000000000050621 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3600_a2_le row3600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3600_k2_margin :
    B_8_exact 2 (3600 : ℝ) (3625 : ℝ) ≤ (0.000000018350 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3600 : ℝ) (3625 : ℝ) 2 5196 1.3966e-15
    (0.000000018350 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3600_a2_le row3600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3600_k3_margin :
    B_8_exact 3 (3600 : ℝ) (3625 : ℝ) ≤ (0.000066520 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3600 : ℝ) (3625 : ℝ) 2 5196 1.3966e-15
    (0.000066520 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3600_a2_le row3600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3600_k4_margin :
    B_8_exact 4 (3600 : ℝ) (3625 : ℝ) ≤ (0.24113 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3600 : ℝ) (3625 : ℝ) 2 5196 1.3966e-15
    (0.24113 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3600_a2_le row3600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3600_k5_margin :
    B_8_exact 5 (3600 : ℝ) (3625 : ℝ) ≤ (874.11 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3600 : ℝ) (3625 : ℝ) 2 5196 1.3966e-15
    (874.11 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3600_a2_le row3600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3625 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3625_k1_margin :
    B_8_exact 1 (3625 : ℝ) (3650 : ℝ) ≤ (0.0000000000044165 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3625 : ℝ) (3650 : ℝ) 2 5232 1.2101e-15
    (0.0000000000044165 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3625_a2_le row3625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3625 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3625_k2_margin :
    B_8_exact 2 (3625 : ℝ) (3650 : ℝ) ≤ (0.000000016120 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3625 : ℝ) (3650 : ℝ) 2 5232 1.2101e-15
    (0.000000016120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3625_a2_le row3625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3625 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3625_k3_margin :
    B_8_exact 3 (3625 : ℝ) (3650 : ℝ) ≤ (0.000058839 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3625 : ℝ) (3650 : ℝ) 2 5232 1.2101e-15
    (0.000058839 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3625_a2_le row3625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3625 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3625_k4_margin :
    B_8_exact 4 (3625 : ℝ) (3650 : ℝ) ≤ (0.21476 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3625 : ℝ) (3650 : ℝ) 2 5232 1.2101e-15
    (0.21476 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3625_a2_le row3625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3625 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3625_k5_margin :
    B_8_exact 5 (3625 : ℝ) (3650 : ℝ) ≤ (783.88 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3625 : ℝ) (3650 : ℝ) 2 5232 1.2101e-15
    (783.88 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3625_a2_le row3625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3650 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3650_k1_margin :
    B_8_exact 1 (3650 : ℝ) (3675 : ℝ) ≤ (0.0000000000038475 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3650 : ℝ) (3675 : ℝ) 2 5268 1.0470e-15
    (0.0000000000038475 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3650_a2_le row3650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3650 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3650_k2_margin :
    B_8_exact 2 (3650 : ℝ) (3675 : ℝ) ≤ (0.000000014140 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3650 : ℝ) (3675 : ℝ) 2 5268 1.0470e-15
    (0.000000014140 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3650_a2_le row3650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3650 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3650_k3_margin :
    B_8_exact 3 (3650 : ℝ) (3675 : ℝ) ≤ (0.000051963 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3650 : ℝ) (3675 : ℝ) 2 5268 1.0470e-15
    (0.000051963 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3650_a2_le row3650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3650 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3650_k4_margin :
    B_8_exact 4 (3650 : ℝ) (3675 : ℝ) ≤ (0.19096 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3650 : ℝ) (3675 : ℝ) 2 5268 1.0470e-15
    (0.19096 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3650_a2_le row3650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3650 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3650_k5_margin :
    B_8_exact 5 (3650 : ℝ) (3675 : ℝ) ≤ (701.79 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3650 : ℝ) (3675 : ℝ) 2 5268 1.0470e-15
    (701.79 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3650_a2_le row3650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3675 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3675_k1_margin :
    B_8_exact 1 (3675 : ℝ) (3700 : ℝ) ≤ (0.0000000000033560 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3675 : ℝ) (3700 : ℝ) 2 5304 9.0704e-16
    (0.0000000000033560 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3675_a2_le row3675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3675 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3675_k2_margin :
    B_8_exact 2 (3675 : ℝ) (3700 : ℝ) ≤ (0.000000012417 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3675 : ℝ) (3700 : ℝ) 2 5304 9.0704e-16
    (0.000000012417 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3675_a2_le row3675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3675 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3675_k3_margin :
    B_8_exact 3 (3675 : ℝ) (3700 : ℝ) ≤ (0.000045944 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3675 : ℝ) (3700 : ℝ) 2 5304 9.0704e-16
    (0.000045944 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3675_a2_le row3675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3675 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3675_k4_margin :
    B_8_exact 4 (3675 : ℝ) (3700 : ℝ) ≤ (0.16999 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3675 : ℝ) (3700 : ℝ) 2 5304 9.0704e-16
    (0.16999 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3675_a2_le row3675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3675 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3675_k5_margin :
    B_8_exact 5 (3675 : ℝ) (3700 : ℝ) ≤ (628.97 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3675 : ℝ) (3700 : ℝ) 2 5304 9.0704e-16
    (628.97 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3675_a2_le row3675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3700_k1_margin :
    B_8_exact 1 (3700 : ℝ) (3725 : ℝ) ≤ (0.0000000000029296 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3700 : ℝ) (3725 : ℝ) 2 5340 7.8647e-16
    (0.0000000000029296 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3700_a2_le row3700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3700_k2_margin :
    B_8_exact 2 (3700 : ℝ) (3725 : ℝ) ≤ (0.000000010913 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3700 : ℝ) (3725 : ℝ) 2 5340 7.8647e-16
    (0.000000010913 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3700_a2_le row3700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3700_k3_margin :
    B_8_exact 3 (3700 : ℝ) (3725 : ℝ) ≤ (0.000040649 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3700 : ℝ) (3725 : ℝ) 2 5340 7.8647e-16
    (0.000040649 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3700_a2_le row3700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3700_k4_margin :
    B_8_exact 4 (3700 : ℝ) (3725 : ℝ) ≤ (0.15142 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3700 : ℝ) (3725 : ℝ) 2 5340 7.8647e-16
    (0.15142 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3700_a2_le row3700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3700_k5_margin :
    B_8_exact 5 (3700 : ℝ) (3725 : ℝ) ≤ (564.04 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3700 : ℝ) (3725 : ℝ) 2 5340 7.8647e-16
    (564.04 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3700_a2_le row3700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3725 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3725_k1_margin :
    B_8_exact 1 (3725 : ℝ) (3750 : ℝ) ≤ (0.0000000000025580 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3725 : ℝ) (3750 : ℝ) 2 5377 6.8213e-16
    (0.0000000000025580 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3725_a2_le row3725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3725 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3725_k2_margin :
    B_8_exact 2 (3725 : ℝ) (3750 : ℝ) ≤ (0.0000000095924 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3725 : ℝ) (3750 : ℝ) 2 5377 6.8213e-16
    (0.0000000095924 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3725_a2_le row3725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3725 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3725_k3_margin :
    B_8_exact 3 (3725 : ℝ) (3750 : ℝ) ≤ (0.000035971 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3725 : ℝ) (3750 : ℝ) 2 5377 6.8213e-16
    (0.000035971 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3725_a2_le row3725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3725 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3725_k4_margin :
    B_8_exact 4 (3725 : ℝ) (3750 : ℝ) ≤ (0.13489 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3725 : ℝ) (3750 : ℝ) 2 5377 6.8213e-16
    (0.13489 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3725_a2_le row3725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3725 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3725_k5_margin :
    B_8_exact 5 (3725 : ℝ) (3750 : ℝ) ≤ (505.85 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3725 : ℝ) (3750 : ℝ) 2 5377 6.8213e-16
    (505.85 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3725_a2_le row3725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3750 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3750_k1_margin :
    B_8_exact 1 (3750 : ℝ) (3775 : ℝ) ≤ (0.0000000000022346 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3750 : ℝ) (3775 : ℝ) 2 5413 5.9196e-16
    (0.0000000000022346 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3750_a2_le row3750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3750 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3750_k2_margin :
    B_8_exact 2 (3750 : ℝ) (3775 : ℝ) ≤ (0.0000000084357 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3750 : ℝ) (3775 : ℝ) 2 5413 5.9196e-16
    (0.0000000084357 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3750_a2_le row3750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3750 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3750_k3_margin :
    B_8_exact 3 (3750 : ℝ) (3775 : ℝ) ≤ (0.000031845 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3750 : ℝ) (3775 : ℝ) 2 5413 5.9196e-16
    (0.000031845 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3750_a2_le row3750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3750 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3750_k4_margin :
    B_8_exact 4 (3750 : ℝ) (3775 : ℝ) ≤ (0.12022 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3750 : ℝ) (3775 : ℝ) 2 5413 5.9196e-16
    (0.12022 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3750_a2_le row3750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3750 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3750_k5_margin :
    B_8_exact 5 (3750 : ℝ) (3775 : ℝ) ≤ (453.81 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3750 : ℝ) (3775 : ℝ) 2 5413 5.9196e-16
    (453.81 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3750_a2_le row3750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3775 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3775_k1_margin :
    B_8_exact 1 (3775 : ℝ) (3800 : ℝ) ≤ (0.0000000000019513 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3775 : ℝ) (3800 : ℝ) 2 5449 5.1352e-16
    (0.0000000000019513 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3775_a2_le row3775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3775 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3775_k2_margin :
    B_8_exact 2 (3775 : ℝ) (3800 : ℝ) ≤ (0.0000000074151 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3775 : ℝ) (3800 : ℝ) 2 5449 5.1352e-16
    (0.0000000074151 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3775_a2_le row3775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3775 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3775_k3_margin :
    B_8_exact 3 (3775 : ℝ) (3800 : ℝ) ≤ (0.000028177 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3775 : ℝ) (3800 : ℝ) 2 5449 5.1352e-16
    (0.000028177 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3775_a2_le row3775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3775 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3775_k4_margin :
    B_8_exact 4 (3775 : ℝ) (3800 : ℝ) ≤ (0.10707 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3775 : ℝ) (3800 : ℝ) 2 5449 5.1352e-16
    (0.10707 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3775_a2_le row3775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3775 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3775_k5_margin :
    B_8_exact 5 (3775 : ℝ) (3800 : ℝ) ≤ (406.88 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3775 : ℝ) (3800 : ℝ) 2 5449 5.1352e-16
    (406.88 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3775_a2_le row3775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3800_k1_margin :
    B_8_exact 1 (3800 : ℝ) (3825 : ℝ) ≤ (0.0000000000017020 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3800 : ℝ) (3825 : ℝ) 2 5485 4.4496e-16
    (0.0000000000017020 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3800_a2_le row3800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3800_k2_margin :
    B_8_exact 2 (3800 : ℝ) (3825 : ℝ) ≤ (0.0000000065099 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3800 : ℝ) (3825 : ℝ) 2 5485 4.4496e-16
    (0.0000000065099 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3800_a2_le row3800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3800_k3_margin :
    B_8_exact 3 (3800 : ℝ) (3825 : ℝ) ≤ (0.000024901 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3800 : ℝ) (3825 : ℝ) 2 5485 4.4496e-16
    (0.000024901 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3800_a2_le row3800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3800_k4_margin :
    B_8_exact 4 (3800 : ℝ) (3825 : ℝ) ≤ (0.095244 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3800 : ℝ) (3825 : ℝ) 2 5485 4.4496e-16
    (0.095244 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3800_a2_le row3800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3800_k5_margin :
    B_8_exact 5 (3800 : ℝ) (3825 : ℝ) ≤ (364.31 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3800 : ℝ) (3825 : ℝ) 2 5485 4.4496e-16
    (364.31 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3800_a2_le row3800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3825 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3825_k1_margin :
    B_8_exact 1 (3825 : ℝ) (3850 : ℝ) ≤ (0.0000000000014854 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3825 : ℝ) (3850 : ℝ) 2 5521 3.8583e-16
    (0.0000000000014854 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3825_a2_le row3825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3825 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3825_k2_margin :
    B_8_exact 2 (3825 : ℝ) (3850 : ℝ) ≤ (0.0000000057189 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3825 : ℝ) (3850 : ℝ) 2 5521 3.8583e-16
    (0.0000000057189 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3825_a2_le row3825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3825 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3825_k3_margin :
    B_8_exact 3 (3825 : ℝ) (3850 : ℝ) ≤ (0.000022018 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3825 : ℝ) (3850 : ℝ) 2 5521 3.8583e-16
    (0.000022018 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3825_a2_le row3825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3825 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3825_k4_margin :
    B_8_exact 4 (3825 : ℝ) (3850 : ℝ) ≤ (0.084768 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3825 : ℝ) (3850 : ℝ) 2 5521 3.8583e-16
    (0.084768 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3825_a2_le row3825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3825 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3825_k5_margin :
    B_8_exact 5 (3825 : ℝ) (3850 : ℝ) ≤ (326.36 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3825 : ℝ) (3850 : ℝ) 2 5521 3.8583e-16
    (326.36 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3825_a2_le row3825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3850 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3850_k1_margin :
    B_8_exact 1 (3850 : ℝ) (3875 : ℝ) ≤ (0.0000000000012972 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3850 : ℝ) (3875 : ℝ) 2 5557 3.3477e-16
    (0.0000000000012972 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3850_a2_le row3850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3850 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3850_k2_margin :
    B_8_exact 2 (3850 : ℝ) (3875 : ℝ) ≤ (0.0000000050267 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3850 : ℝ) (3875 : ℝ) 2 5557 3.3477e-16
    (0.0000000050267 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3850_a2_le row3850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3850 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3850_k3_margin :
    B_8_exact 3 (3850 : ℝ) (3875 : ℝ) ≤ (0.000019478 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3850 : ℝ) (3875 : ℝ) 2 5557 3.3477e-16
    (0.000019478 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3850_a2_le row3850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3850 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3850_k4_margin :
    B_8_exact 4 (3850 : ℝ) (3875 : ℝ) ≤ (0.075479 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3850 : ℝ) (3875 : ℝ) 2 5557 3.3477e-16
    (0.075479 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3850_a2_le row3850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3850 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3850_k5_margin :
    B_8_exact 5 (3850 : ℝ) (3875 : ℝ) ≤ (292.48 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3850 : ℝ) (3875 : ℝ) 2 5557 3.3477e-16
    (292.48 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3850_a2_le row3850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3875 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3875_k1_margin :
    B_8_exact 1 (3875 : ℝ) (3900 : ℝ) ≤ (0.0000000000011314 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3875 : ℝ) (3900 : ℝ) 2 5593 2.9011e-16
    (0.0000000000011314 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3875_a2_le row3875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3875 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3875_k2_margin :
    B_8_exact 2 (3875 : ℝ) (3900 : ℝ) ≤ (0.0000000044124 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3875 : ℝ) (3900 : ℝ) 2 5593 2.9011e-16
    (0.0000000044124 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3875_a2_le row3875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3875 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3875_k3_margin :
    B_8_exact 3 (3875 : ℝ) (3900 : ℝ) ≤ (0.000017208 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3875 : ℝ) (3900 : ℝ) 2 5593 2.9011e-16
    (0.000017208 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3875_a2_le row3875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3875 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3875_k4_margin :
    B_8_exact 4 (3875 : ℝ) (3900 : ℝ) ≤ (0.067112 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3875 : ℝ) (3900 : ℝ) 2 5593 2.9011e-16
    (0.067112 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3875_a2_le row3875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 3875 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3875_k5_margin :
    B_8_exact 5 (3875 : ℝ) (3900 : ℝ) ≤ (261.74 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3875 : ℝ) (3900 : ℝ) 2 5593 2.9011e-16
    (261.74 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3875_a2_le row3875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
