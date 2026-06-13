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

private lemma row2900_a2_le : Inputs.default.a₂ (2900 : ℝ) ≤ (4186 : ℝ) := by
  have h := a2_crude_le (2900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2900 : ℝ) / log 2⌋₊ : ℝ) ≤ (2900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2900 : ℝ) / log 2 ≤ 4184 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4184 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4186 := by norm_num

private lemma row2925_a2_le : Inputs.default.a₂ (2925 : ℝ) ≤ (4222 : ℝ) := by
  have h := a2_crude_le (2925 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2925 : ℝ) / log 2⌋₊ : ℝ) ≤ (2925 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2925 : ℝ) / log 2 ≤ 4220 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2925 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2925 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4220 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4222 := by norm_num

private lemma row2950_a2_le : Inputs.default.a₂ (2950 : ℝ) ≤ (4258 : ℝ) := by
  have h := a2_crude_le (2950 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2950 : ℝ) / log 2⌋₊ : ℝ) ≤ (2950 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2950 : ℝ) / log 2 ≤ 4256 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2950 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2950 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4256 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4258 := by norm_num

private lemma row2975_a2_le : Inputs.default.a₂ (2975 : ℝ) ≤ (4295 : ℝ) := by
  have h := a2_crude_le (2975 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2975 : ℝ) / log 2⌋₊ : ℝ) ≤ (2975 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2975 : ℝ) / log 2 ≤ 4293 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2975 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2975 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4293 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4295 := by norm_num

private lemma row3000_a2_le : Inputs.default.a₂ (3000 : ℝ) ≤ (4331 : ℝ) := by
  have h := a2_crude_le (3000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3000 : ℝ) / log 2⌋₊ : ℝ) ≤ (3000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3000 : ℝ) / log 2 ≤ 4329 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4329 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4331 := by norm_num

private lemma row3025_a2_le : Inputs.default.a₂ (3025 : ℝ) ≤ (4367 : ℝ) := by
  have h := a2_crude_le (3025 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3025 : ℝ) / log 2⌋₊ : ℝ) ≤ (3025 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3025 : ℝ) / log 2 ≤ 4365 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3025 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3025 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4365 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4367 := by norm_num

private lemma row3050_a2_le : Inputs.default.a₂ (3050 : ℝ) ≤ (4403 : ℝ) := by
  have h := a2_crude_le (3050 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3050 : ℝ) / log 2⌋₊ : ℝ) ≤ (3050 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3050 : ℝ) / log 2 ≤ 4401 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3050 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3050 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4401 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4403 := by norm_num

private lemma row3075_a2_le : Inputs.default.a₂ (3075 : ℝ) ≤ (4439 : ℝ) := by
  have h := a2_crude_le (3075 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3075 : ℝ) / log 2⌋₊ : ℝ) ≤ (3075 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3075 : ℝ) / log 2 ≤ 4437 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3075 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3075 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4437 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4439 := by norm_num

private lemma row3100_a2_le : Inputs.default.a₂ (3100 : ℝ) ≤ (4475 : ℝ) := by
  have h := a2_crude_le (3100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3100 : ℝ) / log 2⌋₊ : ℝ) ≤ (3100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3100 : ℝ) / log 2 ≤ 4473 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4473 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4475 := by norm_num

private lemma row3125_a2_le : Inputs.default.a₂ (3125 : ℝ) ≤ (4511 : ℝ) := by
  have h := a2_crude_le (3125 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3125 : ℝ) / log 2⌋₊ : ℝ) ≤ (3125 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3125 : ℝ) / log 2 ≤ 4509 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3125 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3125 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4509 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4511 := by norm_num

private lemma row3150_a2_le : Inputs.default.a₂ (3150 : ℝ) ≤ (4547 : ℝ) := by
  have h := a2_crude_le (3150 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3150 : ℝ) / log 2⌋₊ : ℝ) ≤ (3150 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3150 : ℝ) / log 2 ≤ 4545 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3150 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3150 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4545 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4547 := by norm_num

private lemma row3175_a2_le : Inputs.default.a₂ (3175 : ℝ) ≤ (4583 : ℝ) := by
  have h := a2_crude_le (3175 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3175 : ℝ) / log 2⌋₊ : ℝ) ≤ (3175 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3175 : ℝ) / log 2 ≤ 4581 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3175 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3175 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4581 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4583 := by norm_num

private lemma row3200_a2_le : Inputs.default.a₂ (3200 : ℝ) ≤ (4619 : ℝ) := by
  have h := a2_crude_le (3200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3200 : ℝ) / log 2⌋₊ : ℝ) ≤ (3200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3200 : ℝ) / log 2 ≤ 4617 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4617 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4619 := by norm_num

private lemma row3225_a2_le : Inputs.default.a₂ (3225 : ℝ) ≤ (4655 : ℝ) := by
  have h := a2_crude_le (3225 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3225 : ℝ) / log 2⌋₊ : ℝ) ≤ (3225 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3225 : ℝ) / log 2 ≤ 4653 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3225 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3225 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4653 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4655 := by norm_num

private lemma row3250_a2_le : Inputs.default.a₂ (3250 : ℝ) ≤ (4691 : ℝ) := by
  have h := a2_crude_le (3250 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3250 : ℝ) / log 2⌋₊ : ℝ) ≤ (3250 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3250 : ℝ) / log 2 ≤ 4689 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3250 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3250 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4689 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4691 := by norm_num

private lemma row3275_a2_le : Inputs.default.a₂ (3275 : ℝ) ≤ (4727 : ℝ) := by
  have h := a2_crude_le (3275 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3275 : ℝ) / log 2⌋₊ : ℝ) ≤ (3275 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3275 : ℝ) / log 2 ≤ 4725 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3275 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3275 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4725 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4727 := by norm_num

private lemma row3300_a2_le : Inputs.default.a₂ (3300 : ℝ) ≤ (4763 : ℝ) := by
  have h := a2_crude_le (3300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3300 : ℝ) / log 2⌋₊ : ℝ) ≤ (3300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3300 : ℝ) / log 2 ≤ 4761 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4761 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4763 := by norm_num

private lemma row3325_a2_le : Inputs.default.a₂ (3325 : ℝ) ≤ (4799 : ℝ) := by
  have h := a2_crude_le (3325 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3325 : ℝ) / log 2⌋₊ : ℝ) ≤ (3325 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3325 : ℝ) / log 2 ≤ 4797 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3325 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3325 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4797 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4799 := by norm_num

private lemma row3350_a2_le : Inputs.default.a₂ (3350 : ℝ) ≤ (4836 : ℝ) := by
  have h := a2_crude_le (3350 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3350 : ℝ) / log 2⌋₊ : ℝ) ≤ (3350 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3350 : ℝ) / log 2 ≤ 4834 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3350 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3350 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4834 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4836 := by norm_num

private lemma row3375_a2_le : Inputs.default.a₂ (3375 : ℝ) ≤ (4872 : ℝ) := by
  have h := a2_crude_le (3375 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(3375 : ℝ) / log 2⌋₊ : ℝ) ≤ (3375 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (3375 : ℝ) / log 2 ≤ 4870 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (3375 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(3375 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (4870 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 4872 := by norm_num

set_option maxRecDepth 10000 in
private lemma row2900_table8_mem : (2900, 8.3167e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2900_eps_le : Inputs.default.ε (2900 : ℝ) ≤ 8.3167e-14 := by
  change BKLNW_app.table_8_ε (2900 : ℝ) ≤ 8.3167e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2900)
    (ε := 8.3167e-14) row2900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2925_table8_mem : (2925, 7.1662e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2925_eps_le : Inputs.default.ε (2925 : ℝ) ≤ 7.1662e-14 := by
  change BKLNW_app.table_8_ε (2925 : ℝ) ≤ 7.1662e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2925)
    (ε := 7.1662e-14) row2925_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2950_table8_mem : (2950, 6.1818e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2950_eps_le : Inputs.default.ε (2950 : ℝ) ≤ 6.1818e-14 := by
  change BKLNW_app.table_8_ε (2950 : ℝ) ≤ 6.1818e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2950)
    (ε := 6.1818e-14) row2950_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2975_table8_mem : (2975, 5.3383e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2975_eps_le : Inputs.default.ε (2975 : ℝ) ≤ 5.3383e-14 := by
  change BKLNW_app.table_8_ε (2975 : ℝ) ≤ 5.3383e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2975)
    (ε := 5.3383e-14) row2975_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3000_table8_mem : (3000, 4.5998e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3000_eps_le : Inputs.default.ε (3000 : ℝ) ≤ 4.5998e-14 := by
  change BKLNW_app.table_8_ε (3000 : ℝ) ≤ 4.5998e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3000)
    (ε := 4.5998e-14) row3000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3025_table8_mem : (3025, 3.9721e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3025_eps_le : Inputs.default.ε (3025 : ℝ) ≤ 3.9721e-14 := by
  change BKLNW_app.table_8_ε (3025 : ℝ) ≤ 3.9721e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3025)
    (ε := 3.9721e-14) row3025_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3050_table8_mem : (3050, 3.4247e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3050_eps_le : Inputs.default.ε (3050 : ℝ) ≤ 3.4247e-14 := by
  change BKLNW_app.table_8_ε (3050 : ℝ) ≤ 3.4247e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3050)
    (ε := 3.4247e-14) row3050_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3075_table8_mem : (3075, 2.9576e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3075_eps_le : Inputs.default.ε (3075 : ℝ) ≤ 2.9576e-14 := by
  change BKLNW_app.table_8_ε (3075 : ℝ) ≤ 2.9576e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3075)
    (ε := 2.9576e-14) row3075_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3100_table8_mem : (3100, 2.5535e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3100_eps_le : Inputs.default.ε (3100 : ℝ) ≤ 2.5535e-14 := by
  change BKLNW_app.table_8_ε (3100 : ℝ) ≤ 2.5535e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3100)
    (ε := 2.5535e-14) row3100_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3125_table8_mem : (3125, 2.2031e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3125_eps_le : Inputs.default.ε (3125 : ℝ) ≤ 2.2031e-14 := by
  change BKLNW_app.table_8_ε (3125 : ℝ) ≤ 2.2031e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3125)
    (ε := 2.2031e-14) row3125_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3150_table8_mem : (3150, 1.9028e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3150_eps_le : Inputs.default.ε (3150 : ℝ) ≤ 1.9028e-14 := by
  change BKLNW_app.table_8_ε (3150 : ℝ) ≤ 1.9028e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3150)
    (ε := 1.9028e-14) row3150_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3175_table8_mem : (3175, 1.6430e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3175_eps_le : Inputs.default.ε (3175 : ℝ) ≤ 1.6430e-14 := by
  change BKLNW_app.table_8_ε (3175 : ℝ) ≤ 1.6430e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3175)
    (ε := 1.6430e-14) row3175_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3200_table8_mem : (3200, 1.4197e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3200_eps_le : Inputs.default.ε (3200 : ℝ) ≤ 1.4197e-14 := by
  change BKLNW_app.table_8_ε (3200 : ℝ) ≤ 1.4197e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3200)
    (ε := 1.4197e-14) row3200_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3225_table8_mem : (3225, 1.2278e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3225_eps_le : Inputs.default.ε (3225 : ℝ) ≤ 1.2278e-14 := by
  change BKLNW_app.table_8_ε (3225 : ℝ) ≤ 1.2278e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3225)
    (ε := 1.2278e-14) row3225_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3250_table8_mem : (3250, 1.0627e-14) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3250_eps_le : Inputs.default.ε (3250 : ℝ) ≤ 1.0627e-14 := by
  change BKLNW_app.table_8_ε (3250 : ℝ) ≤ 1.0627e-14
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3250)
    (ε := 1.0627e-14) row3250_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3275_table8_mem : (3275, 9.1915e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3275_eps_le : Inputs.default.ε (3275 : ℝ) ≤ 9.1915e-15 := by
  change BKLNW_app.table_8_ε (3275 : ℝ) ≤ 9.1915e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3275)
    (ε := 9.1915e-15) row3275_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3300_table8_mem : (3300, 7.9435e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3300_eps_le : Inputs.default.ε (3300 : ℝ) ≤ 7.9435e-15 := by
  change BKLNW_app.table_8_ε (3300 : ℝ) ≤ 7.9435e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3300)
    (ε := 7.9435e-15) row3300_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3325_table8_mem : (3325, 6.8702e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3325_eps_le : Inputs.default.ε (3325 : ℝ) ≤ 6.8702e-15 := by
  change BKLNW_app.table_8_ε (3325 : ℝ) ≤ 6.8702e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3325)
    (ε := 6.8702e-15) row3325_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3350_table8_mem : (3350, 5.9387e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3350_eps_le : Inputs.default.ε (3350 : ℝ) ≤ 5.9387e-15 := by
  change BKLNW_app.table_8_ε (3350 : ℝ) ≤ 5.9387e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3350)
    (ε := 5.9387e-15) row3350_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row3375_table8_mem : (3375, 5.1333e-15) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row3375_eps_le : Inputs.default.ε (3375 : ℝ) ≤ 5.1333e-15 := by
  change BKLNW_app.table_8_ε (3375 : ℝ) ≤ 5.1333e-15
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 3375)
    (ε := 5.1333e-15) row3375_table8_mem (by norm_num)

/-- Row 2900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2900_k1_margin :
    B_8_exact 1 (2900 : ℝ) (2925 : ℝ) ≤ (0.00000000024326 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2900 : ℝ) (2925 : ℝ) 2 4186 8.3167e-14
    (0.00000000024326 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2900_a2_le row2900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1450_lt, LogTables.exp_neg_5800_3_lt,
                   Real.exp_pos (-(1450:ℝ)), Real.exp_pos (-(5800/3:ℝ))])

/-- Row 2900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2900_k2_margin :
    B_8_exact 2 (2900 : ℝ) (2925 : ℝ) ≤ (0.00000071154 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2900 : ℝ) (2925 : ℝ) 2 4186 8.3167e-14
    (0.00000071154 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2900_a2_le row2900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1450_lt, LogTables.exp_neg_5800_3_lt,
                   Real.exp_pos (-(1450:ℝ)), Real.exp_pos (-(5800/3:ℝ))])

/-- Row 2900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2900_k3_margin :
    B_8_exact 3 (2900 : ℝ) (2925 : ℝ) ≤ (0.0020813 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2900 : ℝ) (2925 : ℝ) 2 4186 8.3167e-14
    (0.0020813 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2900_a2_le row2900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1450_lt, LogTables.exp_neg_5800_3_lt,
                   Real.exp_pos (-(1450:ℝ)), Real.exp_pos (-(5800/3:ℝ))])

/-- Row 2900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2900_k4_margin :
    B_8_exact 4 (2900 : ℝ) (2925 : ℝ) ≤ (6.0877 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2900 : ℝ) (2925 : ℝ) 2 4186 8.3167e-14
    (6.0877 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2900_a2_le row2900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1450_lt, LogTables.exp_neg_5800_3_lt,
                   Real.exp_pos (-(1450:ℝ)), Real.exp_pos (-(5800/3:ℝ))])

/-- Row 2900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2900_k5_margin :
    B_8_exact 5 (2900 : ℝ) (2925 : ℝ) ≤ (17806 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2900 : ℝ) (2925 : ℝ) 2 4186 8.3167e-14
    (17806 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2900_a2_le row2900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1450_lt, LogTables.exp_neg_5800_3_lt,
                   Real.exp_pos (-(1450:ℝ)), Real.exp_pos (-(5800/3:ℝ))])

/-- Row 2925 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2925_k1_margin :
    B_8_exact 1 (2925 : ℝ) (2950 : ℝ) ≤ (0.00000000021140 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2925 : ℝ) (2950 : ℝ) 2 4222 7.1662e-14
    (0.00000000021140 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2925_a2_le row2925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2925_2_lt, LogTables.exp_neg_1950_lt,
                   Real.exp_pos (-(2925/2:ℝ)), Real.exp_pos (-(1950:ℝ))])

/-- Row 2925 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2925_k2_margin :
    B_8_exact 2 (2925 : ℝ) (2950 : ℝ) ≤ (0.00000062363 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2925 : ℝ) (2950 : ℝ) 2 4222 7.1662e-14
    (0.00000062363 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2925_a2_le row2925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2925_2_lt, LogTables.exp_neg_1950_lt,
                   Real.exp_pos (-(2925/2:ℝ)), Real.exp_pos (-(1950:ℝ))])

/-- Row 2925 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2925_k3_margin :
    B_8_exact 3 (2925 : ℝ) (2950 : ℝ) ≤ (0.0018397 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2925 : ℝ) (2950 : ℝ) 2 4222 7.1662e-14
    (0.0018397 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2925_a2_le row2925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2925_2_lt, LogTables.exp_neg_1950_lt,
                   Real.exp_pos (-(2925/2:ℝ)), Real.exp_pos (-(1950:ℝ))])

/-- Row 2925 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2925_k4_margin :
    B_8_exact 4 (2925 : ℝ) (2950 : ℝ) ≤ (5.4272 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2925 : ℝ) (2950 : ℝ) 2 4222 7.1662e-14
    (5.4272 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2925_a2_le row2925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2925_2_lt, LogTables.exp_neg_1950_lt,
                   Real.exp_pos (-(2925/2:ℝ)), Real.exp_pos (-(1950:ℝ))])

/-- Row 2925 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2925_k5_margin :
    B_8_exact 5 (2925 : ℝ) (2950 : ℝ) ≤ (16010 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2925 : ℝ) (2950 : ℝ) 2 4222 7.1662e-14
    (16010 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2925_a2_le row2925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2925_2_lt, LogTables.exp_neg_1950_lt,
                   Real.exp_pos (-(2925/2:ℝ)), Real.exp_pos (-(1950:ℝ))])

/-- Row 2950 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2950_k1_margin :
    B_8_exact 1 (2950 : ℝ) (2975 : ℝ) ≤ (0.00000000018391 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2950 : ℝ) (2975 : ℝ) 2 4258 6.1818e-14
    (0.00000000018391 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2950_a2_le row2950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1475_lt, LogTables.exp_neg_5900_3_lt,
                   Real.exp_pos (-(1475:ℝ)), Real.exp_pos (-(5900/3:ℝ))])

/-- Row 2950 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2950_k2_margin :
    B_8_exact 2 (2950 : ℝ) (2975 : ℝ) ≤ (0.00000054712 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2950 : ℝ) (2975 : ℝ) 2 4258 6.1818e-14
    (0.00000054712 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2950_a2_le row2950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1475_lt, LogTables.exp_neg_5900_3_lt,
                   Real.exp_pos (-(1475:ℝ)), Real.exp_pos (-(5900/3:ℝ))])

/-- Row 2950 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2950_k3_margin :
    B_8_exact 3 (2950 : ℝ) (2975 : ℝ) ≤ (0.0016277 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2950 : ℝ) (2975 : ℝ) 2 4258 6.1818e-14
    (0.0016277 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2950_a2_le row2950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1475_lt, LogTables.exp_neg_5900_3_lt,
                   Real.exp_pos (-(1475:ℝ)), Real.exp_pos (-(5900/3:ℝ))])

/-- Row 2950 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2950_k4_margin :
    B_8_exact 4 (2950 : ℝ) (2975 : ℝ) ≤ (4.8423 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2950 : ℝ) (2975 : ℝ) 2 4258 6.1818e-14
    (4.8423 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2950_a2_le row2950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1475_lt, LogTables.exp_neg_5900_3_lt,
                   Real.exp_pos (-(1475:ℝ)), Real.exp_pos (-(5900/3:ℝ))])

/-- Row 2950 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2950_k5_margin :
    B_8_exact 5 (2950 : ℝ) (2975 : ℝ) ≤ (14406 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2950 : ℝ) (2975 : ℝ) 2 4258 6.1818e-14
    (14406 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2950_a2_le row2950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1475_lt, LogTables.exp_neg_5900_3_lt,
                   Real.exp_pos (-(1475:ℝ)), Real.exp_pos (-(5900/3:ℝ))])

/-- Row 2975 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2975_k1_margin :
    B_8_exact 1 (2975 : ℝ) (3000 : ℝ) ≤ (0.00000000016015 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2975 : ℝ) (3000 : ℝ) 2 4295 5.3383e-14
    (0.00000000016015 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2975_a2_le row2975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2975_2_lt, LogTables.exp_neg_5950_3_lt,
                   Real.exp_pos (-(2975/2:ℝ)), Real.exp_pos (-(5950/3:ℝ))])

/-- Row 2975 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2975_k2_margin :
    B_8_exact 2 (2975 : ℝ) (3000 : ℝ) ≤ (0.00000048044 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2975 : ℝ) (3000 : ℝ) 2 4295 5.3383e-14
    (0.00000048044 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2975_a2_le row2975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2975_2_lt, LogTables.exp_neg_5950_3_lt,
                   Real.exp_pos (-(2975/2:ℝ)), Real.exp_pos (-(5950/3:ℝ))])

/-- Row 2975 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2975_k3_margin :
    B_8_exact 3 (2975 : ℝ) (3000 : ℝ) ≤ (0.0014413 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2975 : ℝ) (3000 : ℝ) 2 4295 5.3383e-14
    (0.0014413 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2975_a2_le row2975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2975_2_lt, LogTables.exp_neg_5950_3_lt,
                   Real.exp_pos (-(2975/2:ℝ)), Real.exp_pos (-(5950/3:ℝ))])

/-- Row 2975 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2975_k4_margin :
    B_8_exact 4 (2975 : ℝ) (3000 : ℝ) ≤ (4.3240 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2975 : ℝ) (3000 : ℝ) 2 4295 5.3383e-14
    (4.3240 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2975_a2_le row2975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2975_2_lt, LogTables.exp_neg_5950_3_lt,
                   Real.exp_pos (-(2975/2:ℝ)), Real.exp_pos (-(5950/3:ℝ))])

/-- Row 2975 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2975_k5_margin :
    B_8_exact 5 (2975 : ℝ) (3000 : ℝ) ≤ (12972 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2975 : ℝ) (3000 : ℝ) 2 4295 5.3383e-14
    (12972 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2975_a2_le row2975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2975_2_lt, LogTables.exp_neg_5950_3_lt,
                   Real.exp_pos (-(2975/2:ℝ)), Real.exp_pos (-(5950/3:ℝ))])

/-- Row 3000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3000_k1_margin :
    B_8_exact 1 (3000 : ℝ) (3025 : ℝ) ≤ (0.00000000013914 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3000 : ℝ) (3025 : ℝ) 2 4331 4.5998e-14
    (0.00000000013914 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3000_a2_le row3000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1500_lt, LogTables.exp_neg_2000_lt,
                   Real.exp_pos (-(1500:ℝ)), Real.exp_pos (-(2000:ℝ))])

/-- Row 3000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3000_k2_margin :
    B_8_exact 2 (3000 : ℝ) (3025 : ℝ) ≤ (0.00000042090 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3000 : ℝ) (3025 : ℝ) 2 4331 4.5998e-14
    (0.00000042090 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3000_a2_le row3000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1500_lt, LogTables.exp_neg_2000_lt,
                   Real.exp_pos (-(1500:ℝ)), Real.exp_pos (-(2000:ℝ))])

/-- Row 3000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3000_k3_margin :
    B_8_exact 3 (3000 : ℝ) (3025 : ℝ) ≤ (0.0012732 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3000 : ℝ) (3025 : ℝ) 2 4331 4.5998e-14
    (0.0012732 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3000_a2_le row3000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1500_lt, LogTables.exp_neg_2000_lt,
                   Real.exp_pos (-(1500:ℝ)), Real.exp_pos (-(2000:ℝ))])

/-- Row 3000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3000_k4_margin :
    B_8_exact 4 (3000 : ℝ) (3025 : ℝ) ≤ (3.8515 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3000 : ℝ) (3025 : ℝ) 2 4331 4.5998e-14
    (3.8515 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3000_a2_le row3000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1500_lt, LogTables.exp_neg_2000_lt,
                   Real.exp_pos (-(1500:ℝ)), Real.exp_pos (-(2000:ℝ))])

/-- Row 3000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3000_k5_margin :
    B_8_exact 5 (3000 : ℝ) (3025 : ℝ) ≤ (11651 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3000 : ℝ) (3025 : ℝ) 2 4331 4.5998e-14
    (11651 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3000_a2_le row3000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1500_lt, LogTables.exp_neg_2000_lt,
                   Real.exp_pos (-(1500:ℝ)), Real.exp_pos (-(2000:ℝ))])

/-- Row 3025 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3025_k1_margin :
    B_8_exact 1 (3025 : ℝ) (3050 : ℝ) ≤ (0.00000000012115 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3025 : ℝ) (3050 : ℝ) 2 4367 3.9721e-14
    (0.00000000012115 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3025_a2_le row3025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3025_2_lt, LogTables.exp_neg_6050_3_lt,
                   Real.exp_pos (-(3025/2:ℝ)), Real.exp_pos (-(6050/3:ℝ))])

/-- Row 3025 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3025_k2_margin :
    B_8_exact 2 (3025 : ℝ) (3050 : ℝ) ≤ (0.00000036949 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3025 : ℝ) (3050 : ℝ) 2 4367 3.9721e-14
    (0.00000036949 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3025_a2_le row3025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3025_2_lt, LogTables.exp_neg_6050_3_lt,
                   Real.exp_pos (-(3025/2:ℝ)), Real.exp_pos (-(6050/3:ℝ))])

/-- Row 3025 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3025_k3_margin :
    B_8_exact 3 (3025 : ℝ) (3050 : ℝ) ≤ (0.0011270 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3025 : ℝ) (3050 : ℝ) 2 4367 3.9721e-14
    (0.0011270 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3025_a2_le row3025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3025_2_lt, LogTables.exp_neg_6050_3_lt,
                   Real.exp_pos (-(3025/2:ℝ)), Real.exp_pos (-(6050/3:ℝ))])

/-- Row 3025 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3025_k4_margin :
    B_8_exact 4 (3025 : ℝ) (3050 : ℝ) ≤ (3.4372 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3025 : ℝ) (3050 : ℝ) 2 4367 3.9721e-14
    (3.4372 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3025_a2_le row3025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3025_2_lt, LogTables.exp_neg_6050_3_lt,
                   Real.exp_pos (-(3025/2:ℝ)), Real.exp_pos (-(6050/3:ℝ))])

/-- Row 3025 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3025_k5_margin :
    B_8_exact 5 (3025 : ℝ) (3050 : ℝ) ≤ (10484 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3025 : ℝ) (3050 : ℝ) 2 4367 3.9721e-14
    (10484 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3025_a2_le row3025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3025_2_lt, LogTables.exp_neg_6050_3_lt,
                   Real.exp_pos (-(3025/2:ℝ)), Real.exp_pos (-(6050/3:ℝ))])

/-- Row 3050 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3050_k1_margin :
    B_8_exact 1 (3050 : ℝ) (3075 : ℝ) ≤ (0.00000000010531 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3050 : ℝ) (3075 : ℝ) 2 4403 3.4247e-14
    (0.00000000010531 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3050_a2_le row3050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1525_lt, LogTables.exp_neg_6100_3_lt,
                   Real.exp_pos (-(1525:ℝ)), Real.exp_pos (-(6100/3:ℝ))])

/-- Row 3050 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3050_k2_margin :
    B_8_exact 2 (3050 : ℝ) (3075 : ℝ) ≤ (0.00000032382 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3050 : ℝ) (3075 : ℝ) 2 4403 3.4247e-14
    (0.00000032382 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3050_a2_le row3050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1525_lt, LogTables.exp_neg_6100_3_lt,
                   Real.exp_pos (-(1525:ℝ)), Real.exp_pos (-(6100/3:ℝ))])

/-- Row 3050 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3050_k3_margin :
    B_8_exact 3 (3050 : ℝ) (3075 : ℝ) ≤ (0.00099573 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3050 : ℝ) (3075 : ℝ) 2 4403 3.4247e-14
    (0.00099573 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3050_a2_le row3050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1525_lt, LogTables.exp_neg_6100_3_lt,
                   Real.exp_pos (-(1525:ℝ)), Real.exp_pos (-(6100/3:ℝ))])

/-- Row 3050 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3050_k4_margin :
    B_8_exact 4 (3050 : ℝ) (3075 : ℝ) ≤ (3.0619 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3050 : ℝ) (3075 : ℝ) 2 4403 3.4247e-14
    (3.0619 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3050_a2_le row3050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1525_lt, LogTables.exp_neg_6100_3_lt,
                   Real.exp_pos (-(1525:ℝ)), Real.exp_pos (-(6100/3:ℝ))])

/-- Row 3050 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3050_k5_margin :
    B_8_exact 5 (3050 : ℝ) (3075 : ℝ) ≤ (9415.2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3050 : ℝ) (3075 : ℝ) 2 4403 3.4247e-14
    (9415.2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3050_a2_le row3050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1525_lt, LogTables.exp_neg_6100_3_lt,
                   Real.exp_pos (-(1525:ℝ)), Real.exp_pos (-(6100/3:ℝ))])

/-- Row 3075 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3075_k1_margin :
    B_8_exact 1 (3075 : ℝ) (3100 : ℝ) ≤ (0.000000000091684 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3075 : ℝ) (3100 : ℝ) 2 4439 2.9576e-14
    (0.000000000091684 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3075_a2_le row3075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3075_2_lt, LogTables.exp_neg_2050_lt,
                   Real.exp_pos (-(3075/2:ℝ)), Real.exp_pos (-(2050:ℝ))])

/-- Row 3075 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3075_k2_margin :
    B_8_exact 2 (3075 : ℝ) (3100 : ℝ) ≤ (0.00000028422 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3075 : ℝ) (3100 : ℝ) 2 4439 2.9576e-14
    (0.00000028422 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3075_a2_le row3075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3075_2_lt, LogTables.exp_neg_2050_lt,
                   Real.exp_pos (-(3075/2:ℝ)), Real.exp_pos (-(2050:ℝ))])

/-- Row 3075 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3075_k3_margin :
    B_8_exact 3 (3075 : ℝ) (3100 : ℝ) ≤ (0.00088108 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3075 : ℝ) (3100 : ℝ) 2 4439 2.9576e-14
    (0.00088108 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3075_a2_le row3075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3075_2_lt, LogTables.exp_neg_2050_lt,
                   Real.exp_pos (-(3075/2:ℝ)), Real.exp_pos (-(2050:ℝ))])

/-- Row 3075 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3075_k4_margin :
    B_8_exact 4 (3075 : ℝ) (3100 : ℝ) ≤ (2.7314 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3075 : ℝ) (3100 : ℝ) 2 4439 2.9576e-14
    (2.7314 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3075_a2_le row3075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3075_2_lt, LogTables.exp_neg_2050_lt,
                   Real.exp_pos (-(3075/2:ℝ)), Real.exp_pos (-(2050:ℝ))])

/-- Row 3075 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3075_k5_margin :
    B_8_exact 5 (3075 : ℝ) (3100 : ℝ) ≤ (8467.2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3075 : ℝ) (3100 : ℝ) 2 4439 2.9576e-14
    (8467.2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3075_a2_le row3075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3075_2_lt, LogTables.exp_neg_2050_lt,
                   Real.exp_pos (-(3075/2:ℝ)), Real.exp_pos (-(2050:ℝ))])

/-- Row 3100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3100_k1_margin :
    B_8_exact 1 (3100 : ℝ) (3125 : ℝ) ≤ (0.000000000079793 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3100 : ℝ) (3125 : ℝ) 2 4475 2.5535e-14
    (0.000000000079793 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3100_a2_le row3100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1550_lt, LogTables.exp_neg_6200_3_lt,
                   Real.exp_pos (-(1550:ℝ)), Real.exp_pos (-(6200/3:ℝ))])

/-- Row 3100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3100_k2_margin :
    B_8_exact 2 (3100 : ℝ) (3125 : ℝ) ≤ (0.00000024935 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3100 : ℝ) (3125 : ℝ) 2 4475 2.5535e-14
    (0.00000024935 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3100_a2_le row3100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1550_lt, LogTables.exp_neg_6200_3_lt,
                   Real.exp_pos (-(1550:ℝ)), Real.exp_pos (-(6200/3:ℝ))])

/-- Row 3100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3100_k3_margin :
    B_8_exact 3 (3100 : ℝ) (3125 : ℝ) ≤ (0.00077922 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3100 : ℝ) (3125 : ℝ) 2 4475 2.5535e-14
    (0.00077922 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3100_a2_le row3100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1550_lt, LogTables.exp_neg_6200_3_lt,
                   Real.exp_pos (-(1550:ℝ)), Real.exp_pos (-(6200/3:ℝ))])

/-- Row 3100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3100_k4_margin :
    B_8_exact 4 (3100 : ℝ) (3125 : ℝ) ≤ (2.4351 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3100 : ℝ) (3125 : ℝ) 2 4475 2.5535e-14
    (2.4351 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3100_a2_le row3100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1550_lt, LogTables.exp_neg_6200_3_lt,
                   Real.exp_pos (-(1550:ℝ)), Real.exp_pos (-(6200/3:ℝ))])

/-- Row 3100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3100_k5_margin :
    B_8_exact 5 (3100 : ℝ) (3125 : ℝ) ≤ (7609.6 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3100 : ℝ) (3125 : ℝ) 2 4475 2.5535e-14
    (7609.6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3100_a2_le row3100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1550_lt, LogTables.exp_neg_6200_3_lt,
                   Real.exp_pos (-(1550:ℝ)), Real.exp_pos (-(6200/3:ℝ))])

/-- Row 3125 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3125_k1_margin :
    B_8_exact 1 (3125 : ℝ) (3150 : ℝ) ≤ (0.000000000069396 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3125 : ℝ) (3150 : ℝ) 2 4511 2.2031e-14
    (0.000000000069396 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3125_a2_le row3125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3125_2_lt, LogTables.exp_neg_6250_3_lt,
                   Real.exp_pos (-(3125/2:ℝ)), Real.exp_pos (-(6250/3:ℝ))])

/-- Row 3125 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3125_k2_margin :
    B_8_exact 2 (3125 : ℝ) (3150 : ℝ) ≤ (0.00000021860 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3125 : ℝ) (3150 : ℝ) 2 4511 2.2031e-14
    (0.00000021860 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3125_a2_le row3125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3125_2_lt, LogTables.exp_neg_6250_3_lt,
                   Real.exp_pos (-(3125/2:ℝ)), Real.exp_pos (-(6250/3:ℝ))])

/-- Row 3125 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3125_k3_margin :
    B_8_exact 3 (3125 : ℝ) (3150 : ℝ) ≤ (0.00068858 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3125 : ℝ) (3150 : ℝ) 2 4511 2.2031e-14
    (0.00068858 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3125_a2_le row3125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3125_2_lt, LogTables.exp_neg_6250_3_lt,
                   Real.exp_pos (-(3125/2:ℝ)), Real.exp_pos (-(6250/3:ℝ))])

/-- Row 3125 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3125_k4_margin :
    B_8_exact 4 (3125 : ℝ) (3150 : ℝ) ≤ (2.1690 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3125 : ℝ) (3150 : ℝ) 2 4511 2.2031e-14
    (2.1690 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3125_a2_le row3125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3125_2_lt, LogTables.exp_neg_6250_3_lt,
                   Real.exp_pos (-(3125/2:ℝ)), Real.exp_pos (-(6250/3:ℝ))])

/-- Row 3125 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3125_k5_margin :
    B_8_exact 5 (3125 : ℝ) (3150 : ℝ) ≤ (6832.5 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3125 : ℝ) (3150 : ℝ) 2 4511 2.2031e-14
    (6832.5 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3125_a2_le row3125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3125_2_lt, LogTables.exp_neg_6250_3_lt,
                   Real.exp_pos (-(3125/2:ℝ)), Real.exp_pos (-(6250/3:ℝ))])

/-- Row 3150 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3150_k1_margin :
    B_8_exact 1 (3150 : ℝ) (3175 : ℝ) ≤ (0.000000000060410 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3150 : ℝ) (3175 : ℝ) 2 4547 1.9028e-14
    (0.000000000060410 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3150_a2_le row3150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1575_lt, LogTables.exp_neg_2100_lt,
                   Real.exp_pos (-(1575:ℝ)), Real.exp_pos (-(2100:ℝ))])

/-- Row 3150 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3150_k2_margin :
    B_8_exact 2 (3150 : ℝ) (3175 : ℝ) ≤ (0.00000019180 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3150 : ℝ) (3175 : ℝ) 2 4547 1.9028e-14
    (0.00000019180 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3150_a2_le row3150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1575_lt, LogTables.exp_neg_2100_lt,
                   Real.exp_pos (-(1575:ℝ)), Real.exp_pos (-(2100:ℝ))])

/-- Row 3150 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3150_k3_margin :
    B_8_exact 3 (3150 : ℝ) (3175 : ℝ) ≤ (0.00060897 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3150 : ℝ) (3175 : ℝ) 2 4547 1.9028e-14
    (0.00060897 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3150_a2_le row3150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1575_lt, LogTables.exp_neg_2100_lt,
                   Real.exp_pos (-(1575:ℝ)), Real.exp_pos (-(2100:ℝ))])

/-- Row 3150 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3150_k4_margin :
    B_8_exact 4 (3150 : ℝ) (3175 : ℝ) ≤ (1.9335 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3150 : ℝ) (3175 : ℝ) 2 4547 1.9028e-14
    (1.9335 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3150_a2_le row3150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1575_lt, LogTables.exp_neg_2100_lt,
                   Real.exp_pos (-(1575:ℝ)), Real.exp_pos (-(2100:ℝ))])

/-- Row 3150 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3150_k5_margin :
    B_8_exact 5 (3150 : ℝ) (3175 : ℝ) ≤ (6138.8 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3150 : ℝ) (3175 : ℝ) 2 4547 1.9028e-14
    (6138.8 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3150_a2_le row3150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1575_lt, LogTables.exp_neg_2100_lt,
                   Real.exp_pos (-(1575:ℝ)), Real.exp_pos (-(2100:ℝ))])

/-- Row 3175 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3175_k1_margin :
    B_8_exact 1 (3175 : ℝ) (3200 : ℝ) ≤ (0.000000000052572 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3175 : ℝ) (3200 : ℝ) 2 4583 1.6430e-14
    (0.000000000052572 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3175_a2_le row3175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3175_2_lt, LogTables.exp_neg_6350_3_lt,
                   Real.exp_pos (-(3175/2:ℝ)), Real.exp_pos (-(6350/3:ℝ))])

/-- Row 3175 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3175_k2_margin :
    B_8_exact 2 (3175 : ℝ) (3200 : ℝ) ≤ (0.00000016823 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3175 : ℝ) (3200 : ℝ) 2 4583 1.6430e-14
    (0.00000016823 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3175_a2_le row3175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3175_2_lt, LogTables.exp_neg_6350_3_lt,
                   Real.exp_pos (-(3175/2:ℝ)), Real.exp_pos (-(6350/3:ℝ))])

/-- Row 3175 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3175_k3_margin :
    B_8_exact 3 (3175 : ℝ) (3200 : ℝ) ≤ (0.00053834 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3175 : ℝ) (3200 : ℝ) 2 4583 1.6430e-14
    (0.00053834 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3175_a2_le row3175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3175_2_lt, LogTables.exp_neg_6350_3_lt,
                   Real.exp_pos (-(3175/2:ℝ)), Real.exp_pos (-(6350/3:ℝ))])

/-- Row 3175 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3175_k4_margin :
    B_8_exact 4 (3175 : ℝ) (3200 : ℝ) ≤ (1.7227 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3175 : ℝ) (3200 : ℝ) 2 4583 1.6430e-14
    (1.7227 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3175_a2_le row3175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3175_2_lt, LogTables.exp_neg_6350_3_lt,
                   Real.exp_pos (-(3175/2:ℝ)), Real.exp_pos (-(6350/3:ℝ))])

/-- Row 3175 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3175_k5_margin :
    B_8_exact 5 (3175 : ℝ) (3200 : ℝ) ≤ (5512.6 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3175 : ℝ) (3200 : ℝ) 2 4583 1.6430e-14
    (5512.6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3175_a2_le row3175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3175_2_lt, LogTables.exp_neg_6350_3_lt,
                   Real.exp_pos (-(3175/2:ℝ)), Real.exp_pos (-(6350/3:ℝ))])

/-- Row 3200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3200_k1_margin :
    B_8_exact 1 (3200 : ℝ) (3225 : ℝ) ≤ (0.000000000045782 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3200 : ℝ) (3225 : ℝ) 2 4619 1.4197e-14
    (0.000000000045782 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3200_a2_le row3200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1600_lt, LogTables.exp_neg_6400_3_lt,
                   Real.exp_pos (-(1600:ℝ)), Real.exp_pos (-(6400/3:ℝ))])

/-- Row 3200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3200_k2_margin :
    B_8_exact 2 (3200 : ℝ) (3225 : ℝ) ≤ (0.00000014765 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3200 : ℝ) (3225 : ℝ) 2 4619 1.4197e-14
    (0.00000014765 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3200_a2_le row3200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1600_lt, LogTables.exp_neg_6400_3_lt,
                   Real.exp_pos (-(1600:ℝ)), Real.exp_pos (-(6400/3:ℝ))])

/-- Row 3200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3200_k3_margin :
    B_8_exact 3 (3200 : ℝ) (3225 : ℝ) ≤ (0.00047616 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3200 : ℝ) (3225 : ℝ) 2 4619 1.4197e-14
    (0.00047616 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3200_a2_le row3200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1600_lt, LogTables.exp_neg_6400_3_lt,
                   Real.exp_pos (-(1600:ℝ)), Real.exp_pos (-(6400/3:ℝ))])

/-- Row 3200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3200_k4_margin :
    B_8_exact 4 (3200 : ℝ) (3225 : ℝ) ≤ (1.5356 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3200 : ℝ) (3225 : ℝ) 2 4619 1.4197e-14
    (1.5356 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3200_a2_le row3200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1600_lt, LogTables.exp_neg_6400_3_lt,
                   Real.exp_pos (-(1600:ℝ)), Real.exp_pos (-(6400/3:ℝ))])

/-- Row 3200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3200_k5_margin :
    B_8_exact 5 (3200 : ℝ) (3225 : ℝ) ≤ (4952.4 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3200 : ℝ) (3225 : ℝ) 2 4619 1.4197e-14
    (4952.4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3200_a2_le row3200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1600_lt, LogTables.exp_neg_6400_3_lt,
                   Real.exp_pos (-(1600:ℝ)), Real.exp_pos (-(6400/3:ℝ))])

/-- Row 3225 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3225_k1_margin :
    B_8_exact 1 (3225 : ℝ) (3250 : ℝ) ≤ (0.000000000039901 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3225 : ℝ) (3250 : ℝ) 2 4655 1.2278e-14
    (0.000000000039901 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3225_a2_le row3225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3225_2_lt, LogTables.exp_neg_2150_lt,
                   Real.exp_pos (-(3225/2:ℝ)), Real.exp_pos (-(2150:ℝ))])

/-- Row 3225 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3225_k2_margin :
    B_8_exact 2 (3225 : ℝ) (3250 : ℝ) ≤ (0.00000012968 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3225 : ℝ) (3250 : ℝ) 2 4655 1.2278e-14
    (0.00000012968 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3225_a2_le row3225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3225_2_lt, LogTables.exp_neg_2150_lt,
                   Real.exp_pos (-(3225/2:ℝ)), Real.exp_pos (-(2150:ℝ))])

/-- Row 3225 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3225_k3_margin :
    B_8_exact 3 (3225 : ℝ) (3250 : ℝ) ≤ (0.00042146 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3225 : ℝ) (3250 : ℝ) 2 4655 1.2278e-14
    (0.00042146 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3225_a2_le row3225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3225_2_lt, LogTables.exp_neg_2150_lt,
                   Real.exp_pos (-(3225/2:ℝ)), Real.exp_pos (-(2150:ℝ))])

/-- Row 3225 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3225_k4_margin :
    B_8_exact 4 (3225 : ℝ) (3250 : ℝ) ≤ (1.3697 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3225 : ℝ) (3250 : ℝ) 2 4655 1.2278e-14
    (1.3697 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3225_a2_le row3225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3225_2_lt, LogTables.exp_neg_2150_lt,
                   Real.exp_pos (-(3225/2:ℝ)), Real.exp_pos (-(2150:ℝ))])

/-- Row 3225 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3225_k5_margin :
    B_8_exact 5 (3225 : ℝ) (3250 : ℝ) ≤ (4451.6 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3225 : ℝ) (3250 : ℝ) 2 4655 1.2278e-14
    (4451.6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3225_a2_le row3225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3225_2_lt, LogTables.exp_neg_2150_lt,
                   Real.exp_pos (-(3225/2:ℝ)), Real.exp_pos (-(2150:ℝ))])

/-- Row 3250 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3250_k1_margin :
    B_8_exact 1 (3250 : ℝ) (3275 : ℝ) ≤ (0.000000000034800 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3250 : ℝ) (3275 : ℝ) 2 4691 1.0627e-14
    (0.000000000034800 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3250_a2_le row3250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1625_lt, LogTables.exp_neg_6500_3_lt,
                   Real.exp_pos (-(1625:ℝ)), Real.exp_pos (-(6500/3:ℝ))])

/-- Row 3250 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3250_k2_margin :
    B_8_exact 2 (3250 : ℝ) (3275 : ℝ) ≤ (0.00000011397 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3250 : ℝ) (3275 : ℝ) 2 4691 1.0627e-14
    (0.00000011397 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3250_a2_le row3250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1625_lt, LogTables.exp_neg_6500_3_lt,
                   Real.exp_pos (-(1625:ℝ)), Real.exp_pos (-(6500/3:ℝ))])

/-- Row 3250 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3250_k3_margin :
    B_8_exact 3 (3250 : ℝ) (3275 : ℝ) ≤ (0.00037326 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3250 : ℝ) (3275 : ℝ) 2 4691 1.0627e-14
    (0.00037326 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3250_a2_le row3250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1625_lt, LogTables.exp_neg_6500_3_lt,
                   Real.exp_pos (-(1625:ℝ)), Real.exp_pos (-(6500/3:ℝ))])

/-- Row 3250 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3250_k4_margin :
    B_8_exact 4 (3250 : ℝ) (3275 : ℝ) ≤ (1.2224 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3250 : ℝ) (3275 : ℝ) 2 4691 1.0627e-14
    (1.2224 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3250_a2_le row3250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1625_lt, LogTables.exp_neg_6500_3_lt,
                   Real.exp_pos (-(1625:ℝ)), Real.exp_pos (-(6500/3:ℝ))])

/-- Row 3250 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3250_k5_margin :
    B_8_exact 5 (3250 : ℝ) (3275 : ℝ) ≤ (4003.4 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3250 : ℝ) (3275 : ℝ) 2 4691 1.0627e-14
    (4003.4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3250_a2_le row3250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1625_lt, LogTables.exp_neg_6500_3_lt,
                   Real.exp_pos (-(1625:ℝ)), Real.exp_pos (-(6500/3:ℝ))])

/-- Row 3275 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3275_k1_margin :
    B_8_exact 1 (3275 : ℝ) (3300 : ℝ) ≤ (0.000000000030332 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3275 : ℝ) (3300 : ℝ) 2 4727 9.1915e-15
    (0.000000000030332 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3275_a2_le row3275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3275_2_lt, LogTables.exp_neg_6550_3_lt,
                   Real.exp_pos (-(3275/2:ℝ)), Real.exp_pos (-(6550/3:ℝ))])

/-- Row 3275 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3275_k2_margin :
    B_8_exact 2 (3275 : ℝ) (3300 : ℝ) ≤ (0.00000010009 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3275 : ℝ) (3300 : ℝ) 2 4727 9.1915e-15
    (0.00000010009 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3275_a2_le row3275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3275_2_lt, LogTables.exp_neg_6550_3_lt,
                   Real.exp_pos (-(3275/2:ℝ)), Real.exp_pos (-(6550/3:ℝ))])

/-- Row 3275 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3275_k3_margin :
    B_8_exact 3 (3275 : ℝ) (3300 : ℝ) ≤ (0.00033031 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3275 : ℝ) (3300 : ℝ) 2 4727 9.1915e-15
    (0.00033031 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3275_a2_le row3275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3275_2_lt, LogTables.exp_neg_6550_3_lt,
                   Real.exp_pos (-(3275/2:ℝ)), Real.exp_pos (-(6550/3:ℝ))])

/-- Row 3275 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3275_k4_margin :
    B_8_exact 4 (3275 : ℝ) (3300 : ℝ) ≤ (1.0900 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3275 : ℝ) (3300 : ℝ) 2 4727 9.1915e-15
    (1.0900 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3275_a2_le row3275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3275_2_lt, LogTables.exp_neg_6550_3_lt,
                   Real.exp_pos (-(3275/2:ℝ)), Real.exp_pos (-(6550/3:ℝ))])

/-- Row 3275 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3275_k5_margin :
    B_8_exact 5 (3275 : ℝ) (3300 : ℝ) ≤ (3597.1 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3275 : ℝ) (3300 : ℝ) 2 4727 9.1915e-15
    (3597.1 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3275_a2_le row3275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3275_2_lt, LogTables.exp_neg_6550_3_lt,
                   Real.exp_pos (-(3275/2:ℝ)), Real.exp_pos (-(6550/3:ℝ))])

/-- Row 3300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3300_k1_margin :
    B_8_exact 1 (3300 : ℝ) (3325 : ℝ) ≤ (0.000000000026412 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3300 : ℝ) (3325 : ℝ) 2 4763 7.9435e-15
    (0.000000000026412 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3300_a2_le row3300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1650_lt, LogTables.exp_neg_2200_lt,
                   Real.exp_pos (-(1650:ℝ)), Real.exp_pos (-(2200:ℝ))])

/-- Row 3300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3300_k2_margin :
    B_8_exact 2 (3300 : ℝ) (3325 : ℝ) ≤ (0.000000087820 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3300 : ℝ) (3325 : ℝ) 2 4763 7.9435e-15
    (0.000000087820 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3300_a2_le row3300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1650_lt, LogTables.exp_neg_2200_lt,
                   Real.exp_pos (-(1650:ℝ)), Real.exp_pos (-(2200:ℝ))])

/-- Row 3300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3300_k3_margin :
    B_8_exact 3 (3300 : ℝ) (3325 : ℝ) ≤ (0.00029200 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3300 : ℝ) (3325 : ℝ) 2 4763 7.9435e-15
    (0.00029200 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3300_a2_le row3300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1650_lt, LogTables.exp_neg_2200_lt,
                   Real.exp_pos (-(1650:ℝ)), Real.exp_pos (-(2200:ℝ))])

/-- Row 3300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3300_k4_margin :
    B_8_exact 4 (3300 : ℝ) (3325 : ℝ) ≤ (0.97090 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3300 : ℝ) (3325 : ℝ) 2 4763 7.9435e-15
    (0.97090 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3300_a2_le row3300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1650_lt, LogTables.exp_neg_2200_lt,
                   Real.exp_pos (-(1650:ℝ)), Real.exp_pos (-(2200:ℝ))])

/-- Row 3300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3300_k5_margin :
    B_8_exact 5 (3300 : ℝ) (3325 : ℝ) ≤ (3228.3 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3300 : ℝ) (3325 : ℝ) 2 4763 7.9435e-15
    (3228.3 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3300_a2_le row3300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1650_lt, LogTables.exp_neg_2200_lt,
                   Real.exp_pos (-(1650:ℝ)), Real.exp_pos (-(2200:ℝ))])

/-- Row 3325 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3325_k1_margin :
    B_8_exact 1 (3325 : ℝ) (3350 : ℝ) ≤ (0.000000000023015 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3325 : ℝ) (3350 : ℝ) 2 4799 6.8702e-15
    (0.000000000023015 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3325_a2_le row3325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3325_2_lt, LogTables.exp_neg_6650_3_lt,
                   Real.exp_pos (-(3325/2:ℝ)), Real.exp_pos (-(6650/3:ℝ))])

/-- Row 3325 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3325_k2_margin :
    B_8_exact 2 (3325 : ℝ) (3350 : ℝ) ≤ (0.000000077100 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3325 : ℝ) (3350 : ℝ) 2 4799 6.8702e-15
    (0.000000077100 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3325_a2_le row3325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3325_2_lt, LogTables.exp_neg_6650_3_lt,
                   Real.exp_pos (-(3325/2:ℝ)), Real.exp_pos (-(6650/3:ℝ))])

/-- Row 3325 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3325_k3_margin :
    B_8_exact 3 (3325 : ℝ) (3350 : ℝ) ≤ (0.00025829 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3325 : ℝ) (3350 : ℝ) 2 4799 6.8702e-15
    (0.00025829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3325_a2_le row3325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3325_2_lt, LogTables.exp_neg_6650_3_lt,
                   Real.exp_pos (-(3325/2:ℝ)), Real.exp_pos (-(6650/3:ℝ))])

/-- Row 3325 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3325_k4_margin :
    B_8_exact 4 (3325 : ℝ) (3350 : ℝ) ≤ (0.86525 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3325 : ℝ) (3350 : ℝ) 2 4799 6.8702e-15
    (0.86525 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3325_a2_le row3325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3325_2_lt, LogTables.exp_neg_6650_3_lt,
                   Real.exp_pos (-(3325/2:ℝ)), Real.exp_pos (-(6650/3:ℝ))])

/-- Row 3325 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3325_k5_margin :
    B_8_exact 5 (3325 : ℝ) (3350 : ℝ) ≤ (2898.6 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3325 : ℝ) (3350 : ℝ) 2 4799 6.8702e-15
    (2898.6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3325_a2_le row3325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3325_2_lt, LogTables.exp_neg_6650_3_lt,
                   Real.exp_pos (-(3325/2:ℝ)), Real.exp_pos (-(6650/3:ℝ))])

/-- Row 3350 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3350_k1_margin :
    B_8_exact 1 (3350 : ℝ) (3375 : ℝ) ≤ (0.000000000020043 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3350 : ℝ) (3375 : ℝ) 2 4836 5.9387e-15
    (0.000000000020043 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3350_a2_le row3350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1675_lt, LogTables.exp_neg_6700_3_lt,
                   Real.exp_pos (-(1675:ℝ)), Real.exp_pos (-(6700/3:ℝ))])

/-- Row 3350 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3350_k2_margin :
    B_8_exact 2 (3350 : ℝ) (3375 : ℝ) ≤ (0.000000067644 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3350 : ℝ) (3375 : ℝ) 2 4836 5.9387e-15
    (0.000000067644 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3350_a2_le row3350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1675_lt, LogTables.exp_neg_6700_3_lt,
                   Real.exp_pos (-(1675:ℝ)), Real.exp_pos (-(6700/3:ℝ))])

/-- Row 3350 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3350_k3_margin :
    B_8_exact 3 (3350 : ℝ) (3375 : ℝ) ≤ (0.00022830 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3350 : ℝ) (3375 : ℝ) 2 4836 5.9387e-15
    (0.00022830 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3350_a2_le row3350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1675_lt, LogTables.exp_neg_6700_3_lt,
                   Real.exp_pos (-(1675:ℝ)), Real.exp_pos (-(6700/3:ℝ))])

/-- Row 3350 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3350_k4_margin :
    B_8_exact 4 (3350 : ℝ) (3375 : ℝ) ≤ (0.77051 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3350 : ℝ) (3375 : ℝ) 2 4836 5.9387e-15
    (0.77051 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3350_a2_le row3350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1675_lt, LogTables.exp_neg_6700_3_lt,
                   Real.exp_pos (-(1675:ℝ)), Real.exp_pos (-(6700/3:ℝ))])

/-- Row 3350 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3350_k5_margin :
    B_8_exact 5 (3350 : ℝ) (3375 : ℝ) ≤ (2600.5 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3350 : ℝ) (3375 : ℝ) 2 4836 5.9387e-15
    (2600.5 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3350_a2_le row3350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1675_lt, LogTables.exp_neg_6700_3_lt,
                   Real.exp_pos (-(1675:ℝ)), Real.exp_pos (-(6700/3:ℝ))])

/-- Row 3375 (k = 1), exact Table-10 margin target. -/
theorem table_10_row3375_k1_margin :
    B_8_exact 1 (3375 : ℝ) (3400 : ℝ) ≤ (0.000000000017453 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (3375 : ℝ) (3400 : ℝ) 2 4872 5.1333e-15
    (0.000000000017453 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3375_a2_le row3375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3375_2_lt, LogTables.exp_neg_2250_lt,
                   Real.exp_pos (-(3375/2:ℝ)), Real.exp_pos (-(2250:ℝ))])

/-- Row 3375 (k = 2), exact Table-10 margin target. -/
theorem table_10_row3375_k2_margin :
    B_8_exact 2 (3375 : ℝ) (3400 : ℝ) ≤ (0.000000059340 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (3375 : ℝ) (3400 : ℝ) 2 4872 5.1333e-15
    (0.000000059340 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3375_a2_le row3375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3375_2_lt, LogTables.exp_neg_2250_lt,
                   Real.exp_pos (-(3375/2:ℝ)), Real.exp_pos (-(2250:ℝ))])

/-- Row 3375 (k = 3), exact Table-10 margin target. -/
theorem table_10_row3375_k3_margin :
    B_8_exact 3 (3375 : ℝ) (3400 : ℝ) ≤ (0.00020176 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (3375 : ℝ) (3400 : ℝ) 2 4872 5.1333e-15
    (0.00020176 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3375_a2_le row3375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3375_2_lt, LogTables.exp_neg_2250_lt,
                   Real.exp_pos (-(3375/2:ℝ)), Real.exp_pos (-(2250:ℝ))])

/-- Row 3375 (k = 4), exact Table-10 margin target. -/
theorem table_10_row3375_k4_margin :
    B_8_exact 4 (3375 : ℝ) (3400 : ℝ) ≤ (0.68597 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (3375 : ℝ) (3400 : ℝ) 2 4872 5.1333e-15
    (0.68597 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3375_a2_le row3375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3375_2_lt, LogTables.exp_neg_2250_lt,
                   Real.exp_pos (-(3375/2:ℝ)), Real.exp_pos (-(2250:ℝ))])

/-- Row 3375 (k = 5), exact Table-10 margin target. -/
theorem table_10_row3375_k5_margin :
    B_8_exact 5 (3375 : ℝ) (3400 : ℝ) ≤ (2332.3 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (3375 : ℝ) (3400 : ℝ) 2 4872 5.1333e-15
    (2332.3 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row3375_a2_le row3375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_3375_2_lt, LogTables.exp_neg_2250_lt,
                   Real.exp_pos (-(3375/2:ℝ)), Real.exp_pos (-(2250:ℝ))])

end BKLNW
