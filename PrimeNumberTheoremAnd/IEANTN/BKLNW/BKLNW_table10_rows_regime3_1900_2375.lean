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

private lemma row1900_a2_le : Inputs.default.a₂ (1900 : ℝ) ≤ (2744 : ℝ) := by
  have h := a2_crude_le (1900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1900 : ℝ) / log 2⌋₊ : ℝ) ≤ (1900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1900 : ℝ) / log 2 ≤ 2742 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2742 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2744 := by norm_num

private lemma row1925_a2_le : Inputs.default.a₂ (1925 : ℝ) ≤ (2780 : ℝ) := by
  have h := a2_crude_le (1925 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1925 : ℝ) / log 2⌋₊ : ℝ) ≤ (1925 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1925 : ℝ) / log 2 ≤ 2778 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1925 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1925 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2778 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2780 := by norm_num

private lemma row1950_a2_le : Inputs.default.a₂ (1950 : ℝ) ≤ (2816 : ℝ) := by
  have h := a2_crude_le (1950 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1950 : ℝ) / log 2⌋₊ : ℝ) ≤ (1950 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1950 : ℝ) / log 2 ≤ 2814 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1950 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1950 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2814 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2816 := by norm_num

private lemma row1975_a2_le : Inputs.default.a₂ (1975 : ℝ) ≤ (2852 : ℝ) := by
  have h := a2_crude_le (1975 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(1975 : ℝ) / log 2⌋₊ : ℝ) ≤ (1975 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (1975 : ℝ) / log 2 ≤ 2850 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (1975 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(1975 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2850 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2852 := by norm_num

private lemma row2000_a2_le : Inputs.default.a₂ (2000 : ℝ) ≤ (2888 : ℝ) := by
  have h := a2_crude_le (2000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2000 : ℝ) / log 2⌋₊ : ℝ) ≤ (2000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2000 : ℝ) / log 2 ≤ 2886 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2886 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2888 := by norm_num

private lemma row2025_a2_le : Inputs.default.a₂ (2025 : ℝ) ≤ (2924 : ℝ) := by
  have h := a2_crude_le (2025 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2025 : ℝ) / log 2⌋₊ : ℝ) ≤ (2025 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2025 : ℝ) / log 2 ≤ 2922 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2025 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2025 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2922 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2924 := by norm_num

private lemma row2050_a2_le : Inputs.default.a₂ (2050 : ℝ) ≤ (2960 : ℝ) := by
  have h := a2_crude_le (2050 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2050 : ℝ) / log 2⌋₊ : ℝ) ≤ (2050 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2050 : ℝ) / log 2 ≤ 2958 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2050 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2050 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2958 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2960 := by norm_num

private lemma row2075_a2_le : Inputs.default.a₂ (2075 : ℝ) ≤ (2996 : ℝ) := by
  have h := a2_crude_le (2075 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2075 : ℝ) / log 2⌋₊ : ℝ) ≤ (2075 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2075 : ℝ) / log 2 ≤ 2994 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2075 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2075 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (2994 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 2996 := by norm_num

private lemma row2100_a2_le : Inputs.default.a₂ (2100 : ℝ) ≤ (3032 : ℝ) := by
  have h := a2_crude_le (2100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2100 : ℝ) / log 2⌋₊ : ℝ) ≤ (2100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2100 : ℝ) / log 2 ≤ 3030 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3030 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3032 := by norm_num

private lemma row2125_a2_le : Inputs.default.a₂ (2125 : ℝ) ≤ (3068 : ℝ) := by
  have h := a2_crude_le (2125 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2125 : ℝ) / log 2⌋₊ : ℝ) ≤ (2125 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2125 : ℝ) / log 2 ≤ 3066 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2125 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2125 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3066 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3068 := by norm_num

private lemma row2150_a2_le : Inputs.default.a₂ (2150 : ℝ) ≤ (3104 : ℝ) := by
  have h := a2_crude_le (2150 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2150 : ℝ) / log 2⌋₊ : ℝ) ≤ (2150 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2150 : ℝ) / log 2 ≤ 3102 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2150 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2150 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3102 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3104 := by norm_num

private lemma row2175_a2_le : Inputs.default.a₂ (2175 : ℝ) ≤ (3140 : ℝ) := by
  have h := a2_crude_le (2175 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2175 : ℝ) / log 2⌋₊ : ℝ) ≤ (2175 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2175 : ℝ) / log 2 ≤ 3138 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2175 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2175 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3138 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3140 := by norm_num

private lemma row2200_a2_le : Inputs.default.a₂ (2200 : ℝ) ≤ (3176 : ℝ) := by
  have h := a2_crude_le (2200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2200 : ℝ) / log 2⌋₊ : ℝ) ≤ (2200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2200 : ℝ) / log 2 ≤ 3174 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3174 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3176 := by norm_num

private lemma row2225_a2_le : Inputs.default.a₂ (2225 : ℝ) ≤ (3212 : ℝ) := by
  have h := a2_crude_le (2225 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2225 : ℝ) / log 2⌋₊ : ℝ) ≤ (2225 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2225 : ℝ) / log 2 ≤ 3210 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2225 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2225 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3210 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3212 := by norm_num

private lemma row2250_a2_le : Inputs.default.a₂ (2250 : ℝ) ≤ (3249 : ℝ) := by
  have h := a2_crude_le (2250 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2250 : ℝ) / log 2⌋₊ : ℝ) ≤ (2250 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2250 : ℝ) / log 2 ≤ 3247 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2250 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2250 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3247 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3249 := by norm_num

private lemma row2275_a2_le : Inputs.default.a₂ (2275 : ℝ) ≤ (3285 : ℝ) := by
  have h := a2_crude_le (2275 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2275 : ℝ) / log 2⌋₊ : ℝ) ≤ (2275 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2275 : ℝ) / log 2 ≤ 3283 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2275 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2275 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3283 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3285 := by norm_num

private lemma row2300_a2_le : Inputs.default.a₂ (2300 : ℝ) ≤ (3321 : ℝ) := by
  have h := a2_crude_le (2300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2300 : ℝ) / log 2⌋₊ : ℝ) ≤ (2300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2300 : ℝ) / log 2 ≤ 3319 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3319 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3321 := by norm_num

private lemma row2325_a2_le : Inputs.default.a₂ (2325 : ℝ) ≤ (3357 : ℝ) := by
  have h := a2_crude_le (2325 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2325 : ℝ) / log 2⌋₊ : ℝ) ≤ (2325 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2325 : ℝ) / log 2 ≤ 3355 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2325 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2325 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3355 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3357 := by norm_num

private lemma row2350_a2_le : Inputs.default.a₂ (2350 : ℝ) ≤ (3393 : ℝ) := by
  have h := a2_crude_le (2350 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2350 : ℝ) / log 2⌋₊ : ℝ) ≤ (2350 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2350 : ℝ) / log 2 ≤ 3391 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2350 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2350 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3391 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3393 := by norm_num

private lemma row2375_a2_le : Inputs.default.a₂ (2375 : ℝ) ≤ (3429 : ℝ) := by
  have h := a2_crude_le (2375 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(2375 : ℝ) / log 2⌋₊ : ℝ) ≤ (2375 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (2375 : ℝ) / log 2 ≤ 3427 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (2375 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(2375 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (3427 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 3429 := by norm_num

set_option maxRecDepth 10000 in
private lemma row1900_table8_mem : (1900, 1.9242e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1900_eps_le : Inputs.default.ε (1900 : ℝ) ≤ 1.9242e-12 := by
  change BKLNW_app.table_8_ε (1900 : ℝ) ≤ 1.9242e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1900)
    (ε := 1.9242e-12) row1900_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1925_table8_mem : (1925, 1.9239e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1925_eps_le : Inputs.default.ε (1925 : ℝ) ≤ 1.9239e-12 := by
  change BKLNW_app.table_8_ε (1925 : ℝ) ≤ 1.9239e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1925)
    (ε := 1.9239e-12) row1925_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1950_table8_mem : (1950, 1.9235e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1950_eps_le : Inputs.default.ε (1950 : ℝ) ≤ 1.9235e-12 := by
  change BKLNW_app.table_8_ε (1950 : ℝ) ≤ 1.9235e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1950)
    (ε := 1.9235e-12) row1950_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row1975_table8_mem : (1975, 1.9232e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row1975_eps_le : Inputs.default.ε (1975 : ℝ) ≤ 1.9232e-12 := by
  change BKLNW_app.table_8_ε (1975 : ℝ) ≤ 1.9232e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 1975)
    (ε := 1.9232e-12) row1975_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2000_table8_mem : (2000, 1.9229e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2000_eps_le : Inputs.default.ε (2000 : ℝ) ≤ 1.9229e-12 := by
  change BKLNW_app.table_8_ε (2000 : ℝ) ≤ 1.9229e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2000)
    (ε := 1.9229e-12) row2000_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2025_table8_mem : (2025, 1.9225e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2025_eps_le : Inputs.default.ε (2025 : ℝ) ≤ 1.9225e-12 := by
  change BKLNW_app.table_8_ε (2025 : ℝ) ≤ 1.9225e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2025)
    (ε := 1.9225e-12) row2025_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2050_table8_mem : (2050, 1.9222e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2050_eps_le : Inputs.default.ε (2050 : ℝ) ≤ 1.9222e-12 := by
  change BKLNW_app.table_8_ε (2050 : ℝ) ≤ 1.9222e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2050)
    (ε := 1.9222e-12) row2050_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2075_table8_mem : (2075, 1.9219e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2075_eps_le : Inputs.default.ε (2075 : ℝ) ≤ 1.9219e-12 := by
  change BKLNW_app.table_8_ε (2075 : ℝ) ≤ 1.9219e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2075)
    (ε := 1.9219e-12) row2075_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2100_table8_mem : (2100, 1.9217e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2100_eps_le : Inputs.default.ε (2100 : ℝ) ≤ 1.9217e-12 := by
  change BKLNW_app.table_8_ε (2100 : ℝ) ≤ 1.9217e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2100)
    (ε := 1.9217e-12) row2100_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2125_table8_mem : (2125, 1.9214e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2125_eps_le : Inputs.default.ε (2125 : ℝ) ≤ 1.9214e-12 := by
  change BKLNW_app.table_8_ε (2125 : ℝ) ≤ 1.9214e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2125)
    (ε := 1.9214e-12) row2125_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2150_table8_mem : (2150, 1.9211e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2150_eps_le : Inputs.default.ε (2150 : ℝ) ≤ 1.9211e-12 := by
  change BKLNW_app.table_8_ε (2150 : ℝ) ≤ 1.9211e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2150)
    (ε := 1.9211e-12) row2150_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2175_table8_mem : (2175, 1.9208e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2175_eps_le : Inputs.default.ε (2175 : ℝ) ≤ 1.9208e-12 := by
  change BKLNW_app.table_8_ε (2175 : ℝ) ≤ 1.9208e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2175)
    (ε := 1.9208e-12) row2175_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2200_table8_mem : (2200, 1.9206e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2200_eps_le : Inputs.default.ε (2200 : ℝ) ≤ 1.9206e-12 := by
  change BKLNW_app.table_8_ε (2200 : ℝ) ≤ 1.9206e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2200)
    (ε := 1.9206e-12) row2200_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2225_table8_mem : (2225, 1.9203e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2225_eps_le : Inputs.default.ε (2225 : ℝ) ≤ 1.9203e-12 := by
  change BKLNW_app.table_8_ε (2225 : ℝ) ≤ 1.9203e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2225)
    (ε := 1.9203e-12) row2225_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2250_table8_mem : (2250, 1.9200e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2250_eps_le : Inputs.default.ε (2250 : ℝ) ≤ 1.9200e-12 := by
  change BKLNW_app.table_8_ε (2250 : ℝ) ≤ 1.9200e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2250)
    (ε := 1.9200e-12) row2250_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2275_table8_mem : (2275, 1.9198e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2275_eps_le : Inputs.default.ε (2275 : ℝ) ≤ 1.9198e-12 := by
  change BKLNW_app.table_8_ε (2275 : ℝ) ≤ 1.9198e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2275)
    (ε := 1.9198e-12) row2275_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2300_table8_mem : (2300, 1.9195e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2300_eps_le : Inputs.default.ε (2300 : ℝ) ≤ 1.9195e-12 := by
  change BKLNW_app.table_8_ε (2300 : ℝ) ≤ 1.9195e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2300)
    (ε := 1.9195e-12) row2300_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2325_table8_mem : (2325, 1.8751e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2325_eps_le : Inputs.default.ε (2325 : ℝ) ≤ 1.8751e-12 := by
  change BKLNW_app.table_8_ε (2325 : ℝ) ≤ 1.8751e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2325)
    (ε := 1.8751e-12) row2325_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2350_table8_mem : (2350, 1.7788e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2350_eps_le : Inputs.default.ε (2350 : ℝ) ≤ 1.7788e-12 := by
  change BKLNW_app.table_8_ε (2350 : ℝ) ≤ 1.7788e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2350)
    (ε := 1.7788e-12) row2350_table8_mem (by norm_num)

set_option maxRecDepth 10000 in
private lemma row2375_table8_mem : (2375, 1.6875e-12) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row2375_eps_le : Inputs.default.ε (2375 : ℝ) ≤ 1.6875e-12 := by
  change BKLNW_app.table_8_ε (2375 : ℝ) ≤ 1.6875e-12
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 2375)
    (ε := 1.6875e-12) row2375_table8_mem (by norm_num)

/-- Row 1900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1900_k1_margin :
    B_8_exact 1 (1900 : ℝ) (1925 : ℝ) ≤ (0.0000000037040 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1900 : ℝ) (1925 : ℝ) 2 2744 1.9242e-12
    (0.0000000037040 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1900_a2_le row1900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_950_lt, LogTables.exp_neg_3800_3_lt,
                   Real.exp_pos (-(950:ℝ)), Real.exp_pos (-(3800/3:ℝ))])

/-- Row 1900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1900_k2_margin :
    B_8_exact 2 (1900 : ℝ) (1925 : ℝ) ≤ (0.0000071302 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1900 : ℝ) (1925 : ℝ) 2 2744 1.9242e-12
    (0.0000071302 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1900_a2_le row1900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_950_lt, LogTables.exp_neg_3800_3_lt,
                   Real.exp_pos (-(950:ℝ)), Real.exp_pos (-(3800/3:ℝ))])

/-- Row 1900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1900_k3_margin :
    B_8_exact 3 (1900 : ℝ) (1925 : ℝ) ≤ (0.013726 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1900 : ℝ) (1925 : ℝ) 2 2744 1.9242e-12
    (0.013726 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1900_a2_le row1900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_950_lt, LogTables.exp_neg_3800_3_lt,
                   Real.exp_pos (-(950:ℝ)), Real.exp_pos (-(3800/3:ℝ))])

/-- Row 1900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1900_k4_margin :
    B_8_exact 4 (1900 : ℝ) (1925 : ℝ) ≤ (26.422 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1900 : ℝ) (1925 : ℝ) 2 2744 1.9242e-12
    (26.422 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1900_a2_le row1900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_950_lt, LogTables.exp_neg_3800_3_lt,
                   Real.exp_pos (-(950:ℝ)), Real.exp_pos (-(3800/3:ℝ))])

/-- Row 1900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1900_k5_margin :
    B_8_exact 5 (1900 : ℝ) (1925 : ℝ) ≤ (50862 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1900 : ℝ) (1925 : ℝ) 2 2744 1.9242e-12
    (50862 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1900_a2_le row1900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_950_lt, LogTables.exp_neg_3800_3_lt,
                   Real.exp_pos (-(950:ℝ)), Real.exp_pos (-(3800/3:ℝ))])

/-- Row 1925 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1925_k1_margin :
    B_8_exact 1 (1925 : ℝ) (1950 : ℝ) ≤ (0.0000000037514 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1925 : ℝ) (1950 : ℝ) 2 2780 1.9239e-12
    (0.0000000037514 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1925_a2_le row1925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1925_2_lt, LogTables.exp_neg_3850_3_lt,
                   Real.exp_pos (-(1925/2:ℝ)), Real.exp_pos (-(3850/3:ℝ))])

/-- Row 1925 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1925_k2_margin :
    B_8_exact 2 (1925 : ℝ) (1950 : ℝ) ≤ (0.0000073152 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1925 : ℝ) (1950 : ℝ) 2 2780 1.9239e-12
    (0.0000073152 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1925_a2_le row1925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1925_2_lt, LogTables.exp_neg_3850_3_lt,
                   Real.exp_pos (-(1925/2:ℝ)), Real.exp_pos (-(3850/3:ℝ))])

/-- Row 1925 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1925_k3_margin :
    B_8_exact 3 (1925 : ℝ) (1950 : ℝ) ≤ (0.014265 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1925 : ℝ) (1950 : ℝ) 2 2780 1.9239e-12
    (0.014265 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1925_a2_le row1925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1925_2_lt, LogTables.exp_neg_3850_3_lt,
                   Real.exp_pos (-(1925/2:ℝ)), Real.exp_pos (-(3850/3:ℝ))])

/-- Row 1925 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1925_k4_margin :
    B_8_exact 4 (1925 : ℝ) (1950 : ℝ) ≤ (27.816 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1925 : ℝ) (1950 : ℝ) 2 2780 1.9239e-12
    (27.816 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1925_a2_le row1925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1925_2_lt, LogTables.exp_neg_3850_3_lt,
                   Real.exp_pos (-(1925/2:ℝ)), Real.exp_pos (-(3850/3:ℝ))])

/-- Row 1925 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1925_k5_margin :
    B_8_exact 5 (1925 : ℝ) (1950 : ℝ) ≤ (54241 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1925 : ℝ) (1950 : ℝ) 2 2780 1.9239e-12
    (54241 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1925_a2_le row1925_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1925_2_lt, LogTables.exp_neg_3850_3_lt,
                   Real.exp_pos (-(1925/2:ℝ)), Real.exp_pos (-(3850/3:ℝ))])

/-- Row 1950 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1950_k1_margin :
    B_8_exact 1 (1950 : ℝ) (1975 : ℝ) ≤ (0.0000000037988 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1950 : ℝ) (1975 : ℝ) 2 2816 1.9235e-12
    (0.0000000037988 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1950_a2_le row1950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_975_lt, LogTables.exp_neg_1300_lt,
                   Real.exp_pos (-(975:ℝ)), Real.exp_pos (-(1300:ℝ))])

/-- Row 1950 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1950_k2_margin :
    B_8_exact 2 (1950 : ℝ) (1975 : ℝ) ≤ (0.0000075026 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1950 : ℝ) (1975 : ℝ) 2 2816 1.9235e-12
    (0.0000075026 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1950_a2_le row1950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_975_lt, LogTables.exp_neg_1300_lt,
                   Real.exp_pos (-(975:ℝ)), Real.exp_pos (-(1300:ℝ))])

/-- Row 1950 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1950_k3_margin :
    B_8_exact 3 (1950 : ℝ) (1975 : ℝ) ≤ (0.014818 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1950 : ℝ) (1975 : ℝ) 2 2816 1.9235e-12
    (0.014818 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1950_a2_le row1950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_975_lt, LogTables.exp_neg_1300_lt,
                   Real.exp_pos (-(975:ℝ)), Real.exp_pos (-(1300:ℝ))])

/-- Row 1950 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1950_k4_margin :
    B_8_exact 4 (1950 : ℝ) (1975 : ℝ) ≤ (29.265 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1950 : ℝ) (1975 : ℝ) 2 2816 1.9235e-12
    (29.265 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1950_a2_le row1950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_975_lt, LogTables.exp_neg_1300_lt,
                   Real.exp_pos (-(975:ℝ)), Real.exp_pos (-(1300:ℝ))])

/-- Row 1950 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1950_k5_margin :
    B_8_exact 5 (1950 : ℝ) (1975 : ℝ) ≤ (57798 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1950 : ℝ) (1975 : ℝ) 2 2816 1.9235e-12
    (57798 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1950_a2_le row1950_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_975_lt, LogTables.exp_neg_1300_lt,
                   Real.exp_pos (-(975:ℝ)), Real.exp_pos (-(1300:ℝ))])

/-- Row 1975 (k = 1), exact Table-10 margin target. -/
theorem table_10_row1975_k1_margin :
    B_8_exact 1 (1975 : ℝ) (2000 : ℝ) ≤ (0.0000000038462 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (1975 : ℝ) (2000 : ℝ) 2 2852 1.9232e-12
    (0.0000000038462 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1975_a2_le row1975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1975_2_lt, LogTables.exp_neg_3950_3_lt,
                   Real.exp_pos (-(1975/2:ℝ)), Real.exp_pos (-(3950/3:ℝ))])

/-- Row 1975 (k = 2), exact Table-10 margin target. -/
theorem table_10_row1975_k2_margin :
    B_8_exact 2 (1975 : ℝ) (2000 : ℝ) ≤ (0.0000076924 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (1975 : ℝ) (2000 : ℝ) 2 2852 1.9232e-12
    (0.0000076924 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1975_a2_le row1975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1975_2_lt, LogTables.exp_neg_3950_3_lt,
                   Real.exp_pos (-(1975/2:ℝ)), Real.exp_pos (-(3950/3:ℝ))])

/-- Row 1975 (k = 3), exact Table-10 margin target. -/
theorem table_10_row1975_k3_margin :
    B_8_exact 3 (1975 : ℝ) (2000 : ℝ) ≤ (0.015385 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (1975 : ℝ) (2000 : ℝ) 2 2852 1.9232e-12
    (0.015385 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1975_a2_le row1975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1975_2_lt, LogTables.exp_neg_3950_3_lt,
                   Real.exp_pos (-(1975/2:ℝ)), Real.exp_pos (-(3950/3:ℝ))])

/-- Row 1975 (k = 4), exact Table-10 margin target. -/
theorem table_10_row1975_k4_margin :
    B_8_exact 4 (1975 : ℝ) (2000 : ℝ) ≤ (30.770 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (1975 : ℝ) (2000 : ℝ) 2 2852 1.9232e-12
    (30.770 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1975_a2_le row1975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1975_2_lt, LogTables.exp_neg_3950_3_lt,
                   Real.exp_pos (-(1975/2:ℝ)), Real.exp_pos (-(3950/3:ℝ))])

/-- Row 1975 (k = 5), exact Table-10 margin target. -/
theorem table_10_row1975_k5_margin :
    B_8_exact 5 (1975 : ℝ) (2000 : ℝ) ≤ (61540 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (1975 : ℝ) (2000 : ℝ) 2 2852 1.9232e-12
    (61540 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row1975_a2_le row1975_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1975_2_lt, LogTables.exp_neg_3950_3_lt,
                   Real.exp_pos (-(1975/2:ℝ)), Real.exp_pos (-(3950/3:ℝ))])

/-- Row 2000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2000_k1_margin :
    B_8_exact 1 (2000 : ℝ) (2025 : ℝ) ≤ (0.0000000038937 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2000 : ℝ) (2025 : ℝ) 2 2888 1.9229e-12
    (0.0000000038937 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2000_a2_le row2000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1000_lt, LogTables.exp_neg_4000_3_lt,
                   Real.exp_pos (-(1000:ℝ)), Real.exp_pos (-(4000/3:ℝ))])

/-- Row 2000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2000_k2_margin :
    B_8_exact 2 (2000 : ℝ) (2025 : ℝ) ≤ (0.0000078847 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2000 : ℝ) (2025 : ℝ) 2 2888 1.9229e-12
    (0.0000078847 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2000_a2_le row2000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1000_lt, LogTables.exp_neg_4000_3_lt,
                   Real.exp_pos (-(1000:ℝ)), Real.exp_pos (-(4000/3:ℝ))])

/-- Row 2000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2000_k3_margin :
    B_8_exact 3 (2000 : ℝ) (2025 : ℝ) ≤ (0.015966 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2000 : ℝ) (2025 : ℝ) 2 2888 1.9229e-12
    (0.015966 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2000_a2_le row2000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1000_lt, LogTables.exp_neg_4000_3_lt,
                   Real.exp_pos (-(1000:ℝ)), Real.exp_pos (-(4000/3:ℝ))])

/-- Row 2000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2000_k4_margin :
    B_8_exact 4 (2000 : ℝ) (2025 : ℝ) ≤ (32.332 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2000 : ℝ) (2025 : ℝ) 2 2888 1.9229e-12
    (32.332 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2000_a2_le row2000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1000_lt, LogTables.exp_neg_4000_3_lt,
                   Real.exp_pos (-(1000:ℝ)), Real.exp_pos (-(4000/3:ℝ))])

/-- Row 2000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2000_k5_margin :
    B_8_exact 5 (2000 : ℝ) (2025 : ℝ) ≤ (65472 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2000 : ℝ) (2025 : ℝ) 2 2888 1.9229e-12
    (65472 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2000_a2_le row2000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1000_lt, LogTables.exp_neg_4000_3_lt,
                   Real.exp_pos (-(1000:ℝ)), Real.exp_pos (-(4000/3:ℝ))])

/-- Row 2025 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2025_k1_margin :
    B_8_exact 1 (2025 : ℝ) (2050 : ℝ) ≤ (0.0000000039411 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2025 : ℝ) (2050 : ℝ) 2 2924 1.9225e-12
    (0.0000000039411 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2025_a2_le row2025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2025_2_lt, LogTables.exp_neg_1350_lt,
                   Real.exp_pos (-(2025/2:ℝ)), Real.exp_pos (-(1350:ℝ))])

/-- Row 2025 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2025_k2_margin :
    B_8_exact 2 (2025 : ℝ) (2050 : ℝ) ≤ (0.0000080792 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2025 : ℝ) (2050 : ℝ) 2 2924 1.9225e-12
    (0.0000080792 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2025_a2_le row2025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2025_2_lt, LogTables.exp_neg_1350_lt,
                   Real.exp_pos (-(2025/2:ℝ)), Real.exp_pos (-(1350:ℝ))])

/-- Row 2025 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2025_k3_margin :
    B_8_exact 3 (2025 : ℝ) (2050 : ℝ) ≤ (0.016562 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2025 : ℝ) (2050 : ℝ) 2 2924 1.9225e-12
    (0.016562 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2025_a2_le row2025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2025_2_lt, LogTables.exp_neg_1350_lt,
                   Real.exp_pos (-(2025/2:ℝ)), Real.exp_pos (-(1350:ℝ))])

/-- Row 2025 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2025_k4_margin :
    B_8_exact 4 (2025 : ℝ) (2050 : ℝ) ≤ (33.953 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2025 : ℝ) (2050 : ℝ) 2 2924 1.9225e-12
    (33.953 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2025_a2_le row2025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2025_2_lt, LogTables.exp_neg_1350_lt,
                   Real.exp_pos (-(2025/2:ℝ)), Real.exp_pos (-(1350:ℝ))])

/-- Row 2025 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2025_k5_margin :
    B_8_exact 5 (2025 : ℝ) (2050 : ℝ) ≤ (69603 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2025 : ℝ) (2050 : ℝ) 2 2924 1.9225e-12
    (69603 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2025_a2_le row2025_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2025_2_lt, LogTables.exp_neg_1350_lt,
                   Real.exp_pos (-(2025/2:ℝ)), Real.exp_pos (-(1350:ℝ))])

/-- Row 2050 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2050_k1_margin :
    B_8_exact 1 (2050 : ℝ) (2075 : ℝ) ≤ (0.0000000039885 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2050 : ℝ) (2075 : ℝ) 2 2960 1.9222e-12
    (0.0000000039885 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2050_a2_le row2050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1025_lt, LogTables.exp_neg_4100_3_lt,
                   Real.exp_pos (-(1025:ℝ)), Real.exp_pos (-(4100/3:ℝ))])

/-- Row 2050 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2050_k2_margin :
    B_8_exact 2 (2050 : ℝ) (2075 : ℝ) ≤ (0.0000082761 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2050 : ℝ) (2075 : ℝ) 2 2960 1.9222e-12
    (0.0000082761 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2050_a2_le row2050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1025_lt, LogTables.exp_neg_4100_3_lt,
                   Real.exp_pos (-(1025:ℝ)), Real.exp_pos (-(4100/3:ℝ))])

/-- Row 2050 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2050_k3_margin :
    B_8_exact 3 (2050 : ℝ) (2075 : ℝ) ≤ (0.017173 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2050 : ℝ) (2075 : ℝ) 2 2960 1.9222e-12
    (0.017173 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2050_a2_le row2050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1025_lt, LogTables.exp_neg_4100_3_lt,
                   Real.exp_pos (-(1025:ℝ)), Real.exp_pos (-(4100/3:ℝ))])

/-- Row 2050 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2050_k4_margin :
    B_8_exact 4 (2050 : ℝ) (2075 : ℝ) ≤ (35.634 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2050 : ℝ) (2075 : ℝ) 2 2960 1.9222e-12
    (35.634 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2050_a2_le row2050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1025_lt, LogTables.exp_neg_4100_3_lt,
                   Real.exp_pos (-(1025:ℝ)), Real.exp_pos (-(4100/3:ℝ))])

/-- Row 2050 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2050_k5_margin :
    B_8_exact 5 (2050 : ℝ) (2075 : ℝ) ≤ (73940 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2050 : ℝ) (2075 : ℝ) 2 2960 1.9222e-12
    (73940 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2050_a2_le row2050_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1025_lt, LogTables.exp_neg_4100_3_lt,
                   Real.exp_pos (-(1025:ℝ)), Real.exp_pos (-(4100/3:ℝ))])

/-- Row 2075 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2075_k1_margin :
    B_8_exact 1 (2075 : ℝ) (2100 : ℝ) ≤ (0.0000000040359 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2075 : ℝ) (2100 : ℝ) 2 2996 1.9219e-12
    (0.0000000040359 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2075_a2_le row2075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2075_2_lt, LogTables.exp_neg_4150_3_lt,
                   Real.exp_pos (-(2075/2:ℝ)), Real.exp_pos (-(4150/3:ℝ))])

/-- Row 2075 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2075_k2_margin :
    B_8_exact 2 (2075 : ℝ) (2100 : ℝ) ≤ (0.0000084754 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2075 : ℝ) (2100 : ℝ) 2 2996 1.9219e-12
    (0.0000084754 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2075_a2_le row2075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2075_2_lt, LogTables.exp_neg_4150_3_lt,
                   Real.exp_pos (-(2075/2:ℝ)), Real.exp_pos (-(4150/3:ℝ))])

/-- Row 2075 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2075_k3_margin :
    B_8_exact 3 (2075 : ℝ) (2100 : ℝ) ≤ (0.017798 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2075 : ℝ) (2100 : ℝ) 2 2996 1.9219e-12
    (0.017798 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2075_a2_le row2075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2075_2_lt, LogTables.exp_neg_4150_3_lt,
                   Real.exp_pos (-(2075/2:ℝ)), Real.exp_pos (-(4150/3:ℝ))])

/-- Row 2075 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2075_k4_margin :
    B_8_exact 4 (2075 : ℝ) (2100 : ℝ) ≤ (37.377 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2075 : ℝ) (2100 : ℝ) 2 2996 1.9219e-12
    (37.377 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2075_a2_le row2075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2075_2_lt, LogTables.exp_neg_4150_3_lt,
                   Real.exp_pos (-(2075/2:ℝ)), Real.exp_pos (-(4150/3:ℝ))])

/-- Row 2075 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2075_k5_margin :
    B_8_exact 5 (2075 : ℝ) (2100 : ℝ) ≤ (78491 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2075 : ℝ) (2100 : ℝ) 2 2996 1.9219e-12
    (78491 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2075_a2_le row2075_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2075_2_lt, LogTables.exp_neg_4150_3_lt,
                   Real.exp_pos (-(2075/2:ℝ)), Real.exp_pos (-(4150/3:ℝ))])

/-- Row 2100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2100_k1_margin :
    B_8_exact 1 (2100 : ℝ) (2125 : ℝ) ≤ (0.0000000040833 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2100 : ℝ) (2125 : ℝ) 2 3032 1.9217e-12
    (0.0000000040833 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2100_a2_le row2100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1050_lt, LogTables.exp_neg_1400_lt,
                   Real.exp_pos (-(1050:ℝ)), Real.exp_pos (-(1400:ℝ))])

/-- Row 2100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2100_k2_margin :
    B_8_exact 2 (2100 : ℝ) (2125 : ℝ) ≤ (0.0000086771 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2100 : ℝ) (2125 : ℝ) 2 3032 1.9217e-12
    (0.0000086771 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2100_a2_le row2100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1050_lt, LogTables.exp_neg_1400_lt,
                   Real.exp_pos (-(1050:ℝ)), Real.exp_pos (-(1400:ℝ))])

/-- Row 2100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2100_k3_margin :
    B_8_exact 3 (2100 : ℝ) (2125 : ℝ) ≤ (0.018439 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2100 : ℝ) (2125 : ℝ) 2 3032 1.9217e-12
    (0.018439 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2100_a2_le row2100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1050_lt, LogTables.exp_neg_1400_lt,
                   Real.exp_pos (-(1050:ℝ)), Real.exp_pos (-(1400:ℝ))])

/-- Row 2100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2100_k4_margin :
    B_8_exact 4 (2100 : ℝ) (2125 : ℝ) ≤ (39.182 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2100 : ℝ) (2125 : ℝ) 2 3032 1.9217e-12
    (39.182 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2100_a2_le row2100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1050_lt, LogTables.exp_neg_1400_lt,
                   Real.exp_pos (-(1050:ℝ)), Real.exp_pos (-(1400:ℝ))])

/-- Row 2100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2100_k5_margin :
    B_8_exact 5 (2100 : ℝ) (2125 : ℝ) ≤ (83262 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2100 : ℝ) (2125 : ℝ) 2 3032 1.9217e-12
    (83262 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2100_a2_le row2100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1050_lt, LogTables.exp_neg_1400_lt,
                   Real.exp_pos (-(1050:ℝ)), Real.exp_pos (-(1400:ℝ))])

/-- Row 2125 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2125_k1_margin :
    B_8_exact 1 (2125 : ℝ) (2150 : ℝ) ≤ (0.0000000041308 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2125 : ℝ) (2150 : ℝ) 2 3068 1.9214e-12
    (0.0000000041308 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2125_a2_le row2125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2125_2_lt, LogTables.exp_neg_4250_3_lt,
                   Real.exp_pos (-(2125/2:ℝ)), Real.exp_pos (-(4250/3:ℝ))])

/-- Row 2125 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2125_k2_margin :
    B_8_exact 2 (2125 : ℝ) (2150 : ℝ) ≤ (0.0000088811 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2125 : ℝ) (2150 : ℝ) 2 3068 1.9214e-12
    (0.0000088811 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2125_a2_le row2125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2125_2_lt, LogTables.exp_neg_4250_3_lt,
                   Real.exp_pos (-(2125/2:ℝ)), Real.exp_pos (-(4250/3:ℝ))])

/-- Row 2125 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2125_k3_margin :
    B_8_exact 3 (2125 : ℝ) (2150 : ℝ) ≤ (0.019095 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2125 : ℝ) (2150 : ℝ) 2 3068 1.9214e-12
    (0.019095 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2125_a2_le row2125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2125_2_lt, LogTables.exp_neg_4250_3_lt,
                   Real.exp_pos (-(2125/2:ℝ)), Real.exp_pos (-(4250/3:ℝ))])

/-- Row 2125 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2125_k4_margin :
    B_8_exact 4 (2125 : ℝ) (2150 : ℝ) ≤ (41.053 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2125 : ℝ) (2150 : ℝ) 2 3068 1.9214e-12
    (41.053 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2125_a2_le row2125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2125_2_lt, LogTables.exp_neg_4250_3_lt,
                   Real.exp_pos (-(2125/2:ℝ)), Real.exp_pos (-(4250/3:ℝ))])

/-- Row 2125 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2125_k5_margin :
    B_8_exact 5 (2125 : ℝ) (2150 : ℝ) ≤ (88264 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2125 : ℝ) (2150 : ℝ) 2 3068 1.9214e-12
    (88264 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2125_a2_le row2125_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2125_2_lt, LogTables.exp_neg_4250_3_lt,
                   Real.exp_pos (-(2125/2:ℝ)), Real.exp_pos (-(4250/3:ℝ))])

/-- Row 2150 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2150_k1_margin :
    B_8_exact 1 (2150 : ℝ) (2175 : ℝ) ≤ (0.0000000041782 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2150 : ℝ) (2175 : ℝ) 2 3104 1.9211e-12
    (0.0000000041782 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2150_a2_le row2150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1075_lt, LogTables.exp_neg_4300_3_lt,
                   Real.exp_pos (-(1075:ℝ)), Real.exp_pos (-(4300/3:ℝ))])

/-- Row 2150 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2150_k2_margin :
    B_8_exact 2 (2150 : ℝ) (2175 : ℝ) ≤ (0.0000090875 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2150 : ℝ) (2175 : ℝ) 2 3104 1.9211e-12
    (0.0000090875 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2150_a2_le row2150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1075_lt, LogTables.exp_neg_4300_3_lt,
                   Real.exp_pos (-(1075:ℝ)), Real.exp_pos (-(4300/3:ℝ))])

/-- Row 2150 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2150_k3_margin :
    B_8_exact 3 (2150 : ℝ) (2175 : ℝ) ≤ (0.019765 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2150 : ℝ) (2175 : ℝ) 2 3104 1.9211e-12
    (0.019765 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2150_a2_le row2150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1075_lt, LogTables.exp_neg_4300_3_lt,
                   Real.exp_pos (-(1075:ℝ)), Real.exp_pos (-(4300/3:ℝ))])

/-- Row 2150 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2150_k4_margin :
    B_8_exact 4 (2150 : ℝ) (2175 : ℝ) ≤ (42.990 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2150 : ℝ) (2175 : ℝ) 2 3104 1.9211e-12
    (42.990 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2150_a2_le row2150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1075_lt, LogTables.exp_neg_4300_3_lt,
                   Real.exp_pos (-(1075:ℝ)), Real.exp_pos (-(4300/3:ℝ))])

/-- Row 2150 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2150_k5_margin :
    B_8_exact 5 (2150 : ℝ) (2175 : ℝ) ≤ (93503 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2150 : ℝ) (2175 : ℝ) 2 3104 1.9211e-12
    (93503 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2150_a2_le row2150_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1075_lt, LogTables.exp_neg_4300_3_lt,
                   Real.exp_pos (-(1075:ℝ)), Real.exp_pos (-(4300/3:ℝ))])

/-- Row 2175 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2175_k1_margin :
    B_8_exact 1 (2175 : ℝ) (2200 : ℝ) ≤ (0.0000000042256 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2175 : ℝ) (2200 : ℝ) 2 3140 1.9208e-12
    (0.0000000042256 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2175_a2_le row2175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2175_2_lt, LogTables.exp_neg_1450_lt,
                   Real.exp_pos (-(2175/2:ℝ)), Real.exp_pos (-(1450:ℝ))])

/-- Row 2175 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2175_k2_margin :
    B_8_exact 2 (2175 : ℝ) (2200 : ℝ) ≤ (0.0000092963 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2175 : ℝ) (2200 : ℝ) 2 3140 1.9208e-12
    (0.0000092963 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2175_a2_le row2175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2175_2_lt, LogTables.exp_neg_1450_lt,
                   Real.exp_pos (-(2175/2:ℝ)), Real.exp_pos (-(1450:ℝ))])

/-- Row 2175 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2175_k3_margin :
    B_8_exact 3 (2175 : ℝ) (2200 : ℝ) ≤ (0.020452 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2175 : ℝ) (2200 : ℝ) 2 3140 1.9208e-12
    (0.020452 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2175_a2_le row2175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2175_2_lt, LogTables.exp_neg_1450_lt,
                   Real.exp_pos (-(2175/2:ℝ)), Real.exp_pos (-(1450:ℝ))])

/-- Row 2175 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2175_k4_margin :
    B_8_exact 4 (2175 : ℝ) (2200 : ℝ) ≤ (44.994 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2175 : ℝ) (2200 : ℝ) 2 3140 1.9208e-12
    (44.994 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2175_a2_le row2175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2175_2_lt, LogTables.exp_neg_1450_lt,
                   Real.exp_pos (-(2175/2:ℝ)), Real.exp_pos (-(1450:ℝ))])

/-- Row 2175 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2175_k5_margin :
    B_8_exact 5 (2175 : ℝ) (2200 : ℝ) ≤ (98987 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2175 : ℝ) (2200 : ℝ) 2 3140 1.9208e-12
    (98987 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2175_a2_le row2175_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2175_2_lt, LogTables.exp_neg_1450_lt,
                   Real.exp_pos (-(2175/2:ℝ)), Real.exp_pos (-(1450:ℝ))])

/-- Row 2200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2200_k1_margin :
    B_8_exact 1 (2200 : ℝ) (2225 : ℝ) ≤ (0.0000000042730 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2200 : ℝ) (2225 : ℝ) 2 3176 1.9206e-12
    (0.0000000042730 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2200_a2_le row2200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1100_lt, LogTables.exp_neg_4400_3_lt,
                   Real.exp_pos (-(1100:ℝ)), Real.exp_pos (-(4400/3:ℝ))])

/-- Row 2200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2200_k2_margin :
    B_8_exact 2 (2200 : ℝ) (2225 : ℝ) ≤ (0.0000095075 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2200 : ℝ) (2225 : ℝ) 2 3176 1.9206e-12
    (0.0000095075 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2200_a2_le row2200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1100_lt, LogTables.exp_neg_4400_3_lt,
                   Real.exp_pos (-(1100:ℝ)), Real.exp_pos (-(4400/3:ℝ))])

/-- Row 2200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2200_k3_margin :
    B_8_exact 3 (2200 : ℝ) (2225 : ℝ) ≤ (0.021154 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2200 : ℝ) (2225 : ℝ) 2 3176 1.9206e-12
    (0.021154 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2200_a2_le row2200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1100_lt, LogTables.exp_neg_4400_3_lt,
                   Real.exp_pos (-(1100:ℝ)), Real.exp_pos (-(4400/3:ℝ))])

/-- Row 2200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2200_k4_margin :
    B_8_exact 4 (2200 : ℝ) (2225 : ℝ) ≤ (47.068 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2200 : ℝ) (2225 : ℝ) 2 3176 1.9206e-12
    (47.068 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2200_a2_le row2200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1100_lt, LogTables.exp_neg_4400_3_lt,
                   Real.exp_pos (-(1100:ℝ)), Real.exp_pos (-(4400/3:ℝ))])

/-- Row 2200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2200_k5_margin :
    B_8_exact 5 (2200 : ℝ) (2225 : ℝ) ≤ (104730 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2200 : ℝ) (2225 : ℝ) 2 3176 1.9206e-12
    (104730 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2200_a2_le row2200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1100_lt, LogTables.exp_neg_4400_3_lt,
                   Real.exp_pos (-(1100:ℝ)), Real.exp_pos (-(4400/3:ℝ))])

/-- Row 2225 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2225_k1_margin :
    B_8_exact 1 (2225 : ℝ) (2250 : ℝ) ≤ (0.0000000043204 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2225 : ℝ) (2250 : ℝ) 2 3212 1.9203e-12
    (0.0000000043204 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2225_a2_le row2225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2225_2_lt, LogTables.exp_neg_4450_3_lt,
                   Real.exp_pos (-(2225/2:ℝ)), Real.exp_pos (-(4450/3:ℝ))])

/-- Row 2225 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2225_k2_margin :
    B_8_exact 2 (2225 : ℝ) (2250 : ℝ) ≤ (0.0000097210 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2225 : ℝ) (2250 : ℝ) 2 3212 1.9203e-12
    (0.0000097210 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2225_a2_le row2225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2225_2_lt, LogTables.exp_neg_4450_3_lt,
                   Real.exp_pos (-(2225/2:ℝ)), Real.exp_pos (-(4450/3:ℝ))])

/-- Row 2225 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2225_k3_margin :
    B_8_exact 3 (2225 : ℝ) (2250 : ℝ) ≤ (0.021872 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2225 : ℝ) (2250 : ℝ) 2 3212 1.9203e-12
    (0.021872 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2225_a2_le row2225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2225_2_lt, LogTables.exp_neg_4450_3_lt,
                   Real.exp_pos (-(2225/2:ℝ)), Real.exp_pos (-(4450/3:ℝ))])

/-- Row 2225 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2225_k4_margin :
    B_8_exact 4 (2225 : ℝ) (2250 : ℝ) ≤ (49.212 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2225 : ℝ) (2250 : ℝ) 2 3212 1.9203e-12
    (49.212 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2225_a2_le row2225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2225_2_lt, LogTables.exp_neg_4450_3_lt,
                   Real.exp_pos (-(2225/2:ℝ)), Real.exp_pos (-(4450/3:ℝ))])

/-- Row 2225 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2225_k5_margin :
    B_8_exact 5 (2225 : ℝ) (2250 : ℝ) ≤ (110730 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2225 : ℝ) (2250 : ℝ) 2 3212 1.9203e-12
    (110730 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2225_a2_le row2225_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2225_2_lt, LogTables.exp_neg_4450_3_lt,
                   Real.exp_pos (-(2225/2:ℝ)), Real.exp_pos (-(4450/3:ℝ))])

/-- Row 2250 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2250_k1_margin :
    B_8_exact 1 (2250 : ℝ) (2275 : ℝ) ≤ (0.0000000043679 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2250 : ℝ) (2275 : ℝ) 2 3249 1.9200e-12
    (0.0000000043679 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2250_a2_le row2250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1125_lt, LogTables.exp_neg_1500_lt,
                   Real.exp_pos (-(1125:ℝ)), Real.exp_pos (-(1500:ℝ))])

/-- Row 2250 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2250_k2_margin :
    B_8_exact 2 (2250 : ℝ) (2275 : ℝ) ≤ (0.0000099369 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2250 : ℝ) (2275 : ℝ) 2 3249 1.9200e-12
    (0.0000099369 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2250_a2_le row2250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1125_lt, LogTables.exp_neg_1500_lt,
                   Real.exp_pos (-(1125:ℝ)), Real.exp_pos (-(1500:ℝ))])

/-- Row 2250 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2250_k3_margin :
    B_8_exact 3 (2250 : ℝ) (2275 : ℝ) ≤ (0.022607 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2250 : ℝ) (2275 : ℝ) 2 3249 1.9200e-12
    (0.022607 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2250_a2_le row2250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1125_lt, LogTables.exp_neg_1500_lt,
                   Real.exp_pos (-(1125:ℝ)), Real.exp_pos (-(1500:ℝ))])

/-- Row 2250 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2250_k4_margin :
    B_8_exact 4 (2250 : ℝ) (2275 : ℝ) ≤ (51.430 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2250 : ℝ) (2275 : ℝ) 2 3249 1.9200e-12
    (51.430 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2250_a2_le row2250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1125_lt, LogTables.exp_neg_1500_lt,
                   Real.exp_pos (-(1125:ℝ)), Real.exp_pos (-(1500:ℝ))])

/-- Row 2250 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2250_k5_margin :
    B_8_exact 5 (2250 : ℝ) (2275 : ℝ) ≤ (117000 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2250 : ℝ) (2275 : ℝ) 2 3249 1.9200e-12
    (117000 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2250_a2_le row2250_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1125_lt, LogTables.exp_neg_1500_lt,
                   Real.exp_pos (-(1125:ℝ)), Real.exp_pos (-(1500:ℝ))])

/-- Row 2275 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2275_k1_margin :
    B_8_exact 1 (2275 : ℝ) (2300 : ℝ) ≤ (0.0000000044153 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2275 : ℝ) (2300 : ℝ) 2 3285 1.9198e-12
    (0.0000000044153 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2275_a2_le row2275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2275_2_lt, LogTables.exp_neg_4550_3_lt,
                   Real.exp_pos (-(2275/2:ℝ)), Real.exp_pos (-(4550/3:ℝ))])

/-- Row 2275 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2275_k2_margin :
    B_8_exact 2 (2275 : ℝ) (2300 : ℝ) ≤ (0.000010155 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2275 : ℝ) (2300 : ℝ) 2 3285 1.9198e-12
    (0.000010155 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2275_a2_le row2275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2275_2_lt, LogTables.exp_neg_4550_3_lt,
                   Real.exp_pos (-(2275/2:ℝ)), Real.exp_pos (-(4550/3:ℝ))])

/-- Row 2275 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2275_k3_margin :
    B_8_exact 3 (2275 : ℝ) (2300 : ℝ) ≤ (0.023357 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2275 : ℝ) (2300 : ℝ) 2 3285 1.9198e-12
    (0.023357 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2275_a2_le row2275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2275_2_lt, LogTables.exp_neg_4550_3_lt,
                   Real.exp_pos (-(2275/2:ℝ)), Real.exp_pos (-(4550/3:ℝ))])

/-- Row 2275 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2275_k4_margin :
    B_8_exact 4 (2275 : ℝ) (2300 : ℝ) ≤ (53.721 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2275 : ℝ) (2300 : ℝ) 2 3285 1.9198e-12
    (53.721 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2275_a2_le row2275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2275_2_lt, LogTables.exp_neg_4550_3_lt,
                   Real.exp_pos (-(2275/2:ℝ)), Real.exp_pos (-(4550/3:ℝ))])

/-- Row 2275 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2275_k5_margin :
    B_8_exact 5 (2275 : ℝ) (2300 : ℝ) ≤ (123560 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2275 : ℝ) (2300 : ℝ) 2 3285 1.9198e-12
    (123560 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2275_a2_le row2275_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2275_2_lt, LogTables.exp_neg_4550_3_lt,
                   Real.exp_pos (-(2275/2:ℝ)), Real.exp_pos (-(4550/3:ℝ))])

/-- Row 2300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2300_k1_margin :
    B_8_exact 1 (2300 : ℝ) (2325 : ℝ) ≤ (0.0000000044627 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2300 : ℝ) (2325 : ℝ) 2 3321 1.9195e-12
    (0.0000000044627 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2300_a2_le row2300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1150_lt, LogTables.exp_neg_4600_3_lt,
                   Real.exp_pos (-(1150:ℝ)), Real.exp_pos (-(4600/3:ℝ))])

/-- Row 2300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2300_k2_margin :
    B_8_exact 2 (2300 : ℝ) (2325 : ℝ) ≤ (0.000010376 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2300 : ℝ) (2325 : ℝ) 2 3321 1.9195e-12
    (0.000010376 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2300_a2_le row2300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1150_lt, LogTables.exp_neg_4600_3_lt,
                   Real.exp_pos (-(1150:ℝ)), Real.exp_pos (-(4600/3:ℝ))])

/-- Row 2300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2300_k3_margin :
    B_8_exact 3 (2300 : ℝ) (2325 : ℝ) ≤ (0.024124 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2300 : ℝ) (2325 : ℝ) 2 3321 1.9195e-12
    (0.024124 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2300_a2_le row2300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1150_lt, LogTables.exp_neg_4600_3_lt,
                   Real.exp_pos (-(1150:ℝ)), Real.exp_pos (-(4600/3:ℝ))])

/-- Row 2300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2300_k4_margin :
    B_8_exact 4 (2300 : ℝ) (2325 : ℝ) ≤ (56.088 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2300 : ℝ) (2325 : ℝ) 2 3321 1.9195e-12
    (56.088 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2300_a2_le row2300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1150_lt, LogTables.exp_neg_4600_3_lt,
                   Real.exp_pos (-(1150:ℝ)), Real.exp_pos (-(4600/3:ℝ))])

/-- Row 2300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2300_k5_margin :
    B_8_exact 5 (2300 : ℝ) (2325 : ℝ) ≤ (130400 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2300 : ℝ) (2325 : ℝ) 2 3321 1.9195e-12
    (130400 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2300_a2_le row2300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1150_lt, LogTables.exp_neg_4600_3_lt,
                   Real.exp_pos (-(1150:ℝ)), Real.exp_pos (-(4600/3:ℝ))])

/-- Row 2325 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2325_k1_margin :
    B_8_exact 1 (2325 : ℝ) (2350 : ℝ) ≤ (0.0000000044062 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2325 : ℝ) (2350 : ℝ) 2 3357 1.8751e-12
    (0.0000000044062 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2325_a2_le row2325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2325_2_lt, LogTables.exp_neg_1550_lt,
                   Real.exp_pos (-(2325/2:ℝ)), Real.exp_pos (-(1550:ℝ))])

/-- Row 2325 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2325_k2_margin :
    B_8_exact 2 (2325 : ℝ) (2350 : ℝ) ≤ (0.000010355 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2325 : ℝ) (2350 : ℝ) 2 3357 1.8751e-12
    (0.000010355 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2325_a2_le row2325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2325_2_lt, LogTables.exp_neg_1550_lt,
                   Real.exp_pos (-(2325/2:ℝ)), Real.exp_pos (-(1550:ℝ))])

/-- Row 2325 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2325_k3_margin :
    B_8_exact 3 (2325 : ℝ) (2350 : ℝ) ≤ (0.024333 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2325 : ℝ) (2350 : ℝ) 2 3357 1.8751e-12
    (0.024333 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2325_a2_le row2325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2325_2_lt, LogTables.exp_neg_1550_lt,
                   Real.exp_pos (-(2325/2:ℝ)), Real.exp_pos (-(1550:ℝ))])

/-- Row 2325 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2325_k4_margin :
    B_8_exact 4 (2325 : ℝ) (2350 : ℝ) ≤ (57.184 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2325 : ℝ) (2350 : ℝ) 2 3357 1.8751e-12
    (57.184 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2325_a2_le row2325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2325_2_lt, LogTables.exp_neg_1550_lt,
                   Real.exp_pos (-(2325/2:ℝ)), Real.exp_pos (-(1550:ℝ))])

/-- Row 2325 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2325_k5_margin :
    B_8_exact 5 (2325 : ℝ) (2350 : ℝ) ≤ (134380 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2325 : ℝ) (2350 : ℝ) 2 3357 1.8751e-12
    (134380 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2325_a2_le row2325_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2325_2_lt, LogTables.exp_neg_1550_lt,
                   Real.exp_pos (-(2325/2:ℝ)), Real.exp_pos (-(1550:ℝ))])

/-- Row 2350 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2350_k1_margin :
    B_8_exact 1 (2350 : ℝ) (2375 : ℝ) ≤ (0.0000000042245 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2350 : ℝ) (2375 : ℝ) 2 3393 1.7788e-12
    (0.0000000042245 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2350_a2_le row2350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1175_lt, LogTables.exp_neg_4700_3_lt,
                   Real.exp_pos (-(1175:ℝ)), Real.exp_pos (-(4700/3:ℝ))])

/-- Row 2350 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2350_k2_margin :
    B_8_exact 2 (2350 : ℝ) (2375 : ℝ) ≤ (0.000010033 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2350 : ℝ) (2375 : ℝ) 2 3393 1.7788e-12
    (0.000010033 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2350_a2_le row2350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1175_lt, LogTables.exp_neg_4700_3_lt,
                   Real.exp_pos (-(1175:ℝ)), Real.exp_pos (-(4700/3:ℝ))])

/-- Row 2350 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2350_k3_margin :
    B_8_exact 3 (2350 : ℝ) (2375 : ℝ) ≤ (0.023829 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2350 : ℝ) (2375 : ℝ) 2 3393 1.7788e-12
    (0.023829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2350_a2_le row2350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1175_lt, LogTables.exp_neg_4700_3_lt,
                   Real.exp_pos (-(1175:ℝ)), Real.exp_pos (-(4700/3:ℝ))])

/-- Row 2350 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2350_k4_margin :
    B_8_exact 4 (2350 : ℝ) (2375 : ℝ) ≤ (56.593 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2350 : ℝ) (2375 : ℝ) 2 3393 1.7788e-12
    (56.593 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2350_a2_le row2350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1175_lt, LogTables.exp_neg_4700_3_lt,
                   Real.exp_pos (-(1175:ℝ)), Real.exp_pos (-(4700/3:ℝ))])

/-- Row 2350 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2350_k5_margin :
    B_8_exact 5 (2350 : ℝ) (2375 : ℝ) ≤ (134410 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2350 : ℝ) (2375 : ℝ) 2 3393 1.7788e-12
    (134410 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2350_a2_le row2350_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_1175_lt, LogTables.exp_neg_4700_3_lt,
                   Real.exp_pos (-(1175:ℝ)), Real.exp_pos (-(4700/3:ℝ))])

/-- Row 2375 (k = 1), exact Table-10 margin target. -/
theorem table_10_row2375_k1_margin :
    B_8_exact 1 (2375 : ℝ) (2400 : ℝ) ≤ (0.0000000040498 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (2375 : ℝ) (2400 : ℝ) 2 3429 1.6875e-12
    (0.0000000040498 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2375_a2_le row2375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2375_2_lt, LogTables.exp_neg_4750_3_lt,
                   Real.exp_pos (-(2375/2:ℝ)), Real.exp_pos (-(4750/3:ℝ))])

/-- Row 2375 (k = 2), exact Table-10 margin target. -/
theorem table_10_row2375_k2_margin :
    B_8_exact 2 (2375 : ℝ) (2400 : ℝ) ≤ (0.0000097196 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (2375 : ℝ) (2400 : ℝ) 2 3429 1.6875e-12
    (0.0000097196 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2375_a2_le row2375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2375_2_lt, LogTables.exp_neg_4750_3_lt,
                   Real.exp_pos (-(2375/2:ℝ)), Real.exp_pos (-(4750/3:ℝ))])

/-- Row 2375 (k = 3), exact Table-10 margin target. -/
theorem table_10_row2375_k3_margin :
    B_8_exact 3 (2375 : ℝ) (2400 : ℝ) ≤ (0.023327 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (2375 : ℝ) (2400 : ℝ) 2 3429 1.6875e-12
    (0.023327 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2375_a2_le row2375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2375_2_lt, LogTables.exp_neg_4750_3_lt,
                   Real.exp_pos (-(2375/2:ℝ)), Real.exp_pos (-(4750/3:ℝ))])

/-- Row 2375 (k = 4), exact Table-10 margin target. -/
theorem table_10_row2375_k4_margin :
    B_8_exact 4 (2375 : ℝ) (2400 : ℝ) ≤ (55.985 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (2375 : ℝ) (2400 : ℝ) 2 3429 1.6875e-12
    (55.985 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2375_a2_le row2375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2375_2_lt, LogTables.exp_neg_4750_3_lt,
                   Real.exp_pos (-(2375/2:ℝ)), Real.exp_pos (-(4750/3:ℝ))])

/-- Row 2375 (k = 5), exact Table-10 margin target. -/
theorem table_10_row2375_k5_margin :
    B_8_exact 5 (2375 : ℝ) (2400 : ℝ) ≤ (134360 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (2375 : ℝ) (2400 : ℝ) 2 3429 1.6875e-12
    (134360 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row2375_a2_le row2375_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [LogTables.exp_neg_2375_2_lt, LogTables.exp_neg_4750_3_lt,
                   Real.exp_pos (-(2375/2:ℝ)), Real.exp_pos (-(4750/3:ℝ))])

end BKLNW
