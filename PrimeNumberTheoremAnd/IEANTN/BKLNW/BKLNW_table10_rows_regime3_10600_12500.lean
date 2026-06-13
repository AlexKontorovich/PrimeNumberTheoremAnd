import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Generated regime-3 pointwise Table 10 margin certificates.

This shard expects `row_bound_pointwise`
to be available from `BKLNW_table10_rows_core.lean`.
-/

namespace BKLNW

open Real Set Finset

/-! ## Cached exp(-x) bounds shared across this file's k-margin theorems. -/

private lemma exp_neg_5300_lt : Real.exp (-(5300 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5350_lt : Real.exp (-(5350 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5400_lt : Real.exp (-(5400 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5450_lt : Real.exp (-(5450 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5500_lt : Real.exp (-(5500 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5550_lt : Real.exp (-(5550 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5600_lt : Real.exp (-(5600 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5650_lt : Real.exp (-(5650 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5700_lt : Real.exp (-(5700 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5750_lt : Real.exp (-(5750 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5800_lt : Real.exp (-(5800 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5850_lt : Real.exp (-(5850 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5900_lt : Real.exp (-(5900 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_5950_lt : Real.exp (-(5950 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6000_lt : Real.exp (-(6000 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6050_lt : Real.exp (-(6050 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6100_lt : Real.exp (-(6100 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6150_lt : Real.exp (-(6150 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6200_lt : Real.exp (-(6200 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_6250_lt : Real.exp (-(6250 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_21200_3_lt : Real.exp (-(21200/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_21400_3_lt : Real.exp (-(21400/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_7200_lt : Real.exp (-(7200 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_21800_3_lt : Real.exp (-(21800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_22000_3_lt : Real.exp (-(22000/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_7400_lt : Real.exp (-(7400 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_22400_3_lt : Real.exp (-(22400/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_22600_3_lt : Real.exp (-(22600/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_7600_lt : Real.exp (-(7600 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_23000_3_lt : Real.exp (-(23000/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_23200_3_lt : Real.exp (-(23200/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_7800_lt : Real.exp (-(7800 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_23600_3_lt : Real.exp (-(23600/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_23800_3_lt : Real.exp (-(23800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_8000_lt : Real.exp (-(8000 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_24200_3_lt : Real.exp (-(24200/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_24400_3_lt : Real.exp (-(24400/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_8200_lt : Real.exp (-(8200 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_24800_3_lt : Real.exp (-(24800/3 : ℝ)) < 1e-100 := by interval_decide
private lemma exp_neg_25000_3_lt : Real.exp (-(25000/3 : ℝ)) < 1e-100 := by interval_decide



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


private lemma row10600_a2_le : Inputs.default.a₂ (10600 : ℝ) ≤ (15295 : ℝ) := by
  have h := a2_crude_le (10600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10600 : ℝ) / log 2⌋₊ : ℝ) ≤ (10600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10600 : ℝ) / log 2 ≤ 15293 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15293 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15295 := by norm_num


private lemma row10700_a2_le : Inputs.default.a₂ (10700 : ℝ) ≤ (15439 : ℝ) := by
  have h := a2_crude_le (10700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10700 : ℝ) / log 2⌋₊ : ℝ) ≤ (10700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10700 : ℝ) / log 2 ≤ 15437 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15437 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15439 := by norm_num


private lemma row10800_a2_le : Inputs.default.a₂ (10800 : ℝ) ≤ (15584 : ℝ) := by
  have h := a2_crude_le (10800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10800 : ℝ) / log 2⌋₊ : ℝ) ≤ (10800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10800 : ℝ) / log 2 ≤ 15582 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15582 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15584 := by norm_num


private lemma row10900_a2_le : Inputs.default.a₂ (10900 : ℝ) ≤ (15728 : ℝ) := by
  have h := a2_crude_le (10900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(10900 : ℝ) / log 2⌋₊ : ℝ) ≤ (10900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (10900 : ℝ) / log 2 ≤ 15726 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (10900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(10900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15726 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15728 := by norm_num


private lemma row11000_a2_le : Inputs.default.a₂ (11000 : ℝ) ≤ (15872 : ℝ) := by
  have h := a2_crude_le (11000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11000 : ℝ) / log 2⌋₊ : ℝ) ≤ (11000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11000 : ℝ) / log 2 ≤ 15870 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (15870 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 15872 := by norm_num


private lemma row11100_a2_le : Inputs.default.a₂ (11100 : ℝ) ≤ (16016 : ℝ) := by
  have h := a2_crude_le (11100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11100 : ℝ) / log 2⌋₊ : ℝ) ≤ (11100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11100 : ℝ) / log 2 ≤ 16014 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16014 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16016 := by norm_num


private lemma row11200_a2_le : Inputs.default.a₂ (11200 : ℝ) ≤ (16161 : ℝ) := by
  have h := a2_crude_le (11200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11200 : ℝ) / log 2⌋₊ : ℝ) ≤ (11200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11200 : ℝ) / log 2 ≤ 16159 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16159 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16161 := by norm_num


private lemma row11300_a2_le : Inputs.default.a₂ (11300 : ℝ) ≤ (16305 : ℝ) := by
  have h := a2_crude_le (11300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11300 : ℝ) / log 2⌋₊ : ℝ) ≤ (11300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11300 : ℝ) / log 2 ≤ 16303 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16303 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16305 := by norm_num


private lemma row11400_a2_le : Inputs.default.a₂ (11400 : ℝ) ≤ (16449 : ℝ) := by
  have h := a2_crude_le (11400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11400 : ℝ) / log 2⌋₊ : ℝ) ≤ (11400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11400 : ℝ) / log 2 ≤ 16447 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16447 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16449 := by norm_num


private lemma row11500_a2_le : Inputs.default.a₂ (11500 : ℝ) ≤ (16593 : ℝ) := by
  have h := a2_crude_le (11500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11500 : ℝ) / log 2⌋₊ : ℝ) ≤ (11500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11500 : ℝ) / log 2 ≤ 16591 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16591 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16593 := by norm_num


private lemma row11600_a2_le : Inputs.default.a₂ (11600 : ℝ) ≤ (16738 : ℝ) := by
  have h := a2_crude_le (11600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11600 : ℝ) / log 2⌋₊ : ℝ) ≤ (11600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11600 : ℝ) / log 2 ≤ 16736 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16736 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16738 := by norm_num


private lemma row11700_a2_le : Inputs.default.a₂ (11700 : ℝ) ≤ (16882 : ℝ) := by
  have h := a2_crude_le (11700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11700 : ℝ) / log 2⌋₊ : ℝ) ≤ (11700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11700 : ℝ) / log 2 ≤ 16880 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (16880 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 16882 := by norm_num


private lemma row11800_a2_le : Inputs.default.a₂ (11800 : ℝ) ≤ (17026 : ℝ) := by
  have h := a2_crude_le (11800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11800 : ℝ) / log 2⌋₊ : ℝ) ≤ (11800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11800 : ℝ) / log 2 ≤ 17024 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17024 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17026 := by norm_num


private lemma row11900_a2_le : Inputs.default.a₂ (11900 : ℝ) ≤ (17171 : ℝ) := by
  have h := a2_crude_le (11900 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(11900 : ℝ) / log 2⌋₊ : ℝ) ≤ (11900 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (11900 : ℝ) / log 2 ≤ 17169 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (11900 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(11900 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17169 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17171 := by norm_num


private lemma row12000_a2_le : Inputs.default.a₂ (12000 : ℝ) ≤ (17315 : ℝ) := by
  have h := a2_crude_le (12000 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12000 : ℝ) / log 2⌋₊ : ℝ) ≤ (12000 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12000 : ℝ) / log 2 ≤ 17313 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12000 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12000 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17313 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17315 := by norm_num


private lemma row12100_a2_le : Inputs.default.a₂ (12100 : ℝ) ≤ (17459 : ℝ) := by
  have h := a2_crude_le (12100 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12100 : ℝ) / log 2⌋₊ : ℝ) ≤ (12100 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12100 : ℝ) / log 2 ≤ 17457 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12100 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12100 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17457 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17459 := by norm_num


private lemma row12200_a2_le : Inputs.default.a₂ (12200 : ℝ) ≤ (17603 : ℝ) := by
  have h := a2_crude_le (12200 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12200 : ℝ) / log 2⌋₊ : ℝ) ≤ (12200 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12200 : ℝ) / log 2 ≤ 17601 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12200 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12200 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17601 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17603 := by norm_num


private lemma row12300_a2_le : Inputs.default.a₂ (12300 : ℝ) ≤ (17748 : ℝ) := by
  have h := a2_crude_le (12300 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12300 : ℝ) / log 2⌋₊ : ℝ) ≤ (12300 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12300 : ℝ) / log 2 ≤ 17746 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12300 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12300 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17746 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17748 := by norm_num


private lemma row12400_a2_le : Inputs.default.a₂ (12400 : ℝ) ≤ (17892 : ℝ) := by
  have h := a2_crude_le (12400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12400 : ℝ) / log 2⌋₊ : ℝ) ≤ (12400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12400 : ℝ) / log 2 ≤ 17890 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (17890 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 17892 := by norm_num


private lemma row12500_a2_le : Inputs.default.a₂ (12500 : ℝ) ≤ (18036 : ℝ) := by
  have h := a2_crude_le (12500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := LogTables.log_2_gt_d9
  have hfloor : (⌊(12500 : ℝ) / log 2⌋₊ : ℝ) ≤ (12500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (12500 : ℝ) / log 2 ≤ 18034 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (12500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(12500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (18034 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 18036 := by norm_num


set_option maxRecDepth 10000 in
private lemma row10600_table8_mem : (10600, 3.4435e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10600_eps_le : Inputs.default.ε (10600 : ℝ) ≤ 3.4435e-30 := by
  change BKLNW_app.table_8_ε (10600 : ℝ) ≤ 3.4435e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10600)
    (ε := 3.4435e-30) row10600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row10700_table8_mem : (10700, 2.3288e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10700_eps_le : Inputs.default.ε (10700 : ℝ) ≤ 2.3288e-30 := by
  change BKLNW_app.table_8_ε (10700 : ℝ) ≤ 2.3288e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10700)
    (ε := 2.3288e-30) row10700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row10800_table8_mem : (10800, 1.5782e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10800_eps_le : Inputs.default.ε (10800 : ℝ) ≤ 1.5782e-30 := by
  change BKLNW_app.table_8_ε (10800 : ℝ) ≤ 1.5782e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10800)
    (ε := 1.5782e-30) row10800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row10900_table8_mem : (10900, 1.0582e-30) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row10900_eps_le : Inputs.default.ε (10900 : ℝ) ≤ 1.0582e-30 := by
  change BKLNW_app.table_8_ε (10900 : ℝ) ≤ 1.0582e-30
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 10900)
    (ε := 1.0582e-30) row10900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11000_table8_mem : (11000, 7.1427e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11000_eps_le : Inputs.default.ε (11000 : ℝ) ≤ 7.1427e-31 := by
  change BKLNW_app.table_8_ε (11000 : ℝ) ≤ 7.1427e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11000)
    (ε := 7.1427e-31) row11000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11100_table8_mem : (11100, 4.8354e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11100_eps_le : Inputs.default.ε (11100 : ℝ) ≤ 4.8354e-31 := by
  change BKLNW_app.table_8_ε (11100 : ℝ) ≤ 4.8354e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11100)
    (ε := 4.8354e-31) row11100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11200_table8_mem : (11200, 3.2850e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11200_eps_le : Inputs.default.ε (11200 : ℝ) ≤ 3.2850e-31 := by
  change BKLNW_app.table_8_ε (11200 : ℝ) ≤ 3.2850e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11200)
    (ε := 3.2850e-31) row11200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11300_table8_mem : (11300, 2.2377e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11300_eps_le : Inputs.default.ε (11300 : ℝ) ≤ 2.2377e-31 := by
  change BKLNW_app.table_8_ε (11300 : ℝ) ≤ 2.2377e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11300)
    (ε := 2.2377e-31) row11300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11400_table8_mem : (11400, 1.5279e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11400_eps_le : Inputs.default.ε (11400 : ℝ) ≤ 1.5279e-31 := by
  change BKLNW_app.table_8_ε (11400 : ℝ) ≤ 1.5279e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11400)
    (ε := 1.5279e-31) row11400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11500_table8_mem : (11500, 1.0434e-31) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11500_eps_le : Inputs.default.ε (11500 : ℝ) ≤ 1.0434e-31 := by
  change BKLNW_app.table_8_ε (11500 : ℝ) ≤ 1.0434e-31
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11500)
    (ε := 1.0434e-31) row11500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11600_table8_mem : (11600, 7.1321e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11600_eps_le : Inputs.default.ε (11600 : ℝ) ≤ 7.1321e-32 := by
  change BKLNW_app.table_8_ε (11600 : ℝ) ≤ 7.1321e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11600)
    (ε := 7.1321e-32) row11600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11700_table8_mem : (11700, 4.8892e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11700_eps_le : Inputs.default.ε (11700 : ℝ) ≤ 4.8892e-32 := by
  change BKLNW_app.table_8_ε (11700 : ℝ) ≤ 4.8892e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11700)
    (ε := 4.8892e-32) row11700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11800_table8_mem : (11800, 3.3603e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11800_eps_le : Inputs.default.ε (11800 : ℝ) ≤ 3.3603e-32 := by
  change BKLNW_app.table_8_ε (11800 : ℝ) ≤ 3.3603e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11800)
    (ε := 3.3603e-32) row11800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row11900_table8_mem : (11900, 2.3147e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row11900_eps_le : Inputs.default.ε (11900 : ℝ) ≤ 2.3147e-32 := by
  change BKLNW_app.table_8_ε (11900 : ℝ) ≤ 2.3147e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 11900)
    (ε := 2.3147e-32) row11900_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12000_table8_mem : (12000, 1.5976e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12000_eps_le : Inputs.default.ε (12000 : ℝ) ≤ 1.5976e-32 := by
  change BKLNW_app.table_8_ε (12000 : ℝ) ≤ 1.5976e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12000)
    (ε := 1.5976e-32) row12000_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12100_table8_mem : (12100, 1.1048e-32) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12100_eps_le : Inputs.default.ε (12100 : ℝ) ≤ 1.1048e-32 := by
  change BKLNW_app.table_8_ε (12100 : ℝ) ≤ 1.1048e-32
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12100)
    (ε := 1.1048e-32) row12100_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12200_table8_mem : (12200, 7.5730e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12200_eps_le : Inputs.default.ε (12200 : ℝ) ≤ 7.5730e-33 := by
  change BKLNW_app.table_8_ε (12200 : ℝ) ≤ 7.5730e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12200)
    (ε := 7.5730e-33) row12200_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12300_table8_mem : (12300, 5.2476e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12300_eps_le : Inputs.default.ε (12300 : ℝ) ≤ 5.2476e-33 := by
  change BKLNW_app.table_8_ε (12300 : ℝ) ≤ 5.2476e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12300)
    (ε := 5.2476e-33) row12300_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12400_table8_mem : (12400, 3.6432e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12400_eps_le : Inputs.default.ε (12400 : ℝ) ≤ 3.6432e-33 := by
  change BKLNW_app.table_8_ε (12400 : ℝ) ≤ 3.6432e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12400)
    (ε := 3.6432e-33) row12400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row12500_table8_mem : (12500, 2.5337e-33) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row12500_eps_le : Inputs.default.ε (12500 : ℝ) ≤ 2.5337e-33 := by
  change BKLNW_app.table_8_ε (12500 : ℝ) ≤ 2.5337e-33
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 12500)
    (ε := 2.5337e-33) row12500_table8_mem (by norm_num)


/-- Row 10600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10600_k1_margin :
    B_8_exact 1 (10600 : ℝ) (10700 : ℝ) ≤ (0.000000000000000000000000036845 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10600 : ℝ) (10700 : ℝ) 2 15295 3.4435e-30
    (0.000000000000000000000000036845 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10600_a2_le row10600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5300_lt, exp_neg_21200_3_lt,
                   Real.exp_pos (-(5300:ℝ)), Real.exp_pos (-(21200/3:ℝ))])


/-- Row 10600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10600_k2_margin :
    B_8_exact 2 (10600 : ℝ) (10700 : ℝ) ≤ (0.00000000000000000000039424 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10600 : ℝ) (10700 : ℝ) 2 15295 3.4435e-30
    (0.00000000000000000000039424 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10600_a2_le row10600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5300_lt, exp_neg_21200_3_lt,
                   Real.exp_pos (-(5300:ℝ)), Real.exp_pos (-(21200/3:ℝ))])


/-- Row 10600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10600_k3_margin :
    B_8_exact 3 (10600 : ℝ) (10700 : ℝ) ≤ (0.0000000000000000042184 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10600 : ℝ) (10700 : ℝ) 2 15295 3.4435e-30
    (0.0000000000000000042184 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10600_a2_le row10600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5300_lt, exp_neg_21200_3_lt,
                   Real.exp_pos (-(5300:ℝ)), Real.exp_pos (-(21200/3:ℝ))])


/-- Row 10600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10600_k4_margin :
    B_8_exact 4 (10600 : ℝ) (10700 : ℝ) ≤ (0.000000000000045136 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10600 : ℝ) (10700 : ℝ) 2 15295 3.4435e-30
    (0.000000000000045136 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10600_a2_le row10600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5300_lt, exp_neg_21200_3_lt,
                   Real.exp_pos (-(5300:ℝ)), Real.exp_pos (-(21200/3:ℝ))])


/-- Row 10600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10600_k5_margin :
    B_8_exact 5 (10600 : ℝ) (10700 : ℝ) ≤ (0.00000000048296 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10600 : ℝ) (10700 : ℝ) 2 15295 3.4435e-30
    (0.00000000048296 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10600_a2_le row10600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5300_lt, exp_neg_21200_3_lt,
                   Real.exp_pos (-(5300:ℝ)), Real.exp_pos (-(21200/3:ℝ))])


/-- Row 10700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10700_k1_margin :
    B_8_exact 1 (10700 : ℝ) (10800 : ℝ) ≤ (0.000000000000000000000000025150 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10700 : ℝ) (10800 : ℝ) 2 15439 2.3288e-30
    (0.000000000000000000000000025150 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10700_a2_le row10700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5350_lt, exp_neg_21400_3_lt,
                   Real.exp_pos (-(5350:ℝ)), Real.exp_pos (-(21400/3:ℝ))])


/-- Row 10700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10700_k2_margin :
    B_8_exact 2 (10700 : ℝ) (10800 : ℝ) ≤ (0.00000000000000000000027162 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10700 : ℝ) (10800 : ℝ) 2 15439 2.3288e-30
    (0.00000000000000000000027162 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10700_a2_le row10700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5350_lt, exp_neg_21400_3_lt,
                   Real.exp_pos (-(5350:ℝ)), Real.exp_pos (-(21400/3:ℝ))])


/-- Row 10700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10700_k3_margin :
    B_8_exact 3 (10700 : ℝ) (10800 : ℝ) ≤ (0.0000000000000000029335 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10700 : ℝ) (10800 : ℝ) 2 15439 2.3288e-30
    (0.0000000000000000029335 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10700_a2_le row10700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5350_lt, exp_neg_21400_3_lt,
                   Real.exp_pos (-(5350:ℝ)), Real.exp_pos (-(21400/3:ℝ))])


/-- Row 10700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10700_k4_margin :
    B_8_exact 4 (10700 : ℝ) (10800 : ℝ) ≤ (0.000000000000031682 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10700 : ℝ) (10800 : ℝ) 2 15439 2.3288e-30
    (0.000000000000031682 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10700_a2_le row10700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5350_lt, exp_neg_21400_3_lt,
                   Real.exp_pos (-(5350:ℝ)), Real.exp_pos (-(21400/3:ℝ))])


/-- Row 10700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10700_k5_margin :
    B_8_exact 5 (10700 : ℝ) (10800 : ℝ) ≤ (0.00000000034216 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10700 : ℝ) (10800 : ℝ) 2 15439 2.3288e-30
    (0.00000000034216 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10700_a2_le row10700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5350_lt, exp_neg_21400_3_lt,
                   Real.exp_pos (-(5350:ℝ)), Real.exp_pos (-(21400/3:ℝ))])


/-- Row 10800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10800_k1_margin :
    B_8_exact 1 (10800 : ℝ) (10900 : ℝ) ≤ (0.000000000000000000000000017201 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10800 : ℝ) (10900 : ℝ) 2 15584 1.5782e-30
    (0.000000000000000000000000017201 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10800_a2_le row10800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5400_lt, exp_neg_7200_lt,
                   Real.exp_pos (-(5400:ℝ)), Real.exp_pos (-(7200:ℝ))])


/-- Row 10800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10800_k2_margin :
    B_8_exact 2 (10800 : ℝ) (10900 : ℝ) ≤ (0.00000000000000000000018749 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10800 : ℝ) (10900 : ℝ) 2 15584 1.5782e-30
    (0.00000000000000000000018749 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10800_a2_le row10800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5400_lt, exp_neg_7200_lt,
                   Real.exp_pos (-(5400:ℝ)), Real.exp_pos (-(7200:ℝ))])


/-- Row 10800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10800_k3_margin :
    B_8_exact 3 (10800 : ℝ) (10900 : ℝ) ≤ (0.0000000000000000020436 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10800 : ℝ) (10900 : ℝ) 2 15584 1.5782e-30
    (0.0000000000000000020436 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10800_a2_le row10800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5400_lt, exp_neg_7200_lt,
                   Real.exp_pos (-(5400:ℝ)), Real.exp_pos (-(7200:ℝ))])


/-- Row 10800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10800_k4_margin :
    B_8_exact 4 (10800 : ℝ) (10900 : ℝ) ≤ (0.000000000000022276 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10800 : ℝ) (10900 : ℝ) 2 15584 1.5782e-30
    (0.000000000000022276 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10800_a2_le row10800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5400_lt, exp_neg_7200_lt,
                   Real.exp_pos (-(5400:ℝ)), Real.exp_pos (-(7200:ℝ))])


/-- Row 10800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10800_k5_margin :
    B_8_exact 5 (10800 : ℝ) (10900 : ℝ) ≤ (0.00000000024280 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10800 : ℝ) (10900 : ℝ) 2 15584 1.5782e-30
    (0.00000000024280 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10800_a2_le row10800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5400_lt, exp_neg_7200_lt,
                   Real.exp_pos (-(5400:ℝ)), Real.exp_pos (-(7200:ℝ))])


/-- Row 10900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row10900_k1_margin :
    B_8_exact 1 (10900 : ℝ) (11000 : ℝ) ≤ (0.000000000000000000000000011639 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (10900 : ℝ) (11000 : ℝ) 2 15728 1.0582e-30
    (0.000000000000000000000000011639 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10900_a2_le row10900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5450_lt, exp_neg_21800_3_lt,
                   Real.exp_pos (-(5450:ℝ)), Real.exp_pos (-(21800/3:ℝ))])


/-- Row 10900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row10900_k2_margin :
    B_8_exact 2 (10900 : ℝ) (11000 : ℝ) ≤ (0.00000000000000000000012803 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (10900 : ℝ) (11000 : ℝ) 2 15728 1.0582e-30
    (0.00000000000000000000012803 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10900_a2_le row10900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5450_lt, exp_neg_21800_3_lt,
                   Real.exp_pos (-(5450:ℝ)), Real.exp_pos (-(21800/3:ℝ))])


/-- Row 10900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row10900_k3_margin :
    B_8_exact 3 (10900 : ℝ) (11000 : ℝ) ≤ (0.0000000000000000014083 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (10900 : ℝ) (11000 : ℝ) 2 15728 1.0582e-30
    (0.0000000000000000014083 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10900_a2_le row10900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5450_lt, exp_neg_21800_3_lt,
                   Real.exp_pos (-(5450:ℝ)), Real.exp_pos (-(21800/3:ℝ))])


/-- Row 10900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row10900_k4_margin :
    B_8_exact 4 (10900 : ℝ) (11000 : ℝ) ≤ (0.000000000000015492 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (10900 : ℝ) (11000 : ℝ) 2 15728 1.0582e-30
    (0.000000000000015492 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10900_a2_le row10900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5450_lt, exp_neg_21800_3_lt,
                   Real.exp_pos (-(5450:ℝ)), Real.exp_pos (-(21800/3:ℝ))])


/-- Row 10900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row10900_k5_margin :
    B_8_exact 5 (10900 : ℝ) (11000 : ℝ) ≤ (0.00000000017041 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (10900 : ℝ) (11000 : ℝ) 2 15728 1.0582e-30
    (0.00000000017041 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row10900_a2_le row10900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5450_lt, exp_neg_21800_3_lt,
                   Real.exp_pos (-(5450:ℝ)), Real.exp_pos (-(21800/3:ℝ))])


/-- Row 11000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11000_k1_margin :
    B_8_exact 1 (11000 : ℝ) (11100 : ℝ) ≤ (0.0000000000000000000000000079283 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11000 : ℝ) (11100 : ℝ) 2 15872 7.1427e-31
    (0.0000000000000000000000000079283 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11000_a2_le row11000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5500_lt, exp_neg_22000_3_lt,
                   Real.exp_pos (-(5500:ℝ)), Real.exp_pos (-(22000/3:ℝ))])


/-- Row 11000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11000_k2_margin :
    B_8_exact 2 (11000 : ℝ) (11100 : ℝ) ≤ (0.000000000000000000000088005 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11000 : ℝ) (11100 : ℝ) 2 15872 7.1427e-31
    (0.000000000000000000000088005 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11000_a2_le row11000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5500_lt, exp_neg_22000_3_lt,
                   Real.exp_pos (-(5500:ℝ)), Real.exp_pos (-(22000/3:ℝ))])


/-- Row 11000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11000_k3_margin :
    B_8_exact 3 (11000 : ℝ) (11100 : ℝ) ≤ (0.00000000000000000097685 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11000 : ℝ) (11100 : ℝ) 2 15872 7.1427e-31
    (0.00000000000000000097685 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11000_a2_le row11000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5500_lt, exp_neg_22000_3_lt,
                   Real.exp_pos (-(5500:ℝ)), Real.exp_pos (-(22000/3:ℝ))])


/-- Row 11000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11000_k4_margin :
    B_8_exact 4 (11000 : ℝ) (11100 : ℝ) ≤ (0.000000000000010843 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11000 : ℝ) (11100 : ℝ) 2 15872 7.1427e-31
    (0.000000000000010843 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11000_a2_le row11000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5500_lt, exp_neg_22000_3_lt,
                   Real.exp_pos (-(5500:ℝ)), Real.exp_pos (-(22000/3:ℝ))])


/-- Row 11000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11000_k5_margin :
    B_8_exact 5 (11000 : ℝ) (11100 : ℝ) ≤ (0.00000000012036 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11000 : ℝ) (11100 : ℝ) 2 15872 7.1427e-31
    (0.00000000012036 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11000_a2_le row11000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5500_lt, exp_neg_22000_3_lt,
                   Real.exp_pos (-(5500:ℝ)), Real.exp_pos (-(22000/3:ℝ))])


/-- Row 11100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11100_k1_margin :
    B_8_exact 1 (11100 : ℝ) (11200 : ℝ) ≤ (0.0000000000000000000000000054156 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11100 : ℝ) (11200 : ℝ) 2 16016 4.8354e-31
    (0.0000000000000000000000000054156 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11100_a2_le row11100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5550_lt, exp_neg_7400_lt,
                   Real.exp_pos (-(5550:ℝ)), Real.exp_pos (-(7400:ℝ))])


/-- Row 11100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11100_k2_margin :
    B_8_exact 2 (11100 : ℝ) (11200 : ℝ) ≤ (0.000000000000000000000060654 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11100 : ℝ) (11200 : ℝ) 2 16016 4.8354e-31
    (0.000000000000000000000060654 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11100_a2_le row11100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5550_lt, exp_neg_7400_lt,
                   Real.exp_pos (-(5550:ℝ)), Real.exp_pos (-(7400:ℝ))])


/-- Row 11100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11100_k3_margin :
    B_8_exact 3 (11100 : ℝ) (11200 : ℝ) ≤ (0.00000000000000000067933 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11100 : ℝ) (11200 : ℝ) 2 16016 4.8354e-31
    (0.00000000000000000067933 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11100_a2_le row11100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5550_lt, exp_neg_7400_lt,
                   Real.exp_pos (-(5550:ℝ)), Real.exp_pos (-(7400:ℝ))])


/-- Row 11100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11100_k4_margin :
    B_8_exact 4 (11100 : ℝ) (11200 : ℝ) ≤ (0.0000000000000076085 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11100 : ℝ) (11200 : ℝ) 2 16016 4.8354e-31
    (0.0000000000000076085 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11100_a2_le row11100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5550_lt, exp_neg_7400_lt,
                   Real.exp_pos (-(5550:ℝ)), Real.exp_pos (-(7400:ℝ))])


/-- Row 11100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11100_k5_margin :
    B_8_exact 5 (11100 : ℝ) (11200 : ℝ) ≤ (0.000000000085215 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11100 : ℝ) (11200 : ℝ) 2 16016 4.8354e-31
    (0.000000000085215 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11100_a2_le row11100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5550_lt, exp_neg_7400_lt,
                   Real.exp_pos (-(5550:ℝ)), Real.exp_pos (-(7400:ℝ))])


/-- Row 11200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11200_k1_margin :
    B_8_exact 1 (11200 : ℝ) (11300 : ℝ) ≤ (0.0000000000000000000000000037120 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11200 : ℝ) (11300 : ℝ) 2 16161 3.2850e-31
    (0.0000000000000000000000000037120 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11200_a2_le row11200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5600_lt, exp_neg_22400_3_lt,
                   Real.exp_pos (-(5600:ℝ)), Real.exp_pos (-(22400/3:ℝ))])


/-- Row 11200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11200_k2_margin :
    B_8_exact 2 (11200 : ℝ) (11300 : ℝ) ≤ (0.000000000000000000000041945 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11200 : ℝ) (11300 : ℝ) 2 16161 3.2850e-31
    (0.000000000000000000000041945 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11200_a2_le row11200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5600_lt, exp_neg_22400_3_lt,
                   Real.exp_pos (-(5600:ℝ)), Real.exp_pos (-(22400/3:ℝ))])


/-- Row 11200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11200_k3_margin :
    B_8_exact 3 (11200 : ℝ) (11300 : ℝ) ≤ (0.00000000000000000047398 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11200 : ℝ) (11300 : ℝ) 2 16161 3.2850e-31
    (0.00000000000000000047398 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11200_a2_le row11200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5600_lt, exp_neg_22400_3_lt,
                   Real.exp_pos (-(5600:ℝ)), Real.exp_pos (-(22400/3:ℝ))])


/-- Row 11200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11200_k4_margin :
    B_8_exact 4 (11200 : ℝ) (11300 : ℝ) ≤ (0.0000000000000053560 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11200 : ℝ) (11300 : ℝ) 2 16161 3.2850e-31
    (0.0000000000000053560 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11200_a2_le row11200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5600_lt, exp_neg_22400_3_lt,
                   Real.exp_pos (-(5600:ℝ)), Real.exp_pos (-(22400/3:ℝ))])


/-- Row 11200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11200_k5_margin :
    B_8_exact 5 (11200 : ℝ) (11300 : ℝ) ≤ (0.000000000060522 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11200 : ℝ) (11300 : ℝ) 2 16161 3.2850e-31
    (0.000000000060522 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11200_a2_le row11200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5600_lt, exp_neg_22400_3_lt,
                   Real.exp_pos (-(5600:ℝ)), Real.exp_pos (-(22400/3:ℝ))])


/-- Row 11300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11300_k1_margin :
    B_8_exact 1 (11300 : ℝ) (11400 : ℝ) ≤ (0.0000000000000000000000000025509 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11300 : ℝ) (11400 : ℝ) 2 16305 2.2377e-31
    (0.0000000000000000000000000025509 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11300_a2_le row11300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5650_lt, exp_neg_22600_3_lt,
                   Real.exp_pos (-(5650:ℝ)), Real.exp_pos (-(22600/3:ℝ))])


/-- Row 11300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11300_k2_margin :
    B_8_exact 2 (11300 : ℝ) (11400 : ℝ) ≤ (0.000000000000000000000029080 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11300 : ℝ) (11400 : ℝ) 2 16305 2.2377e-31
    (0.000000000000000000000029080 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11300_a2_le row11300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5650_lt, exp_neg_22600_3_lt,
                   Real.exp_pos (-(5650:ℝ)), Real.exp_pos (-(22600/3:ℝ))])


/-- Row 11300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11300_k3_margin :
    B_8_exact 3 (11300 : ℝ) (11400 : ℝ) ≤ (0.00000000000000000033151 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11300 : ℝ) (11400 : ℝ) 2 16305 2.2377e-31
    (0.00000000000000000033151 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11300_a2_le row11300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5650_lt, exp_neg_22600_3_lt,
                   Real.exp_pos (-(5650:ℝ)), Real.exp_pos (-(22600/3:ℝ))])


/-- Row 11300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11300_k4_margin :
    B_8_exact 4 (11300 : ℝ) (11400 : ℝ) ≤ (0.0000000000000037792 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11300 : ℝ) (11400 : ℝ) 2 16305 2.2377e-31
    (0.0000000000000037792 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11300_a2_le row11300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5650_lt, exp_neg_22600_3_lt,
                   Real.exp_pos (-(5650:ℝ)), Real.exp_pos (-(22600/3:ℝ))])


/-- Row 11300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11300_k5_margin :
    B_8_exact 5 (11300 : ℝ) (11400 : ℝ) ≤ (0.000000000043083 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11300 : ℝ) (11400 : ℝ) 2 16305 2.2377e-31
    (0.000000000043083 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11300_a2_le row11300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5650_lt, exp_neg_22600_3_lt,
                   Real.exp_pos (-(5650:ℝ)), Real.exp_pos (-(22600/3:ℝ))])


/-- Row 11400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11400_k1_margin :
    B_8_exact 1 (11400 : ℝ) (11500 : ℝ) ≤ (0.0000000000000000000000000017569 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11400 : ℝ) (11500 : ℝ) 2 16449 1.5279e-31
    (0.0000000000000000000000000017569 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11400_a2_le row11400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5700_lt, exp_neg_7600_lt,
                   Real.exp_pos (-(5700:ℝ)), Real.exp_pos (-(7600:ℝ))])


/-- Row 11400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11400_k2_margin :
    B_8_exact 2 (11400 : ℝ) (11500 : ℝ) ≤ (0.000000000000000000000020205 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11400 : ℝ) (11500 : ℝ) 2 16449 1.5279e-31
    (0.000000000000000000000020205 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11400_a2_le row11400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5700_lt, exp_neg_7600_lt,
                   Real.exp_pos (-(5700:ℝ)), Real.exp_pos (-(7600:ℝ))])


/-- Row 11400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11400_k3_margin :
    B_8_exact 3 (11400 : ℝ) (11500 : ℝ) ≤ (0.00000000000000000023235 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11400 : ℝ) (11500 : ℝ) 2 16449 1.5279e-31
    (0.00000000000000000023235 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11400_a2_le row11400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5700_lt, exp_neg_7600_lt,
                   Real.exp_pos (-(5700:ℝ)), Real.exp_pos (-(7600:ℝ))])


/-- Row 11400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11400_k4_margin :
    B_8_exact 4 (11400 : ℝ) (11500 : ℝ) ≤ (0.0000000000000026721 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11400 : ℝ) (11500 : ℝ) 2 16449 1.5279e-31
    (0.0000000000000026721 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11400_a2_le row11400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5700_lt, exp_neg_7600_lt,
                   Real.exp_pos (-(5700:ℝ)), Real.exp_pos (-(7600:ℝ))])


/-- Row 11400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11400_k5_margin :
    B_8_exact 5 (11400 : ℝ) (11500 : ℝ) ≤ (0.000000000030729 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11400 : ℝ) (11500 : ℝ) 2 16449 1.5279e-31
    (0.000000000030729 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11400_a2_le row11400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5700_lt, exp_neg_7600_lt,
                   Real.exp_pos (-(5700:ℝ)), Real.exp_pos (-(7600:ℝ))])


/-- Row 11500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11500_k1_margin :
    B_8_exact 1 (11500 : ℝ) (11600 : ℝ) ≤ (0.0000000000000000000000000012102 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11500 : ℝ) (11600 : ℝ) 2 16593 1.0434e-31
    (0.0000000000000000000000000012102 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11500_a2_le row11500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5750_lt, exp_neg_23000_3_lt,
                   Real.exp_pos (-(5750:ℝ)), Real.exp_pos (-(23000/3:ℝ))])


/-- Row 11500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11500_k2_margin :
    B_8_exact 2 (11500 : ℝ) (11600 : ℝ) ≤ (0.000000000000000000000014039 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11500 : ℝ) (11600 : ℝ) 2 16593 1.0434e-31
    (0.000000000000000000000014039 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11500_a2_le row11500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5750_lt, exp_neg_23000_3_lt,
                   Real.exp_pos (-(5750:ℝ)), Real.exp_pos (-(23000/3:ℝ))])


/-- Row 11500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11500_k3_margin :
    B_8_exact 3 (11500 : ℝ) (11600 : ℝ) ≤ (0.00000000000000000016285 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11500 : ℝ) (11600 : ℝ) 2 16593 1.0434e-31
    (0.00000000000000000016285 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11500_a2_le row11500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5750_lt, exp_neg_23000_3_lt,
                   Real.exp_pos (-(5750:ℝ)), Real.exp_pos (-(23000/3:ℝ))])


/-- Row 11500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11500_k4_margin :
    B_8_exact 4 (11500 : ℝ) (11600 : ℝ) ≤ (0.0000000000000018890 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11500 : ℝ) (11600 : ℝ) 2 16593 1.0434e-31
    (0.0000000000000018890 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11500_a2_le row11500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5750_lt, exp_neg_23000_3_lt,
                   Real.exp_pos (-(5750:ℝ)), Real.exp_pos (-(23000/3:ℝ))])


/-- Row 11500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11500_k5_margin :
    B_8_exact 5 (11500 : ℝ) (11600 : ℝ) ≤ (0.000000000021913 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11500 : ℝ) (11600 : ℝ) 2 16593 1.0434e-31
    (0.000000000021913 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11500_a2_le row11500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5750_lt, exp_neg_23000_3_lt,
                   Real.exp_pos (-(5750:ℝ)), Real.exp_pos (-(23000/3:ℝ))])


/-- Row 11600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11600_k1_margin :
    B_8_exact 1 (11600 : ℝ) (11700 : ℝ) ≤ (0.00000000000000000000000000083444 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11600 : ℝ) (11700 : ℝ) 2 16738 7.1321e-32
    (0.00000000000000000000000000083444 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11600_a2_le row11600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5800_lt, exp_neg_23200_3_lt,
                   Real.exp_pos (-(5800:ℝ)), Real.exp_pos (-(23200/3:ℝ))])


/-- Row 11600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11600_k2_margin :
    B_8_exact 2 (11600 : ℝ) (11700 : ℝ) ≤ (0.0000000000000000000000097630 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11600 : ℝ) (11700 : ℝ) 2 16738 7.1321e-32
    (0.0000000000000000000000097630 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11600_a2_le row11600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5800_lt, exp_neg_23200_3_lt,
                   Real.exp_pos (-(5800:ℝ)), Real.exp_pos (-(23200/3:ℝ))])


/-- Row 11600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11600_k3_margin :
    B_8_exact 3 (11600 : ℝ) (11700 : ℝ) ≤ (0.00000000000000000011423 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11600 : ℝ) (11700 : ℝ) 2 16738 7.1321e-32
    (0.00000000000000000011423 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11600_a2_le row11600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5800_lt, exp_neg_23200_3_lt,
                   Real.exp_pos (-(5800:ℝ)), Real.exp_pos (-(23200/3:ℝ))])


/-- Row 11600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11600_k4_margin :
    B_8_exact 4 (11600 : ℝ) (11700 : ℝ) ≤ (0.0000000000000013365 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11600 : ℝ) (11700 : ℝ) 2 16738 7.1321e-32
    (0.0000000000000013365 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11600_a2_le row11600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5800_lt, exp_neg_23200_3_lt,
                   Real.exp_pos (-(5800:ℝ)), Real.exp_pos (-(23200/3:ℝ))])


/-- Row 11600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11600_k5_margin :
    B_8_exact 5 (11600 : ℝ) (11700 : ℝ) ≤ (0.000000000015637 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11600 : ℝ) (11700 : ℝ) 2 16738 7.1321e-32
    (0.000000000015637 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11600_a2_le row11600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5800_lt, exp_neg_23200_3_lt,
                   Real.exp_pos (-(5800:ℝ)), Real.exp_pos (-(23200/3:ℝ))])


/-- Row 11700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11700_k1_margin :
    B_8_exact 1 (11700 : ℝ) (11800 : ℝ) ≤ (0.00000000000000000000000000057692 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11700 : ℝ) (11800 : ℝ) 2 16882 4.8892e-32
    (0.00000000000000000000000000057692 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11700_a2_le row11700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5850_lt, exp_neg_7800_lt,
                   Real.exp_pos (-(5850:ℝ)), Real.exp_pos (-(7800:ℝ))])


/-- Row 11700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11700_k2_margin :
    B_8_exact 2 (11700 : ℝ) (11800 : ℝ) ≤ (0.0000000000000000000000068076 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11700 : ℝ) (11800 : ℝ) 2 16882 4.8892e-32
    (0.0000000000000000000000068076 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11700_a2_le row11700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5850_lt, exp_neg_7800_lt,
                   Real.exp_pos (-(5850:ℝ)), Real.exp_pos (-(7800:ℝ))])


/-- Row 11700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11700_k3_margin :
    B_8_exact 3 (11700 : ℝ) (11800 : ℝ) ≤ (0.000000000000000000080330 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11700 : ℝ) (11800 : ℝ) 2 16882 4.8892e-32
    (0.000000000000000000080330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11700_a2_le row11700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5850_lt, exp_neg_7800_lt,
                   Real.exp_pos (-(5850:ℝ)), Real.exp_pos (-(7800:ℝ))])


/-- Row 11700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11700_k4_margin :
    B_8_exact 4 (11700 : ℝ) (11800 : ℝ) ≤ (0.00000000000000094789 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11700 : ℝ) (11800 : ℝ) 2 16882 4.8892e-32
    (0.00000000000000094789 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11700_a2_le row11700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5850_lt, exp_neg_7800_lt,
                   Real.exp_pos (-(5850:ℝ)), Real.exp_pos (-(7800:ℝ))])


/-- Row 11700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11700_k5_margin :
    B_8_exact 5 (11700 : ℝ) (11800 : ℝ) ≤ (0.000000000011185 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11700 : ℝ) (11800 : ℝ) 2 16882 4.8892e-32
    (0.000000000011185 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11700_a2_le row11700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5850_lt, exp_neg_7800_lt,
                   Real.exp_pos (-(5850:ℝ)), Real.exp_pos (-(7800:ℝ))])


/-- Row 11800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11800_k1_margin :
    B_8_exact 1 (11800 : ℝ) (11900 : ℝ) ≤ (0.00000000000000000000000000039987 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11800 : ℝ) (11900 : ℝ) 2 17026 3.3603e-32
    (0.00000000000000000000000000039987 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11800_a2_le row11800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5900_lt, exp_neg_23600_3_lt,
                   Real.exp_pos (-(5900:ℝ)), Real.exp_pos (-(23600/3:ℝ))])


/-- Row 11800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11800_k2_margin :
    B_8_exact 2 (11800 : ℝ) (11900 : ℝ) ≤ (0.0000000000000000000000047584 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11800 : ℝ) (11900 : ℝ) 2 17026 3.3603e-32
    (0.0000000000000000000000047584 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11800_a2_le row11800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5900_lt, exp_neg_23600_3_lt,
                   Real.exp_pos (-(5900:ℝ)), Real.exp_pos (-(23600/3:ℝ))])


/-- Row 11800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11800_k3_margin :
    B_8_exact 3 (11800 : ℝ) (11900 : ℝ) ≤ (0.000000000000000000056625 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11800 : ℝ) (11900 : ℝ) 2 17026 3.3603e-32
    (0.000000000000000000056625 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11800_a2_le row11800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5900_lt, exp_neg_23600_3_lt,
                   Real.exp_pos (-(5900:ℝ)), Real.exp_pos (-(23600/3:ℝ))])


/-- Row 11800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11800_k4_margin :
    B_8_exact 4 (11800 : ℝ) (11900 : ℝ) ≤ (0.00000000000000067384 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11800 : ℝ) (11900 : ℝ) 2 17026 3.3603e-32
    (0.00000000000000067384 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11800_a2_le row11800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5900_lt, exp_neg_23600_3_lt,
                   Real.exp_pos (-(5900:ℝ)), Real.exp_pos (-(23600/3:ℝ))])


/-- Row 11800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11800_k5_margin :
    B_8_exact 5 (11800 : ℝ) (11900 : ℝ) ≤ (0.0000000000080187 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11800 : ℝ) (11900 : ℝ) 2 17026 3.3603e-32
    (0.0000000000080187 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11800_a2_le row11800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5900_lt, exp_neg_23600_3_lt,
                   Real.exp_pos (-(5900:ℝ)), Real.exp_pos (-(23600/3:ℝ))])


/-- Row 11900 (k = 1), exact Table-10 margin target. -/
theorem table_10_row11900_k1_margin :
    B_8_exact 1 (11900 : ℝ) (12000 : ℝ) ≤ (0.00000000000000000000000000027776 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (11900 : ℝ) (12000 : ℝ) 2 17171 2.3147e-32
    (0.00000000000000000000000000027776 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11900_a2_le row11900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5950_lt, exp_neg_23800_3_lt,
                   Real.exp_pos (-(5950:ℝ)), Real.exp_pos (-(23800/3:ℝ))])


/-- Row 11900 (k = 2), exact Table-10 margin target. -/
theorem table_10_row11900_k2_margin :
    B_8_exact 2 (11900 : ℝ) (12000 : ℝ) ≤ (0.0000000000000000000000033331 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (11900 : ℝ) (12000 : ℝ) 2 17171 2.3147e-32
    (0.0000000000000000000000033331 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11900_a2_le row11900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5950_lt, exp_neg_23800_3_lt,
                   Real.exp_pos (-(5950:ℝ)), Real.exp_pos (-(23800/3:ℝ))])


/-- Row 11900 (k = 3), exact Table-10 margin target. -/
theorem table_10_row11900_k3_margin :
    B_8_exact 3 (11900 : ℝ) (12000 : ℝ) ≤ (0.000000000000000000039997 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (11900 : ℝ) (12000 : ℝ) 2 17171 2.3147e-32
    (0.000000000000000000039997 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11900_a2_le row11900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5950_lt, exp_neg_23800_3_lt,
                   Real.exp_pos (-(5950:ℝ)), Real.exp_pos (-(23800/3:ℝ))])


/-- Row 11900 (k = 4), exact Table-10 margin target. -/
theorem table_10_row11900_k4_margin :
    B_8_exact 4 (11900 : ℝ) (12000 : ℝ) ≤ (0.00000000000000047996 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (11900 : ℝ) (12000 : ℝ) 2 17171 2.3147e-32
    (0.00000000000000047996 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11900_a2_le row11900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5950_lt, exp_neg_23800_3_lt,
                   Real.exp_pos (-(5950:ℝ)), Real.exp_pos (-(23800/3:ℝ))])


/-- Row 11900 (k = 5), exact Table-10 margin target. -/
theorem table_10_row11900_k5_margin :
    B_8_exact 5 (11900 : ℝ) (12000 : ℝ) ≤ (0.0000000000057595 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (11900 : ℝ) (12000 : ℝ) 2 17171 2.3147e-32
    (0.0000000000057595 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row11900_a2_le row11900_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_5950_lt, exp_neg_23800_3_lt,
                   Real.exp_pos (-(5950:ℝ)), Real.exp_pos (-(23800/3:ℝ))])


/-- Row 12000 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12000_k1_margin :
    B_8_exact 1 (12000 : ℝ) (12100 : ℝ) ≤ (0.00000000000000000000000000019330 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12000 : ℝ) (12100 : ℝ) 2 17315 1.5976e-32
    (0.00000000000000000000000000019330 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12000_a2_le row12000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6000_lt, exp_neg_8000_lt,
                   Real.exp_pos (-(6000:ℝ)), Real.exp_pos (-(8000:ℝ))])


/-- Row 12000 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12000_k2_margin :
    B_8_exact 2 (12000 : ℝ) (12100 : ℝ) ≤ (0.0000000000000000000000023390 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12000 : ℝ) (12100 : ℝ) 2 17315 1.5976e-32
    (0.0000000000000000000000023390 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12000_a2_le row12000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6000_lt, exp_neg_8000_lt,
                   Real.exp_pos (-(6000:ℝ)), Real.exp_pos (-(8000:ℝ))])


/-- Row 12000 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12000_k3_margin :
    B_8_exact 3 (12000 : ℝ) (12100 : ℝ) ≤ (0.000000000000000000028302 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12000 : ℝ) (12100 : ℝ) 2 17315 1.5976e-32
    (0.000000000000000000028302 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12000_a2_le row12000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6000_lt, exp_neg_8000_lt,
                   Real.exp_pos (-(6000:ℝ)), Real.exp_pos (-(8000:ℝ))])


/-- Row 12000 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12000_k4_margin :
    B_8_exact 4 (12000 : ℝ) (12100 : ℝ) ≤ (0.00000000000000034245 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12000 : ℝ) (12100 : ℝ) 2 17315 1.5976e-32
    (0.00000000000000034245 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12000_a2_le row12000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6000_lt, exp_neg_8000_lt,
                   Real.exp_pos (-(6000:ℝ)), Real.exp_pos (-(8000:ℝ))])


/-- Row 12000 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12000_k5_margin :
    B_8_exact 5 (12000 : ℝ) (12100 : ℝ) ≤ (0.0000000000041436 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12000 : ℝ) (12100 : ℝ) 2 17315 1.5976e-32
    (0.0000000000041436 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12000_a2_le row12000_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6000_lt, exp_neg_8000_lt,
                   Real.exp_pos (-(6000:ℝ)), Real.exp_pos (-(8000:ℝ))])


/-- Row 12100 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12100_k1_margin :
    B_8_exact 1 (12100 : ℝ) (12200 : ℝ) ≤ (0.00000000000000000000000000013477 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12100 : ℝ) (12200 : ℝ) 2 17459 1.1048e-32
    (0.00000000000000000000000000013477 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12100_a2_le row12100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6050_lt, exp_neg_24200_3_lt,
                   Real.exp_pos (-(6050:ℝ)), Real.exp_pos (-(24200/3:ℝ))])


/-- Row 12100 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12100_k2_margin :
    B_8_exact 2 (12100 : ℝ) (12200 : ℝ) ≤ (0.0000000000000000000000016442 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12100 : ℝ) (12200 : ℝ) 2 17459 1.1048e-32
    (0.0000000000000000000000016442 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12100_a2_le row12100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6050_lt, exp_neg_24200_3_lt,
                   Real.exp_pos (-(6050:ℝ)), Real.exp_pos (-(24200/3:ℝ))])


/-- Row 12100 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12100_k3_margin :
    B_8_exact 3 (12100 : ℝ) (12200 : ℝ) ≤ (0.000000000000000000020060 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12100 : ℝ) (12200 : ℝ) 2 17459 1.1048e-32
    (0.000000000000000000020060 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12100_a2_le row12100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6050_lt, exp_neg_24200_3_lt,
                   Real.exp_pos (-(6050:ℝ)), Real.exp_pos (-(24200/3:ℝ))])


/-- Row 12100 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12100_k4_margin :
    B_8_exact 4 (12100 : ℝ) (12200 : ℝ) ≤ (0.00000000000000024473 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12100 : ℝ) (12200 : ℝ) 2 17459 1.1048e-32
    (0.00000000000000024473 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12100_a2_le row12100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6050_lt, exp_neg_24200_3_lt,
                   Real.exp_pos (-(6050:ℝ)), Real.exp_pos (-(24200/3:ℝ))])


/-- Row 12100 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12100_k5_margin :
    B_8_exact 5 (12100 : ℝ) (12200 : ℝ) ≤ (0.0000000000029857 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12100 : ℝ) (12200 : ℝ) 2 17459 1.1048e-32
    (0.0000000000029857 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12100_a2_le row12100_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6050_lt, exp_neg_24200_3_lt,
                   Real.exp_pos (-(6050:ℝ)), Real.exp_pos (-(24200/3:ℝ))])


/-- Row 12200 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12200_k1_margin :
    B_8_exact 1 (12200 : ℝ) (12300 : ℝ) ≤ (0.000000000000000000000000000093146 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12200 : ℝ) (12300 : ℝ) 2 17603 7.5730e-33
    (0.000000000000000000000000000093146 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12200_a2_le row12200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6100_lt, exp_neg_24400_3_lt,
                   Real.exp_pos (-(6100:ℝ)), Real.exp_pos (-(24400/3:ℝ))])


/-- Row 12200 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12200_k2_margin :
    B_8_exact 2 (12200 : ℝ) (12300 : ℝ) ≤ (0.0000000000000000000000011457 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12200 : ℝ) (12300 : ℝ) 2 17603 7.5730e-33
    (0.0000000000000000000000011457 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12200_a2_le row12200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6100_lt, exp_neg_24400_3_lt,
                   Real.exp_pos (-(6100:ℝ)), Real.exp_pos (-(24400/3:ℝ))])


/-- Row 12200 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12200_k3_margin :
    B_8_exact 3 (12200 : ℝ) (12300 : ℝ) ≤ (0.000000000000000000014092 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12200 : ℝ) (12300 : ℝ) 2 17603 7.5730e-33
    (0.000000000000000000014092 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12200_a2_le row12200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6100_lt, exp_neg_24400_3_lt,
                   Real.exp_pos (-(6100:ℝ)), Real.exp_pos (-(24400/3:ℝ))])


/-- Row 12200 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12200_k4_margin :
    B_8_exact 4 (12200 : ℝ) (12300 : ℝ) ≤ (0.00000000000000017333 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12200 : ℝ) (12300 : ℝ) 2 17603 7.5730e-33
    (0.00000000000000017333 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12200_a2_le row12200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6100_lt, exp_neg_24400_3_lt,
                   Real.exp_pos (-(6100:ℝ)), Real.exp_pos (-(24400/3:ℝ))])


/-- Row 12200 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12200_k5_margin :
    B_8_exact 5 (12200 : ℝ) (12300 : ℝ) ≤ (0.0000000000021320 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12200 : ℝ) (12300 : ℝ) 2 17603 7.5730e-33
    (0.0000000000021320 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12200_a2_le row12200_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6100_lt, exp_neg_24400_3_lt,
                   Real.exp_pos (-(6100:ℝ)), Real.exp_pos (-(24400/3:ℝ))])


/-- Row 12300 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12300_k1_margin :
    B_8_exact 1 (12300 : ℝ) (12400 : ℝ) ≤ (0.000000000000000000000000000065069 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12300 : ℝ) (12400 : ℝ) 2 17748 5.2476e-33
    (0.000000000000000000000000000065069 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12300_a2_le row12300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6150_lt, exp_neg_8200_lt,
                   Real.exp_pos (-(6150:ℝ)), Real.exp_pos (-(8200:ℝ))])


/-- Row 12300 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12300_k2_margin :
    B_8_exact 2 (12300 : ℝ) (12400 : ℝ) ≤ (0.00000000000000000000000080685 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12300 : ℝ) (12400 : ℝ) 2 17748 5.2476e-33
    (0.00000000000000000000000080685 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12300_a2_le row12300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6150_lt, exp_neg_8200_lt,
                   Real.exp_pos (-(6150:ℝ)), Real.exp_pos (-(8200:ℝ))])


/-- Row 12300 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12300_k3_margin :
    B_8_exact 3 (12300 : ℝ) (12400 : ℝ) ≤ (0.000000000000000000010005 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12300 : ℝ) (12400 : ℝ) 2 17748 5.2476e-33
    (0.000000000000000000010005 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12300_a2_le row12300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6150_lt, exp_neg_8200_lt,
                   Real.exp_pos (-(6150:ℝ)), Real.exp_pos (-(8200:ℝ))])


/-- Row 12300 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12300_k4_margin :
    B_8_exact 4 (12300 : ℝ) (12400 : ℝ) ≤ (0.00000000000000012406 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12300 : ℝ) (12400 : ℝ) 2 17748 5.2476e-33
    (0.00000000000000012406 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12300_a2_le row12300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6150_lt, exp_neg_8200_lt,
                   Real.exp_pos (-(6150:ℝ)), Real.exp_pos (-(8200:ℝ))])


/-- Row 12300 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12300_k5_margin :
    B_8_exact 5 (12300 : ℝ) (12400 : ℝ) ≤ (0.0000000000015384 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12300 : ℝ) (12400 : ℝ) 2 17748 5.2476e-33
    (0.0000000000015384 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12300_a2_le row12300_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6150_lt, exp_neg_8200_lt,
                   Real.exp_pos (-(6150:ℝ)), Real.exp_pos (-(8200:ℝ))])


/-- Row 12400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12400_k1_margin :
    B_8_exact 1 (12400 : ℝ) (12500 : ℝ) ≤ (0.000000000000000000000000000045539 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12400 : ℝ) (12500 : ℝ) 2 17892 3.6432e-33
    (0.000000000000000000000000000045539 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12400_a2_le row12400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6200_lt, exp_neg_24800_3_lt,
                   Real.exp_pos (-(6200:ℝ)), Real.exp_pos (-(24800/3:ℝ))])


/-- Row 12400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12400_k2_margin :
    B_8_exact 2 (12400 : ℝ) (12500 : ℝ) ≤ (0.00000000000000000000000056924 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12400 : ℝ) (12500 : ℝ) 2 17892 3.6432e-33
    (0.00000000000000000000000056924 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12400_a2_le row12400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6200_lt, exp_neg_24800_3_lt,
                   Real.exp_pos (-(6200:ℝ)), Real.exp_pos (-(24800/3:ℝ))])


/-- Row 12400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12400_k3_margin :
    B_8_exact 3 (12400 : ℝ) (12500 : ℝ) ≤ (0.0000000000000000000071155 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12400 : ℝ) (12500 : ℝ) 2 17892 3.6432e-33
    (0.0000000000000000000071155 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12400_a2_le row12400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6200_lt, exp_neg_24800_3_lt,
                   Real.exp_pos (-(6200:ℝ)), Real.exp_pos (-(24800/3:ℝ))])


/-- Row 12400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12400_k4_margin :
    B_8_exact 4 (12400 : ℝ) (12500 : ℝ) ≤ (0.000000000000000088944 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12400 : ℝ) (12500 : ℝ) 2 17892 3.6432e-33
    (0.000000000000000088944 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12400_a2_le row12400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6200_lt, exp_neg_24800_3_lt,
                   Real.exp_pos (-(6200:ℝ)), Real.exp_pos (-(24800/3:ℝ))])


/-- Row 12400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12400_k5_margin :
    B_8_exact 5 (12400 : ℝ) (12500 : ℝ) ≤ (0.0000000000011118 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12400 : ℝ) (12500 : ℝ) 2 17892 3.6432e-33
    (0.0000000000011118 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12400_a2_le row12400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6200_lt, exp_neg_24800_3_lt,
                   Real.exp_pos (-(6200:ℝ)), Real.exp_pos (-(24800/3:ℝ))])


/-- Row 12500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row12500_k1_margin :
    B_8_exact 1 (12500 : ℝ) (12600 : ℝ) ≤ (0.000000000000000000000000000031924 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (12500 : ℝ) (12600 : ℝ) 2 18036 2.5337e-33
    (0.000000000000000000000000000031924 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12500_a2_le row12500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6250_lt, exp_neg_25000_3_lt,
                   Real.exp_pos (-(6250:ℝ)), Real.exp_pos (-(25000/3:ℝ))])


/-- Row 12500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row12500_k2_margin :
    B_8_exact 2 (12500 : ℝ) (12600 : ℝ) ≤ (0.00000000000000000000000040224 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (12500 : ℝ) (12600 : ℝ) 2 18036 2.5337e-33
    (0.00000000000000000000000040224 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12500_a2_le row12500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6250_lt, exp_neg_25000_3_lt,
                   Real.exp_pos (-(6250:ℝ)), Real.exp_pos (-(25000/3:ℝ))])


/-- Row 12500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row12500_k3_margin :
    B_8_exact 3 (12500 : ℝ) (12600 : ℝ) ≤ (0.0000000000000000000050682 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (12500 : ℝ) (12600 : ℝ) 2 18036 2.5337e-33
    (0.0000000000000000000050682 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12500_a2_le row12500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6250_lt, exp_neg_25000_3_lt,
                   Real.exp_pos (-(6250:ℝ)), Real.exp_pos (-(25000/3:ℝ))])


/-- Row 12500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row12500_k4_margin :
    B_8_exact 4 (12500 : ℝ) (12600 : ℝ) ≤ (0.000000000000000063859 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (12500 : ℝ) (12600 : ℝ) 2 18036 2.5337e-33
    (0.000000000000000063859 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12500_a2_le row12500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6250_lt, exp_neg_25000_3_lt,
                   Real.exp_pos (-(6250:ℝ)), Real.exp_pos (-(25000/3:ℝ))])


/-- Row 12500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row12500_k5_margin :
    B_8_exact 5 (12500 : ℝ) (12600 : ℝ) ≤ (0.00000000000080462 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (12500 : ℝ) (12600 : ℝ) 2 18036 2.5337e-33
    (0.00000000000080462 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row12500_a2_le row12500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]
        nlinarith [exp_neg_6250_lt, exp_neg_25000_3_lt,
                   Real.exp_pos (-(6250:ℝ)), Real.exp_pos (-(25000/3:ℝ))])

end BKLNW
