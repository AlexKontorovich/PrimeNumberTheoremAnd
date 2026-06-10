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


private lemma row4400_a2_le : Inputs.default.a₂ (4400 : ℝ) ≤ (6350 : ℝ) := by
  have h := a2_crude_le (4400 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4400 : ℝ) / log 2⌋₊ : ℝ) ≤ (4400 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4400 : ℝ) / log 2 ≤ 6348 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4400 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4400 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6348 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6350 := by norm_num


private lemma row4425_a2_le : Inputs.default.a₂ (4425 : ℝ) ≤ (6386 : ℝ) := by
  have h := a2_crude_le (4425 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4425 : ℝ) / log 2⌋₊ : ℝ) ≤ (4425 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4425 : ℝ) / log 2 ≤ 6384 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4425 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4425 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6384 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6386 := by norm_num


private lemma row4450_a2_le : Inputs.default.a₂ (4450 : ℝ) ≤ (6422 : ℝ) := by
  have h := a2_crude_le (4450 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4450 : ℝ) / log 2⌋₊ : ℝ) ≤ (4450 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4450 : ℝ) / log 2 ≤ 6420 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4450 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4450 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6420 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6422 := by norm_num


private lemma row4475_a2_le : Inputs.default.a₂ (4475 : ℝ) ≤ (6459 : ℝ) := by
  have h := a2_crude_le (4475 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4475 : ℝ) / log 2⌋₊ : ℝ) ≤ (4475 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4475 : ℝ) / log 2 ≤ 6457 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4475 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4475 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6457 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6459 := by norm_num


private lemma row4500_a2_le : Inputs.default.a₂ (4500 : ℝ) ≤ (6495 : ℝ) := by
  have h := a2_crude_le (4500 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4500 : ℝ) / log 2⌋₊ : ℝ) ≤ (4500 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4500 : ℝ) / log 2 ≤ 6493 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4500 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4500 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6493 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6495 := by norm_num


private lemma row4525_a2_le : Inputs.default.a₂ (4525 : ℝ) ≤ (6531 : ℝ) := by
  have h := a2_crude_le (4525 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4525 : ℝ) / log 2⌋₊ : ℝ) ≤ (4525 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4525 : ℝ) / log 2 ≤ 6529 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4525 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4525 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6529 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6531 := by norm_num


private lemma row4550_a2_le : Inputs.default.a₂ (4550 : ℝ) ≤ (6567 : ℝ) := by
  have h := a2_crude_le (4550 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4550 : ℝ) / log 2⌋₊ : ℝ) ≤ (4550 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4550 : ℝ) / log 2 ≤ 6565 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4550 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4550 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6565 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6567 := by norm_num


private lemma row4575_a2_le : Inputs.default.a₂ (4575 : ℝ) ≤ (6603 : ℝ) := by
  have h := a2_crude_le (4575 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4575 : ℝ) / log 2⌋₊ : ℝ) ≤ (4575 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4575 : ℝ) / log 2 ≤ 6601 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4575 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4575 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6601 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6603 := by norm_num


private lemma row4600_a2_le : Inputs.default.a₂ (4600 : ℝ) ≤ (6639 : ℝ) := by
  have h := a2_crude_le (4600 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4600 : ℝ) / log 2⌋₊ : ℝ) ≤ (4600 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4600 : ℝ) / log 2 ≤ 6637 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4600 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4600 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6637 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6639 := by norm_num


private lemma row4625_a2_le : Inputs.default.a₂ (4625 : ℝ) ≤ (6675 : ℝ) := by
  have h := a2_crude_le (4625 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4625 : ℝ) / log 2⌋₊ : ℝ) ≤ (4625 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4625 : ℝ) / log 2 ≤ 6673 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4625 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4625 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6673 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6675 := by norm_num


private lemma row4650_a2_le : Inputs.default.a₂ (4650 : ℝ) ≤ (6711 : ℝ) := by
  have h := a2_crude_le (4650 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4650 : ℝ) / log 2⌋₊ : ℝ) ≤ (4650 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4650 : ℝ) / log 2 ≤ 6709 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4650 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4650 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6709 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6711 := by norm_num


private lemma row4675_a2_le : Inputs.default.a₂ (4675 : ℝ) ≤ (6747 : ℝ) := by
  have h := a2_crude_le (4675 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4675 : ℝ) / log 2⌋₊ : ℝ) ≤ (4675 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4675 : ℝ) / log 2 ≤ 6745 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4675 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4675 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6745 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6747 := by norm_num


private lemma row4700_a2_le : Inputs.default.a₂ (4700 : ℝ) ≤ (6783 : ℝ) := by
  have h := a2_crude_le (4700 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4700 : ℝ) / log 2⌋₊ : ℝ) ≤ (4700 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4700 : ℝ) / log 2 ≤ 6781 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4700 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4700 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6781 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6783 := by norm_num


private lemma row4725_a2_le : Inputs.default.a₂ (4725 : ℝ) ≤ (6819 : ℝ) := by
  have h := a2_crude_le (4725 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4725 : ℝ) / log 2⌋₊ : ℝ) ≤ (4725 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4725 : ℝ) / log 2 ≤ 6817 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4725 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4725 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6817 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6819 := by norm_num


private lemma row4750_a2_le : Inputs.default.a₂ (4750 : ℝ) ≤ (6855 : ℝ) := by
  have h := a2_crude_le (4750 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4750 : ℝ) / log 2⌋₊ : ℝ) ≤ (4750 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4750 : ℝ) / log 2 ≤ 6853 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4750 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4750 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6853 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6855 := by norm_num


private lemma row4775_a2_le : Inputs.default.a₂ (4775 : ℝ) ≤ (6891 : ℝ) := by
  have h := a2_crude_le (4775 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4775 : ℝ) / log 2⌋₊ : ℝ) ≤ (4775 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4775 : ℝ) / log 2 ≤ 6889 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4775 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4775 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6889 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6891 := by norm_num


private lemma row4800_a2_le : Inputs.default.a₂ (4800 : ℝ) ≤ (6927 : ℝ) := by
  have h := a2_crude_le (4800 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4800 : ℝ) / log 2⌋₊ : ℝ) ≤ (4800 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4800 : ℝ) / log 2 ≤ 6925 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4800 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4800 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6925 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6927 := by norm_num


private lemma row4825_a2_le : Inputs.default.a₂ (4825 : ℝ) ≤ (6964 : ℝ) := by
  have h := a2_crude_le (4825 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4825 : ℝ) / log 2⌋₊ : ℝ) ≤ (4825 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4825 : ℝ) / log 2 ≤ 6962 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4825 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4825 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6962 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 6964 := by norm_num


private lemma row4850_a2_le : Inputs.default.a₂ (4850 : ℝ) ≤ (7000 : ℝ) := by
  have h := a2_crude_le (4850 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4850 : ℝ) / log 2⌋₊ : ℝ) ≤ (4850 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4850 : ℝ) / log 2 ≤ 6998 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4850 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4850 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (6998 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7000 := by norm_num


private lemma row4875_a2_le : Inputs.default.a₂ (4875 : ℝ) ≤ (7036 : ℝ) := by
  have h := a2_crude_le (4875 : ℝ) (by norm_num)
  have hlog2 : (0.6931471803 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(4875 : ℝ) / log 2⌋₊ : ℝ) ≤ (4875 : ℝ) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (4875 : ℝ) / log 2 ≤ 7034 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]
    nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (4875 : ℝ)
      ≤ (1 + Inputs.default.α) * ((⌊(4875 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (7034 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 7036 := by norm_num


set_option maxRecDepth 10000 in
private lemma row4400_table8_mem : (4400, 1.5084e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4400_eps_le : Inputs.default.ε (4400 : ℝ) ≤ 1.5084e-17 := by
  change BKLNW_app.table_8_ε (4400 : ℝ) ≤ 1.5084e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4400)
    (ε := 1.5084e-17) row4400_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4425_table8_mem : (4425, 1.3153e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4425_eps_le : Inputs.default.ε (4425 : ℝ) ≤ 1.3153e-17 := by
  change BKLNW_app.table_8_ε (4425 : ℝ) ≤ 1.3153e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4425)
    (ε := 1.3153e-17) row4425_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4450_table8_mem : (4450, 1.1437e-17) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4450_eps_le : Inputs.default.ε (4450 : ℝ) ≤ 1.1437e-17 := by
  change BKLNW_app.table_8_ε (4450 : ℝ) ≤ 1.1437e-17
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4450)
    (ε := 1.1437e-17) row4450_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4475_table8_mem : (4475, 9.9627e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4475_eps_le : Inputs.default.ε (4475 : ℝ) ≤ 9.9627e-18 := by
  change BKLNW_app.table_8_ε (4475 : ℝ) ≤ 9.9627e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4475)
    (ε := 9.9627e-18) row4475_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4500_table8_mem : (4500, 8.6830e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4500_eps_le : Inputs.default.ε (4500 : ℝ) ≤ 8.6830e-18 := by
  change BKLNW_app.table_8_ε (4500 : ℝ) ≤ 8.6830e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4500)
    (ε := 8.6830e-18) row4500_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4525_table8_mem : (4525, 7.5706e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4525_eps_le : Inputs.default.ε (4525 : ℝ) ≤ 7.5706e-18 := by
  change BKLNW_app.table_8_ε (4525 : ℝ) ≤ 7.5706e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4525)
    (ε := 7.5706e-18) row4525_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4550_table8_mem : (4550, 6.5914e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4550_eps_le : Inputs.default.ε (4550 : ℝ) ≤ 6.5914e-18 := by
  change BKLNW_app.table_8_ε (4550 : ℝ) ≤ 6.5914e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4550)
    (ε := 6.5914e-18) row4550_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4575_table8_mem : (4575, 5.7400e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4575_eps_le : Inputs.default.ε (4575 : ℝ) ≤ 5.7400e-18 := by
  change BKLNW_app.table_8_ε (4575 : ℝ) ≤ 5.7400e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4575)
    (ε := 5.7400e-18) row4575_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4600_table8_mem : (4600, 5.0071e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4600_eps_le : Inputs.default.ε (4600 : ℝ) ≤ 5.0071e-18 := by
  change BKLNW_app.table_8_ε (4600 : ℝ) ≤ 5.0071e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4600)
    (ε := 5.0071e-18) row4600_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4625_table8_mem : (4625, 4.3570e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4625_eps_le : Inputs.default.ε (4625 : ℝ) ≤ 4.3570e-18 := by
  change BKLNW_app.table_8_ε (4625 : ℝ) ≤ 4.3570e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4625)
    (ε := 4.3570e-18) row4625_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4650_table8_mem : (4650, 3.7976e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4650_eps_le : Inputs.default.ε (4650 : ℝ) ≤ 3.7976e-18 := by
  change BKLNW_app.table_8_ε (4650 : ℝ) ≤ 3.7976e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4650)
    (ε := 3.7976e-18) row4650_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4675_table8_mem : (4675, 3.3113e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4675_eps_le : Inputs.default.ε (4675 : ℝ) ≤ 3.3113e-18 := by
  change BKLNW_app.table_8_ε (4675 : ℝ) ≤ 3.3113e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4675)
    (ε := 3.3113e-18) row4675_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4700_table8_mem : (4700, 2.8885e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4700_eps_le : Inputs.default.ε (4700 : ℝ) ≤ 2.8885e-18 := by
  change BKLNW_app.table_8_ε (4700 : ℝ) ≤ 2.8885e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4700)
    (ε := 2.8885e-18) row4700_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4725_table8_mem : (4725, 2.5214e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4725_eps_le : Inputs.default.ε (4725 : ℝ) ≤ 2.5214e-18 := by
  change BKLNW_app.table_8_ε (4725 : ℝ) ≤ 2.5214e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4725)
    (ε := 2.5214e-18) row4725_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4750_table8_mem : (4750, 2.1972e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4750_eps_le : Inputs.default.ε (4750 : ℝ) ≤ 2.1972e-18 := by
  change BKLNW_app.table_8_ε (4750 : ℝ) ≤ 2.1972e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4750)
    (ε := 2.1972e-18) row4750_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4775_table8_mem : (4775, 1.9146e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4775_eps_le : Inputs.default.ε (4775 : ℝ) ≤ 1.9146e-18 := by
  change BKLNW_app.table_8_ε (4775 : ℝ) ≤ 1.9146e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4775)
    (ε := 1.9146e-18) row4775_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4800_table8_mem : (4800, 1.6693e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4800_eps_le : Inputs.default.ε (4800 : ℝ) ≤ 1.6693e-18 := by
  change BKLNW_app.table_8_ε (4800 : ℝ) ≤ 1.6693e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4800)
    (ε := 1.6693e-18) row4800_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4825_table8_mem : (4825, 1.4561e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4825_eps_le : Inputs.default.ε (4825 : ℝ) ≤ 1.4561e-18 := by
  change BKLNW_app.table_8_ε (4825 : ℝ) ≤ 1.4561e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4825)
    (ε := 1.4561e-18) row4825_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4850_table8_mem : (4850, 1.2709e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4850_eps_le : Inputs.default.ε (4850 : ℝ) ≤ 1.2709e-18 := by
  change BKLNW_app.table_8_ε (4850 : ℝ) ≤ 1.2709e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4850)
    (ε := 1.2709e-18) row4850_table8_mem (by norm_num)


set_option maxRecDepth 10000 in
private lemma row4875_table8_mem : (4875, 1.1095e-18) ∈ BKLNW_app.table_8 := by
  norm_num [BKLNW_app.table_8]

private lemma row4875_eps_le : Inputs.default.ε (4875 : ℝ) ≤ 1.1095e-18 := by
  change BKLNW_app.table_8_ε (4875 : ℝ) ≤ 1.1095e-18
  exact BKLNW_app.table_8_ε_le_of_row (b₀ := 4875)
    (ε := 1.1095e-18) row4875_table8_mem (by norm_num)


/-- Row 4400 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4400_k1_margin :
    B_8_exact 1 (4400 : ℝ) (4425 : ℝ) ≤ (0.000000000000066744 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4400 : ℝ) (4425 : ℝ) 2 6350 1.5084e-17
    (0.000000000000066744 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4400_a2_le row4400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4400 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4400_k2_margin :
    B_8_exact 2 (4400 : ℝ) (4425 : ℝ) ≤ (0.00000000029534 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4400 : ℝ) (4425 : ℝ) 2 6350 1.5084e-17
    (0.00000000029534 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4400_a2_le row4400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4400 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4400_k3_margin :
    B_8_exact 3 (4400 : ℝ) (4425 : ℝ) ≤ (0.0000013069 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4400 : ℝ) (4425 : ℝ) 2 6350 1.5084e-17
    (0.0000013069 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4400_a2_le row4400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4400 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4400_k4_margin :
    B_8_exact 4 (4400 : ℝ) (4425 : ℝ) ≤ (0.0057829 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4400 : ℝ) (4425 : ℝ) 2 6350 1.5084e-17
    (0.0057829 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4400_a2_le row4400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4400 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4400_k5_margin :
    B_8_exact 5 (4400 : ℝ) (4425 : ℝ) ≤ (25.590 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4400 : ℝ) (4425 : ℝ) 2 6350 1.5084e-17
    (25.590 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4400_a2_le row4400_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4425 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4425_k1_margin :
    B_8_exact 1 (4425 : ℝ) (4450 : ℝ) ≤ (0.000000000000058436 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4425 : ℝ) (4450 : ℝ) 2 6386 1.3153e-17
    (0.000000000000058436 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4425_a2_le row4425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4425 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4425_k2_margin :
    B_8_exact 2 (4425 : ℝ) (4450 : ℝ) ≤ (0.00000000026004 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4425 : ℝ) (4450 : ℝ) 2 6386 1.3153e-17
    (0.00000000026004 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4425_a2_le row4425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4425 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4425_k3_margin :
    B_8_exact 3 (4425 : ℝ) (4450 : ℝ) ≤ (0.0000011572 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4425 : ℝ) (4450 : ℝ) 2 6386 1.3153e-17
    (0.0000011572 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4425_a2_le row4425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4425 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4425_k4_margin :
    B_8_exact 4 (4425 : ℝ) (4450 : ℝ) ≤ (0.0051495 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4425 : ℝ) (4450 : ℝ) 2 6386 1.3153e-17
    (0.0051495 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4425_a2_le row4425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4425 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4425_k5_margin :
    B_8_exact 5 (4425 : ℝ) (4450 : ℝ) ≤ (22.915 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4425 : ℝ) (4450 : ℝ) 2 6386 1.3153e-17
    (22.915 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4425_a2_le row4425_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4450 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4450_k1_margin :
    B_8_exact 1 (4450 : ℝ) (4475 : ℝ) ≤ (0.000000000000051174 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4450 : ℝ) (4475 : ℝ) 2 6422 1.1437e-17
    (0.000000000000051174 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4450_a2_le row4450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4450 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4450_k2_margin :
    B_8_exact 2 (4450 : ℝ) (4475 : ℝ) ≤ (0.00000000022901 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4450 : ℝ) (4475 : ℝ) 2 6422 1.1437e-17
    (0.00000000022901 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4450_a2_le row4450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4450 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4450_k3_margin :
    B_8_exact 3 (4450 : ℝ) (4475 : ℝ) ≤ (0.0000010248 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4450 : ℝ) (4475 : ℝ) 2 6422 1.1437e-17
    (0.0000010248 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4450_a2_le row4450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4450 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4450_k4_margin :
    B_8_exact 4 (4450 : ℝ) (4475 : ℝ) ≤ (0.0045860 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4450 : ℝ) (4475 : ℝ) 2 6422 1.1437e-17
    (0.0045860 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4450_a2_le row4450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4450 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4450_k5_margin :
    B_8_exact 5 (4450 : ℝ) (4475 : ℝ) ≤ (20.522 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4450 : ℝ) (4475 : ℝ) 2 6422 1.1437e-17
    (20.522 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4450_a2_le row4450_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4475 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4475_k1_margin :
    B_8_exact 1 (4475 : ℝ) (4500 : ℝ) ≤ (0.000000000000044832 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4475 : ℝ) (4500 : ℝ) 2 6459 9.9627e-18
    (0.000000000000044832 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4475_a2_le row4475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4475 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4475_k2_margin :
    B_8_exact 2 (4475 : ℝ) (4500 : ℝ) ≤ (0.00000000020174 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4475 : ℝ) (4500 : ℝ) 2 6459 9.9627e-18
    (0.00000000020174 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4475_a2_le row4475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4475 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4475_k3_margin :
    B_8_exact 3 (4475 : ℝ) (4500 : ℝ) ≤ (0.00000090785 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4475 : ℝ) (4500 : ℝ) 2 6459 9.9627e-18
    (0.00000090785 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4475_a2_le row4475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4475 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4475_k4_margin :
    B_8_exact 4 (4475 : ℝ) (4500 : ℝ) ≤ (0.0040853 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4475 : ℝ) (4500 : ℝ) 2 6459 9.9627e-18
    (0.0040853 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4475_a2_le row4475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4475 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4475_k5_margin :
    B_8_exact 5 (4475 : ℝ) (4500 : ℝ) ≤ (18.384 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4475 : ℝ) (4500 : ℝ) 2 6459 9.9627e-18
    (18.384 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4475_a2_le row4475_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4500 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4500_k1_margin :
    B_8_exact 1 (4500 : ℝ) (4525 : ℝ) ≤ (0.000000000000039290 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4500 : ℝ) (4525 : ℝ) 2 6495 8.6830e-18
    (0.000000000000039290 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4500_a2_le row4500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4500 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4500_k2_margin :
    B_8_exact 2 (4500 : ℝ) (4525 : ℝ) ≤ (0.00000000017779 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4500 : ℝ) (4525 : ℝ) 2 6495 8.6830e-18
    (0.00000000017779 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4500_a2_le row4500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4500 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4500_k3_margin :
    B_8_exact 3 (4500 : ℝ) (4525 : ℝ) ≤ (0.00000080450 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4500 : ℝ) (4525 : ℝ) 2 6495 8.6830e-18
    (0.00000080450 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4500_a2_le row4500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4500 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4500_k4_margin :
    B_8_exact 4 (4500 : ℝ) (4525 : ℝ) ≤ (0.0036403 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4500 : ℝ) (4525 : ℝ) 2 6495 8.6830e-18
    (0.0036403 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4500_a2_le row4500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4500 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4500_k5_margin :
    B_8_exact 5 (4500 : ℝ) (4525 : ℝ) ≤ (16.473 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4500 : ℝ) (4525 : ℝ) 2 6495 8.6830e-18
    (16.473 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4500_a2_le row4500_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4525 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4525_k1_margin :
    B_8_exact 1 (4525 : ℝ) (4550 : ℝ) ≤ (0.000000000000034446 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4525 : ℝ) (4550 : ℝ) 2 6531 7.5706e-18
    (0.000000000000034446 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4525_a2_le row4525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4525 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4525_k2_margin :
    B_8_exact 2 (4525 : ℝ) (4550 : ℝ) ≤ (0.00000000015673 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4525 : ℝ) (4550 : ℝ) 2 6531 7.5706e-18
    (0.00000000015673 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4525_a2_le row4525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4525 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4525_k3_margin :
    B_8_exact 3 (4525 : ℝ) (4550 : ℝ) ≤ (0.00000071312 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4525 : ℝ) (4550 : ℝ) 2 6531 7.5706e-18
    (0.00000071312 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4525_a2_le row4525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4525 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4525_k4_margin :
    B_8_exact 4 (4525 : ℝ) (4550 : ℝ) ≤ (0.0032447 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4525 : ℝ) (4550 : ℝ) 2 6531 7.5706e-18
    (0.0032447 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4525_a2_le row4525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4525 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4525_k5_margin :
    B_8_exact 5 (4525 : ℝ) (4550 : ℝ) ≤ (14.763 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4525 : ℝ) (4550 : ℝ) 2 6531 7.5706e-18
    (14.763 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4525_a2_le row4525_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4550 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4550_k1_margin :
    B_8_exact 1 (4550 : ℝ) (4575 : ℝ) ≤ (0.000000000000030155 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4550 : ℝ) (4575 : ℝ) 2 6567 6.5914e-18
    (0.000000000000030155 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4550_a2_le row4550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4550 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4550_k2_margin :
    B_8_exact 2 (4550 : ℝ) (4575 : ℝ) ≤ (0.00000000013796 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4550 : ℝ) (4575 : ℝ) 2 6567 6.5914e-18
    (0.00000000013796 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4550_a2_le row4550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4550 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4550_k3_margin :
    B_8_exact 3 (4550 : ℝ) (4575 : ℝ) ≤ (0.00000063117 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4550 : ℝ) (4575 : ℝ) 2 6567 6.5914e-18
    (0.00000063117 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4550_a2_le row4550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4550 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4550_k4_margin :
    B_8_exact 4 (4550 : ℝ) (4575 : ℝ) ≤ (0.0028876 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4550 : ℝ) (4575 : ℝ) 2 6567 6.5914e-18
    (0.0028876 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4550_a2_le row4550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4550 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4550_k5_margin :
    B_8_exact 5 (4550 : ℝ) (4575 : ℝ) ≤ (13.211 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4550 : ℝ) (4575 : ℝ) 2 6567 6.5914e-18
    (13.211 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4550_a2_le row4550_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4575 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4575_k1_margin :
    B_8_exact 1 (4575 : ℝ) (4600 : ℝ) ≤ (0.000000000000026404 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4575 : ℝ) (4600 : ℝ) 2 6603 5.7400e-18
    (0.000000000000026404 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4575_a2_le row4575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4575 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4575_k2_margin :
    B_8_exact 2 (4575 : ℝ) (4600 : ℝ) ≤ (0.00000000012146 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4575 : ℝ) (4600 : ℝ) 2 6603 5.7400e-18
    (0.00000000012146 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4575_a2_le row4575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4575 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4575_k3_margin :
    B_8_exact 3 (4575 : ℝ) (4600 : ℝ) ≤ (0.00000055870 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4575 : ℝ) (4600 : ℝ) 2 6603 5.7400e-18
    (0.00000055870 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4575_a2_le row4575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4575 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4575_k4_margin :
    B_8_exact 4 (4575 : ℝ) (4600 : ℝ) ≤ (0.0025700 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4575 : ℝ) (4600 : ℝ) 2 6603 5.7400e-18
    (0.0025700 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4575_a2_le row4575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4575 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4575_k5_margin :
    B_8_exact 5 (4575 : ℝ) (4600 : ℝ) ≤ (11.822 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4575 : ℝ) (4600 : ℝ) 2 6603 5.7400e-18
    (11.822 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4575_a2_le row4575_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4600 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4600_k1_margin :
    B_8_exact 1 (4600 : ℝ) (4625 : ℝ) ≤ (0.000000000000023157 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4600 : ℝ) (4625 : ℝ) 2 6639 5.0071e-18
    (0.000000000000023157 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4600_a2_le row4600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4600 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4600_k2_margin :
    B_8_exact 2 (4600 : ℝ) (4625 : ℝ) ≤ (0.00000000010710 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4600 : ℝ) (4625 : ℝ) 2 6639 5.0071e-18
    (0.00000000010710 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4600_a2_le row4600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4600 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4600_k3_margin :
    B_8_exact 3 (4600 : ℝ) (4625 : ℝ) ≤ (0.00000049535 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4600 : ℝ) (4625 : ℝ) 2 6639 5.0071e-18
    (0.00000049535 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4600_a2_le row4600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4600 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4600_k4_margin :
    B_8_exact 4 (4600 : ℝ) (4625 : ℝ) ≤ (0.0022910 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4600 : ℝ) (4625 : ℝ) 2 6639 5.0071e-18
    (0.0022910 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4600_a2_le row4600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4600 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4600_k5_margin :
    B_8_exact 5 (4600 : ℝ) (4625 : ℝ) ≤ (10.596 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4600 : ℝ) (4625 : ℝ) 2 6639 5.0071e-18
    (10.596 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4600_a2_le row4600_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4625 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4625_k1_margin :
    B_8_exact 1 (4625 : ℝ) (4650 : ℝ) ≤ (0.000000000000020259 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4625 : ℝ) (4650 : ℝ) 2 6675 4.3570e-18
    (0.000000000000020259 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4625_a2_le row4625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4625 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4625_k2_margin :
    B_8_exact 2 (4625 : ℝ) (4650 : ℝ) ≤ (0.000000000094206 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4625 : ℝ) (4650 : ℝ) 2 6675 4.3570e-18
    (0.000000000094206 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4625_a2_le row4625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4625 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4625_k3_margin :
    B_8_exact 3 (4625 : ℝ) (4650 : ℝ) ≤ (0.00000043806 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4625 : ℝ) (4650 : ℝ) 2 6675 4.3570e-18
    (0.00000043806 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4625_a2_le row4625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4625 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4625_k4_margin :
    B_8_exact 4 (4625 : ℝ) (4650 : ℝ) ≤ (0.0020370 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4625 : ℝ) (4650 : ℝ) 2 6675 4.3570e-18
    (0.0020370 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4625_a2_le row4625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4625 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4625_k5_margin :
    B_8_exact 5 (4625 : ℝ) (4650 : ℝ) ≤ (9.4719 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4625 : ℝ) (4650 : ℝ) 2 6675 4.3570e-18
    (9.4719 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4625_a2_le row4625_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4650 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4650_k1_margin :
    B_8_exact 1 (4650 : ℝ) (4675 : ℝ) ≤ (0.000000000000017753 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4650 : ℝ) (4675 : ℝ) 2 6711 3.7976e-18
    (0.000000000000017753 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4650_a2_le row4650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4650 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4650_k2_margin :
    B_8_exact 2 (4650 : ℝ) (4675 : ℝ) ≤ (0.000000000082997 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4650 : ℝ) (4675 : ℝ) 2 6711 3.7976e-18
    (0.000000000082997 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4650_a2_le row4650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4650 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4650_k3_margin :
    B_8_exact 3 (4650 : ℝ) (4675 : ℝ) ≤ (0.00000038801 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4650 : ℝ) (4675 : ℝ) 2 6711 3.7976e-18
    (0.00000038801 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4650_a2_le row4650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4650 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4650_k4_margin :
    B_8_exact 4 (4650 : ℝ) (4675 : ℝ) ≤ (0.0018140 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4650 : ℝ) (4675 : ℝ) 2 6711 3.7976e-18
    (0.0018140 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4650_a2_le row4650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4650 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4650_k5_margin :
    B_8_exact 5 (4650 : ℝ) (4675 : ℝ) ≤ (8.4802 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4650 : ℝ) (4675 : ℝ) 2 6711 3.7976e-18
    (8.4802 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4650_a2_le row4650_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4675 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4675_k1_margin :
    B_8_exact 1 (4675 : ℝ) (4700 : ℝ) ≤ (0.000000000000015563 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4675 : ℝ) (4700 : ℝ) 2 6747 3.3113e-18
    (0.000000000000015563 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4675_a2_le row4675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4675 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4675_k2_margin :
    B_8_exact 2 (4675 : ℝ) (4700 : ℝ) ≤ (0.000000000073144 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4675 : ℝ) (4700 : ℝ) 2 6747 3.3113e-18
    (0.000000000073144 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4675_a2_le row4675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4675 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4675_k3_margin :
    B_8_exact 3 (4675 : ℝ) (4700 : ℝ) ≤ (0.00000034378 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4675 : ℝ) (4700 : ℝ) 2 6747 3.3113e-18
    (0.00000034378 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4675_a2_le row4675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4675 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4675_k4_margin :
    B_8_exact 4 (4675 : ℝ) (4700 : ℝ) ≤ (0.0016158 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4675 : ℝ) (4700 : ℝ) 2 6747 3.3113e-18
    (0.0016158 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4675_a2_le row4675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4675 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4675_k5_margin :
    B_8_exact 5 (4675 : ℝ) (4700 : ℝ) ≤ (7.5941 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4675 : ℝ) (4700 : ℝ) 2 6747 3.3113e-18
    (7.5941 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4675_a2_le row4675_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4700 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4700_k1_margin :
    B_8_exact 1 (4700 : ℝ) (4725 : ℝ) ≤ (0.000000000000013648 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4700 : ℝ) (4725 : ℝ) 2 6783 2.8885e-18
    (0.000000000000013648 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4700_a2_le row4700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4700 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4700_k2_margin :
    B_8_exact 2 (4700 : ℝ) (4725 : ℝ) ≤ (0.000000000064486 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4700 : ℝ) (4725 : ℝ) 2 6783 2.8885e-18
    (0.000000000064486 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4700_a2_le row4700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4700 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4700_k3_margin :
    B_8_exact 3 (4700 : ℝ) (4725 : ℝ) ≤ (0.00000030470 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4700 : ℝ) (4725 : ℝ) 2 6783 2.8885e-18
    (0.00000030470 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4700_a2_le row4700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4700 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4700_k4_margin :
    B_8_exact 4 (4700 : ℝ) (4725 : ℝ) ≤ (0.0014397 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4700 : ℝ) (4725 : ℝ) 2 6783 2.8885e-18
    (0.0014397 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4700_a2_le row4700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4700 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4700_k5_margin :
    B_8_exact 5 (4700 : ℝ) (4725 : ℝ) ≤ (6.8026 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4700 : ℝ) (4725 : ℝ) 2 6783 2.8885e-18
    (6.8026 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4700_a2_le row4700_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4725 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4725_k1_margin :
    B_8_exact 1 (4725 : ℝ) (4750 : ℝ) ≤ (0.000000000000011976 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4725 : ℝ) (4750 : ℝ) 2 6819 2.5214e-18
    (0.000000000000011976 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4725_a2_le row4725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4725 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4725_k2_margin :
    B_8_exact 2 (4725 : ℝ) (4750 : ℝ) ≤ (0.000000000056887 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4725 : ℝ) (4750 : ℝ) 2 6819 2.5214e-18
    (0.000000000056887 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4725_a2_le row4725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4725 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4725_k3_margin :
    B_8_exact 3 (4725 : ℝ) (4750 : ℝ) ≤ (0.00000027021 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4725 : ℝ) (4750 : ℝ) 2 6819 2.5214e-18
    (0.00000027021 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4725_a2_le row4725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4725 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4725_k4_margin :
    B_8_exact 4 (4725 : ℝ) (4750 : ℝ) ≤ (0.0012835 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4725 : ℝ) (4750 : ℝ) 2 6819 2.5214e-18
    (0.0012835 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4725_a2_le row4725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4725 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4725_k5_margin :
    B_8_exact 5 (4725 : ℝ) (4750 : ℝ) ≤ (6.0967 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4725 : ℝ) (4750 : ℝ) 2 6819 2.5214e-18
    (6.0967 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4725_a2_le row4725_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4750 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4750_k1_margin :
    B_8_exact 1 (4750 : ℝ) (4775 : ℝ) ≤ (0.000000000000010491 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4750 : ℝ) (4775 : ℝ) 2 6855 2.1972e-18
    (0.000000000000010491 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4750_a2_le row4750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4750 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4750_k2_margin :
    B_8_exact 2 (4750 : ℝ) (4775 : ℝ) ≤ (0.000000000050095 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4750 : ℝ) (4775 : ℝ) 2 6855 2.1972e-18
    (0.000000000050095 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4750_a2_le row4750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4750 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4750_k3_margin :
    B_8_exact 3 (4750 : ℝ) (4775 : ℝ) ≤ (0.00000023920 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4750 : ℝ) (4775 : ℝ) 2 6855 2.1972e-18
    (0.00000023920 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4750_a2_le row4750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4750 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4750_k4_margin :
    B_8_exact 4 (4750 : ℝ) (4775 : ℝ) ≤ (0.0011422 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4750 : ℝ) (4775 : ℝ) 2 6855 2.1972e-18
    (0.0011422 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4750_a2_le row4750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4750 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4750_k5_margin :
    B_8_exact 5 (4750 : ℝ) (4775 : ℝ) ≤ (5.4540 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4750 : ℝ) (4775 : ℝ) 2 6855 2.1972e-18
    (5.4540 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4750_a2_le row4750_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4775 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4775_k1_margin :
    B_8_exact 1 (4775 : ℝ) (4800 : ℝ) ≤ (0.0000000000000091894 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4775 : ℝ) (4800 : ℝ) 2 6891 1.9146e-18
    (0.0000000000000091894 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4775_a2_le row4775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4775 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4775_k2_margin :
    B_8_exact 2 (4775 : ℝ) (4800 : ℝ) ≤ (0.000000000044109 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4775 : ℝ) (4800 : ℝ) 2 6891 1.9146e-18
    (0.000000000044109 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4775_a2_le row4775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4775 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4775_k3_margin :
    B_8_exact 3 (4775 : ℝ) (4800 : ℝ) ≤ (0.00000021172 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4775 : ℝ) (4800 : ℝ) 2 6891 1.9146e-18
    (0.00000021172 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4775_a2_le row4775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4775 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4775_k4_margin :
    B_8_exact 4 (4775 : ℝ) (4800 : ℝ) ≤ (0.0010163 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4775 : ℝ) (4800 : ℝ) 2 6891 1.9146e-18
    (0.0010163 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4775_a2_le row4775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4775 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4775_k5_margin :
    B_8_exact 5 (4775 : ℝ) (4800 : ℝ) ≤ (4.8781 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4775 : ℝ) (4800 : ℝ) 2 6891 1.9146e-18
    (4.8781 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4775_a2_le row4775_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4800 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4800_k1_margin :
    B_8_exact 1 (4800 : ℝ) (4825 : ℝ) ≤ (0.0000000000000080537 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4800 : ℝ) (4825 : ℝ) 2 6927 1.6693e-18
    (0.0000000000000080537 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4800_a2_le row4800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4800 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4800_k2_margin :
    B_8_exact 2 (4800 : ℝ) (4825 : ℝ) ≤ (0.000000000038859 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4800 : ℝ) (4825 : ℝ) 2 6927 1.6693e-18
    (0.000000000038859 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4800_a2_le row4800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4800 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4800_k3_margin :
    B_8_exact 3 (4800 : ℝ) (4825 : ℝ) ≤ (0.00000018750 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4800 : ℝ) (4825 : ℝ) 2 6927 1.6693e-18
    (0.00000018750 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4800_a2_le row4800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4800 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4800_k4_margin :
    B_8_exact 4 (4800 : ℝ) (4825 : ℝ) ≤ (0.00090466 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4800 : ℝ) (4825 : ℝ) 2 6927 1.6693e-18
    (0.00090466 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4800_a2_le row4800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4800 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4800_k5_margin :
    B_8_exact 5 (4800 : ℝ) (4825 : ℝ) ≤ (4.3650 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4800 : ℝ) (4825 : ℝ) 2 6927 1.6693e-18
    (4.3650 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4800_a2_le row4800_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4825 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4825_k1_margin :
    B_8_exact 1 (4825 : ℝ) (4850 : ℝ) ≤ (0.0000000000000070614 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4825 : ℝ) (4850 : ℝ) 2 6964 1.4561e-18
    (0.0000000000000070614 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4825_a2_le row4825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4825 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4825_k2_margin :
    B_8_exact 2 (4825 : ℝ) (4850 : ℝ) ≤ (0.000000000034248 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4825 : ℝ) (4850 : ℝ) 2 6964 1.4561e-18
    (0.000000000034248 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4825_a2_le row4825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4825 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4825_k3_margin :
    B_8_exact 3 (4825 : ℝ) (4850 : ℝ) ≤ (0.00000016610 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4825 : ℝ) (4850 : ℝ) 2 6964 1.4561e-18
    (0.00000016610 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4825_a2_le row4825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4825 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4825_k4_margin :
    B_8_exact 4 (4825 : ℝ) (4850 : ℝ) ≤ (0.00080560 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4825 : ℝ) (4850 : ℝ) 2 6964 1.4561e-18
    (0.00080560 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4825_a2_le row4825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4825 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4825_k5_margin :
    B_8_exact 5 (4825 : ℝ) (4850 : ℝ) ≤ (3.9072 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4825 : ℝ) (4850 : ℝ) 2 6964 1.4561e-18
    (3.9072 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4825_a2_le row4825_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4850 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4850_k1_margin :
    B_8_exact 1 (4850 : ℝ) (4875 : ℝ) ≤ (0.0000000000000061951 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4850 : ℝ) (4875 : ℝ) 2 7000 1.2709e-18
    (0.0000000000000061951 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4850_a2_le row4850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4850 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4850_k2_margin :
    B_8_exact 2 (4850 : ℝ) (4875 : ℝ) ≤ (0.000000000030201 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4850 : ℝ) (4875 : ℝ) 2 7000 1.2709e-18
    (0.000000000030201 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4850_a2_le row4850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4850 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4850_k3_margin :
    B_8_exact 3 (4850 : ℝ) (4875 : ℝ) ≤ (0.00000014723 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4850 : ℝ) (4875 : ℝ) 2 7000 1.2709e-18
    (0.00000014723 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4850_a2_le row4850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4850 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4850_k4_margin :
    B_8_exact 4 (4850 : ℝ) (4875 : ℝ) ≤ (0.00071775 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4850 : ℝ) (4875 : ℝ) 2 7000 1.2709e-18
    (0.00071775 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4850_a2_le row4850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4850 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4850_k5_margin :
    B_8_exact 5 (4850 : ℝ) (4875 : ℝ) ≤ (3.4990 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4850 : ℝ) (4875 : ℝ) 2 7000 1.2709e-18
    (3.4990 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4850_a2_le row4850_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4875 (k = 1), exact Table-10 margin target. -/
theorem table_10_row4875_k1_margin :
    B_8_exact 1 (4875 : ℝ) (4900 : ℝ) ≤ (0.0000000000000054361 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 (4875 : ℝ) (4900 : ℝ) 2 7036 1.1095e-18
    (0.0000000000000054361 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4875_a2_le row4875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4875 (k = 2), exact Table-10 margin target. -/
theorem table_10_row4875_k2_margin :
    B_8_exact 2 (4875 : ℝ) (4900 : ℝ) ≤ (0.000000000026637 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 (4875 : ℝ) (4900 : ℝ) 2 7036 1.1095e-18
    (0.000000000026637 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4875_a2_le row4875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4875 (k = 3), exact Table-10 margin target. -/
theorem table_10_row4875_k3_margin :
    B_8_exact 3 (4875 : ℝ) (4900 : ℝ) ≤ (0.00000013052 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 (4875 : ℝ) (4900 : ℝ) 2 7036 1.1095e-18
    (0.00000013052 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4875_a2_le row4875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4875 (k = 4), exact Table-10 margin target. -/
theorem table_10_row4875_k4_margin :
    B_8_exact 4 (4875 : ℝ) (4900 : ℝ) ≤ (0.00063955 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 (4875 : ℝ) (4900 : ℝ) 2 7036 1.1095e-18
    (0.00063955 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4875_a2_le row4875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-- Row 4875 (k = 5), exact Table-10 margin target. -/
theorem table_10_row4875_k5_margin :
    B_8_exact 5 (4875 : ℝ) (4900 : ℝ) ≤ (3.1338 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 (4875 : ℝ) (4900 : ℝ) 2 7036 1.1095e-18
    (3.1338 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_large_le_two (by norm_num)) row4875_a2_le row4875_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
