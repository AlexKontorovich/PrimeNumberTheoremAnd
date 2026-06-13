import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! Rows 90 and 95, where `a₁` uses the `if_neg` branch. -/

namespace BKLNW

open Real Set Finset

private lemma logx1_lt_44 : log Inputs.default.x₁ < 44 := by
  change log (1e19 : ℝ) < 44
  have h : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
  rw [h, Real.log_pow]; push_cast; nlinarith [LogTables.log_10_lt]

private lemma row90_a1_le : Inputs.default.a₁ (90 : ℝ) ≤ (2 : ℝ) := by
  rw [Inputs.a₁, if_neg (by linarith [logx1_lt_44] : ¬ ((90 : ℝ) ≤ 2 * log Inputs.default.x₁))]
  have heps : Inputs.default.ε ((90 : ℝ) / 2) ≤ 1.0908e-8 := by
    change BKLNW_app.table_8_ε ((90 : ℝ) / 2) ≤ 1.0908e-8
    rw [show (90 : ℝ) / 2 = 45 by norm_num]
    exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_45 le_rfl
  linarith

private lemma row95_a1_le : Inputs.default.a₁ (95 : ℝ) ≤ (2 : ℝ) := by
  rw [Inputs.a₁, if_neg (by linarith [logx1_lt_44] : ¬ ((95 : ℝ) ≤ 2 * log Inputs.default.x₁))]
  have heps : Inputs.default.ε ((95 : ℝ) / 2) ≤ 4.4013e-9 := by
    change BKLNW_app.table_8_ε ((95 : ℝ) / 2) ≤ 4.4013e-9
    rw [show (95 : ℝ) / 2 = 47.5 by norm_num]
    exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_47 (by norm_num)
  linarith

private lemma row90_a2_le : Inputs.default.a₂ (90 : ℝ) ≤ (132 : ℝ) := by
  have h := a2_crude_le 90 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(90 : ℝ) / log 2⌋₊ : ℝ) ≤ 90 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (90 : ℝ) / log 2 ≤ 130 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 90
      ≤ (1 + Inputs.default.α) * ((⌊(90 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (130 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 132 := by norm_num

private lemma row95_a2_le : Inputs.default.a₂ (95 : ℝ) ≤ (140 : ℝ) := by
  have h := a2_crude_le 95 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(95 : ℝ) / log 2⌋₊ : ℝ) ≤ 95 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (95 : ℝ) / log 2 ≤ 138 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 95
      ≤ (1 + Inputs.default.α) * ((⌊(95 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (138 + 1) :=
        mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 140 := by norm_num

private lemma row90_eps_le : Inputs.default.ε (90 : ℝ) ≤ 2.5214e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_90 le_rfl

private lemma row95_eps_le : Inputs.default.ε (95 : ℝ) ≤ 2.4920e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_95 le_rfl

/-- Row 90 (k = 1), exact Table-10 margin target. -/
theorem table_10_row90_k1_margin : B_8_exact 1 90 95 ≤ (2.3952e-10 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 90 95 2 132 2.5214e-12 (2.3952e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row90_a1_le row90_a2_le row90_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 90 (k = 2), exact Table-10 margin target. -/
theorem table_10_row90_k2_margin : B_8_exact 2 90 95 ≤ (2.2755e-8 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 90 95 2 132 2.5214e-12 (2.2755e-8 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row90_a1_le row90_a2_le row90_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 90 (k = 3), exact Table-10 margin target. -/
theorem table_10_row90_k3_margin : B_8_exact 3 90 95 ≤ (2.1617e-6 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 90 95 2 132 2.5214e-12 (2.1617e-6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row90_a1_le row90_a2_le row90_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 90 (k = 4), exact Table-10 margin target. -/
theorem table_10_row90_k4_margin : B_8_exact 4 90 95 ≤ (2.0536e-4 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 90 95 2 132 2.5214e-12 (2.0536e-4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row90_a1_le row90_a2_le row90_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 90 (k = 5), exact Table-10 margin target. -/
theorem table_10_row90_k5_margin : B_8_exact 5 90 95 ≤ (1.9509e-2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 90 95 2 132 2.5214e-12 (1.9509e-2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row90_a1_le row90_a2_le row90_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 95 (k = 1), exact Table-10 margin target. -/
theorem table_10_row95_k1_margin : B_8_exact 1 95 100 ≤ (2.4919e-10 * table_10_margin : ℝ) :=
  row_bound_pointwise 1 95 100 2 140 2.4920e-12 (2.4919e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row95_a1_le row95_a2_le row95_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 95 (k = 2), exact Table-10 margin target. -/
theorem table_10_row95_k2_margin : B_8_exact 2 95 100 ≤ (2.4919e-8 * table_10_margin : ℝ) :=
  row_bound_pointwise 2 95 100 2 140 2.4920e-12 (2.4919e-8 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row95_a1_le row95_a2_le row95_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 95 (k = 3), exact Table-10 margin target. -/
theorem table_10_row95_k3_margin : B_8_exact 3 95 100 ≤ (2.4919e-6 * table_10_margin : ℝ) :=
  row_bound_pointwise 3 95 100 2 140 2.4920e-12 (2.4919e-6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row95_a1_le row95_a2_le row95_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 95 (k = 4), exact Table-10 margin target. -/
theorem table_10_row95_k4_margin : B_8_exact 4 95 100 ≤ (2.4919e-4 * table_10_margin : ℝ) :=
  row_bound_pointwise 4 95 100 2 140 2.4920e-12 (2.4919e-4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row95_a1_le row95_a2_le row95_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 95 (k = 5), exact Table-10 margin target. -/
theorem table_10_row95_k5_margin : B_8_exact 5 95 100 ≤ (2.4919e-2 * table_10_margin : ℝ) :=
  row_bound_pointwise 5 95 100 2 140 2.4920e-12 (2.4919e-2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row95_a1_le row95_a2_le row95_eps_le
    (by norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
