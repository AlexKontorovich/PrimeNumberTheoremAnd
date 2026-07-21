import LeanCert.Tactic
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_a2_bounds
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

/-! # Table 10 row theorems: 5-step rows 65-85 (k = 1..5)

Crude cert-free a₂ suffices from b = 44 up (tolerance scan); every literal comes from the
canonical parsed grid and was float-verified before emission. -/

open Real Set Finset

set_option maxRecDepth 10000

namespace BKLNW

private lemma row65_a2_le : Inputs.default.a₂ (65 : ℝ) ≤ (96 : ℝ) := by
  have h := a2_crude_le 65 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(65 : ℝ) / log 2⌋₊ : ℝ) ≤ 65 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (65 : ℝ) / log 2 ≤ 94 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 65
      ≤ (1 + Inputs.default.α) * ((⌊(65 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (94 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 96 := by norm_num

private lemma row65_eps_le : Inputs.default.ε (65 : ℝ) ≤ 3.5713e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_65 le_rfl
/-- Row 65 (k = 1), exact Table-10 margin target (crude a₂). -/
theorem table_10_row65_k1_margin : B_8_exact 1 65 70 ≤ (2.5003e-10 * table_10_margin : ℝ) :=
  row_bound_k1 65 70 1.00000002 96 3.5713e-12 (2.5003e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row65_a2_le row65_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 65 (k = 2), exact Table-10 margin target (crude a₂). -/
theorem table_10_row65_k2_margin : B_8_exact 2 65 70 ≤ (1.7502e-08 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 65 70 1.00000002 96 3.5713e-12 (1.7502e-08 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row65_a2_le row65_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 65 (k = 3), exact Table-10 margin target (crude a₂). -/
theorem table_10_row65_k3_margin : B_8_exact 3 65 70 ≤ (1.2252e-06 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 65 70 1.00000002 96 3.5713e-12 (1.2252e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row65_a2_le row65_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 65 (k = 4), exact Table-10 margin target (crude a₂). -/
theorem table_10_row65_k4_margin : B_8_exact 4 65 70 ≤ (8.5761e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 65 70 1.00000002 96 3.5713e-12 (8.5761e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row65_a2_le row65_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 65 (k = 5), exact Table-10 margin target (crude a₂). -/
theorem table_10_row65_k5_margin : B_8_exact 5 65 70 ≤ (0.0060033 * table_10_margin : ℝ) :=
  row_bound_k5 65 70 1.00000002 96 3.5713e-12 (0.0060033 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row65_a2_le row65_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


private lemma row70_a2_le : Inputs.default.a₂ (70 : ℝ) ≤ (103 : ℝ) := by
  have h := a2_crude_le 70 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(70 : ℝ) / log 2⌋₊ : ℝ) ≤ 70 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (70 : ℝ) / log 2 ≤ 101 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 70
      ≤ (1 + Inputs.default.α) * ((⌊(70 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (101 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 103 := by norm_num

private lemma row70_eps_le : Inputs.default.ε (70 : ℝ) ≤ 2.7924e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_70 le_rfl
/-- Row 70 (k = 1), exact Table-10 margin target (crude a₂). -/
theorem table_10_row70_k1_margin : B_8_exact 1 70 75 ≤ (2.0943e-10 * table_10_margin : ℝ) :=
  row_bound_k1 70 75 1.00000002 103 2.7924e-12 (2.0943e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row70_a2_le row70_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 70 (k = 2), exact Table-10 margin target (crude a₂). -/
theorem table_10_row70_k2_margin : B_8_exact 2 70 75 ≤ (1.5707e-08 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 70 75 1.00000002 103 2.7924e-12 (1.5707e-08 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row70_a2_le row70_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 70 (k = 3), exact Table-10 margin target (crude a₂). -/
theorem table_10_row70_k3_margin : B_8_exact 3 70 75 ≤ (1.178e-06 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 70 75 1.00000002 103 2.7924e-12 (1.178e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row70_a2_le row70_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 70 (k = 4), exact Table-10 margin target (crude a₂). -/
theorem table_10_row70_k4_margin : B_8_exact 4 70 75 ≤ (8.8353e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 70 75 1.00000002 103 2.7924e-12 (8.8353e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row70_a2_le row70_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 70 (k = 5), exact Table-10 margin target (crude a₂). -/
theorem table_10_row70_k5_margin : B_8_exact 5 70 75 ≤ (0.0066265 * table_10_margin : ℝ) :=
  row_bound_k5 70 75 1.00000002 103 2.7924e-12 (0.0066265 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row70_a2_le row70_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


private lemma row75_a2_le : Inputs.default.a₂ (75 : ℝ) ≤ (111 : ℝ) := by
  have h := a2_crude_le 75 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(75 : ℝ) / log 2⌋₊ : ℝ) ≤ 75 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (75 : ℝ) / log 2 ≤ 109 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 75
      ≤ (1 + Inputs.default.α) * ((⌊(75 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (109 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 111 := by norm_num

private lemma row75_eps_le : Inputs.default.ε (75 : ℝ) ≤ 2.7037e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_75 le_rfl
/-- Row 75 (k = 1), exact Table-10 margin target (crude a₂). -/
theorem table_10_row75_k1_margin : B_8_exact 1 75 80 ≤ (2.1629e-10 * table_10_margin : ℝ) :=
  row_bound_k1 75 80 1.00000002 111 2.7037e-12 (2.1629e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row75_a2_le row75_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 75 (k = 2), exact Table-10 margin target (crude a₂). -/
theorem table_10_row75_k2_margin : B_8_exact 2 75 80 ≤ (1.7303e-08 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 75 80 1.00000002 111 2.7037e-12 (1.7303e-08 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row75_a2_le row75_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 75 (k = 3), exact Table-10 margin target (crude a₂). -/
theorem table_10_row75_k3_margin : B_8_exact 3 75 80 ≤ (1.3842e-06 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 75 80 1.00000002 111 2.7037e-12 (1.3842e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row75_a2_le row75_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 75 (k = 4), exact Table-10 margin target (crude a₂). -/
theorem table_10_row75_k4_margin : B_8_exact 4 75 80 ≤ (0.00011074 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 75 80 1.00000002 111 2.7037e-12 (0.00011074 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row75_a2_le row75_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 75 (k = 5), exact Table-10 margin target (crude a₂). -/
theorem table_10_row75_k5_margin : B_8_exact 5 75 80 ≤ (0.0088591 * table_10_margin : ℝ) :=
  row_bound_k5 75 80 1.00000002 111 2.7037e-12 (0.0088591 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row75_a2_le row75_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


private lemma row80_a2_le : Inputs.default.a₂ (80 : ℝ) ≤ (118 : ℝ) := by
  have h := a2_crude_le 80 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(80 : ℝ) / log 2⌋₊ : ℝ) ≤ 80 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (80 : ℝ) / log 2 ≤ 116 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 80
      ≤ (1 + Inputs.default.α) * ((⌊(80 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (116 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 118 := by norm_num

private lemma row80_eps_le : Inputs.default.ε (80 : ℝ) ≤ 2.6109e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_80 le_rfl
/-- Row 80 (k = 1), exact Table-10 margin target (crude a₂). -/
theorem table_10_row80_k1_margin : B_8_exact 1 80 85 ≤ (2.2192e-10 * table_10_margin : ℝ) :=
  row_bound_k1 80 85 1.00000002 118 2.6109e-12 (2.2192e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row80_a2_le row80_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 80 (k = 2), exact Table-10 margin target (crude a₂). -/
theorem table_10_row80_k2_margin : B_8_exact 2 80 85 ≤ (1.8863e-08 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 80 85 1.00000002 118 2.6109e-12 (1.8863e-08 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row80_a2_le row80_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 80 (k = 3), exact Table-10 margin target (crude a₂). -/
theorem table_10_row80_k3_margin : B_8_exact 3 80 85 ≤ (1.6034e-06 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 80 85 1.00000002 118 2.6109e-12 (1.6034e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row80_a2_le row80_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 80 (k = 4), exact Table-10 margin target (crude a₂). -/
theorem table_10_row80_k4_margin : B_8_exact 4 80 85 ≤ (0.00013629 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 80 85 1.00000002 118 2.6109e-12 (0.00013629 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row80_a2_le row80_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 80 (k = 5), exact Table-10 margin target (crude a₂). -/
theorem table_10_row80_k5_margin : B_8_exact 5 80 85 ≤ (0.011584 * table_10_margin : ℝ) :=
  row_bound_k5 80 85 1.00000002 118 2.6109e-12 (0.011584 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row80_a2_le row80_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


private lemma row85_a2_le : Inputs.default.a₂ (85 : ℝ) ≤ (125 : ℝ) := by
  have h := a2_crude_le 85 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := LogTables.log_2_gt_d3
  have hfloor : (⌊(85 : ℝ) / log 2⌋₊ : ℝ) ≤ 85 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (85 : ℝ) / log 2 ≤ 123 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; linarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 85
      ≤ (1 + Inputs.default.α) * ((⌊(85 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (123 + 1) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 125 := by norm_num

private lemma row85_eps_le : Inputs.default.ε (85 : ℝ) ≤ 2.5693e-12 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_85 le_rfl
/-- Row 85 (k = 1), exact Table-10 margin target (crude a₂). -/
theorem table_10_row85_k1_margin : B_8_exact 1 85 90 ≤ (2.3123e-10 * table_10_margin : ℝ) :=
  row_bound_k1 85 90 1.00000002 125 2.5693e-12 (2.3123e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row85_a2_le row85_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 85 (k = 2), exact Table-10 margin target (crude a₂). -/
theorem table_10_row85_k2_margin : B_8_exact 2 85 90 ≤ (2.0811e-08 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 85 90 1.00000002 125 2.5693e-12 (2.0811e-08 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row85_a2_le row85_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 85 (k = 3), exact Table-10 margin target (crude a₂). -/
theorem table_10_row85_k3_margin : B_8_exact 3 85 90 ≤ (1.873e-06 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 85 90 1.00000002 125 2.5693e-12 (1.873e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row85_a2_le row85_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 85 (k = 4), exact Table-10 margin target (crude a₂). -/
theorem table_10_row85_k4_margin : B_8_exact 4 85 90 ≤ (0.00016857 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 85 90 1.00000002 125 2.5693e-12 (0.00016857 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row85_a2_le row85_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 85 (k = 5), exact Table-10 margin target (crude a₂). -/
theorem table_10_row85_k5_margin : B_8_exact 5 85 90 ≤ (0.015171 * table_10_margin : ℝ) :=
  row_bound_k5 85 90 1.00000002 125 2.5693e-12 (0.015171 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row85_a2_le row85_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


end BKLNW
