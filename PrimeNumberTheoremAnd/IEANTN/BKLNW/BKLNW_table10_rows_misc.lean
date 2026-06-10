import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_rows_core

open Real Set Finset

namespace BKLNW

/-! Extra row checks kept outside the dense generated shards. -/

private lemma row60_a1_le : Inputs.default.a₁ (60 : ℝ) ≤ (1.00000002 : ℝ) := by
  have hlog : (43 : ℝ) < log Inputs.default.x₁ ∧ log Inputs.default.x₁ < 44 := by
    change (43 : ℝ) < log (1e19 : ℝ) ∧ log (1e19 : ℝ) < 44
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]; push_cast
    constructor <;> nlinarith [LogTables.log_10_gt, LogTables.log_10_lt]
  have hε19 : Inputs.default.ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin := by
    change BKLNW_app.table_8_ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    grw [BKLNW_app.table_8_ε.le_simp (log Inputs.default.x₁) (by linarith [hlog.1])]
    grind [BKLNW_app.table_8_ε']
  unfold Inputs.a₁
  rw [if_pos (by linarith [hlog.1] : (60 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

private lemma row60_a2_le : Inputs.default.a₂ (60 : ℝ) ≤ (89 : ℝ) := by
  have h := a2_crude_le 60 (by norm_num)
  have hlog2 : (0.6931 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(60 : ℝ) / log 2⌋₊ : ℝ) ≤ 60 / log 2 := Nat.floor_le (by positivity)
  have hdiv : (60 : ℝ) / log 2 ≤ 87 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; nlinarith [hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ 60
      ≤ (1 + Inputs.default.α) * ((⌊(60 : ℝ) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (87 + 1) := by
        apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
    _ ≤ 89 := by norm_num

private lemma row60_eps_le : Inputs.default.ε (60 : ℝ) ≤ 1.2216e-11 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_60 le_rfl

/-- Regime-2 row 60 (k=5): convexity template + CRUDE (cert-free) a₂ bound. b'=65 = next
    unabridged-grid entry; T = listed 1.4182e-2 × composed safety margin (≥ ×1.002). -/
theorem table_10_row60_k5 : B_8_exact 5 60 65 ≤ (0.014211 : ℝ) :=
  row_bound_k5 60 65 1.00000002 89 1.2216e-11 0.014211
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)


/-! ## Margin-target bridge theorem -/

/-- Row 60 (k = 1), exact Table-10 margin target. -/
theorem table_10_row60_k1_margin : B_8_exact 1 60 65 ≤ (7.9446e-10 * table_10_margin : ℝ) :=
  row_bound_k1 60 65 1.00000002 89 1.2216e-11 (7.9446e-10 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 60 (k = 2), exact Table-10 margin target. -/
theorem table_10_row60_k2_margin : B_8_exact 2 60 65 ≤ (5.1640e-8 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 60 65 1.00000002 89 1.2216e-11 (5.1640e-8 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 60 (k = 3), exact Table-10 margin target. -/
theorem table_10_row60_k3_margin : B_8_exact 3 60 65 ≤ (3.3566e-6 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 60 65 1.00000002 89 1.2216e-11 (3.3566e-6 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 60 (k = 4), exact Table-10 margin target. -/
theorem table_10_row60_k4_margin : B_8_exact 4 60 65 ≤ (2.1818e-4 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 60 65 1.00000002 89 1.2216e-11 (2.1818e-4 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 60 (k = 5), exact Table-10 margin target. -/
theorem table_10_row60_k5_margin : B_8_exact 5 60 65 ≤ (1.4182e-2 * table_10_margin : ℝ) :=
  row_bound_k5 60 65 1.00000002 89 1.2216e-11 (1.4182e-2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row60_a1_le row60_a2_le row60_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


/-! ## The 19·log 10 transcendental row, ALL FIVE COLUMNS (ported from v13 + k=1..4 new).
    Convexity regime; left endpoint via powers-of-10 exp bounds (k-independent). -/
private lemma r19_ge20 : (20 : ℝ) ≤ 19 * log 10 := by nlinarith [LogTables.log_10_gt]
private lemma r19_le44 : 19 * log 10 ≤ 44 := by nlinarith [LogTables.log_10_lt]
private lemma r19_le_4375 : 19 * log 10 ≤ (43.75 : ℝ) := by nlinarith [LogTables.log_10_lt]

private lemma row19_a1_le : Inputs.default.a₁ (19 * log 10) ≤ (1.00000002 : ℝ) := by
  have hlog : (43 : ℝ) < log Inputs.default.x₁ ∧ log Inputs.default.x₁ < 44 := by
    change (43 : ℝ) < log (1e19 : ℝ) ∧ log (1e19 : ℝ) < 44
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]; push_cast
    constructor <;> nlinarith [LogTables.log_10_gt, LogTables.log_10_lt]
  have hε19 : Inputs.default.ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin := by
    change BKLNW_app.table_8_ε (log Inputs.default.x₁) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    grw [BKLNW_app.table_8_ε.le_simp (log Inputs.default.x₁) (by linarith [hlog.1])]
    grind [BKLNW_app.table_8_ε']
  have hlx1 : log Inputs.default.x₁ = 19 * log 10 := by
    change log (1e19 : ℝ) = 19 * log 10
    have h1e19 : (1e19 : ℝ) = (10 : ℝ) ^ 19 := by norm_num
    rw [h1e19, Real.log_pow]; push_cast; ring
  unfold Inputs.a₁
  rw [if_pos (by rw [hlx1]; nlinarith [LogTables.log_10_gt] : (19 * log 10 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

private lemma row19_a2_le : Inputs.default.a₂ (19 * log 10) ≤ (66 : ℝ) := by
  have h := a2_crude_le (19 * log 10) (by linarith [r19_ge20])
  have hlog2 : (0.6931 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hfloor : (⌊(19 * log 10) / log 2⌋₊ : ℝ) ≤ (19 * log 10) / log 2 := Nat.floor_le (by positivity)
  have hdiv : (19 * log 10) / log 2 ≤ 64 := by
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < log 2)]; nlinarith [r19_le_4375, hlog2]
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  calc Inputs.default.a₂ (19 * log 10)
      ≤ (1 + Inputs.default.α) * ((⌊(19 * log 10) / log 2⌋₊ : ℝ) + 1) := h
    _ ≤ (1 + 1e-7) * (64 + 1) := by
        apply mul_le_mul (by linarith) (by linarith [hfloor, hdiv]) (by positivity) (by linarith)
    _ ≤ 66 := by norm_num

private lemma row19_eps_le : Inputs.default.ε (19 * log 10) ≤ (1.9339e-8 : ℝ) := by
  change BKLNW_app.table_8_ε (19 * log 10) ≤ 1.9339e-8
  exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_40 (by nlinarith [LogTables.log_10_gt])

/-- LEFT (transcendental) endpoint bound, via `(19log10)^5 ≤ 43.75^5` + powers-of-10 exp bounds. -/
private lemma row19_Gp_left : Gp 1.00000002 66 1.9339e-8 (19 * log 10) ≤ (3.2352 * table_10_margin : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r19_ge20]
  have hb5 : (19 * log 10) ^ 5 ≤ (43.75 : ℝ) ^ 5 := by gcongr; exact r19_le_4375
  have he1 : Real.exp (-(1 / 2 * (19 * log 10))) ≤ 3.17e-10 := by
    have h1' : exp (-(1 / 2 * (19 * log 10))) = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
      have hmul : -(1 / 2 * (19 * log 10)) = (log 10) * (-(19 : ℝ) / 2) := by ring
      calc exp (-(1 / 2 * (19 * log 10))) = exp (log 10 * (-(19 : ℝ) / 2)) := by rw [hmul]
        _ = exp (log 10) ^ (-(19 : ℝ) / 2) := by simpa using (Real.exp_mul (log 10) (-(19 : ℝ) / 2))
        _ = exp (log 10) ^ (-( (19:ℝ) / 2)) := by simp [neg_div]
        _ = (10 : ℝ) ^ (-( (19:ℝ) / 2)) := by simp [Real.exp_log (by norm_num : (0:ℝ) < 10)]
        _ = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
            simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((19:ℝ) / 2))
    rw [h1']
    refine rpow_le_of_pow_le (a:=1/10) (c:=3.17e-10) (by norm_num) (by norm_num)
      (p:=19) (q:=2) (by norm_num) ?_
    norm_num
  have he2 : Real.exp (-(2 / 3 * (19 * log 10))) ≤ 2.16e-13 := by
    have h2' : exp (-(2 / 3 * (19 * log 10))) = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
      have hmul : -(2 / 3 * (19 * log 10)) = (log 10) * (-(38 : ℝ) / 3) := by ring
      calc exp (-(2 / 3 * (19 * log 10))) = exp (log 10 * (-(38 : ℝ) / 3)) := by rw [hmul]
        _ = exp (log 10) ^ (-(38 : ℝ) / 3) := by simpa using (Real.exp_mul (log 10) (-(38 : ℝ) / 3))
        _ = exp (log 10) ^ (-( (38:ℝ) / 3)) := by simp [neg_div]
        _ = (10 : ℝ) ^ (-( (38:ℝ) / 3)) := by simp [Real.exp_log (by norm_num : (0:ℝ) < 10)]
        _ = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
            simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((38:ℝ) / 3))
    rw [h2']
    refine rpow_le_of_pow_le (a:=1/10) (c:=2.16e-13) (by norm_num) (by norm_num)
      (p:=38) (q:=3) (by norm_num) ?_
    norm_num
  unfold Gp expT
  have t1 : 1.00000002 * ((19 * log 10) ^ 5 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 5 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb5 he1 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 66 * ((19 * log 10) ^ 5 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 66 * ((43.75 : ℝ) ^ 5 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb5 he2 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 5 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_left hb5 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 5 * 3.17e-10) + 66 * ((43.75 : ℝ) ^ 5 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 5 ≤ 3.2352 * table_10_margin := by
      norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

/-- The 19·log10 row (k=5), exact Lemma-8 B, via the v7 convexity template. -/
theorem table_10_row19log10_k5_margin : B_8_exact 5 (19 * log 10) 44 ≤ (3.2352 * table_10_margin : ℝ) :=
  row_bound_k5 (19 * log 10) 44 1.00000002 66 1.9339e-8 (3.2352 * table_10_margin)
    r19_le44 r19_ge20 (by norm_num) (by norm_num) (by norm_num)
    row19_a1_le row19_a2_le row19_eps_le
    row19_Gp_left
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)


private lemma he1_19log10 : Real.exp (-(1 / 2 * (19 * log 10))) ≤ 3.17e-10 := by
  have h1' : exp (-(1 / 2 * (19 * log 10))) = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
    have hmul : -(1 / 2 * (19 * log 10)) = (log 10) * (-(19 : ℝ) / 2) := by ring
    calc exp (-(1 / 2 * (19 * log 10))) = exp (log 10 * (-(19 : ℝ) / 2)) := by rw [hmul]
      _ = exp (log 10) ^ (-(19 : ℝ) / 2) := by simpa using (Real.exp_mul (log 10) (-(19 : ℝ) / 2))
      _ = exp (log 10) ^ (-( (19:ℝ) / 2)) := by simp [neg_div]
      _ = (10 : ℝ) ^ (-( (19:ℝ) / 2)) := by simp [Real.exp_log (by norm_num : (0:ℝ) < 10)]
      _ = (1/10 : ℝ) ^ ((19:ℝ) / 2) := by
          simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((19:ℝ) / 2))
  rw [h1']
  refine rpow_le_of_pow_le (a:=1/10) (c:=3.17e-10) (by norm_num) (by norm_num)
    (p:=19) (q:=2) (by norm_num) ?_
  norm_num

private lemma he2_19log10 : Real.exp (-(2 / 3 * (19 * log 10))) ≤ 2.16e-13 := by
  have h2' : exp (-(2 / 3 * (19 * log 10))) = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
    have hmul : -(2 / 3 * (19 * log 10)) = (log 10) * (-(38 : ℝ) / 3) := by ring
    calc exp (-(2 / 3 * (19 * log 10))) = exp (log 10 * (-(38 : ℝ) / 3)) := by rw [hmul]
      _ = exp (log 10) ^ (-(38 : ℝ) / 3) := by simpa using (Real.exp_mul (log 10) (-(38 : ℝ) / 3))
      _ = exp (log 10) ^ (-( (38:ℝ) / 3)) := by simp [neg_div]
      _ = (10 : ℝ) ^ (-( (38:ℝ) / 3)) := by simp [Real.exp_log (by norm_num : (0:ℝ) < 10)]
      _ = (1/10 : ℝ) ^ ((38:ℝ) / 3) := by
          simpa [one_div] using (rpow_neg_eq_inv_rpow (10:ℝ) ((38:ℝ) / 3))
  rw [h2']
  refine rpow_le_of_pow_le (a:=1/10) (c:=2.16e-13) (by norm_num) (by norm_num)
    (p:=38) (q:=3) (by norm_num) ?_
  norm_num

private lemma row19_G1_left : G1 1.00000002 66 1.9339e-8 (19 * log 10) ≤ (8.6315e-7 * table_10_margin : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r19_ge20]
  have hbK : (19 * log 10) ^ 1 ≤ (43.75 : ℝ) ^ 1 := by gcongr; exact r19_le_4375
  unfold G1 eT
  norm_num
  have t1 : 1.00000002 * ((19 * log 10) ^ 1 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 1 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he1_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 66 * ((19 * log 10) ^ 1 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 66 * ((43.75 : ℝ) ^ 1 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he2_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 1 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 1 :=
    mul_le_mul_of_nonneg_left hbK (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 1 * 3.17e-10) + 66 * ((43.75 : ℝ) ^ 1 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 1 ≤ 8.6315e-7 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row19_Pp0_left : Pp 0 1.00000002 66 1.9339e-8 (19 * log 10) ≤ (3.7978e-5 * table_10_margin : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r19_ge20]
  have hbK : (19 * log 10) ^ 2 ≤ (43.75 : ℝ) ^ 2 := by gcongr; exact r19_le_4375
  unfold Pp pT
  norm_num
  have t1 : 1.00000002 * ((19 * log 10) ^ 2 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 2 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he1_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 66 * ((19 * log 10) ^ 2 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 66 * ((43.75 : ℝ) ^ 2 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he2_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 2 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hbK (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 2 * 3.17e-10) + 66 * ((43.75 : ℝ) ^ 2 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 2 ≤ 3.7978e-5 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row19_Pp1_left : Pp 1 1.00000002 66 1.9339e-8 (19 * log 10) ≤ (1.6711e-3 * table_10_margin : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r19_ge20]
  have hbK : (19 * log 10) ^ 3 ≤ (43.75 : ℝ) ^ 3 := by gcongr; exact r19_le_4375
  unfold Pp pT
  norm_num
  have t1 : 1.00000002 * ((19 * log 10) ^ 3 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 3 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he1_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 66 * ((19 * log 10) ^ 3 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 66 * ((43.75 : ℝ) ^ 3 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he2_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 3 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_left hbK (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 3 * 3.17e-10) + 66 * ((43.75 : ℝ) ^ 3 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 3 ≤ 1.6711e-3 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row19_Pp2_left : Pp 2 1.00000002 66 1.9339e-8 (19 * log 10) ≤ (7.3526e-2 * table_10_margin : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r19_ge20]
  have hbK : (19 * log 10) ^ 4 ≤ (43.75 : ℝ) ^ 4 := by gcongr; exact r19_le_4375
  unfold Pp pT
  norm_num
  have t1 : 1.00000002 * ((19 * log 10) ^ 4 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 4 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he1_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 66 * ((19 * log 10) ^ 4 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 66 * ((43.75 : ℝ) ^ 4 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hbK he2_19log10 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 4 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left hbK (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 4 * 3.17e-10) + 66 * ((43.75 : ℝ) ^ 4 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 4 ≤ 7.3526e-2 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

/-- The 19·log 10 row (k = 1), exact Table-10 margin target. -/
theorem table_10_row19log10_k1_margin : B_8_exact 1 (19 * log 10) 44 ≤ (8.6315e-7 * table_10_margin : ℝ) :=
  row_bound_k1 (19 * log 10) 44 1.00000002 66 1.9339e-8 (8.6315e-7 * table_10_margin)
    r19_le44 r19_ge20 (by norm_num) (by norm_num) (by norm_num)
    row19_a1_le row19_a2_le row19_eps_le
    row19_G1_left
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- The 19·log 10 row (k = 2), exact Table-10 margin target. -/
theorem table_10_row19log10_k2_margin : B_8_exact 2 (19 * log 10) 44 ≤ (3.7978e-5 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) (19 * log 10) 44 1.00000002 66 1.9339e-8 (3.7978e-5 * table_10_margin)
    r19_le44 r19_ge20 (by norm_num) (by norm_num) (by norm_num)
    row19_a1_le row19_a2_le row19_eps_le
    row19_Pp0_left
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- The 19·log 10 row (k = 3), exact Table-10 margin target. -/
theorem table_10_row19log10_k3_margin : B_8_exact 3 (19 * log 10) 44 ≤ (1.6711e-3 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) (19 * log 10) 44 1.00000002 66 1.9339e-8 (1.6711e-3 * table_10_margin)
    r19_le44 r19_ge20 (by norm_num) (by norm_num) (by norm_num)
    row19_a1_le row19_a2_le row19_eps_le
    row19_Pp1_left
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- The 19·log 10 row (k = 4), exact Table-10 margin target. -/
theorem table_10_row19log10_k4_margin : B_8_exact 4 (19 * log 10) 44 ≤ (7.3526e-2 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) (19 * log 10) 44 1.00000002 66 1.9339e-8 (7.3526e-2 * table_10_margin)
    r19_le44 r19_ge20 (by norm_num) (by norm_num) (by norm_num)
    row19_a1_le row19_a2_le row19_eps_le
    row19_Pp2_left
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
