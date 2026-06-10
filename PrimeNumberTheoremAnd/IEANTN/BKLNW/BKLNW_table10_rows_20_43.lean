import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_next
import PrimeNumberTheoremAnd.IEANTN.BKLNW.BKLNW_table10_values

open Real Set Finset

namespace BKLNW

/-! Row-specific k = 5 Table 10 bounds for the dense block 20 through 43. -/

private lemma row20_eps_le : Inputs.default.ε (20 : ℝ) ≤ (4.2676e-5 : ℝ) := by
  exact BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_20 le_rfl

private lemma row20_a2_le : Inputs.default.a₂ (20 : ℝ) ≤ (1.4263 : ℝ) := by
  have hf : (0 : ℝ) ≤ f (exp 20) := by
    unfold f
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (exp_pos 20).le _)
  have hmax : (0 : ℝ) ≤ max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1))) :=
    le_trans hf (le_max_left _ _)
  have hα : Inputs.default.α ≤ 193571378 / (10 : ℝ) ^ 16 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 193571378 / (10 : ℝ) ^ 16
    norm_num [BKLNW_app.table_8_margin]
  unfold Inputs.a₂
  calc (1 + Inputs.default.α) * max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1)))
      ≤ (1 + 193571378 / (10 : ℝ) ^ 16) * max (f (exp 20)) (f ((2 : ℝ) ^ (⌊(20 : ℝ) / log 2⌋₊ + 1))) := by
        gcongr
    _ ≤ 1.4262 + 1 / 10 ^ 4 := a2_20_mem_Icc.2
    _ ≤ 1.4263 := by norm_num

private lemma row20_a1_le : Inputs.default.a₁ (20 : ℝ) ≤ (1.00000002 : ℝ) := by
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
  rw [if_pos (by linarith [hlog.1] : (20 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

/-- Row 20 (k=5): now just an instantiation, with three coefficient bounds and two endpoint
`interval_decide` calls. -/
theorem table_10_row20_k5 : B_8_exact 5 20 21 ≤ (292.184 : ℝ) :=  -- listed 291.60 × table_10_margin (1.002001)
  row_bound_k5 20 21 1.00000002 1.4263 4.2676e-5 292.184
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

/-! Blocker-4 fix: row 25 WITH the unified margin (regime 1 generalizes within its cert family).
    Same regime/template as row 20, but proves ≤ listed·table_10_margin (NOT bare listed, which
    is provably false here: Gp(25)=71.2922 > 71.291). T = 71.434 ≥ 71.291 × 1.002001. -/

private lemma row25_a1_le : Inputs.default.a₁ (25 : ℝ) ≤ (1.00000002 : ℝ) := by
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
  rw [if_pos (by linarith [hlog.1] : (25 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

private lemma row25_a2_le : Inputs.default.a₂ (25 : ℝ) ≤ (1.2196 : ℝ) := by
  have hf : (0 : ℝ) ≤ f (exp 25) := by
    unfold f
    exact Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (exp_pos 25).le _)
  have hmax : (0 : ℝ) ≤ max (f (exp 25)) (f ((2 : ℝ) ^ (⌊(25 : ℝ) / log 2⌋₊ + 1))) :=
    le_trans hf (le_max_left _ _)
  have hα : Inputs.default.α ≤ 193571378 / (10 : ℝ) ^ 16 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 193571378 / (10 : ℝ) ^ 16
    norm_num [BKLNW_app.table_8_margin]
  unfold Inputs.a₂
  calc (1 + Inputs.default.α) * max (f (exp 25)) (f ((2 : ℝ) ^ (⌊(25 : ℝ) / log 2⌋₊ + 1)))
      ≤ (1 + 193571378 / (10 : ℝ) ^ 16) * max (f (exp 25)) (f ((2 : ℝ) ^ (⌊(25 : ℝ) / log 2⌋₊ + 1))) := by
        gcongr
    _ ≤ 1.2195 + 1 / 10 ^ 4 := a2_25_mem_Icc.2
    _ ≤ 1.2196 := by norm_num

private lemma row25_eps_le : Inputs.default.ε (25 : ℝ) ≤ 3.5032e-6 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_25 le_rfl

/-- Row 25 (k=5), regime 1, WITH the unified safety margin (T = listed 71.291 × 1.002001). -/
theorem table_10_row25_k5 : B_8_exact 5 25 26 ≤ (71.434 : ℝ) :=
  row_bound_k5 25 26 1.00000002 1.2196 3.5032e-6 71.434
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

/-! Row 26 (k = 5): the exemplar, a dense small-b row with no existing LeanCert cert,
    previously thought to require one (the P3 blocker). -/

private lemma floor_26 : ⌊(26 : ℝ) / log 2⌋₊ = 37 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  constructor
  · rw [le_div_iff₀ hlog2]
    push_cast
    nlinarith [hlt]
  · rw [div_lt_iff₀ hlog2]
    push_cast
    nlinarith [hgt]

private lemma row26_a2_le : Inputs.default.a₂ (26 : ℝ) ≤ (1.25 : ℝ) := by
  have h := a2_mid_le 26 (by norm_num) 37 floor_26 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((26 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      ((37 : ℕ) - 11 : ℝ) * Real.exp ((26 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.2499 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from rfl]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  calc (1 + Inputs.default.α) *
      ((∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((26:ℝ) * (1 / (k : ℝ) - 1 / 3))) +
        (((37:ℕ) : ℝ) - 11) * Real.exp ((26:ℝ) * (1 / 13 - 1 / 3)))
      ≤ (1 + 1e-7) * 1.2499 := by
        apply mul_le_mul (by linarith) (by exact_mod_cast hsum) ?_ (by linarith)
        positivity
    _ ≤ 1.25 := by norm_num

private lemma row26_a1_le : Inputs.default.a₁ (26 : ℝ) ≤ (1.00000002 : ℝ) := by
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
  rw [if_pos (by linarith [hlog.1] : (26 : ℝ) ≤ 2 * log Inputs.default.x₁)]
  have hb : (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1.00000002 - 1 := by
    norm_num [BKLNW_app.table_8_margin]
  linarith [hε19, hb]

private lemma row26_eps_le : Inputs.default.ε (26 : ℝ) ≤ 2.1248e-6 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_26 le_rfl

/-- Row 26 (k = 5): convexity template + MID-TIER cert-free a₂ (no LeanCert cert exists
    for b = 26). T = listed 5.2521e1 × table_10_margin (1.002001) = 52.626. -/
theorem table_10_row26_k5 : B_8_exact 5 26 27 ≤ (52.626 : ℝ) :=
  row_bound_k5 26 27 1.00000002 1.25 2.1248e-6 52.626
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row26_a1_le row26_a2_le row26_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)


/-! ## Batch: rows 27-29 via the same mid-tier pattern, plus a GENERAL small-b a₁ lemma
    (replaces per-row a₁ copies for every row with b ≤ 86 < 2·log x₁). -/

private lemma floor_27 : ⌊(27 : ℝ) / log 2⌋₊ = 38 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma row27_a2_le : Inputs.default.a₂ (27 : ℝ) ≤ (1.22 : ℝ) := by
  have h := a2_mid_le 27 (by norm_num) 38 floor_27 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((27 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((38 : ℕ) : ℝ) - 11) * Real.exp ((27 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.2199 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((27 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((38 : ℕ) : ℝ) - 11) * Real.exp ((27 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((27 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((38 : ℕ) : ℝ) - 11) * Real.exp ((27 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma floor_28 : ⌊(28 : ℝ) / log 2⌋₊ = 40 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma row28_a2_le : Inputs.default.a₂ (28 : ℝ) ≤ (1.20 : ℝ) := by
  have h := a2_mid_le 28 (by norm_num) 40 floor_28 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((28 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((40 : ℕ) : ℝ) - 11) * Real.exp ((28 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1999 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((28 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((40 : ℕ) : ℝ) - 11) * Real.exp ((28 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((28 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((40 : ℕ) : ℝ) - 11) * Real.exp ((28 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma floor_29 : ⌊(29 : ℝ) / log 2⌋₊ = 41 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma row29_a2_le : Inputs.default.a₂ (29 : ℝ) ≤ (1.18 : ℝ) := by
  have h := a2_mid_le 29 (by norm_num) 41 floor_29 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((29 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((41 : ℕ) : ℝ) - 11) * Real.exp ((29 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1799 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((29 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((41 : ℕ) : ℝ) - 11) * Real.exp ((29 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((29 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((41 : ℕ) : ℝ) - 11) * Real.exp ((29 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row27_eps_le : Inputs.default.ε (27 : ℝ) ≤ 1.2888e-6 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_27 le_rfl

/-- Row 27 (k = 5): T = listed 3.8419e1 × 1.002001 = 38.495. Mid-tier a₂, no LeanCert cert. -/
theorem table_10_row27_k5 : B_8_exact 5 27 28 ≤ (38.495 : ℝ) :=
  row_bound_k5 27 28 1.00000002 1.22 1.2888e-6 38.495
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row27_a2_le row27_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row28_eps_le : Inputs.default.ε (28 : ℝ) ≤ 7.8165e-7 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_28 le_rfl

/-- Row 28 (k = 5): T = listed 2.7918e1 × 1.002001 = 27.973. Mid-tier a₂, no LeanCert cert. -/
theorem table_10_row28_k5 : B_8_exact 5 28 29 ≤ (27.973 : ℝ) :=
  row_bound_k5 28 29 1.00000002 1.20 7.8165e-7 27.973
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row28_a2_le row28_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row29_eps_le : Inputs.default.ε (29 : ℝ) ≤ 4.7410e-7 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_29 le_rfl

/-- Row 29 (k = 5): T = listed 2.0162e1 × 1.002001 = 20.202. Mid-tier a₂, no LeanCert cert. -/
theorem table_10_row29_k5 : B_8_exact 5 29 30 ≤ (20.202 : ℝ) :=
  row_bound_k5 29 30 1.00000002 1.18 4.7410e-7 20.202
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row29_a2_le row29_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)


/-! ## Dense rows 21-24 + 30-42

    These are mid-tier a₂ rows; every literal was float-verified against source values
    before emission. -/

private lemma floor_21 : ⌊(21 : ℝ) / log 2⌋₊ = 30 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_22 : ⌊(22 : ℝ) / log 2⌋₊ = 31 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_23 : ⌊(23 : ℝ) / log 2⌋₊ = 33 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_24 : ⌊(24 : ℝ) / log 2⌋₊ = 34 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_30 : ⌊(30 : ℝ) / log 2⌋₊ = 43 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_31 : ⌊(31 : ℝ) / log 2⌋₊ = 44 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_32 : ⌊(32 : ℝ) / log 2⌋₊ = 46 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_33 : ⌊(33 : ℝ) / log 2⌋₊ = 47 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_34 : ⌊(34 : ℝ) / log 2⌋₊ = 49 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_35 : ⌊(35 : ℝ) / log 2⌋₊ = 50 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_36 : ⌊(36 : ℝ) / log 2⌋₊ = 51 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_37 : ⌊(37 : ℝ) / log 2⌋₊ = 53 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_38 : ⌊(38 : ℝ) / log 2⌋₊ = 54 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_39 : ⌊(39 : ℝ) / log 2⌋₊ = 56 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_40 : ⌊(40 : ℝ) / log 2⌋₊ = 57 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_41 : ⌊(41 : ℝ) / log 2⌋₊ = 59 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma floor_42 : ⌊(42 : ℝ) / log 2⌋₊ = 60 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma row21_a2_le : Inputs.default.a₂ (21 : ℝ) ≤ (1.4394 : ℝ) := by
  have h := a2_mid_le 21 (by norm_num) 30 floor_21 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((21 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((30 : ℕ) : ℝ) - 11) * Real.exp ((21 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.4393 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((21 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((30 : ℕ) : ℝ) - 11) * Real.exp ((21 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((21 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((30 : ℕ) : ℝ) - 11) * Real.exp ((21 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row22_a2_le : Inputs.default.a₂ (22 : ℝ) ≤ (1.3845 : ℝ) := by
  have h := a2_mid_le 22 (by norm_num) 31 floor_22 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((22 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((31 : ℕ) : ℝ) - 11) * Real.exp ((22 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.3844 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((22 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((31 : ℕ) : ℝ) - 11) * Real.exp ((22 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((22 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((31 : ℕ) : ℝ) - 11) * Real.exp ((22 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row23_a2_le : Inputs.default.a₂ (23 : ℝ) ≤ (1.3405 : ℝ) := by
  have h := a2_mid_le 23 (by norm_num) 33 floor_23 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((23 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((33 : ℕ) : ℝ) - 11) * Real.exp ((23 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.3404 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((23 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((33 : ℕ) : ℝ) - 11) * Real.exp ((23 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((23 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((33 : ℕ) : ℝ) - 11) * Real.exp ((23 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row24_a2_le : Inputs.default.a₂ (24 : ℝ) ≤ (1.2999 : ℝ) := by
  have h := a2_mid_le 24 (by norm_num) 34 floor_24 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((24 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((34 : ℕ) : ℝ) - 11) * Real.exp ((24 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.2998 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((24 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((34 : ℕ) : ℝ) - 11) * Real.exp ((24 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((24 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((34 : ℕ) : ℝ) - 11) * Real.exp ((24 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row30_a2_le : Inputs.default.a₂ (30 : ℝ) ≤ (1.1531 : ℝ) := by
  have h := a2_mid_le 30 (by norm_num) 43 floor_30 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((30 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((43 : ℕ) : ℝ) - 11) * Real.exp ((30 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1530 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((30 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((43 : ℕ) : ℝ) - 11) * Real.exp ((30 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((30 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((43 : ℕ) : ℝ) - 11) * Real.exp ((30 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row31_a2_le : Inputs.default.a₂ (31 : ℝ) ≤ (1.1383 : ℝ) := by
  have h := a2_mid_le 31 (by norm_num) 44 floor_31 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((31 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((44 : ℕ) : ℝ) - 11) * Real.exp ((31 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1382 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((31 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((44 : ℕ) : ℝ) - 11) * Real.exp ((31 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((31 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((44 : ℕ) : ℝ) - 11) * Real.exp ((31 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row32_a2_le : Inputs.default.a₂ (32 : ℝ) ≤ (1.1257 : ℝ) := by
  have h := a2_mid_le 32 (by norm_num) 46 floor_32 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((32 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((46 : ℕ) : ℝ) - 11) * Real.exp ((32 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1256 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((32 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((46 : ℕ) : ℝ) - 11) * Real.exp ((32 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((32 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((46 : ℕ) : ℝ) - 11) * Real.exp ((32 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row33_a2_le : Inputs.default.a₂ (33 : ℝ) ≤ (1.1144 : ℝ) := by
  have h := a2_mid_le 33 (by norm_num) 47 floor_33 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((33 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((47 : ℕ) : ℝ) - 11) * Real.exp ((33 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1143 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((33 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((47 : ℕ) : ℝ) - 11) * Real.exp ((33 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((33 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((47 : ℕ) : ℝ) - 11) * Real.exp ((33 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row34_a2_le : Inputs.default.a₂ (34 : ℝ) ≤ (1.1047 : ℝ) := by
  have h := a2_mid_le 34 (by norm_num) 49 floor_34 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((34 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((49 : ℕ) : ℝ) - 11) * Real.exp ((34 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.1046 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((34 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((49 : ℕ) : ℝ) - 11) * Real.exp ((34 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((34 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((49 : ℕ) : ℝ) - 11) * Real.exp ((34 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row35_a2_le : Inputs.default.a₂ (35 : ℝ) ≤ (1.0959 : ℝ) := by
  have h := a2_mid_le 35 (by norm_num) 50 floor_35 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((35 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((50 : ℕ) : ℝ) - 11) * Real.exp ((35 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0958 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((35 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((50 : ℕ) : ℝ) - 11) * Real.exp ((35 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((35 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((50 : ℕ) : ℝ) - 11) * Real.exp ((35 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row36_a2_le : Inputs.default.a₂ (36 : ℝ) ≤ (1.0883 : ℝ) := by
  have h := a2_mid_le 36 (by norm_num) 51 floor_36 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((36 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((51 : ℕ) : ℝ) - 11) * Real.exp ((36 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0882 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((36 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((51 : ℕ) : ℝ) - 11) * Real.exp ((36 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((36 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((51 : ℕ) : ℝ) - 11) * Real.exp ((36 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row37_a2_le : Inputs.default.a₂ (37 : ℝ) ≤ (1.0815 : ℝ) := by
  have h := a2_mid_le 37 (by norm_num) 53 floor_37 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((37 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((53 : ℕ) : ℝ) - 11) * Real.exp ((37 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0814 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((37 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((53 : ℕ) : ℝ) - 11) * Real.exp ((37 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((37 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((53 : ℕ) : ℝ) - 11) * Real.exp ((37 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row38_a2_le : Inputs.default.a₂ (38 : ℝ) ≤ (1.0755 : ℝ) := by
  have h := a2_mid_le 38 (by norm_num) 54 floor_38 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((38 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((54 : ℕ) : ℝ) - 11) * Real.exp ((38 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0754 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((38 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((54 : ℕ) : ℝ) - 11) * Real.exp ((38 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((38 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((54 : ℕ) : ℝ) - 11) * Real.exp ((38 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row39_a2_le : Inputs.default.a₂ (39 : ℝ) ≤ (1.0702 : ℝ) := by
  have h := a2_mid_le 39 (by norm_num) 56 floor_39 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((39 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((56 : ℕ) : ℝ) - 11) * Real.exp ((39 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0701 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((39 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((56 : ℕ) : ℝ) - 11) * Real.exp ((39 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((39 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((56 : ℕ) : ℝ) - 11) * Real.exp ((39 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row40_a2_le : Inputs.default.a₂ (40 : ℝ) ≤ (1.0654 : ℝ) := by
  have h := a2_mid_le 40 (by norm_num) 57 floor_40 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((40 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((57 : ℕ) : ℝ) - 11) * Real.exp ((40 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0653 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((40 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((57 : ℕ) : ℝ) - 11) * Real.exp ((40 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((40 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((57 : ℕ) : ℝ) - 11) * Real.exp ((40 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row41_a2_le : Inputs.default.a₂ (41 : ℝ) ≤ (1.0612 : ℝ) := by
  have h := a2_mid_le 41 (by norm_num) 59 floor_41 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((41 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((59 : ℕ) : ℝ) - 11) * Real.exp ((41 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0611 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((41 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((59 : ℕ) : ℝ) - 11) * Real.exp ((41 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((41 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((59 : ℕ) : ℝ) - 11) * Real.exp ((41 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row42_a2_le : Inputs.default.a₂ (42 : ℝ) ≤ (1.0573 : ℝ) := by
  have h := a2_mid_le 42 (by norm_num) 60 floor_42 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((42 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((60 : ℕ) : ℝ) - 11) * Real.exp ((42 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0572 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((42 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((60 : ℕ) : ℝ) - 11) * Real.exp ((42 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((42 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((60 : ℕ) : ℝ) - 11) * Real.exp ((42 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row21_eps_le : Inputs.default.ε (21 : ℝ) ≤ 2.5885e-5 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_21 le_rfl

/-- Row 21 (k = 5): T = listed 222.84 × 1.002001 = 223.28 (slack 0.0955%). Mid-tier a₂. -/
theorem table_10_row21_k5 : B_8_exact 5 21 22 ≤ (223.28 : ℝ) :=
  row_bound_k5 21 22 1.00000002 1.4394 2.5885e-5 223.28
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row21_a2_le row21_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row22_eps_le : Inputs.default.ε (22 : ℝ) ≤ 1.5701e-5 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_22 le_rfl

/-- Row 22 (k = 5): T = listed 169.9 × 1.002001 = 170.23 (slack 0.1129%). Mid-tier a₂. -/
theorem table_10_row22_k5 : B_8_exact 5 22 23 ≤ (170.23 : ℝ) :=
  row_bound_k5 22 23 1.00000002 1.3845 1.5701e-5 170.23
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row22_a2_le row22_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row23_eps_le : Inputs.default.ε (23 : ℝ) ≤ 9.5224e-6 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_23 le_rfl

/-- Row 23 (k = 5): T = listed 128.3 × 1.002001 = 128.55 (slack 0.1312%). Mid-tier a₂. -/
theorem table_10_row23_k5 : B_8_exact 5 23 24 ≤ (128.55 : ℝ) :=
  row_bound_k5 23 24 1.00000002 1.3405 9.5224e-6 128.55
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row23_a2_le row23_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row24_eps_le : Inputs.default.ε (24 : ℝ) ≤ 5.7757e-6 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_24 le_rfl

/-- Row 24 (k = 5): T = listed 96.032 × 1.002001 = 96.224 (slack 0.1511%). Mid-tier a₂. -/
theorem table_10_row24_k5 : B_8_exact 5 24 25 ≤ (96.224 : ℝ) :=
  row_bound_k5 24 25 1.00000002 1.2999 5.7757e-6 96.224
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row24_a2_le row24_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row30_eps_le : Inputs.default.ε (30 : ℝ) ≤ 2.8756e-7 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_30 le_rfl

/-- Row 30 (k = 5): T = listed 14.477 × 1.002001 = 14.505 (slack 0.1800%). Mid-tier a₂. -/
theorem table_10_row30_k5 : B_8_exact 5 30 31 ≤ (14.505 : ℝ) :=
  row_bound_k5 30 31 1.00000002 1.1531 2.8756e-7 14.505
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row30_a2_le row30_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row31_eps_le : Inputs.default.ε (31 : ℝ) ≤ 1.7442e-7 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_31 le_rfl

/-- Row 31 (k = 5): T = listed 10.339 × 1.002001 = 10.359 (slack 0.1852%). Mid-tier a₂. -/
theorem table_10_row31_k5 : B_8_exact 5 31 32 ≤ (10.359 : ℝ) :=
  row_bound_k5 31 32 1.00000002 1.1383 1.7442e-7 10.359
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row31_a2_le row31_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row32_eps_le : Inputs.default.ε (32 : ℝ) ≤ 1.0579e-7 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_32 le_rfl

/-- Row 32 (k = 5): T = listed 7.3456 × 1.002001 = 7.3602 (slack 0.1889%). Mid-tier a₂. -/
theorem table_10_row32_k5 : B_8_exact 5 32 33 ≤ (7.3602 : ℝ) :=
  row_bound_k5 32 33 1.00000002 1.1257 1.0579e-7 7.3602
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row32_a2_le row32_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row33_eps_le : Inputs.default.ε (33 : ℝ) ≤ 6.4162e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_33 le_rfl

/-- Row 33 (k = 5): T = listed 5.1941 × 1.002001 = 5.2044 (slack 0.1922%). Mid-tier a₂. -/
theorem table_10_row33_k5 : B_8_exact 5 33 34 ≤ (5.2044 : ℝ) :=
  row_bound_k5 33 34 1.00000002 1.1144 6.4162e-8 5.2044
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row33_a2_le row33_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row34_eps_le : Inputs.default.ε (34 : ℝ) ≤ 3.8917e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_34 le_rfl

/-- Row 34 (k = 5): T = listed 3.6562 × 1.002001 = 3.6635 (slack 0.1939%). Mid-tier a₂. -/
theorem table_10_row34_k5 : B_8_exact 5 34 35 ≤ (3.6635 : ℝ) :=
  row_bound_k5 34 35 1.00000002 1.1047 3.8917e-8 3.6635
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row34_a2_le row34_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row35_eps_le : Inputs.default.ε (35 : ℝ) ≤ 2.3604e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_35 le_rfl

/-- Row 35 (k = 5): T = listed 2.5627 × 1.002001 = 2.5678 (slack 0.1954%). Mid-tier a₂. -/
theorem table_10_row35_k5 : B_8_exact 5 35 36 ≤ (2.5678 : ℝ) :=
  row_bound_k5 35 36 1.00000002 1.0959 2.3604e-8 2.5678
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row35_a2_le row35_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row36_eps_le : Inputs.default.ε (36 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_36 le_rfl

/-- Row 36 (k = 5): T = listed 2.0926 × 1.002001 = 2.0967 (slack 0.1890%). Mid-tier a₂. -/
theorem table_10_row36_k5 : B_8_exact 5 36 37 ≤ (2.0967 : ℝ) :=
  row_bound_k5 36 37 1.00000002 1.0883 1.9339e-8 2.0967
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row36_a2_le row36_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row37_eps_le : Inputs.default.ε (37 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_37 le_rfl

/-- Row 37 (k = 5): T = listed 1.983 × 1.002001 = 1.9869 (slack 0.1934%). Mid-tier a₂. -/
theorem table_10_row37_k5 : B_8_exact 5 37 38 ≤ (1.9869 : ℝ) :=
  row_bound_k5 37 38 1.00000002 1.0815 1.9339e-8 1.9869
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row37_a2_le row37_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row38_eps_le : Inputs.default.ε (38 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_38 le_rfl

/-- Row 38 (k = 5): T = listed 2.0518 × 1.002001 = 2.0559 (slack 0.1922%). Mid-tier a₂. -/
theorem table_10_row38_k5 : B_8_exact 5 38 39 ≤ (2.0559 : ℝ) :=
  row_bound_k5 38 39 1.00000002 1.0755 1.9339e-8 2.0559
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row38_a2_le row38_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row39_eps_le : Inputs.default.ε (39 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_39 le_rfl

/-- Row 39 (k = 5): T = listed 2.1915 × 1.002001 = 2.1958 (slack 0.1884%). Mid-tier a₂. -/
theorem table_10_row39_k5 : B_8_exact 5 39 40 ≤ (2.1958 : ℝ) :=
  row_bound_k5 39 40 1.00000002 1.0702 1.9339e-8 2.1958
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row39_a2_le row39_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row40_eps_le : Inputs.default.ε (40 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_40 le_rfl

/-- Row 40 (k = 5): T = listed 2.3854 × 1.002001 = 2.3901 (slack 0.1905%). Mid-tier a₂. -/
theorem table_10_row40_k5 : B_8_exact 5 40 41 ≤ (2.3901 : ℝ) :=
  row_bound_k5 40 41 1.00000002 1.0654 1.9339e-8 2.3901
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row40_a2_le row40_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row41_eps_le : Inputs.default.ε (41 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_41 le_rfl

/-- Row 41 (k = 5): T = listed 2.6265 × 1.002001 = 2.6317 (slack 0.1926%). Mid-tier a₂. -/
theorem table_10_row41_k5 : B_8_exact 5 41 42 ≤ (2.6317 : ℝ) :=
  row_bound_k5 41 42 1.00000002 1.0612 1.9339e-8 2.6317
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row41_a2_le row41_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

private lemma row42_eps_le : Inputs.default.ε (42 : ℝ) ≤ 1.9338e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_42 le_rfl

/-- Row 42 (k = 5): T = listed 2.9105 × 1.002001 = 2.9163 (slack 0.1984%). Mid-tier a₂. -/
theorem table_10_row42_k5 : B_8_exact 5 42 43 ≤ (2.9163 : ℝ) :=
  row_bound_k5 42 43 1.00000002 1.0573 1.9338e-8 2.9163
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row42_a2_le row42_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    (by unfold Gp expT; norm_num; interval_decide)

/-! ## v16 special row: 43 to 19 * log 10.

This closes the integer dense block 20..43. The right endpoint is transcendental,
so it reuses the power-of-10 endpoint bound style from the earlier 19log10 row. -/

private lemma r43_le_r19 : (43 : ℝ) ≤ 19 * log 10 := by
  nlinarith [LogTables.log_10_gt]

private lemma r19_le_4375_for_row43 : 19 * log 10 ≤ (43.75 : ℝ) := by
  nlinarith [LogTables.log_10_lt]

private lemma floor_43 : ⌊(43 : ℝ) / log 2⌋₊ = 62 := by
  have hlog2 : (0 : ℝ) < log 2 := Real.log_pos one_lt_two
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hgt : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [Nat.floor_eq_iff (by positivity)]
  refine ⟨by rw [le_div_iff₀ hlog2]; push_cast; nlinarith [hlt],
          by rw [div_lt_iff₀ hlog2]; push_cast; nlinarith [hgt]⟩

private lemma row43_a2_le : Inputs.default.a₂ (43 : ℝ) ≤ (1.054 : ℝ) := by
  have h := a2_mid_le 43 (by norm_num) 62 floor_43 (by norm_num)
  refine h.trans ?_
  have hα : Inputs.default.α ≤ 1e-7 := by
    change (1.93378e-8 * BKLNW_app.table_8_margin : ℝ) ≤ 1e-7
    norm_num [BKLNW_app.table_8_margin]
  have hα0 : (0 : ℝ) ≤ Inputs.default.α := by
    change (0 : ℝ) ≤ 1.93378e-8 * BKLNW_app.table_8_margin
    norm_num [BKLNW_app.table_8_margin]
  have hsum : (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((43 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((62 : ℕ) : ℝ) - 11) * Real.exp ((43 : ℝ) * (1 / 13 - 1 / 3)) ≤ 1.0539 := by
    rw [show Finset.Icc (3:ℕ) 12 = {3, 4, 5, 6, 7, 8, 9, 10, 11, 12} from by decide]
    norm_num [Finset.sum_insert, Finset.mem_insert]
    interval_decide
  have hpos : (0 : ℝ) ≤ (∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((43 : ℝ) * (1 / (k : ℝ) - 1 / 3))) +
      (((62 : ℕ) : ℝ) - 11) * Real.exp ((43 : ℝ) * (1 / 13 - 1 / 3)) := by
    have h1 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc (3:ℕ) 12, Real.exp ((43 : ℝ) * (1 / (k : ℝ) - 1 / 3)) :=
      Finset.sum_nonneg fun k _ => (Real.exp_pos _).le
    have h2 : (0:ℝ) ≤ (((62 : ℕ) : ℝ) - 11) * Real.exp ((43 : ℝ) * (1 / 13 - 1 / 3)) := by
      apply mul_nonneg (by push_cast; norm_num) (Real.exp_pos _).le
    linarith
  nlinarith [hsum, hα, hα0, hpos]

private lemma row43_eps_le : Inputs.default.ε (43 : ℝ) ≤ 1.9339e-8 :=
  BKLNW_app.table_8_ε_le_of_row BKLNW_app.table_8_mem_43 le_rfl

private lemma row43_exp_half_le :
    Real.exp (-(1 / 2 * (19 * log 10))) ≤ (3.17e-10 : ℝ) := by
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

private lemma row43_exp_twothirds_le :
    Real.exp (-(2 / 3 * (19 * log 10))) ≤ (2.16e-13 : ℝ) := by
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

private lemma row43_G1_right :
    G1 1.00000002 1.054 1.9339e-8 (19 * log 10) ≤
      (8.5986e-7 * table_10_margin : ℝ) := by
  have hb1 : 19 * log 10 ≤ (43.75 : ℝ) := r19_le_4375_for_row43
  unfold G1 eT
  have t1 : 1.00000002 * ((19 * log 10) * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb1 row43_exp_half_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 1.054 * ((19 * log 10) * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 1.054 * ((43.75 : ℝ) * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb1 row43_exp_twothirds_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ≤ 1.9339e-8 * (43.75 : ℝ) :=
    mul_le_mul_of_nonneg_left hb1 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) * 3.17e-10) + 1.054 * ((43.75 : ℝ) * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ≤ 8.5986e-7 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row43_Pp0_right :
    Pp 0 1.00000002 1.054 1.9339e-8 (19 * log 10) ≤
      (3.7618e-5 * table_10_margin : ℝ) := by
  have hb2 : (19 * log 10) ^ 2 ≤ (43.75 : ℝ) ^ 2 := by
    gcongr
    exact r19_le_4375_for_row43
  unfold Pp pT
  have t1 : 1.00000002 * ((19 * log 10) ^ 2 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 2 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb2 row43_exp_half_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 1.054 * ((19 * log 10) ^ 2 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 1.054 * ((43.75 : ℝ) ^ 2 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb2 row43_exp_twothirds_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 2 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left hb2 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 2 * 3.17e-10) + 1.054 * ((43.75 : ℝ) ^ 2 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 2 ≤ 3.7618e-5 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row43_Pp1_right :
    Pp 1 1.00000002 1.054 1.9339e-8 (19 * log 10) ≤
      (0.0016458 * table_10_margin : ℝ) := by
  have hb3 : (19 * log 10) ^ 3 ≤ (43.75 : ℝ) ^ 3 := by
    gcongr
    exact r19_le_4375_for_row43
  unfold Pp pT
  have t1 : 1.00000002 * ((19 * log 10) ^ 3 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 3 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb3 row43_exp_half_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 1.054 * ((19 * log 10) ^ 3 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 1.054 * ((43.75 : ℝ) ^ 3 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb3 row43_exp_twothirds_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 3 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 3 :=
    mul_le_mul_of_nonneg_left hb3 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 3 * 3.17e-10) + 1.054 * ((43.75 : ℝ) ^ 3 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 3 ≤ 0.0016458 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row43_Pp2_right :
    Pp 2 1.00000002 1.054 1.9339e-8 (19 * log 10) ≤
      (0.072000 * table_10_margin : ℝ) := by
  have hb4 : (19 * log 10) ^ 4 ≤ (43.75 : ℝ) ^ 4 := by
    gcongr
    exact r19_le_4375_for_row43
  unfold Pp pT
  have t1 : 1.00000002 * ((19 * log 10) ^ 4 * Real.exp (-(1 / 2 * (19 * log 10))))
      ≤ 1.00000002 * ((43.75 : ℝ) ^ 4 * 3.17e-10) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb4 row43_exp_half_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t2 : 1.054 * ((19 * log 10) ^ 4 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 1.054 * ((43.75 : ℝ) ^ 4 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb4 row43_exp_twothirds_le (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 4 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left hb4 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 4 * 3.17e-10) + 1.054 * ((43.75 : ℝ) ^ 4 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 4 ≤ 0.072000 * table_10_margin := by
    norm_num [table_10_margin, BKLNW_app.table_8_margin]
  linarith [t1, t2, t3, hconst]

private lemma row43_Gp_right : Gp 1.00000002 1.054 1.9339e-8 (19 * log 10) ≤ (3.1563 : ℝ) := by
  have hpos : (0 : ℝ) ≤ 19 * log 10 := by linarith [r43_le_r19]
  have hb5 : (19 * log 10) ^ 5 ≤ (43.75 : ℝ) ^ 5 := by
    gcongr
    exact r19_le_4375_for_row43
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
  have t2 : 1.054 * ((19 * log 10) ^ 5 * Real.exp (-(2 / 3 * (19 * log 10))))
      ≤ 1.054 * ((43.75 : ℝ) ^ 5 * 2.16e-13) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hb5 he2 (Real.exp_pos _).le (by positivity)) (by norm_num)
  have t3 : 1.9339e-8 * (19 * log 10) ^ 5 ≤ 1.9339e-8 * (43.75 : ℝ) ^ 5 :=
    mul_le_mul_of_nonneg_left hb5 (by norm_num)
  have hconst : 1.00000002 * ((43.75 : ℝ) ^ 5 * 3.17e-10) + 1.054 * ((43.75 : ℝ) ^ 5 * 2.16e-13)
      + 1.9339e-8 * (43.75 : ℝ) ^ 5 ≤ 3.1563 := by norm_num
  linarith [t1, t2, t3, hconst]

/-- Row 43 (k = 5): T = listed 3.1500 × 1.002001 = 3.1563. -/
theorem table_10_row43_k5 : B_8_exact 5 43 (19 * log 10) ≤ (3.1563 : ℝ) :=
  row_bound_k5 43 (19 * log 10) 1.00000002 1.054 1.9339e-8 3.1563
    r43_le_r19 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row43_a2_le row43_eps_le
    (by unfold Gp expT; norm_num; interval_decide)
    row43_Gp_right


/-! ## Margin-target bridge theorems

These are the forms consumed by the margin-amended `bklnw_table_10_verification` target.
Most rows follow by transitivity from the rounded decimal theorem above; rows 20 and 25
are re-run at the exact `listed * table_10_margin` target because their display literals
were rounded slightly above that product. -/

/-- Row 20 (k = 5), exact Table-10 margin target. -/
theorem table_10_row20_k5_margin : B_8_exact 5 20 21 ≤ (2.9160e2 * table_10_margin : ℝ) :=
  row_bound_k5 20 21 1.00000002 1.4263 4.2676e-5 (2.9160e2 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 25 (k = 5), exact Table-10 margin target. -/
theorem table_10_row25_k5_margin : B_8_exact 5 25 26 ≤ (7.1291e1 * table_10_margin : ℝ) :=
  row_bound_k5 25 26 1.00000002 1.2196 3.5032e-6 (7.1291e1 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Gp expT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 21 (k = 5), exact Table-10 margin target. -/
theorem table_10_row21_k5_margin : B_8_exact 5 21 22 ≤ (2.2284e2 * table_10_margin : ℝ) :=
  table_10_row21_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 22 (k = 5), exact Table-10 margin target. -/
theorem table_10_row22_k5_margin : B_8_exact 5 22 23 ≤ (1.6990e2 * table_10_margin : ℝ) :=
  table_10_row22_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 23 (k = 5), exact Table-10 margin target. -/
theorem table_10_row23_k5_margin : B_8_exact 5 23 24 ≤ (1.2830e2 * table_10_margin : ℝ) :=
  table_10_row23_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 24 (k = 5), exact Table-10 margin target. -/
theorem table_10_row24_k5_margin : B_8_exact 5 24 25 ≤ (9.6032e1 * table_10_margin : ℝ) :=
  table_10_row24_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 26 (k = 5), exact Table-10 margin target. -/
theorem table_10_row26_k5_margin : B_8_exact 5 26 27 ≤ (5.2521e1 * table_10_margin : ℝ) :=
  table_10_row26_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 27 (k = 5), exact Table-10 margin target. -/
theorem table_10_row27_k5_margin : B_8_exact 5 27 28 ≤ (3.8419e1 * table_10_margin : ℝ) :=
  table_10_row27_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 28 (k = 5), exact Table-10 margin target. -/
theorem table_10_row28_k5_margin : B_8_exact 5 28 29 ≤ (2.7918e1 * table_10_margin : ℝ) :=
  table_10_row28_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 29 (k = 5), exact Table-10 margin target. -/
theorem table_10_row29_k5_margin : B_8_exact 5 29 30 ≤ (2.0162e1 * table_10_margin : ℝ) :=
  table_10_row29_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 30 (k = 5), exact Table-10 margin target. -/
theorem table_10_row30_k5_margin : B_8_exact 5 30 31 ≤ (1.4477e1 * table_10_margin : ℝ) :=
  table_10_row30_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 31 (k = 5), exact Table-10 margin target. -/
theorem table_10_row31_k5_margin : B_8_exact 5 31 32 ≤ (1.0339e1 * table_10_margin : ℝ) :=
  table_10_row31_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 32 (k = 5), exact Table-10 margin target. -/
theorem table_10_row32_k5_margin : B_8_exact 5 32 33 ≤ (7.3456e0 * table_10_margin : ℝ) :=
  table_10_row32_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 33 (k = 5), exact Table-10 margin target. -/
theorem table_10_row33_k5_margin : B_8_exact 5 33 34 ≤ (5.1941e0 * table_10_margin : ℝ) :=
  table_10_row33_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 34 (k = 5), exact Table-10 margin target. -/
theorem table_10_row34_k5_margin : B_8_exact 5 34 35 ≤ (3.6562e0 * table_10_margin : ℝ) :=
  table_10_row34_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 35 (k = 5), exact Table-10 margin target. -/
theorem table_10_row35_k5_margin : B_8_exact 5 35 36 ≤ (2.5627e0 * table_10_margin : ℝ) :=
  table_10_row35_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 36 (k = 5), exact Table-10 margin target. -/
theorem table_10_row36_k5_margin : B_8_exact 5 36 37 ≤ (2.0926e0 * table_10_margin : ℝ) :=
  table_10_row36_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 37 (k = 5), exact Table-10 margin target. -/
theorem table_10_row37_k5_margin : B_8_exact 5 37 38 ≤ (1.9830e0 * table_10_margin : ℝ) :=
  table_10_row37_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 38 (k = 5), exact Table-10 margin target. -/
theorem table_10_row38_k5_margin : B_8_exact 5 38 39 ≤ (2.0518e0 * table_10_margin : ℝ) :=
  table_10_row38_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 39 (k = 5), exact Table-10 margin target. -/
theorem table_10_row39_k5_margin : B_8_exact 5 39 40 ≤ (2.1915e0 * table_10_margin : ℝ) :=
  table_10_row39_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 40 (k = 5), exact Table-10 margin target. -/
theorem table_10_row40_k5_margin : B_8_exact 5 40 41 ≤ (2.3854e0 * table_10_margin : ℝ) :=
  table_10_row40_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 41 (k = 5), exact Table-10 margin target. -/
theorem table_10_row41_k5_margin : B_8_exact 5 41 42 ≤ (2.6265e0 * table_10_margin : ℝ) :=
  table_10_row41_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 42 (k = 5), exact Table-10 margin target. -/
theorem table_10_row42_k5_margin : B_8_exact 5 42 43 ≤ (2.9105e0 * table_10_margin : ℝ) :=
  table_10_row42_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-- Row 43 (k = 1), exact Table-10 margin target. -/
theorem table_10_row43_k1_margin : B_8_exact 1 43 (19 * log 10) ≤ (8.5986e-7 * table_10_margin : ℝ) :=
  row_bound_k1 43 (19 * log 10) 1.00000002 1.054 1.9339e-8 (8.5986e-7 * table_10_margin)
    (by exact r43_le_r19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row43_a2_le row43_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    row43_G1_right

/-- Row 43 (k = 2), exact Table-10 margin target. -/
theorem table_10_row43_k2_margin : B_8_exact 2 43 (19 * log 10) ≤ (3.7618e-5 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 43 (19 * log 10) 1.00000002 1.054 1.9339e-8 (3.7618e-5 * table_10_margin)
    (by exact r43_le_r19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row43_a2_le row43_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    row43_Pp0_right

/-- Row 43 (k = 3), exact Table-10 margin target. -/
theorem table_10_row43_k3_margin : B_8_exact 3 43 (19 * log 10) ≤ (0.0016458 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 43 (19 * log 10) 1.00000002 1.054 1.9339e-8 (0.0016458 * table_10_margin)
    (by exact r43_le_r19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row43_a2_le row43_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    row43_Pp1_right

/-- Row 43 (k = 4), exact Table-10 margin target. -/
theorem table_10_row43_k4_margin : B_8_exact 4 43 (19 * log 10) ≤ (0.072000 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 43 (19 * log 10) 1.00000002 1.054 1.9339e-8 (0.072000 * table_10_margin)
    (by exact r43_le_r19) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row43_a2_le row43_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    row43_Pp2_right

/-- Row 43 (k = 5), exact Table-10 margin target. -/
theorem table_10_row43_k5_margin : B_8_exact 5 43 (19 * log 10) ≤ (3.1500e0 * table_10_margin : ℝ) :=
  table_10_row43_k5.trans (by norm_num [table_10_margin, BKLNW_app.table_8_margin])

/-! ## First membership-dispatch wiring

This row-20 slice tests the in-tree shape needed by `bklnw_table_10_verification`:
recover the next table abscissa, recover the printed k = 5 value from table membership,
then chain to the margin theorem above. The full row set should be generated in shards,
because direct case splits over the 287-row table are expensive. -/

lemma table_10_next_row20 : table_10_next 20 = 21 := by
  exact table_10_next_cert_20

lemma table_10_row20_B5_of_mem (B : ℕ → ℝ)
    (h : ((20 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B 5 = 2.9160e2 := by
  exact (table_10_row20_values_of_mem B h).2.2.2.2

theorem table_10_row20_k5_dispatch (B : ℕ → ℝ)
    (h : ((20 : ℝ), B 1, B 2, B 3, B 4, B 5) ∈ table_10) :
    B_8_exact 5 20 (table_10_next 20) ≤ B 5 * table_10_margin := by
  rw [table_10_next_row20, table_10_row20_B5_of_mem B h]
  exact table_10_row20_k5_margin


/-! ## k = 1..4 margin bridges

    Per-row arguments are parsed from the compiled k = 5 theorems; listed values come
    from the canonical parsed grid; every bound was float-verified before emission. -/

/-- Row 20 (k = 1), exact Table-10 margin target. -/
theorem table_10_row20_k1_margin : B_8_exact 1 20 21 ≤ (0.0018077 * table_10_margin : ℝ) :=
  row_bound_k1 20 21 1.00000002 1.4263 4.2676e-5 (0.0018077 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 20 (k = 2), exact Table-10 margin target. -/
theorem table_10_row20_k2_margin : B_8_exact 2 20 21 ≤ (0.036154 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 20 21 1.00000002 1.4263 4.2676e-5 (0.036154 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 20 (k = 3), exact Table-10 margin target. -/
theorem table_10_row20_k3_margin : B_8_exact 3 20 21 ≤ (0.72309 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 20 21 1.00000002 1.4263 4.2676e-5 (0.72309 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 20 (k = 4), exact Table-10 margin target. -/
theorem table_10_row20_k4_margin : B_8_exact 4 20 21 ≤ (14.462 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 20 21 1.00000002 1.4263 4.2676e-5 (14.462 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row20_a1_le row20_a2_le row20_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 21 (k = 1), exact Table-10 margin target. -/
theorem table_10_row21_k1_margin : B_8_exact 1 21 22 ≤ (0.0011458 * table_10_margin : ℝ) :=
  row_bound_k1 21 22 1.00000002 1.4394 2.5885e-5 (0.0011458 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row21_a2_le row21_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 21 (k = 2), exact Table-10 margin target. -/
theorem table_10_row21_k2_margin : B_8_exact 2 21 22 ≤ (0.024062 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 21 22 1.00000002 1.4394 2.5885e-5 (0.024062 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row21_a2_le row21_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 21 (k = 3), exact Table-10 margin target. -/
theorem table_10_row21_k3_margin : B_8_exact 3 21 22 ≤ (0.5053 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 21 22 1.00000002 1.4394 2.5885e-5 (0.5053 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row21_a2_le row21_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 21 (k = 4), exact Table-10 margin target. -/
theorem table_10_row21_k4_margin : B_8_exact 4 21 22 ≤ (10.611 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 21 22 1.00000002 1.4394 2.5885e-5 (10.611 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row21_a2_le row21_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 22 (k = 1), exact Table-10 margin target. -/
theorem table_10_row22_k1_margin : B_8_exact 1 22 23 ≤ (0.00072527 * table_10_margin : ℝ) :=
  row_bound_k1 22 23 1.00000002 1.3845 1.5701e-5 (0.00072527 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row22_a2_le row22_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 22 (k = 2), exact Table-10 margin target. -/
theorem table_10_row22_k2_margin : B_8_exact 2 22 23 ≤ (0.015956 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 22 23 1.00000002 1.3845 1.5701e-5 (0.015956 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row22_a2_le row22_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 22 (k = 3), exact Table-10 margin target. -/
theorem table_10_row22_k3_margin : B_8_exact 3 22 23 ≤ (0.35103 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 22 23 1.00000002 1.3845 1.5701e-5 (0.35103 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row22_a2_le row22_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 22 (k = 4), exact Table-10 margin target. -/
theorem table_10_row22_k4_margin : B_8_exact 4 22 23 ≤ (7.7226 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 22 23 1.00000002 1.3845 1.5701e-5 (7.7226 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row22_a2_le row22_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 23 (k = 1), exact Table-10 margin target. -/
theorem table_10_row23_k1_margin : B_8_exact 1 23 24 ≤ (0.00045848 * table_10_margin : ℝ) :=
  row_bound_k1 23 24 1.00000002 1.3405 9.5224e-6 (0.00045848 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row23_a2_le row23_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 23 (k = 2), exact Table-10 margin target. -/
theorem table_10_row23_k2_margin : B_8_exact 2 23 24 ≤ (0.010545 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 23 24 1.00000002 1.3405 9.5224e-6 (0.010545 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row23_a2_le row23_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 23 (k = 3), exact Table-10 margin target. -/
theorem table_10_row23_k3_margin : B_8_exact 3 23 24 ≤ (0.24254 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 23 24 1.00000002 1.3405 9.5224e-6 (0.24254 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row23_a2_le row23_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 23 (k = 4), exact Table-10 margin target. -/
theorem table_10_row23_k4_margin : B_8_exact 4 23 24 ≤ (5.5783 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 23 24 1.00000002 1.3405 9.5224e-6 (5.5783 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row23_a2_le row23_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 24 (k = 1), exact Table-10 margin target. -/
theorem table_10_row24_k1_margin : B_8_exact 1 24 25 ≤ (0.00028945 * table_10_margin : ℝ) :=
  row_bound_k1 24 25 1.00000002 1.2999 5.7757e-6 (0.00028945 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row24_a2_le row24_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 24 (k = 2), exact Table-10 margin target. -/
theorem table_10_row24_k2_margin : B_8_exact 2 24 25 ≤ (0.0069468 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 24 25 1.00000002 1.2999 5.7757e-6 (0.0069468 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row24_a2_le row24_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 24 (k = 3), exact Table-10 margin target. -/
theorem table_10_row24_k3_margin : B_8_exact 3 24 25 ≤ (0.16672 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 24 25 1.00000002 1.2999 5.7757e-6 (0.16672 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row24_a2_le row24_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 24 (k = 4), exact Table-10 margin target. -/
theorem table_10_row24_k4_margin : B_8_exact 4 24 25 ≤ (4.0013 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 24 25 1.00000002 1.2999 5.7757e-6 (4.0013 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row24_a2_le row24_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 25 (k = 1), exact Table-10 margin target. -/
theorem table_10_row25_k1_margin : B_8_exact 1 25 26 ≤ (0.00018251 * table_10_margin : ℝ) :=
  row_bound_k1 25 26 1.00000002 1.2196 3.5032e-6 (0.00018251 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 25 (k = 2), exact Table-10 margin target. -/
theorem table_10_row25_k2_margin : B_8_exact 2 25 26 ≤ (0.0045626 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 25 26 1.00000002 1.2196 3.5032e-6 (0.0045626 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 25 (k = 3), exact Table-10 margin target. -/
theorem table_10_row25_k3_margin : B_8_exact 3 25 26 ≤ (0.11407 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 25 26 1.00000002 1.2196 3.5032e-6 (0.11407 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 25 (k = 4), exact Table-10 margin target. -/
theorem table_10_row25_k4_margin : B_8_exact 4 25 26 ≤ (2.8516 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 25 26 1.00000002 1.2196 3.5032e-6 (2.8516 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row25_a1_le row25_a2_le row25_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 26 (k = 1), exact Table-10 margin target. -/
theorem table_10_row26_k1_margin : B_8_exact 1 26 27 ≤ (0.00011493 * table_10_margin : ℝ) :=
  row_bound_k1 26 27 1.00000002 1.25 2.1248e-6 (0.00011493 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row26_a1_le row26_a2_le row26_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 26 (k = 2), exact Table-10 margin target. -/
theorem table_10_row26_k2_margin : B_8_exact 2 26 27 ≤ (0.0029882 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 26 27 1.00000002 1.25 2.1248e-6 (0.0029882 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row26_a1_le row26_a2_le row26_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 26 (k = 3), exact Table-10 margin target. -/
theorem table_10_row26_k3_margin : B_8_exact 3 26 27 ≤ (0.077694 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 26 27 1.00000002 1.25 2.1248e-6 (0.077694 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row26_a1_le row26_a2_le row26_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 26 (k = 4), exact Table-10 margin target. -/
theorem table_10_row26_k4_margin : B_8_exact 4 26 27 ≤ (2.02 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 26 27 1.00000002 1.25 2.1248e-6 (2.02 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    row26_a1_le row26_a2_le row26_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 27 (k = 1), exact Table-10 margin target. -/
theorem table_10_row27_k1_margin : B_8_exact 1 27 28 ≤ (7.2293e-05 * table_10_margin : ℝ) :=
  row_bound_k1 27 28 1.00000002 1.22 1.2888e-6 (7.2293e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row27_a2_le row27_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 27 (k = 2), exact Table-10 margin target. -/
theorem table_10_row27_k2_margin : B_8_exact 2 27 28 ≤ (0.0019519 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 27 28 1.00000002 1.22 1.2888e-6 (0.0019519 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row27_a2_le row27_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 27 (k = 3), exact Table-10 margin target. -/
theorem table_10_row27_k3_margin : B_8_exact 3 27 28 ≤ (0.052702 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 27 28 1.00000002 1.22 1.2888e-6 (0.052702 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row27_a2_le row27_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 27 (k = 4), exact Table-10 margin target. -/
theorem table_10_row27_k4_margin : B_8_exact 4 27 28 ≤ (1.4229 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 27 28 1.00000002 1.22 1.2888e-6 (1.4229 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row27_a2_le row27_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 28 (k = 1), exact Table-10 margin target. -/
theorem table_10_row28_k1_margin : B_8_exact 1 28 29 ≤ (4.5421e-05 * table_10_margin : ℝ) :=
  row_bound_k1 28 29 1.00000002 1.20 7.8165e-7 (4.5421e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row28_a2_le row28_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 28 (k = 2), exact Table-10 margin target. -/
theorem table_10_row28_k2_margin : B_8_exact 2 28 29 ≤ (0.0012718 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 28 29 1.00000002 1.20 7.8165e-7 (0.0012718 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row28_a2_le row28_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 28 (k = 3), exact Table-10 margin target. -/
theorem table_10_row28_k3_margin : B_8_exact 3 28 29 ≤ (0.03561 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 28 29 1.00000002 1.20 7.8165e-7 (0.03561 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row28_a2_le row28_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 28 (k = 4), exact Table-10 margin target. -/
theorem table_10_row28_k4_margin : B_8_exact 4 28 29 ≤ (0.99708 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 28 29 1.00000002 1.20 7.8165e-7 (0.99708 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row28_a2_le row28_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 29 (k = 1), exact Table-10 margin target. -/
theorem table_10_row29_k1_margin : B_8_exact 1 29 30 ≤ (2.8507e-05 * table_10_margin : ℝ) :=
  row_bound_k1 29 30 1.00000002 1.18 4.7410e-7 (2.8507e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row29_a2_le row29_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 29 (k = 2), exact Table-10 margin target. -/
theorem table_10_row29_k2_margin : B_8_exact 2 29 30 ≤ (0.0008267 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 29 30 1.00000002 1.18 4.7410e-7 (0.0008267 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row29_a2_le row29_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 29 (k = 3), exact Table-10 margin target. -/
theorem table_10_row29_k3_margin : B_8_exact 3 29 30 ≤ (0.023974 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 29 30 1.00000002 1.18 4.7410e-7 (0.023974 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row29_a2_le row29_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 29 (k = 4), exact Table-10 margin target. -/
theorem table_10_row29_k4_margin : B_8_exact 4 29 30 ≤ (0.69525 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 29 30 1.00000002 1.18 4.7410e-7 (0.69525 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row29_a2_le row29_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 30 (k = 1), exact Table-10 margin target. -/
theorem table_10_row30_k1_margin : B_8_exact 1 30 31 ≤ (1.7873e-05 * table_10_margin : ℝ) :=
  row_bound_k1 30 31 1.00000002 1.1531 2.8756e-7 (1.7873e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row30_a2_le row30_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 30 (k = 2), exact Table-10 margin target. -/
theorem table_10_row30_k2_margin : B_8_exact 2 30 31 ≤ (0.00053619 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 30 31 1.00000002 1.1531 2.8756e-7 (0.00053619 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row30_a2_le row30_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 30 (k = 3), exact Table-10 margin target. -/
theorem table_10_row30_k3_margin : B_8_exact 3 30 31 ≤ (0.016086 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 30 31 1.00000002 1.1531 2.8756e-7 (0.016086 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row30_a2_le row30_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 30 (k = 4), exact Table-10 margin target. -/
theorem table_10_row30_k4_margin : B_8_exact 4 30 31 ≤ (0.48257 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 30 31 1.00000002 1.1531 2.8756e-7 (0.48257 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row30_a2_le row30_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 31 (k = 1), exact Table-10 margin target. -/
theorem table_10_row31_k1_margin : B_8_exact 1 31 32 ≤ (1.1195e-05 * table_10_margin : ℝ) :=
  row_bound_k1 31 32 1.00000002 1.1383 1.7442e-7 (1.1195e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row31_a2_le row31_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 31 (k = 2), exact Table-10 margin target. -/
theorem table_10_row31_k2_margin : B_8_exact 2 31 32 ≤ (0.00034704 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 31 32 1.00000002 1.1383 1.7442e-7 (0.00034704 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row31_a2_le row31_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 31 (k = 3), exact Table-10 margin target. -/
theorem table_10_row31_k3_margin : B_8_exact 3 31 32 ≤ (0.010758 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 31 32 1.00000002 1.1383 1.7442e-7 (0.010758 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row31_a2_le row31_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 31 (k = 4), exact Table-10 margin target. -/
theorem table_10_row31_k4_margin : B_8_exact 4 31 32 ≤ (0.3335 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 31 32 1.00000002 1.1383 1.7442e-7 (0.3335 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row31_a2_le row31_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 32 (k = 1), exact Table-10 margin target. -/
theorem table_10_row32_k1_margin : B_8_exact 1 32 33 ≤ (7.0053e-06 * table_10_margin : ℝ) :=
  row_bound_k1 32 33 1.00000002 1.1257 1.0579e-7 (7.0053e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row32_a2_le row32_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 32 (k = 2), exact Table-10 margin target. -/
theorem table_10_row32_k2_margin : B_8_exact 2 32 33 ≤ (0.00022417 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 32 33 1.00000002 1.1257 1.0579e-7 (0.00022417 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row32_a2_le row32_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 32 (k = 3), exact Table-10 margin target. -/
theorem table_10_row32_k3_margin : B_8_exact 3 32 33 ≤ (0.0071734 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 32 33 1.00000002 1.1257 1.0579e-7 (0.0071734 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row32_a2_le row32_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 32 (k = 4), exact Table-10 margin target. -/
theorem table_10_row32_k4_margin : B_8_exact 4 32 33 ≤ (0.22955 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 32 33 1.00000002 1.1257 1.0579e-7 (0.22955 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row32_a2_le row32_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 33 (k = 1), exact Table-10 margin target. -/
theorem table_10_row33_k1_margin : B_8_exact 1 33 34 ≤ (4.3798e-06 * table_10_margin : ℝ) :=
  row_bound_k1 33 34 1.00000002 1.1144 6.4162e-8 (4.3798e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row33_a2_le row33_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 33 (k = 2), exact Table-10 margin target. -/
theorem table_10_row33_k2_margin : B_8_exact 2 33 34 ≤ (0.00014453 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 33 34 1.00000002 1.1144 6.4162e-8 (0.00014453 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row33_a2_le row33_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 33 (k = 3), exact Table-10 margin target. -/
theorem table_10_row33_k3_margin : B_8_exact 3 33 34 ≤ (0.0047696 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 33 34 1.00000002 1.1144 6.4162e-8 (0.0047696 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row33_a2_le row33_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 33 (k = 4), exact Table-10 margin target. -/
theorem table_10_row33_k4_margin : B_8_exact 4 33 34 ≤ (0.1574 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 33 34 1.00000002 1.1144 6.4162e-8 (0.1574 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row33_a2_le row33_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 34 (k = 1), exact Table-10 margin target. -/
theorem table_10_row34_k1_margin : B_8_exact 1 34 35 ≤ (2.736e-06 * table_10_margin : ℝ) :=
  row_bound_k1 34 35 1.00000002 1.1047 3.8917e-8 (2.736e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row34_a2_le row34_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 34 (k = 2), exact Table-10 margin target. -/
theorem table_10_row34_k2_margin : B_8_exact 2 34 35 ≤ (9.3023e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 34 35 1.00000002 1.1047 3.8917e-8 (9.3023e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row34_a2_le row34_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 34 (k = 3), exact Table-10 margin target. -/
theorem table_10_row34_k3_margin : B_8_exact 3 34 35 ≤ (0.0031628 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 34 35 1.00000002 1.1047 3.8917e-8 (0.0031628 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row34_a2_le row34_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 34 (k = 4), exact Table-10 margin target. -/
theorem table_10_row34_k4_margin : B_8_exact 4 34 35 ≤ (0.10754 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 34 35 1.00000002 1.1047 3.8917e-8 (0.10754 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row34_a2_le row34_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 35 (k = 1), exact Table-10 margin target. -/
theorem table_10_row35_k1_margin : B_8_exact 1 35 36 ≤ (1.7077e-06 * table_10_margin : ℝ) :=
  row_bound_k1 35 36 1.00000002 1.0959 2.3604e-8 (1.7077e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row35_a2_le row35_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 35 (k = 2), exact Table-10 margin target. -/
theorem table_10_row35_k2_margin : B_8_exact 2 35 36 ≤ (5.977e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 35 36 1.00000002 1.0959 2.3604e-8 (5.977e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row35_a2_le row35_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 35 (k = 3), exact Table-10 margin target. -/
theorem table_10_row35_k3_margin : B_8_exact 3 35 36 ≤ (0.002092 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 35 36 1.00000002 1.0959 2.3604e-8 (0.002092 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row35_a2_le row35_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 35 (k = 4), exact Table-10 margin target. -/
theorem table_10_row35_k4_margin : B_8_exact 4 35 36 ≤ (0.073219 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 35 36 1.00000002 1.0959 2.3604e-8 (0.073219 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row35_a2_le row35_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 36 (k = 1), exact Table-10 margin target. -/
theorem table_10_row36_k1_margin : B_8_exact 1 36 37 ≤ (1.2459e-06 * table_10_margin : ℝ) :=
  row_bound_k1 36 37 1.00000002 1.0883 1.9339e-8 (1.2459e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row36_a2_le row36_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 36 (k = 2), exact Table-10 margin target. -/
theorem table_10_row36_k2_margin : B_8_exact 2 36 37 ≤ (4.4852e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 36 37 1.00000002 1.0883 1.9339e-8 (4.4852e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row36_a2_le row36_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 36 (k = 3), exact Table-10 margin target. -/
theorem table_10_row36_k3_margin : B_8_exact 3 36 37 ≤ (0.0016147 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 36 37 1.00000002 1.0883 1.9339e-8 (0.0016147 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row36_a2_le row36_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 36 (k = 4), exact Table-10 margin target. -/
theorem table_10_row36_k4_margin : B_8_exact 4 36 37 ≤ (0.058128 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 36 37 1.00000002 1.0883 1.9339e-8 (0.058128 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row36_a2_le row36_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 37 (k = 1), exact Table-10 margin target. -/
theorem table_10_row37_k1_margin : B_8_exact 1 37 38 ≤ (1.0581e-06 * table_10_margin : ℝ) :=
  row_bound_k1 37 38 1.00000002 1.0815 1.9339e-8 (1.0581e-06 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row37_a2_le row37_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 37 (k = 2), exact Table-10 margin target. -/
theorem table_10_row37_k2_margin : B_8_exact 2 37 38 ≤ (3.9148e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 37 38 1.00000002 1.0815 1.9339e-8 (3.9148e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row37_a2_le row37_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 37 (k = 3), exact Table-10 margin target. -/
theorem table_10_row37_k3_margin : B_8_exact 3 37 38 ≤ (0.0014485 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 37 38 1.00000002 1.0815 1.9339e-8 (0.0014485 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row37_a2_le row37_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 37 (k = 4), exact Table-10 margin target. -/
theorem table_10_row37_k4_margin : B_8_exact 4 37 38 ≤ (0.053593 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 37 38 1.00000002 1.0815 1.9339e-8 (0.053593 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row37_a2_le row37_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 38 (k = 1), exact Table-10 margin target. -/
theorem table_10_row38_k1_margin : B_8_exact 1 38 39 ≤ (9.4814e-07 * table_10_margin : ℝ) :=
  row_bound_k1 38 39 1.00000002 1.0755 1.9339e-8 (9.4814e-07 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row38_a2_le row38_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 38 (k = 2), exact Table-10 margin target. -/
theorem table_10_row38_k2_margin : B_8_exact 2 38 39 ≤ (3.6029e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 38 39 1.00000002 1.0755 1.9339e-8 (3.6029e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row38_a2_le row38_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 38 (k = 3), exact Table-10 margin target. -/
theorem table_10_row38_k3_margin : B_8_exact 3 38 39 ≤ (0.0013691 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 38 39 1.00000002 1.0755 1.9339e-8 (0.0013691 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row38_a2_le row38_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 38 (k = 4), exact Table-10 margin target. -/
theorem table_10_row38_k4_margin : B_8_exact 4 38 39 ≤ (0.052611 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 38 39 1.00000002 1.0755 1.9339e-8 (0.052611 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row38_a2_le row38_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 39 (k = 1), exact Table-10 margin target. -/
theorem table_10_row39_k1_margin : B_8_exact 1 39 40 ≤ (8.8692e-07 * table_10_margin : ℝ) :=
  row_bound_k1 39 40 1.00000002 1.0702 1.9339e-8 (8.8692e-07 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row39_a2_le row39_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 39 (k = 2), exact Table-10 margin target. -/
theorem table_10_row39_k2_margin : B_8_exact 2 39 40 ≤ (3.459e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 39 40 1.00000002 1.0702 1.9339e-8 (3.459e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row39_a2_le row39_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 39 (k = 3), exact Table-10 margin target. -/
theorem table_10_row39_k3_margin : B_8_exact 3 39 40 ≤ (0.0013697 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 39 40 1.00000002 1.0702 1.9339e-8 (0.0013697 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row39_a2_le row39_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 39 (k = 4), exact Table-10 margin target. -/
theorem table_10_row39_k4_margin : B_8_exact 4 39 40 ≤ (0.054788 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 39 40 1.00000002 1.0702 1.9339e-8 (0.054788 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row39_a2_le row39_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 40 (k = 1), exact Table-10 margin target. -/
theorem table_10_row40_k1_margin : B_8_exact 1 40 41 ≤ (8.5607e-07 * table_10_margin : ℝ) :=
  row_bound_k1 40 41 1.00000002 1.0654 1.9339e-8 (8.5607e-07 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row40_a2_le row40_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 40 (k = 2), exact Table-10 margin target. -/
theorem table_10_row40_k2_margin : B_8_exact 2 40 41 ≤ (3.4611e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 40 41 1.00000002 1.0654 1.9339e-8 (3.4611e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row40_a2_le row40_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 40 (k = 3), exact Table-10 margin target. -/
theorem table_10_row40_k3_margin : B_8_exact 3 40 41 ≤ (0.001419 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 40 41 1.00000002 1.0654 1.9339e-8 (0.001419 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row40_a2_le row40_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 40 (k = 4), exact Table-10 margin target. -/
theorem table_10_row40_k4_margin : B_8_exact 4 40 41 ≤ (0.058181 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 40 41 1.00000002 1.0654 1.9339e-8 (0.058181 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row40_a2_le row40_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 41 (k = 1), exact Table-10 margin target. -/
theorem table_10_row41_k1_margin : B_8_exact 1 41 42 ≤ (8.4416e-07 * table_10_margin : ℝ) :=
  row_bound_k1 41 42 1.00000002 1.0612 1.9339e-8 (8.4416e-07 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row41_a2_le row41_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 41 (k = 2), exact Table-10 margin target. -/
theorem table_10_row41_k2_margin : B_8_exact 2 41 42 ≤ (3.5451e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 41 42 1.00000002 1.0612 1.9339e-8 (3.5451e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row41_a2_le row41_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 41 (k = 3), exact Table-10 margin target. -/
theorem table_10_row41_k3_margin : B_8_exact 3 41 42 ≤ (0.0014889 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 41 42 1.00000002 1.0612 1.9339e-8 (0.0014889 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row41_a2_le row41_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 41 (k = 4), exact Table-10 margin target. -/
theorem table_10_row41_k4_margin : B_8_exact 4 41 42 ≤ (0.062535 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 41 42 1.00000002 1.0612 1.9339e-8 (0.062535 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row41_a2_le row41_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 42 (k = 1), exact Table-10 margin target. -/
theorem table_10_row42_k1_margin : B_8_exact 1 42 43 ≤ (8.5132e-07 * table_10_margin : ℝ) :=
  row_bound_k1 42 43 1.00000002 1.0573 1.9338e-8 (8.5132e-07 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row42_a2_le row42_eps_le
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold G1 eT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 42 (k = 2), exact Table-10 margin target. -/
theorem table_10_row42_k2_margin : B_8_exact 2 42 43 ≤ (3.6607e-05 * table_10_margin : ℝ) :=
  row_bound_kge2 0 (by norm_num) 42 43 1.00000002 1.0573 1.9338e-8 (3.6607e-05 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row42_a2_le row42_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 42 (k = 3), exact Table-10 margin target. -/
theorem table_10_row42_k3_margin : B_8_exact 3 42 43 ≤ (0.0015741 * table_10_margin : ℝ) :=
  row_bound_kge2 1 (by norm_num) 42 43 1.00000002 1.0573 1.9338e-8 (0.0015741 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row42_a2_le row42_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

/-- Row 42 (k = 4), exact Table-10 margin target. -/
theorem table_10_row42_k4_margin : B_8_exact 4 42 43 ≤ (0.067686 * table_10_margin : ℝ) :=
  row_bound_kge2 2 (by norm_num) 42 43 1.00000002 1.0573 1.9338e-8 (0.067686 * table_10_margin)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (a1_le_small (by norm_num)) row42_a2_le row42_eps_le
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)
    (by unfold Pp pT; norm_num [table_10_margin, BKLNW_app.table_8_margin]; interval_decide)

end BKLNW
