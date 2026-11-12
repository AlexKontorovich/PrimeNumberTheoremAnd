import RSBounds.QuarticFirst29BudgetApplication

/-! Scalar budgets for the global RS62 prime-product handoff. -/

open Real

namespace TernaryGoldbach.RSBounds.RS62ProductBudget

open BacklundLowScalar

noncomputable def error (L s e j : ℝ) : ℝ :=
  e / L + 2 * j * (1 / L + 1 / L ^ 2) + 5.6 / (s * L)

noncomputable def jModel (x : ℝ) : ℝ :=
  0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 + 6000 * x ^ (-3 / 2 : ℝ) +
    Real.log (2 * Real.pi) / x

private theorem log10_bounds : (2.3 : ℝ) ≤ Real.log 10 ∧ Real.log 10 ≤ 2.3026 := by
  let c : LogCert := ⟨3, 4, 1⟩
  have hv : c.Valid := by decide +kernel
  have hl : (2.3 : ℚ) ≤ c.lower := by decide +kernel
  have hu : c.upper ≤ (2.3026 : ℚ) := by decide +kernel
  have hb := LogCert.log_bounds hv
  have he : (c.ratio : ℝ) = 10 := by norm_num [c, LogCert.ratio]
  rw [he] at hb
  constructor
  · have hlr : (2.3 : ℝ) ≤ (c.lower : ℝ) := by
      simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).mpr hl
    exact hlr.trans hb.1
  · have hur : (c.upper : ℝ) ≤ 2.3026 := by
      simpa only [Rat.cast_ofScientific] using (Rat.cast_le (K := ℝ)).mpr hu
    exact hb.2.trans hur

theorem log_hundred_thousand_bounds :
    (11.5 : ℝ) ≤ Real.log 100000 ∧ Real.log 100000 ≤ 11.513 := by
  have he : Real.log (100000 : ℝ) = 5 * Real.log 10 := by
    rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]
    norm_num
  rw [he]
  constructor <;> linarith [log10_bounds.1, log10_bounds.2]

private theorem log_two_pi_le_three : Real.log (2 * Real.pi) ≤ 3 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo 3
  rw [← Real.exp_nat_mul] at hh
  norm_num only [Nat.cast_ofNat, mul_one] at hh
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 2 * Real.pi)).mpr
  linarith [Real.pi_lt_d4]

/-- Monotonicity is obtained directly from log t≤t−1, without new calculus. -/
theorem log_div_sqrt_le {a x : ℝ} (ha : 0 < a) (hax : a ≤ x)
    (hlog : 2 ≤ Real.log a) :
    Real.log x / Real.sqrt x ≤ Real.log a / Real.sqrt a := by
  have hx : 0 < x := ha.trans_le hax
  have hsx := Real.sqrt_pos.mpr hx
  have hsa := Real.sqrt_pos.mpr ha
  have hs := Real.sqrt_le_sqrt hax
  have hq : 1 ≤ Real.sqrt x / Real.sqrt a := by
    apply (le_div_iff₀ hsa).mpr
    simpa using hs
  have ht := Real.log_le_sub_one_of_pos (div_pos hsx hsa)
  rw [Real.log_div hsx.ne' hsa.ne', Real.log_sqrt hx.le, Real.log_sqrt ha.le] at ht
  have hm := mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hq)
  have hb : Real.log x ≤ Real.log a * (Real.sqrt x / Real.sqrt a) := by
    nlinarith only [ht, hm]
  apply (div_le_div_iff₀ hsx hsa).mpr
  calc
    _ ≤ (Real.log a * (Real.sqrt x / Real.sqrt a)) * Real.sqrt a :=
      mul_le_mul_of_nonneg_right hb hsa.le
    _ = _ := by field_simp [hsa.ne'] <;> ring

private theorem moderate_points {x : ℝ} (hx : 100000 ≤ x) :
    11.5 ≤ Real.log x ∧ 316 ≤ Real.sqrt x ∧ Real.log x / Real.sqrt x ≤ 0.0365 := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 100000) hx
  have hs : (316 : ℝ) ≤ Real.sqrt 100000 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  refine ⟨log_hundred_thousand_bounds.1.trans hlog, hs.trans (Real.sqrt_le_sqrt hx), ?_⟩
  have hq := log_div_sqrt_le (by norm_num : (0 : ℝ) < 100000) hx
    (by linarith [log_hundred_thousand_bounds.1])
  calc
    _ ≤ Real.log 100000 / Real.sqrt 100000 := hq
    _ ≤ 11.513 / Real.sqrt 100000 := div_le_div_of_nonneg_right
      log_hundred_thousand_bounds.2 (Real.sqrt_nonneg _)
    _ ≤ 11.513 / 316 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
    _ ≤ _ := by norm_num

private theorem b23_points {x : ℝ} (hx : Real.exp 23 ≤ x) :
    23 ≤ Real.log x ∧ 90000 ≤ Real.sqrt x ∧ Real.log x / Real.sqrt x ≤ 23 / 90000 := by
  have hlog := Real.log_le_log (Real.exp_pos 23) hx
  rw [Real.log_exp] at hlog
  have hs := QuarticFirst29BudgetApplication.sqrt_lower hx
  refine ⟨hlog, by linarith, ?_⟩
  have hq := log_div_sqrt_le (Real.exp_pos 23) hx (by rw [Real.log_exp]; norm_num)
  rw [Real.log_exp] at hq
  exact hq.trans (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    (show (90000 : ℝ) ≤ Real.sqrt (Real.exp 23) by
      linarith [QuarticFirst29BudgetApplication.sqrt_lower (x := Real.exp 23) le_rfl]))

theorem jModel_le {x : ℝ} (hx : 0 < x) :
    jModel x ≤ 0.0463 / Real.sqrt x + 2.4e-6 +
      6000 / (x * Real.sqrt x) + 3 / x := by
  have hh : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le,
      ← Real.sqrt_eq_rpow, one_div]
  have ht : x ^ (3 / 2 : ℝ) = x * Real.sqrt x := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add hx,
      Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hn : x ^ (-3 / 2 : ℝ) = 1 / (x * Real.sqrt x) := by
    rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring, Real.rpow_neg hx.le, ht, one_div]
  unfold jModel
  rw [hh, hn]
  simp only [mul_one_div]
  exact add_le_add le_rfl (div_le_div_of_nonneg_right log_two_pi_le_three hx.le)

private theorem scaled_error_le {L s e j E J : ℝ} (hL : 0 < L) (hs : 0 < s)
    (he : e ≤ E) (hj : j ≤ J) :
    error L s e j * L ^ 2 ≤ E * L + 2 * J * (L + 1) + 5.6 * L / s := by
  have heq : error L s e j * L ^ 2 = e * L + 2 * j * (L + 1) + 5.6 * L / s := by
    unfold error
    field_simp [hL.ne', hs.ne'] <;> ring
  rw [heq]
  have h1 := mul_le_mul_of_nonneg_right he hL.le
  have h2 := mul_le_mul_of_nonneg_right hj (show 0 ≤ 2 * (L + 1) by linarith)
  nlinarith only [h1, h2]

noncomputable def model (x L s e0 k : ℝ) : ℝ :=
  e0 * L + (k + 5.6) * (L / s) + 0.0926 * ((L + 1) / s) +
    4.8e-6 * (L + 1) + 12000 * ((L + 1) / s) / x + 6 * ((L + 1) / s) / s

private theorem scaled_model_le {x e j e0 k : ℝ} (hx : 0 < x) (hL : 0 < Real.log x)
    (he : e ≤ e0 + k / Real.sqrt x) (hj : j ≤ jModel x) :
    error (Real.log x) (Real.sqrt x) e j * (Real.log x) ^ 2 ≤
      model x (Real.log x) (Real.sqrt x) e0 k := by
  have hs := Real.sqrt_pos.mpr hx
  have hb := scaled_error_le hL hs he (hj.trans (jModel_le hx))
  refine hb.trans_eq ?_
  have halg {u s L e0 k : ℝ} (hs0 : s ≠ 0) (hsq : s ^ 2 = u) :
      (e0 + k / s) * L +
        2 * (0.0463 / s + 2.4e-6 + 6000 / (u * s) + 3 / u) * (L + 1) +
        5.6 * L / s = model u L s e0 k := by
    subst u
    unfold model
    field_simp [hs0] <;> ring
  exact halg hs.ne' (Real.sq_sqrt hx.le)

private theorem moderate_model_lt {x L s : ℝ} (hx : 100000 ≤ x)
    (hL0 : 11.5 ≤ L) (hL : L ≤ 23) (hs : 316 ≤ s) (hq : L / s ≤ 0.0365) :
    model x L s 0.0023 6 < 0.49 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < s := by linarith
  have hi : 1 / s ≤ 0.0032 :=
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs).trans (by norm_num)
  have hq1 : (L + 1) / s ≤ 0.0397 := by
    rw [add_div]
    linarith
  have ht : 12000 * ((L + 1) / s) / x ≤ 12000 * 0.0397 / 100000 := by
    calc
      _ ≤ 12000 * 0.0397 / x := div_le_div_of_nonneg_right (by linarith) hx0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hu : 6 * ((L + 1) / s) / s ≤ 6 * 0.0397 / 316 := by
    calc
      _ ≤ 6 * 0.0397 / s := div_le_div_of_nonneg_right (by linarith) hs0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  unfold model
  have h0 := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 0.0023)
  have h1 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 11.6)
  have h2 := mul_le_mul_of_nonneg_left hq1 (by norm_num : (0 : ℝ) ≤ 0.0926)
  have h3 := mul_le_mul_of_nonneg_left (show L + 1 ≤ 24 by linarith)
    (by norm_num : (0 : ℝ) ≤ 4.8e-6)
  norm_num at ht hu
  linarith

private theorem b23_model_lt {x L s : ℝ} (hx : (90000 : ℝ) ^ 2 ≤ x)
    (hL0 : 23 ≤ L) (hL : L ≤ 2400) (hs : 90000 ≤ s) (hq : L / s ≤ 23 / 90000) :
    model x L s 0.00020211 0 < 0.499 := by
  have hx0 : 0 < x := by nlinarith
  have hs0 : 0 < s := by linarith
  have hi : 1 / s ≤ 1 / 90000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  have hq1 : (L + 1) / s ≤ 24 / 90000 := by rw [add_div]; linarith
  have ht : 12000 * ((L + 1) / s) / x ≤ 12000 * (24 / 90000) / 90000 ^ 2 := by
    calc
      _ ≤ 12000 * (24 / 90000) / x := div_le_div_of_nonneg_right (by linarith) hx0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have hu : 6 * ((L + 1) / s) / s ≤ 6 * (24 / 90000) / 90000 := by
    calc
      _ ≤ 6 * (24 / 90000) / s := div_le_div_of_nonneg_right (by linarith) hs0.le
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs
  unfold model
  have h0 := mul_le_mul_of_nonneg_left hL (by norm_num : (0 : ℝ) ≤ 0.00020211)
  have h1 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 5.6)
  have h2 := mul_le_mul_of_nonneg_left hq1 (by norm_num : (0 : ℝ) ≤ 0.0926)
  have h3 := mul_le_mul_of_nonneg_left (show L + 1 ≤ 2401 by linarith)
    (by norm_num : (0 : ℝ) ≤ 4.8e-6)
  norm_num at ht hu
  linarith

private theorem lt_log_of_scaled {L E c : ℝ} (hL : 0 < L)
    (hE : E * L ^ 2 < c) (hc : c * (2 * L ^ 2 + 1) < L ^ 2) :
    E < Real.log (1 + 1 / (2 * L ^ 2)) := by
  have hs : 0 < L ^ 2 := sq_pos_of_pos hL
  have hd : 0 < 2 * L ^ 2 + 1 := by positivity
  have hl := Real.one_sub_inv_le_log_of_pos (by positivity : 0 < 1 + 1 / (2 * L ^ 2))
  have heq : 1 - (1 + 1 / (2 * L ^ 2))⁻¹ = 1 / (2 * L ^ 2 + 1) := by
    field_simp [hL.ne', hd.ne'] <;> ring
  rw [heq] at hl
  exact ((lt_div_iff₀ hs).mpr hE).trans
    (((div_lt_div_iff₀ hs hd).mpr (by simpa using hc)).trans_le hl)

theorem moderate_log_budget {x e j : ℝ} (hx : 100000 ≤ x) (hL : Real.log x ≤ 23)
    (he : e ≤ 0.0023 + 6 / Real.sqrt x)
    (hj : j ≤ 0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 +
      6000 * x ^ (-3 / 2 : ℝ) + Real.log (2 * Real.pi) / x) :
    e / Real.log x + 2 * j * (1 / Real.log x + 1 / (Real.log x) ^ 2) +
      5.6 / (Real.sqrt x * Real.log x) < Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  obtain ⟨hL0, hs, hq⟩ := moderate_points hx
  have hpos : 0 < Real.log x := by linarith
  have hb := (scaled_model_le (by linarith : 0 < x) hpos he hj).trans_lt
    (moderate_model_lt hx hL0 hL hs hq)
  apply lt_log_of_scaled hpos hb
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 11.5) hL0 2]

theorem b23_log_budget {x e j : ℝ} (hx : Real.exp 23 ≤ x) (hL : Real.log x ≤ 2400)
    (he : e ≤ 0.00020211)
    (hj : j ≤ 0.0463 * x ^ (-1 / 2 : ℝ) + 2.4e-6 +
      6000 * x ^ (-3 / 2 : ℝ) + Real.log (2 * Real.pi) / x) :
    e / Real.log x + 2 * j * (1 / Real.log x + 1 / (Real.log x) ^ 2) +
      5.6 / (Real.sqrt x * Real.log x) < Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  obtain ⟨hL0, hs, hq⟩ := b23_points hx
  have hx0 : 0 < x := (Real.exp_pos 23).trans_le hx
  have hpos : 0 < Real.log x := by linarith
  have he0 : e ≤ 0.00020211 + 0 / Real.sqrt x := by simpa using he
  have hxlo : (90000 : ℝ) ^ 2 ≤ x := by nlinarith [QuarticFirst29BudgetApplication.x_lower hx]
  have hb := (scaled_model_le hx0 hpos he0 hj).trans_lt
    (b23_model_lt hxlo hL0 hL hs hq)
  apply lt_log_of_scaled hpos hb
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 23) hL0 2]

theorem large_log_budget {x e j : ℝ} (hx : Real.exp 2400 ≤ x)
    (he : e ≤ 0.1 / Real.log x) (hj : j ≤ 1 / (Real.log x) ^ 2) :
    e / Real.log x + 2 * j * (1 / Real.log x + 1 / (Real.log x) ^ 2) +
      5.6 / (Real.sqrt x * Real.log x) < Real.log (1 + 1 / (2 * (Real.log x) ^ 2)) := by
  have hx23 : Real.exp 23 ≤ x := (Real.exp_le_exp.mpr (by norm_num : (23 : ℝ) ≤ 2400)).trans hx
  obtain ⟨_, hs, hq⟩ := b23_points hx23
  have hx0 : 0 < x := (Real.exp_pos 2400).trans_le hx
  have hL := Real.log_le_log (Real.exp_pos 2400) hx
  rw [Real.log_exp] at hL
  have hpos : 0 < Real.log x := by linarith
  have hb := scaled_error_le hpos (Real.sqrt_pos.mpr hx0) he hj
  have heq : (0.1 / Real.log x) * Real.log x +
      2 * (1 / (Real.log x) ^ 2) * (Real.log x + 1) + 5.6 * Real.log x / Real.sqrt x =
      0.1 + 2 / Real.log x + 2 / (Real.log x) ^ 2 + 5.6 * (Real.log x / Real.sqrt x) := by
    field_simp [hpos.ne'] <;> ring
  rw [heq] at hb
  have h1 : 2 / Real.log x ≤ 2 / 2400 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hL
  have h2 : 2 / (Real.log x) ^ 2 ≤ 2 / 2400 ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2400) hL 2)
  have h3 := mul_le_mul_of_nonneg_left hq (by norm_num : (0 : ℝ) ≤ 5.6)
  have hscaled : error (Real.log x) (Real.sqrt x) e j * (Real.log x) ^ 2 < 0.2 := by
    linarith
  apply lt_log_of_scaled hpos hscaled
  nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2400) hL 2]

end TernaryGoldbach.RSBounds.RS62ProductBudget
