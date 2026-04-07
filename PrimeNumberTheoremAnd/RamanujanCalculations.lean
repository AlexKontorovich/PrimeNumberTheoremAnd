import PrimeNumberTheoremAnd.Defs
import LeanCert.Tactic.IntervalAuto

namespace Ramanujan

open Real Set MeasureTheory intervalIntegral

noncomputable def styleVal (y : ℝ) : ℝ :=
  y * (y * (y * (y * y))) *
    ((3797 / 10 : ℝ) *
      exp (log (y * (250000 / 1393353 : ℝ)) * (38 / 25 : ℝ)) *
      exp ((-189 / 100 : ℝ) * sqrt (y * (250000 / 1393353 : ℝ))))

theorem styleVal_bound {L C : ℝ}
    (haux :
      ∀ y ∈ Set.Icc L L,
        y * (y * (y * (y * y))) *
            ((3797 / 10 : ℝ) *
              exp (log (y * (250000 / 1393353 : ℝ)) * (38 / 25 : ℝ)) *
              exp ((-189 / 100 : ℝ) * sqrt (y * (250000 / 1393353 : ℝ)))) ≤
          C) :
    ∀ y ∈ Set.Icc L L, styleVal y ≤ C := by
  intro y hy
  simpa [styleVal] using haux y hy

theorem style_eq (y : ℝ) (hy : 0 < y) :
    y ^ 5 * ((379.7 : ℝ) * (y / 5.573412) ^ (1.52 : ℝ) *
      exp (-(1.89 : ℝ) * (sqrt y / sqrt (5.573412 : ℝ))))
    =
    styleVal y := by
  have hdiv : y / (1393353 / 250000 : ℝ) = y * (250000 / 1393353 : ℝ) := by field_simp
  have hposbase : 0 < y * (250000 / 1393353 : ℝ) := by positivity
  unfold styleVal
  rw [show y ^ 5 = y * (y * (y * (y * y))) by ring,
    show (379.7 : ℝ) = (3797 / 10 : ℝ) by norm_num,
    show (5.573412 : ℝ) = (1393353 / 250000 : ℝ) by norm_num, hdiv,
    rpow_def_of_pos hposbase, show (1.52 : ℝ) = (38 / 25 : ℝ) by norm_num,
    show sqrt y / sqrt (1393353 / 250000 : ℝ) = sqrt (y * (250000 / 1393353 : ℝ)) by
      rw [← sqrt_div (le_of_lt hy), hdiv],
    show (1.89 : ℝ) = (189 / 100 : ℝ) by norm_num,
    show (-(189 / 100 : ℝ)) * sqrt (y * (250000 / 1393353 : ℝ)) =
      (-189 / 100 : ℝ) * sqrt (y * (250000 / 1393353 : ℝ)) by ring]

lemma rpow_652_split {y : ℝ} (hy : 0 < y) :
    y ^ (6.52 : ℝ) = y ^ (5 : ℕ) * y ^ (1.52 : ℝ) := by
  rw [show (6.52 : ℝ) = 5 + 1.52 by norm_num, rpow_add hy]; simp

lemma sqrt_ratio_5573412 {y : ℝ} (hy : 0 ≤ y) :
    (y / 5.573412) ^ ((1 : ℝ) / 2) = sqrt y / sqrt (5.573412 : ℝ) := by
  rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) by norm_num, ← sqrt_eq_rpow]
  rw [sqrt_div hy]

theorem not_mem_Ico_of_ge_exp3000
    {z lo hi : ℝ} (hz : z ≥ exp 3000) (hhi : hi ≤ exp 3000) :
    ¬ z ∈ Set.Ico lo hi :=
  fun hzmem => (not_lt_of_ge (le_trans hhi hz)) hzmem.2

theorem styleVal_bound_3914_1311 :
    ∀ y ∈ Set.Icc (3914 : ℝ) 3914, styleVal y ≤ (1311 : ℝ) := by
  exact styleVal_bound (L := (3914 : ℝ)) (C := (1311 : ℝ)) (by interval_bound 20)

theorem styleVal_bound_3870_1800 :
    ∀ y ∈ Set.Icc (3870 : ℝ) 3870, styleVal y ≤ (1800 : ℝ) := by
  exact styleVal_bound (L := (3870 : ℝ)) (C := (1800 : ℝ)) (by interval_bound 20)

theorem styleVal_bound_3915_13042_div_10 :
    ∀ y ∈ Set.Icc (3915 : ℝ) 3915, styleVal y ≤ (13042 / 10 : ℝ) := by
  exact
    styleVal_bound (L := (3915 : ℝ)) (C := (13042 / 10 : ℝ)) (by interval_bound 20)

theorem tail_small :
    7 * (3914 : ℝ) ^ 6 * exp (-(1957 : ℝ)) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 := by
  have h := (show ∀ y ∈ Set.Icc (3914 : ℝ) 3914,
      7 * y ^ 6 * exp (-y / 2) / (log 2) ^ 8 ≤ (1 : ℝ) / 1000000 by
    interval_bound 20) 3914 ⟨le_refl _, le_refl _⟩
  simpa [show (-(3914 : ℝ) / 2) = -(1957 : ℝ) by ring] using h

theorem exp_3914_poly_small :
    2 * (3914 : ℝ) ^ 6 * exp (-(3914 : ℝ)) ≤ (1 : ℝ) / 1000000 :=
  (show ∀ y ∈ Set.Icc (3914 : ℝ) 3914, 2 * y ^ 6 * exp (-y) ≤ (1 : ℝ) / 1000000 by
    interval_bound 20) 3914 ⟨le_refl _, le_refl _⟩

theorem exp_1169_small :
    exp (-(1.89 : ℝ) * sqrt ((1169 : ℝ) / 5.573412)) ≤ (1 : ℝ) / 10000000 :=
  (show ∀ z ∈ Set.Icc (1169 : ℝ) 1169,
      exp (-(1.89 : ℝ) * sqrt (z / 5.573412)) ≤ (1 : ℝ) / 10000000 by
    interval_bound 20) 1169 ⟨le_refl _, le_refl _⟩

theorem high_branch_aux {t c : ℝ}
    (ht : t ∈ Set.Icc (exp 1169) (exp 3870))
    (hc : c ≤ 462) :
    (log t) ^ 5 *
      (c * (log t / 5.573412) ^ (1.52 : ℝ) *
        exp (-(1.89 : ℝ) * sqrt (log t / 5.573412)))
      ≤ (100000000000000000000 : ℝ) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < exp 1169) ht.1
  have hlog_ge : (1169 : ℝ) ≤ log t := by
    have h := log_le_log (by positivity : (0 : ℝ) < exp 1169) ht.1
    simpa [log_exp] using h
  have hlog_le : log t ≤ (3870 : ℝ) := by
    have h := log_le_log htpos ht.2
    simpa [log_exp] using h
  have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
  have hratio_ge_one : (1 : ℝ) ≤ log t / 5.573412 := by
    have htmp : (5.573412 : ℝ) ≤ log t := by linarith [hlog_ge]
    exact (one_le_div (by positivity)).2 htmp
  have hratio_le : log t / 5.573412 ≤ (3870 : ℝ) / 5.573412 := by
    gcongr
  have hrpow_le_sq :
      (log t / 5.573412) ^ (1.52 : ℝ) ≤ (log t / 5.573412) ^ (2 : ℝ) := by
    exact rpow_le_rpow_of_exponent_le hratio_ge_one (by norm_num : (1.52 : ℝ) ≤ 2)
  have hratio_sq_le :
      (log t / 5.573412) ^ (2 : ℝ) ≤ ((3870 : ℝ) / 5.573412) ^ (2 : ℝ) := by
    exact rpow_le_rpow (by positivity) hratio_le (by positivity)
  have hexp_le :
      exp (-(1.89 : ℝ) * sqrt (log t / 5.573412)) ≤ (1 : ℝ) / 10000000 := by
    have : sqrt ((1169 : ℝ) / 5.573412) ≤ sqrt (log t / 5.573412) :=
      sqrt_le_sqrt (by gcongr)
    have : (-(1.89 : ℝ)) * sqrt (log t / 5.573412) ≤
        (-(1.89 : ℝ)) * sqrt ((1169 : ℝ) / 5.573412) := by nlinarith
    exact le_trans (by simpa [mul_comm, mul_left_comm, mul_assoc] using exp_le_exp.mpr this)
      exp_1169_small
  have hlog5_le : (log t) ^ 5 ≤ (3870 : ℝ) ^ 5 := pow_le_pow_left₀ hlog_nonneg hlog_le 5
  calc
    (log t) ^ 5 *
      (c * (log t / 5.573412) ^ (1.52 : ℝ) *
        exp (-(1.89 : ℝ) * sqrt (log t / 5.573412)))
      ≤ (log t) ^ 5 * (462 * (log t / 5.573412) ^ (2 : ℝ) * ((1 : ℝ) / 10000000)) := by
      gcongr
    _ ≤ (3870 : ℝ) ^ 5 * (462 * (((3870 : ℝ) / 5.573412) ^ (2 : ℝ)) * ((1 : ℝ) / 10000000)) := by
      gcongr
    _ ≤ (100000000000000000000 : ℝ) := by
      norm_num

theorem branch3_aux {t : ℝ} (ht : t ∈ Set.Ico (exp 58) (exp 1169)) :
    (log t) ^ 5 *
      (sqrt (8 / (17 * Real.pi)) * (log t / 6.455) ^ ((1 : ℝ) / 4) *
        exp (-sqrt (log t / 6.455)))
      ≤ (100000000000000000000 : ℝ) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < exp 58) ht.1
  have hlog_ge : (58 : ℝ) ≤ log t := by
    have h := log_le_log (by positivity : (0 : ℝ) < exp 58) ht.1
    simpa [log_exp] using h
  have hlog_le : log t ≤ (1169 : ℝ) := by
    have h := log_le_log htpos (le_of_lt ht.2)
    simpa [log_exp] using h
  have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
  have hsqrt_le_one : sqrt (8 / (17 * Real.pi)) ≤ (1 : ℝ) :=
    (sqrt_le_iff).2 ⟨by norm_num,
      (div_le_iff₀ (by positivity : (0 : ℝ) < 17 * Real.pi)).2
        (by simpa using show (8 : ℝ) ≤ 17 * Real.pi by nlinarith [Real.pi_gt_three])⟩
  have hbase_ge_one : (1 : ℝ) ≤ log t / 6.455 := by
    have : (6.455 : ℝ) ≤ log t := by linarith [hlog_ge]
    exact (one_le_div (by positivity)).2 this
  have hrpow_le_base :
      (log t / 6.455) ^ ((1 : ℝ) / 4) ≤ (log t / 6.455) ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one (by norm_num)
  have hrpow_le : (log t / 6.455) ^ ((1 : ℝ) / 4) ≤ log t / 6.455 := by
    simpa using hrpow_le_base
  have hexp_le_one : exp (-sqrt (log t / 6.455)) ≤ 1 := by
    have harg : -sqrt (log t / 6.455) ≤ 0 := by
      nlinarith [sqrt_nonneg (log t / 6.455)]
    exact exp_le_one_iff.mpr harg
  have hlog5_le : (log t) ^ 5 ≤ (1169 : ℝ) ^ 5 := by
    exact pow_le_pow_left₀ hlog_nonneg hlog_le 5
  have hratio_le : log t / 6.455 ≤ (1169 : ℝ) / 6.455 := by
    gcongr
  calc
    (log t) ^ 5 *
      (sqrt (8 / (17 * Real.pi)) * (log t / 6.455) ^ ((1 : ℝ) / 4) *
        exp (-sqrt (log t / 6.455)))
      ≤ (log t) ^ 5 * (1 * (log t / 6.455) * 1) := by
      gcongr
    _ ≤ (1169 : ℝ) ^ 5 * (1 * ((1169 : ℝ) / 6.455) * 1) := by
      gcongr
    _ ≤ (100000000000000000000 : ℝ) := by
      norm_num

lemma integral_Icc_split
    (f : ℝ → ℝ) {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hInt : IntegrableOn f (Set.Icc a c) volume) :
    ∫ t in Set.Icc a c, f t = (∫ t in Set.Icc a b, f t) + (∫ t in Set.Icc b c, f t) := by
  have h_int_left : IntegrableOn f (Set.Icc a b) volume :=
    hInt.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 hbc⟩)
  have h_int_right : IntegrableOn f (Set.Icc b c) volume :=
    hInt.mono_set (by intro t ht; exact ⟨le_trans hab ht.1, ht.2⟩)
  have h_int_left_u : IntegrableOn f (Set.uIcc a b) volume := by
    simpa [Set.uIcc_of_le hab] using h_int_left
  have h_int_right_u : IntegrableOn f (Set.uIcc b c) volume := by
    simpa [Set.uIcc_of_le hbc] using h_int_right
  have h_split_interval :
      ∫ t in a..c, f t = (∫ t in a..b, f t) + (∫ t in b..c, f t) := by
    exact (intervalIntegral.integral_add_adjacent_intervals
      (MeasureTheory.IntegrableOn.intervalIntegrable h_int_left_u)
      (MeasureTheory.IntegrableOn.intervalIntegrable h_int_right_u)).symm
  simpa [MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (le_trans hab hbc),
      intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_of_le hbc] using h_split_interval

theorem exp_neg44_small :
    exp (-(44 : ℝ)) ≤ (1 : ℝ) / 1000000000000000000 :=
  (show ∀ z ∈ Set.Icc (44 : ℝ) 44,
      exp (-z) ≤ (1 : ℝ) / 1000000000000000000 by interval_bound 20) 44 ⟨le_refl _, le_refl _⟩

theorem exp_neg1979_small :
    exp (-(1979 : ℝ))
      ≤ (1 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 :=
  (show ∀ z ∈ Set.Icc (1979 : ℝ) 1979, exp (-z)
      ≤ (1 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 by
    interval_bound 20) 1979 ⟨le_refl _, le_refl _⟩

theorem inv_log2_pow8_le_1000 : 1 / (log 2) ^ 8 ≤ (1000 : ℝ) := by
  have hhalf : (1 / 2 : ℝ) ≤ log 2 :=
    (show ∀ z ∈ Set.Icc (2 : ℝ) 2, (1 / 2 : ℝ) ≤ log z by interval_bound 20)
      2 ⟨le_refl _, le_refl _⟩
  calc 1 / (log 2) ^ 8
      ≤ 1 / (1 / 2 : ℝ) ^ 8 :=
        one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by norm_num) hhalf 8)
    _ ≤ (1000 : ℝ) := by norm_num

theorem low_contrib_le_three_tenths :
    (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
      (exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
        + 7 * (exp (-(1979 : ℝ)) / (log 2) ^ 8
          + (2 : ℝ) ^ 8 * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8))
      ≤ (3 : ℝ) / 10 := by
  have hAcoeff :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) / (3870 : ℝ) ^ 7 ≤
        (30000000000000000 : ℝ) := by
    norm_num
  have hCcoeff :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) / (3870 : ℝ) ^ 8
        ≤ (20000000000000000 : ℝ) := by
    norm_num
  have hBcoeff0 :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 ≤
        (30000000000000000000000000000000000000000000 : ℝ) := by
    norm_num
  have hA :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7 ≤
        (1 : ℝ) / 20 := by
    rw [show (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
        = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) / (3870 : ℝ) ^ 7) *
            exp (-(44 : ℝ)) by ring]
    exact le_trans (mul_le_mul hAcoeff exp_neg44_small (by positivity) (by positivity))
      (by norm_num)
  have hC :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
        (7 * (2 : ℝ) ^ 8) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8 ≤ (1 : ℝ) / 20 := by
    rw [show (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
          (7 * (2 : ℝ) ^ 8) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8
        = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) /
              (3870 : ℝ) ^ 8) * exp (-(44 : ℝ)) by ring]
    exact le_trans (mul_le_mul hCcoeff exp_neg44_small (by positivity) (by positivity))
      (by norm_num)
  have hB :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
        (exp (-(1979 : ℝ)) / (log 2) ^ 8) ≤ (1 : ℝ) / 20 := by
    have hBcoeff :
        (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (log 2) ^ 8
          ≤ (30000000000000000000000000000000000000000000 : ℝ) * 1000 := by
      rw [show (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (log 2) ^ 8
          = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7) * (1 / (log 2) ^ 8) by ring]
      exact le_trans (mul_le_mul_of_nonneg_left inv_log2_pow8_le_1000 (by positivity))
        (mul_le_mul_of_nonneg_right hBcoeff0 (by positivity))
    rw [show (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
          (exp (-(1979 : ℝ)) / (log 2) ^ 8)
        = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (log 2) ^ 8) *
            exp (-(1979 : ℝ)) by ring]
    exact le_trans (mul_le_mul hBcoeff exp_neg1979_small (by positivity) (by positivity))
      (by norm_num)
  have hrewrite_main :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
        (exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
          + 7 * (exp (-(1979 : ℝ)) / (log 2) ^ 8
            + (2 : ℝ) ^ 8 * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8))
      = (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
        + (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
            (exp (-(1979 : ℝ)) / (log 2) ^ 8)
        + (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8 := by
    ring
  rw [hrewrite_main]
  nlinarith [hA, hB, hC]

theorem sqrt_exp_3870 : sqrt (exp (3870 : ℝ)) = exp (1935 : ℝ) := by
  rw [show (3870 : ℝ) = 1935 + 1935 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (1935 : ℝ) by positivity)]

theorem low_contrib_raw_le_three_tenths :
    (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
      ((100000000000000000720 : ℝ) *
        (exp (3870 : ℝ) / (3870 : ℝ) ^ 7
          + 7 *
            (sqrt (exp (3870 : ℝ)) / (log 2) ^ 8
              + (2 : ℝ) ^ 8 * exp (3870 : ℝ) / (3870 : ℝ) ^ 8)))
      ≤ (3 : ℝ) / 10 := by
  have h44 : exp (3870 : ℝ) / exp (3914 : ℝ) = exp (-(44 : ℝ)) := by
    have h := (exp_sub (3870 : ℝ) (3914 : ℝ)).symm
    simpa [show (3870 : ℝ) - 3914 = (-(44 : ℝ)) by norm_num] using h
  have h1979 : exp (1935 : ℝ) / exp (3914 : ℝ) = exp (-(1979 : ℝ)) := by
    have h := (exp_sub (1935 : ℝ) (3914 : ℝ)).symm
    simpa [show (1935 : ℝ) - 3914 = (-(1979 : ℝ)) by norm_num] using h
  rw [sqrt_exp_3870]
  have hrewrite :
      (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
          ((100000000000000000720 : ℝ) *
            (exp (3870 : ℝ) / (3870 : ℝ) ^ 7
              + 7 *
                (exp (1935 : ℝ) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp (3870 : ℝ) / (3870 : ℝ) ^ 8)))
        = (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
            (exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
              + 7 * (exp (-(1979 : ℝ)) / (log 2) ^ 8
                + (2 : ℝ) ^ 8 * exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8)) := by
    rw [← h44, ← h1979]
    field_simp
  rw [hrewrite]
  exact low_contrib_le_three_tenths

theorem exp_23_gt_4e9 : (4000000000 : ℝ) < exp (23 : ℝ) :=
  (show ∀ y ∈ Set.Icc (23 : ℝ) 23, (4000000000 : ℝ) < exp y by interval_bound 20)
    23 ⟨le_refl _, le_refl _⟩

theorem exp_8_lt_3914 : exp (8 : ℝ) < (3914 : ℝ) :=
  (show ∀ y ∈ Set.Icc (8 : ℝ) 8, exp y < (3914 : ℝ) by interval_bound 20)
    8 ⟨le_refl _, le_refl _⟩

namespace Calculations

theorem a_exp_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_3000 :
      ∀ {z : ℝ}, z ≥ exp 3000 →
        a z = admissible_bound (379.7 * 5.573412 ^ 5) 6.52 1.89 5.573412 z)
    {L C : ℝ}
    (hL : 3000 ≤ L)
    (hpow5 : (5.573412 : ℝ) ^ (5 : ℕ) * ((L / 5.573412) ^ (5 : ℕ)) = L ^ (5 : ℕ))
    (haux : ∀ y ∈ Set.Icc L L, styleVal y ≤ C) :
    a (exp L) ≤ C := by
  have hLpos : 0 < L := by linarith
  rw [ha_eq_admissible_ge_3000 (z := exp L) (exp_le_exp.mpr hL)]
  unfold admissible_bound
  rw [log_exp, rpow_652_split (by positivity : 0 < L / 5.573412),
    sqrt_ratio_5573412 (y := L) hLpos.le]
  let A : ℝ := (L / 5.573412) ^ (1.52 : ℝ)
  let E : ℝ := exp (-(1.89 : ℝ) * (sqrt L / sqrt (5.573412 : ℝ)))
  have hrewrite :
      (379.7 * 5.573412 ^ 5) * ((L / 5.573412) ^ 5 * A) * E
      = L ^ 5 * ((379.7 : ℝ) * A * E) := by
    calc
      (379.7 * 5.573412 ^ 5) * ((L / 5.573412) ^ 5 * A) * E
          = (5.573412 ^ 5 * (L / 5.573412) ^ 5) * ((379.7 : ℝ) * A * E) := by
              ring
      _ = L ^ 5 * ((379.7 : ℝ) * A * E) := by rw [hpow5]
  rw [hrewrite, style_eq L hLpos]
  exact haux L ⟨le_rfl, le_rfl⟩

theorem sqrt_exp_3914 : sqrt (exp (3914 : ℝ)) = exp (1957 : ℝ) := by
  rw [show (3914 : ℝ) = 1957 + 1957 by norm_num, exp_add, sqrt_mul (by positivity)]
  nlinarith [Real.sq_sqrt (show 0 ≤ exp (1957 : ℝ) by positivity)]

theorem B_le_small_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (3914 : ℝ))
    (hlogxₐ : log xₐ = (3914 : ℝ)) :
    1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2
      + 7 * log xₐ ^ 6 / (sqrt xₐ * (log 2) ^ 8)
      ≤ (3 : ℝ) / 8000 := by
  rw [hlogxₐ]
  rw [hxₐ, sqrt_exp_3914]
  have htail : 7 * (3914 : ℝ) ^ 6 / (exp (1957 : ℝ) * (log 2) ^ 8) ≤ (1 : ℝ) / 1000000 := by
    rw [show 7 * (3914 : ℝ) ^ 6 / (exp (1957 : ℝ) * (log 2) ^ 8) =
      7 * (3914 : ℝ) ^ 6 * exp (-(1957 : ℝ)) / (log 2) ^ 8 by
      field_simp [(show (0 : ℝ) < exp (1957 : ℝ) by positivity).ne']
      rw [show (1 : ℝ) = exp (1957 : ℝ) * exp (-(1957 : ℝ)) by rw [← exp_add]; norm_num]]
    exact tail_small
  linarith [htail, show (1 / (3914 : ℝ) + 7 * 2 ^ 8 / (3914 : ℝ) ^ 2 +
    (1 : ℝ) / 1000000) ≤ (3 : ℝ) / 8000 by norm_num]

theorem C3_le_one_of
    {xₐ : ℝ}
    (hxₐ : xₐ = exp (3914 : ℝ))
    (hlogxₐ : log xₐ = (3914 : ℝ)) :
    2 * log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, (k.factorial : ℝ) / log 2 ^ (k + 1)
      ≤ (1 : ℝ) := by
  rw [hlogxₐ, hxₐ]
  simp only [Nat.reduceAdd, Nat.one_le_ofNat, Finset.sum_Icc_succ_top, Finset.Icc_self,
    Finset.sum_singleton, Nat.factorial, Nat.succ_eq_add_one, zero_add, mul_one, Nat.cast_one,
    one_div, Nat.cast_ofNat, Nat.reduceMul]
  have hA : 2 * (3914 : ℝ) ^ 6 * exp (-(3914 : ℝ)) ≤ (1 : ℝ) / 1000000 := exp_3914_poly_small
  let u : ℝ := (log 2)⁻¹
  have hu_le : u ≤ (2 : ℝ) := by
    dsimp [u]
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    simpa [one_div] using h
  have hB :
      ((log 2 ^ 2)⁻¹ + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5 + 120 / log 2 ^ 6) ≤ (9000 : ℝ) := by
    rw [show ((log 2 ^ 2)⁻¹ + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5 + 120 / log 2 ^ 6)
        = u ^ 2 + 2 * u ^ 3 + 6 * u ^ 4 + 24 * u ^ 5 + 120 * u ^ 6 by dsimp [u]; ring_nf]
    exact le_trans (show u ^ 2 + 2 * u ^ 3 + 6 * u ^ 4 + 24 * u ^ 5 + 120 * u ^ 6
        ≤ 2 ^ 2 + 2 * 2 ^ 3 + 6 * 2 ^ 4 + 24 * 2 ^ 5 + 120 * 2 ^ 6 by gcongr) (by norm_num)
  rw [show 2 * (3914 : ℝ) ^ 6 / exp (3914 : ℝ)
      = 2 * (3914 : ℝ) ^ 6 * exp (-(3914 : ℝ)) by
    field_simp; rw [show (1 : ℝ) = exp (3914 : ℝ) * exp (-(3914 : ℝ)) by rw [← exp_add]; norm_num]]
  exact le_trans (mul_le_mul hA hB (by positivity) (by positivity)) (by norm_num)

theorem C1_le_one_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = exp (3914 : ℝ))
    (h2xa : 2 ≤ xₐ)
    (h3870le : exp 3870 ≤ xₐ)
    (ha_int : IntegrableOn (fun t ↦ a t / log t ^ 7) (Set.Icc 2 xₐ) volume)
    (ha_le_low_huge : ∀ t ∈ Set.Icc 2 (exp 3870), a t ≤ (100000000000000000000 : ℝ))
    (ha_mono_3000 : AntitoneOn a (Set.Ici (exp 3000)))
    (ha_3870_upper : a (exp 3870) ≤ (1800 : ℝ))
    (hJ3870 :
      ∫ t in Set.Icc 2 (exp 3870), 1 / log t ^ 7
        ≤ exp 3870 / log (exp 3870) ^ 7
          + 7 * (sqrt (exp 3870) / log 2 ^ 8
            + 2 ^ 8 * exp 3870 / log (exp 3870) ^ 8)) :
    log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7 ≤ (1 : ℝ) := by
  let K : ℝ := (100000000000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / log t ^ 7 + a t / log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hsplit :
      ∫ t in Set.Icc 2 xₐ, f t
        = (∫ t in Set.Icc 2 (exp 3870), f t)
          + (∫ t in Set.Icc (exp 3870) xₐ, f t) :=
    integral_Icc_split (f := f) (a := 2) (b := exp 3870) (c := xₐ)
      (by linarith [add_one_le_exp (3870 : ℝ)]) h3870le hf_int

  have hf_int_low : IntegrableOn f (Set.Icc 2 (exp 3870)) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 h3870le⟩)
  have hlow_rhs_int : IntegrableOn (fun t : ℝ ↦ K / log t ^ 7) (Set.Icc 2 (exp 3870)) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ K * (1 / log t ^ 7)) (Set.Icc 2 (exp 3870)) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
        intro t ht
        exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))).const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 (exp 3870), f t ≤ K / log t ^ 7 := by
    intro t ht
    have ha_le : a t ≤ (100000000000000000000 : ℝ) := ha_le_low_huge t ht
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ log t := log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 (exp 3870), f t
        ≤ ∫ t in Set.Icc 2 (exp 3870), K / log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_low hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 (exp 3870), K / log t ^ 7
        = K * ∫ t in Set.Icc 2 (exp 3870), 1 / log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 (exp 3870), f t
        ≤ K * (exp 3870 / log (exp 3870) ^ 7
          + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / log (exp 3870) ^ 8)) := by
    rw [hlow_factor] at hlow_le_rhs
    exact le_trans hlow_le_rhs (mul_le_mul_of_nonneg_left hJ3870 hK_nonneg)

  have hf_int_high : IntegrableOn f (Set.Icc (exp 3870) xₐ) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨le_trans (by linarith [add_one_le_exp (3870 : ℝ)]) ht.1, ht.2⟩)
  have hconst_high_int : IntegrableOn (fun _ : ℝ ↦ (2520 : ℝ) / (3870 : ℝ) ^ 7) (Set.Icc (exp 3870) xₐ) volume :=
    ContinuousOn.integrableOn_Icc continuousOn_const
  have hhigh_pt : ∀ t ∈ Set.Icc (exp 3870) xₐ, f t ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 := by
    intro t ht
    have ht3000 : exp 3000 ≤ t :=
      le_trans (exp_le_exp.mpr (by norm_num : (3000 : ℝ) ≤ 3870)) ht.1
    have hat3870 : a t ≤ a (exp 3870) :=
      ha_mono_3000
        (Set.mem_Ici.mpr (exp_le_exp.mpr (by norm_num : (3000 : ℝ) ≤ 3870)))
        (Set.mem_Ici.mpr ht3000) ht.1
    have hat : a t ≤ 1800 := le_trans hat3870 ha_3870_upper
    have hnum_le : 720 + a t ≤ 2520 := by linarith
    have hlog_ge : (3870 : ℝ) ≤ log t := by
      have h := log_le_log (by positivity : (0 : ℝ) < exp 3870) ht.1
      simpa [log_exp] using h
    have hpow : (3870 : ℝ) ^ 7 ≤ log t ^ 7 := pow_le_pow_left₀ (by norm_num) hlog_ge 7
    have hlog_nonneg : 0 ≤ log t := by linarith [hlog_ge]
    calc
      f t = (720 + a t) / log t ^ 7 := rfl
      _ ≤ (2520 : ℝ) / log t ^ 7 := by
        exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
      _ ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 := by
        exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2520 : ℝ)) (by positivity) hpow
  have hhigh_le_const :
      ∫ t in Set.Icc (exp 3870) xₐ, f t
        ≤ ∫ t in Set.Icc (exp 3870) xₐ, (2520 : ℝ) / (3870 : ℝ) ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_high hconst_high_int measurableSet_Icc hhigh_pt
  have hhigh_const_eval :
      ∫ t in Set.Icc (exp 3870) xₐ, (2520 : ℝ) / (3870 : ℝ) ^ 7
        = (2520 : ℝ) / (3870 : ℝ) ^ 7 * (xₐ - exp 3870) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h3870le,
      intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  have hhigh_le :
      ∫ t in Set.Icc (exp 3870) xₐ, f t
        ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 * xₐ :=
    le_trans (by simpa [hhigh_const_eval] using hhigh_le_const)
      (mul_le_mul_of_nonneg_left (by linarith [show (0 : ℝ) ≤ exp 3870 by positivity])
        (by positivity))

  have hmain :
      log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (exp 3870), f t) + (∫ t in Set.Icc (exp 3870) xₐ, f t))
        ≤ log xₐ ^ 6 / xₐ *
            (K * (exp 3870 / log (exp 3870) ^ 7
              + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / log (exp 3870) ^ 8))
              + (2520 : ℝ) / (3870 : ℝ) ^ 7 * xₐ) :=
    mul_le_mul_of_nonneg_left (by linarith [hlow_le, hhigh_le]) (by positivity)
  have hmain' :
      (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
          ((∫ t in Set.Icc 2 (exp 3870), f t) + (∫ t in Set.Icc (exp 3870) (exp (3914 : ℝ)), f t))
        ≤ (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
          (K * (exp 3870 / (3870 : ℝ) ^ 7
            + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / (3870 : ℝ) ^ 8))
            + (2520 : ℝ) / (3870 : ℝ) ^ 7 * exp (3914 : ℝ)) := by
    simpa [hxₐ, log_exp] using hmain
  have hdecomp :
      (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
          (K * (exp 3870 / (3870 : ℝ) ^ 7
            + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / (3870 : ℝ) ^ 8))
            + (2520 : ℝ) / (3870 : ℝ) ^ 7 * exp (3914 : ℝ))
        = (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
            (K * (exp 3870 / (3870 : ℝ) ^ 7
              + 7 * (sqrt (exp 3870) / log 2 ^ 8 + 2 ^ 8 * exp 3870 / (3870 : ℝ) ^ 8)))
          + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 := by
    field_simp
  rw [hdecomp] at hmain'; dsimp [K] at hmain'
  have hfin :
      (3914 : ℝ) ^ 6 / exp (3914 : ℝ) *
          ((100000000000000000720 : ℝ) *
            (exp 3870 / (3870 : ℝ) ^ 7
              + 7 *
                (sqrt (exp 3870) / (log 2) ^ 8
                  + (2 : ℝ) ^ 8 * exp 3870 / (3870 : ℝ) ^ 8)))
          + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 ≤ 1 := by
    nlinarith [low_contrib_raw_le_three_tenths,
      show (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 ≤ (7 : ℝ) / 10 by norm_num]
  exact le_trans (by rw [hsplit]; simpa [f, hxₐ, log_exp] using hmain') hfin

theorem m_upper_from_bounds
    {a_xa C1 C2 C3 B : ℝ}
    (hax0 : 0 ≤ a_xa) (hC3 : 0 ≤ C3) (hB0 : 0 ≤ B)
    (hC2abs : |C2| ≤ C1) (hC1 : C1 ≤ (1 : ℝ)) :
    120 - a_xa - (C2 + C3) - a_xa * B ≤ (121 : ℝ) := by
  have : -(C2 + C3) ≤ |C2| :=
    le_trans (by linarith : -(C2 + C3) ≤ -C2) (by nlinarith [neg_abs_le C2])
  nlinarith [hax0, hC3, hB0, hC2abs, hC1]

theorem M_nonneg_from_bounds
    {a_xa a_exa C1 B : ℝ}
    (hax0 : 0 ≤ a_xa)
    (haex0 : 0 ≤ a_exa)
    (hC10 : 0 ≤ C1)
    (hB0 : 0 ≤ B) :
    0 ≤ 120 + a_exa + C1 + (720 + a_xa) * B := by
  nlinarith [hax0, haex0, hC10, hB0]

theorem M_upper_from_bounds
    {a_xa a_exa C1 B : ℝ}
    (hax0 : 0 ≤ a_xa) (hC1 : C1 ≤ (1 : ℝ))
    (hax : a_xa ≤ (1311 : ℝ)) (haex : a_exa ≤ (13042 / 10 : ℝ))
    (hB : B ≤ (3 : ℝ) / 8000) :
    120 + a_exa + C1 + (720 + a_xa) * B ≤ (1426 : ℝ) := by
  have : (720 + a_xa) * B ≤ (2031 : ℝ) * ((3 : ℝ) / 8000) :=
    le_trans (mul_le_mul_of_nonneg_left hB (by linarith))
      (mul_le_mul_of_nonneg_right (by linarith) (by positivity))
  nlinarith [hC1, haex]

theorem m_lower_from_bounds
    {a_xa C1 C2 C3 B : ℝ}
    (hax0 : 0 ≤ a_xa) (hax : a_xa ≤ (1311 : ℝ))
    (hC1 : C1 ≤ (1 : ℝ)) (hC2abs : |C2| ≤ C1)
    (hC3 : C3 ≤ (1 : ℝ)) (hB : B ≤ (3 : ℝ) / 8000) :
    (-1194 : ℝ) ≤ 120 - a_xa - (C2 + C3) - a_xa * B := by
  have hC2le : C2 ≤ (1 : ℝ) := (abs_le.mp (le_trans hC2abs hC1)).2
  have : a_xa * B ≤ (1311 : ℝ) * ((3 : ℝ) / 8000) :=
    le_trans (mul_le_mul_of_nonneg_left hB hax0)
      (mul_le_mul_of_nonneg_right hax (by positivity))
  nlinarith

end Calculations

end Ramanujan
