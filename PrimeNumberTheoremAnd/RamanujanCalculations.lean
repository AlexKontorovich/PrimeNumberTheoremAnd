import PrimeNumberTheoremAnd.Defs
import LeanCert.Tactic.IntervalAuto

namespace Ramanujan

open Real Set MeasureTheory intervalIntegral

noncomputable def styleVal (y : ℝ) : ℝ :=
  y * (y * (y * (y * y))) *
    ((3797 / 10 : ℝ) *
      Real.exp (Real.log (y * (250000 / 1393353 : ℝ)) * (38 / 25 : ℝ)) *
      Real.exp ((-189 / 100 : ℝ) * Real.sqrt (y * (250000 / 1393353 : ℝ))))

theorem styleVal_bound {L C : ℝ}
    (haux :
      ∀ y ∈ Set.Icc L L,
        y * (y * (y * (y * y))) *
            ((3797 / 10 : ℝ) *
              Real.exp (Real.log (y * (250000 / 1393353 : ℝ)) * (38 / 25 : ℝ)) *
              Real.exp ((-189 / 100 : ℝ) * Real.sqrt (y * (250000 / 1393353 : ℝ)))) ≤
          C) :
    ∀ y ∈ Set.Icc L L, styleVal y ≤ C := by
  intro y hy
  simpa [styleVal] using haux y hy

theorem style_eq (y : ℝ) (hy : 0 < y) :
    y ^ 5 * ((379.7 : ℝ) * (y / 5.573412) ^ (1.52 : ℝ) *
      Real.exp (-(1.89 : ℝ) * (Real.sqrt y / Real.sqrt (5.573412 : ℝ))))
    =
    styleVal y := by
  have hpow5 : y ^ 5 = y * (y * (y * (y * y))) := by ring
  rw [hpow5]
  have hconst1 : (379.7 : ℝ) = (3797 / 10 : ℝ) := by norm_num
  rw [hconst1]
  have hconst2 : (5.573412 : ℝ) = (1393353 / 250000 : ℝ) := by norm_num
  rw [hconst2]
  have hdiv : y / (1393353 / 250000 : ℝ) = y * (250000 / 1393353 : ℝ) := by
    field_simp
  rw [hdiv]
  have hposbase : 0 < y * (250000 / 1393353 : ℝ) := by positivity
  have hrpow : (y * (250000 / 1393353 : ℝ)) ^ (1.52 : ℝ) =
      Real.exp (Real.log (y * (250000 / 1393353 : ℝ)) * (38 / 25 : ℝ)) := by
    rw [Real.rpow_def_of_pos hposbase]
    congr 1
    norm_num
  rw [hrpow]
  have hsqrt :
      Real.sqrt y / Real.sqrt (1393353 / 250000 : ℝ) =
        Real.sqrt (y * (250000 / 1393353 : ℝ)) := by
    have hs :
        Real.sqrt (y / (1393353 / 250000 : ℝ)) =
          Real.sqrt y / Real.sqrt (1393353 / 250000 : ℝ) := by
      rw [Real.sqrt_div (le_of_lt hy)]
    rw [← hs, hdiv]
  rw [hsqrt]
  have hconst3 : (1.89 : ℝ) = (189 / 100 : ℝ) := by norm_num
  rw [hconst3]
  have hneg :
      (-(189 / 100 : ℝ)) * Real.sqrt (y * (250000 / 1393353 : ℝ))
        = (-189 / 100 : ℝ) * Real.sqrt (y * (250000 / 1393353 : ℝ)) := by
    ring
  rw [hneg]
  simp only [styleVal]

lemma rpow_652_split {y : ℝ} (hy : 0 < y) :
    y ^ (6.52 : ℝ) = y ^ (5 : ℕ) * y ^ (1.52 : ℝ) := by
  have hdecomp : (6.52 : ℝ) = (5 : ℝ) + (1.52 : ℝ) := by
    norm_num
  rw [hdecomp]
  calc
    y ^ ((5 : ℝ) + (1.52 : ℝ)) = y ^ (5 : ℝ) * y ^ (1.52 : ℝ) := by
      simpa using (Real.rpow_add hy (5 : ℝ) (1.52 : ℝ))
    _ = y ^ (5 : ℕ) * y ^ (1.52 : ℝ) := by
      simp

lemma sqrt_ratio_5573412 {y : ℝ} (hy : 0 ≤ y) :
    (y / 5.573412) ^ ((1 : ℝ) / 2) = Real.sqrt y / Real.sqrt (5.573412 : ℝ) := by
  rw [show ((1 : ℝ) / 2) = (1 / 2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  rw [Real.sqrt_div hy]

theorem not_mem_Ico_of_ge_exp3000
    {z lo hi : ℝ}
    (hz : z ≥ exp 3000)
    (hhi : hi ≤ exp 3000) :
    ¬ z ∈ Set.Ico lo hi := by
  intro hzmem
  exact (not_lt_of_ge (le_trans hhi hz)) hzmem.2

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
    7 * (3914 : ℝ) ^ 6 * Real.exp (-(1957 : ℝ)) / (Real.log 2) ^ 8 ≤ (1 : ℝ) / 1000000 := by
  have haux : ∀ y ∈ Set.Icc (3914 : ℝ) 3914,
      7 * y ^ 6 * Real.exp (-y / 2) / (Real.log 2) ^ 8 ≤ (1 : ℝ) / 1000000 := by
    interval_bound 20
  have h := haux 3914 (by constructor <;> norm_num)
  have hy : (-(3914 : ℝ) / 2) = (-(1957 : ℝ)) := by ring
  simpa [hy] using h

theorem exp_3914_poly_small :
    2 * (3914 : ℝ) ^ 6 * Real.exp (-(3914 : ℝ)) ≤ (1 : ℝ) / 1000000 := by
  have haux : ∀ y ∈ Set.Icc (3914 : ℝ) 3914,
      2 * y ^ 6 * Real.exp (-y) ≤ (1 : ℝ) / 1000000 := by
    interval_bound 20
  exact haux 3914 (by constructor <;> norm_num)

theorem exp_1169_small :
    Real.exp (-(1.89 : ℝ) * Real.sqrt ((1169 : ℝ) / 5.573412)) ≤ (1 : ℝ) / 10000000 := by
  have haux : ∀ z ∈ Set.Icc (1169 : ℝ) 1169,
      Real.exp (-(1.89 : ℝ) * Real.sqrt (z / 5.573412)) ≤ (1 : ℝ) / 10000000 := by
    interval_bound 20
  exact haux 1169 (by constructor <;> norm_num)

theorem high_branch_aux {t c : ℝ}
    (ht : t ∈ Set.Icc (Real.exp 1169) (Real.exp 3870))
    (hc : c ≤ 462) :
    (Real.log t) ^ 5 *
      (c * (Real.log t / 5.573412) ^ (1.52 : ℝ) *
        Real.exp (-(1.89 : ℝ) * Real.sqrt (Real.log t / 5.573412)))
      ≤ (100000000000000000000 : ℝ) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.exp 1169) ht.1
  have hlog_ge : (1169 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp 1169) ht.1
    simpa [Real.log_exp] using h
  have hlog_le : Real.log t ≤ (3870 : ℝ) := by
    have h := Real.log_le_log htpos ht.2
    simpa [Real.log_exp] using h
  have hlog_nonneg : 0 ≤ Real.log t := by linarith [hlog_ge]
  have hratio_ge_one : (1 : ℝ) ≤ Real.log t / 5.573412 := by
    have htmp : (5.573412 : ℝ) ≤ Real.log t := by linarith [hlog_ge]
    exact (one_le_div (by positivity)).2 htmp
  have hratio_le : Real.log t / 5.573412 ≤ (3870 : ℝ) / 5.573412 := by
    gcongr
  have hrpow_le_sq :
      (Real.log t / 5.573412) ^ (1.52 : ℝ) ≤ (Real.log t / 5.573412) ^ (2 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hratio_ge_one (by norm_num : (1.52 : ℝ) ≤ 2)
  have hratio_sq_le :
      (Real.log t / 5.573412) ^ (2 : ℝ) ≤ ((3870 : ℝ) / 5.573412) ^ (2 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hratio_le (by positivity)
  have hexp_le_1169 :
      Real.exp (-(1.89 : ℝ) * Real.sqrt (Real.log t / 5.573412)) ≤
        Real.exp (-(1.89 : ℝ) * Real.sqrt ((1169 : ℝ) / 5.573412)) := by
    have hsqrt_le :
        Real.sqrt ((1169 : ℝ) / 5.573412) ≤ Real.sqrt (Real.log t / 5.573412) := by
      apply Real.sqrt_le_sqrt
      have : (1169 : ℝ) / 5.573412 ≤ Real.log t / 5.573412 := by gcongr
      exact this
    have hneg_mul :
        (-(1.89 : ℝ)) * Real.sqrt (Real.log t / 5.573412) ≤
          (-(1.89 : ℝ)) * Real.sqrt ((1169 : ℝ) / 5.573412) := by
      nlinarith
    simpa [mul_comm, mul_left_comm, mul_assoc] using Real.exp_le_exp.mpr hneg_mul
  have hexp_le :
      Real.exp (-(1.89 : ℝ) * Real.sqrt (Real.log t / 5.573412)) ≤ (1 : ℝ) / 10000000 :=
    le_trans hexp_le_1169 exp_1169_small
  have hlog5_le : (Real.log t) ^ 5 ≤ (3870 : ℝ) ^ 5 := by
    exact pow_le_pow_left₀ hlog_nonneg hlog_le 5
  calc
    (Real.log t) ^ 5 *
      (c * (Real.log t / 5.573412) ^ (1.52 : ℝ) *
        Real.exp (-(1.89 : ℝ) * Real.sqrt (Real.log t / 5.573412)))
      ≤ (Real.log t) ^ 5 * (462 * (Real.log t / 5.573412) ^ (2 : ℝ) * ((1 : ℝ) / 10000000)) := by
      gcongr
    _ ≤ (3870 : ℝ) ^ 5 * (462 * (((3870 : ℝ) / 5.573412) ^ (2 : ℝ)) * ((1 : ℝ) / 10000000)) := by
      gcongr
    _ ≤ (100000000000000000000 : ℝ) := by
      norm_num

theorem branch3_aux {t : ℝ} (ht : t ∈ Set.Ico (Real.exp 58) (Real.exp 1169)) :
    (Real.log t) ^ 5 *
      (Real.sqrt (8 / (17 * Real.pi)) * (Real.log t / 6.455) ^ ((1 : ℝ) / 4) *
        Real.exp (-Real.sqrt (Real.log t / 6.455)))
      ≤ (100000000000000000000 : ℝ) := by
  have htpos : 0 < t := lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.exp 58) ht.1
  have hlog_ge : (58 : ℝ) ≤ Real.log t := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp 58) ht.1
    simpa [Real.log_exp] using h
  have hlog_le : Real.log t ≤ (1169 : ℝ) := by
    have h := Real.log_le_log htpos (le_of_lt ht.2)
    simpa [Real.log_exp] using h
  have hlog_nonneg : 0 ≤ Real.log t := by linarith [hlog_ge]
  have hsqrt_le_one : Real.sqrt (8 / (17 * Real.pi)) ≤ (1 : ℝ) := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · have hden : (8 : ℝ) ≤ 17 * Real.pi := by nlinarith [Real.pi_gt_three]
      have hden_pos : 0 < 17 * Real.pi := by positivity
      have hmul : (8 : ℝ) ≤ (1 : ℝ) ^ 2 * (17 * Real.pi) := by simpa using hden
      exact (div_le_iff₀ hden_pos).2 hmul
  have hbase_ge_one : (1 : ℝ) ≤ Real.log t / 6.455 := by
    have : (6.455 : ℝ) ≤ Real.log t := by linarith [hlog_ge]
    exact (one_le_div (by positivity)).2 this
  have hrpow_le_base :
      (Real.log t / 6.455) ^ ((1 : ℝ) / 4) ≤ (Real.log t / 6.455) ^ (1 : ℝ) := by
    exact Real.rpow_le_rpow_of_exponent_le hbase_ge_one (by norm_num)
  have hrpow_le : (Real.log t / 6.455) ^ ((1 : ℝ) / 4) ≤ Real.log t / 6.455 := by
    simpa using hrpow_le_base
  have hexp_le_one : Real.exp (-Real.sqrt (Real.log t / 6.455)) ≤ 1 := by
    have harg : -Real.sqrt (Real.log t / 6.455) ≤ 0 := by
      nlinarith [Real.sqrt_nonneg (Real.log t / 6.455)]
    exact Real.exp_le_one_iff.mpr harg
  have hlog5_le : (Real.log t) ^ 5 ≤ (1169 : ℝ) ^ 5 := by
    exact pow_le_pow_left₀ hlog_nonneg hlog_le 5
  have hratio_le : Real.log t / 6.455 ≤ (1169 : ℝ) / 6.455 := by
    gcongr
  calc
    (Real.log t) ^ 5 *
      (Real.sqrt (8 / (17 * Real.pi)) * (Real.log t / 6.455) ^ ((1 : ℝ) / 4) *
        Real.exp (-Real.sqrt (Real.log t / 6.455)))
      ≤ (Real.log t) ^ 5 * (1 * (Real.log t / 6.455) * 1) := by
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
    Real.exp (-(44 : ℝ)) ≤ (1 : ℝ) / 1000000000000000000 := by
  have haux : ∀ z ∈ Set.Icc (44 : ℝ) 44,
      Real.exp (-z) ≤ (1 : ℝ) / 1000000000000000000 := by
    interval_bound 20
  exact haux 44 (by constructor <;> norm_num)

theorem exp_neg1979_small :
    Real.exp (-(1979 : ℝ))
      ≤ (1 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
  have haux : ∀ z ∈ Set.Icc (1979 : ℝ) 1979,
      Real.exp (-z)
        ≤ (1 : ℝ) / 100000000000000000000000000000000000000000000000000000000000000000000000000000000 := by
    interval_bound 20
  exact haux 1979 (by constructor <;> norm_num)

theorem inv_log2_pow8_le_1000 : 1 / (Real.log 2) ^ 8 ≤ (1000 : ℝ) := by
  have hhalf_aux : ∀ z ∈ Set.Icc (2 : ℝ) 2, (1 / 2 : ℝ) ≤ Real.log z := by
    interval_bound 20
  have hhalf : (1 / 2 : ℝ) ≤ Real.log 2 := hhalf_aux 2 (by constructor <;> norm_num)
  have hpow : (1 / 2 : ℝ) ^ 8 ≤ (Real.log 2) ^ 8 :=
    pow_le_pow_left₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) hhalf 8
  have hdiv : 1 / (Real.log 2) ^ 8 ≤ 1 / (1 / 2 : ℝ) ^ 8 :=
    one_div_le_one_div_of_le (by positivity : 0 < (1 / 2 : ℝ) ^ 8) hpow
  have hnum : (1 / (1 / 2 : ℝ) ^ 8) ≤ (1000 : ℝ) := by norm_num
  exact le_trans hdiv hnum

theorem low_contrib_le_three_tenths :
    (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
      (Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
        + 7 * (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8
          + (2 : ℝ) ^ 8 * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8))
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
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7 ≤
        (1 : ℝ) / 20 := by
    have hnum :
        (30000000000000000 : ℝ) * ((1 : ℝ) / 1000000000000000000) ≤ (1 : ℝ) / 20 := by
      norm_num
    have htmp1 :
        (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
          = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) / (3870 : ℝ) ^ 7) *
              Real.exp (-(44 : ℝ)) := by
      ring
    rw [htmp1]
    have hstep :
        ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) / (3870 : ℝ) ^ 7) *
            Real.exp (-(44 : ℝ))
          ≤ (30000000000000000 : ℝ) * ((1 : ℝ) / 1000000000000000000) := by
      exact mul_le_mul hAcoeff exp_neg44_small (by positivity) (by positivity)
    exact le_trans hstep hnum
  have hC :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
        (7 * (2 : ℝ) ^ 8) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8 ≤ (1 : ℝ) / 20 := by
    have hnum :
        (20000000000000000 : ℝ) * ((1 : ℝ) / 1000000000000000000) ≤ (1 : ℝ) / 20 := by
      norm_num
    have htmp1 :
        (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8
          = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) /
                (3870 : ℝ) ^ 8) * Real.exp (-(44 : ℝ)) := by
      ring
    rw [htmp1]
    have hstep :
        ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * (7 * (2 : ℝ) ^ 8) / (3870 : ℝ) ^ 8) *
            Real.exp (-(44 : ℝ))
          ≤ (20000000000000000 : ℝ) * ((1 : ℝ) / 1000000000000000000) := by
      exact mul_le_mul hCcoeff exp_neg44_small (by positivity) (by positivity)
    exact le_trans hstep hnum
  have hB :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
        (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8) ≤ (1 : ℝ) / 20 := by
    have hBcoeff :
        (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (Real.log 2) ^ 8
          ≤ (30000000000000000000000000000000000000000000 : ℝ) * 1000 := by
      have hrewrite :
          (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (Real.log 2) ^ 8
            = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7) * (1 / (Real.log 2) ^ 8) := by
        ring
      rw [hrewrite]
      have hstep1 :
          ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7) * (1 / (Real.log 2) ^ 8)
            ≤ ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7) * 1000 := by
        exact mul_le_mul_of_nonneg_left inv_log2_pow8_le_1000 (by positivity)
      have hstep2 :
          ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7) * 1000
            ≤ (30000000000000000000000000000000000000000000 : ℝ) * 1000 := by
        exact mul_le_mul_of_nonneg_right hBcoeff0 (by positivity)
      exact le_trans hstep1 hstep2
    have hnum :
        ((30000000000000000000000000000000000000000000 : ℝ) * 1000) *
            ((1 : ℝ) /
              100000000000000000000000000000000000000000000000000000000000000000000000000000000)
          ≤ (1 : ℝ) / 20 := by
      norm_num
    have hrewrite :
        (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
            (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8)
          = ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (Real.log 2) ^ 8) *
              Real.exp (-(1979 : ℝ)) := by
      ring
    rw [hrewrite]
    have hstep :
        ((3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 / (Real.log 2) ^ 8) *
            Real.exp (-(1979 : ℝ))
          ≤ ((30000000000000000000000000000000000000000000 : ℝ) * 1000) *
              ((1 : ℝ) /
                100000000000000000000000000000000000000000000000000000000000000000000000000000000) := by
      exact mul_le_mul hBcoeff exp_neg1979_small (by positivity) (by positivity)
    exact le_trans hstep hnum
  have hrewrite_main :
      (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
        (Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
          + 7 * (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8
            + (2 : ℝ) ^ 8 * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8))
      = (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
        + (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) * 7 *
            (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8)
        + (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
            (7 * (2 : ℝ) ^ 8) * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8 := by
    ring
  rw [hrewrite_main]
  nlinarith [hA, hB, hC]

theorem sqrt_exp_3870 : Real.sqrt (Real.exp (3870 : ℝ)) = Real.exp (1935 : ℝ) := by
  have h : (3870 : ℝ) = (1935 : ℝ) + (1935 : ℝ) := by norm_num
  rw [h, Real.exp_add, Real.sqrt_mul]
  · have hs : (Real.sqrt (Real.exp (1935 : ℝ))) ^ 2 = Real.exp (1935 : ℝ) := by
      simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ Real.exp (1935 : ℝ) by positivity))
    nlinarith [hs]
  · positivity

theorem low_contrib_raw_le_three_tenths :
    (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
      ((100000000000000000720 : ℝ) *
        (Real.exp (3870 : ℝ) / (3870 : ℝ) ^ 7
          + 7 *
            (Real.sqrt (Real.exp (3870 : ℝ)) / (Real.log 2) ^ 8
              + (2 : ℝ) ^ 8 * Real.exp (3870 : ℝ) / (3870 : ℝ) ^ 8)))
      ≤ (3 : ℝ) / 10 := by
  have h44 : Real.exp (3870 : ℝ) / Real.exp (3914 : ℝ) = Real.exp (-(44 : ℝ)) := by
    have h := (Real.exp_sub (3870 : ℝ) (3914 : ℝ)).symm
    simpa [show (3870 : ℝ) - 3914 = (-(44 : ℝ)) by norm_num] using h
  have h1979 : Real.exp (1935 : ℝ) / Real.exp (3914 : ℝ) = Real.exp (-(1979 : ℝ)) := by
    have h := (Real.exp_sub (1935 : ℝ) (3914 : ℝ)).symm
    simpa [show (1935 : ℝ) - 3914 = (-(1979 : ℝ)) by norm_num] using h
  rw [sqrt_exp_3870]
  have hrewrite :
      (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          ((100000000000000000720 : ℝ) *
            (Real.exp (3870 : ℝ) / (3870 : ℝ) ^ 7
              + 7 *
                (Real.exp (1935 : ℝ) / (Real.log 2) ^ 8
                  + (2 : ℝ) ^ 8 * Real.exp (3870 : ℝ) / (3870 : ℝ) ^ 8)))
        = (3914 : ℝ) ^ 6 * (100000000000000000720 : ℝ) *
            (Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 7
              + 7 * (Real.exp (-(1979 : ℝ)) / (Real.log 2) ^ 8
                + (2 : ℝ) ^ 8 * Real.exp (-(44 : ℝ)) / (3870 : ℝ) ^ 8)) := by
    rw [← h44, ← h1979]
    field_simp
  rw [hrewrite]
  exact low_contrib_le_three_tenths

theorem exp_23_gt_4e9 : (4000000000 : ℝ) < Real.exp (23 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (23 : ℝ) 23, (4000000000 : ℝ) < Real.exp y := by
    interval_bound 20
  exact haux 23 (by constructor <;> norm_num)

theorem exp_8_lt_3914 : Real.exp (8 : ℝ) < (3914 : ℝ) := by
  have haux : ∀ y ∈ Set.Icc (8 : ℝ) 8, Real.exp y < (3914 : ℝ) := by
    interval_bound 20
  exact haux 8 (by constructor <;> norm_num)

namespace Calculations

theorem a_exp_upper_of
    {a : ℝ → ℝ}
    (ha_eq_admissible_ge_3000 :
      ∀ {z : ℝ}, z ≥ Real.exp 3000 →
        a z = admissible_bound (379.7 * 5.573412 ^ 5) 6.52 1.89 5.573412 z)
    {L C : ℝ}
    (hL : 3000 ≤ L)
    (hpow5 : (5.573412 : ℝ) ^ (5 : ℕ) * ((L / 5.573412) ^ (5 : ℕ)) = L ^ (5 : ℕ))
    (haux : ∀ y ∈ Set.Icc L L, styleVal y ≤ C) :
    a (Real.exp L) ≤ C := by
  have hge : Real.exp 3000 ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  rw [ha_eq_admissible_ge_3000 (z := Real.exp L) hge]
  unfold admissible_bound
  rw [Real.log_exp]
  have hpos : 0 < (L / 5.573412) := by positivity
  rw [rpow_652_split hpos]
  rw [sqrt_ratio_5573412 (y := L) hL0]
  let A : ℝ := (L / 5.573412) ^ (1.52 : ℝ)
  let E : ℝ := Real.exp (-(1.89 : ℝ) * (Real.sqrt L / Real.sqrt (5.573412 : ℝ)))
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

theorem sqrt_exp_3914 : Real.sqrt (Real.exp (3914 : ℝ)) = Real.exp (1957 : ℝ) := by
  have h : (3914 : ℝ) = (1957 : ℝ) + (1957 : ℝ) := by norm_num
  rw [h, Real.exp_add, Real.sqrt_mul]
  · have hs : (Real.sqrt (Real.exp (1957 : ℝ))) ^ 2 = Real.exp (1957 : ℝ) := by
      simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ Real.exp (1957 : ℝ) by positivity))
    nlinarith [hs]
  · positivity

theorem B_le_small_of
    {xₐ : ℝ}
    (hxₐ : xₐ = Real.exp (3914 : ℝ))
    (hlogxₐ : Real.log xₐ = (3914 : ℝ)) :
    1 / Real.log xₐ + 7 * 2 ^ 8 / Real.log xₐ ^ 2
      + 7 * Real.log xₐ ^ 6 / (Real.sqrt xₐ * (Real.log 2) ^ 8)
      ≤ (3 : ℝ) / 8000 := by
  rw [hlogxₐ]
  rw [hxₐ, sqrt_exp_3914]
  have htail : 7 * (3914 : ℝ) ^ 6 / (Real.exp (1957 : ℝ) * (Real.log 2) ^ 8) ≤ (1 : ℝ) / 1000000 := by
    have ht0 : 0 < (Real.exp (1957 : ℝ)) := by positivity
    have : 7 * (3914 : ℝ) ^ 6 / (Real.exp (1957 : ℝ) * (Real.log 2) ^ 8) =
      7 * (3914 : ℝ) ^ 6 * Real.exp (-(1957 : ℝ)) / (Real.log 2) ^ 8 := by
      field_simp [ht0.ne']
      rw [show (1 : ℝ) = Real.exp (1957 : ℝ) * Real.exp (-(1957 : ℝ)) by
        rw [← Real.exp_add]; norm_num]
    rw [this]
    exact tail_small
  have hmain : (1 / (3914 : ℝ) + 7 * 2 ^ 8 / (3914 : ℝ) ^ 2 + (1 : ℝ) / 1000000) ≤ (3 : ℝ) / 8000 := by
    norm_num
  have hle : 1 / (3914 : ℝ) + 7 * 2 ^ 8 / (3914 : ℝ) ^ 2
      + 7 * (3914 : ℝ) ^ 6 / (Real.exp (1957 : ℝ) * (Real.log 2) ^ 8)
      ≤ 1 / (3914 : ℝ) + 7 * 2 ^ 8 / (3914 : ℝ) ^ 2 + (1 : ℝ) / 1000000 := by
    linarith [htail]
  linarith [hle, hmain]

theorem C3_le_one_of
    {xₐ : ℝ}
    (hxₐ : xₐ = Real.exp (3914 : ℝ))
    (hlogxₐ : Real.log xₐ = (3914 : ℝ)) :
    2 * Real.log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, (k.factorial : ℝ) / Real.log 2 ^ (k + 1)
      ≤ (1 : ℝ) := by
  rw [hlogxₐ, hxₐ]
  simp [Finset.sum_Icc_succ_top, Nat.factorial]
  have hA : 2 * (3914 : ℝ) ^ 6 * Real.exp (-(3914 : ℝ)) ≤ (1 : ℝ) / 1000000 := by
    exact exp_3914_poly_small
  let u : ℝ := (log 2)⁻¹
  have hu_le : u ≤ (2 : ℝ) := by
    dsimp [u]
    have hhalf : (1 / 2 : ℝ) ≤ log 2 := by linarith [log_two_gt_d9]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2) hhalf
    simpa [one_div] using h
  have hBaux :
      (u ^ 2 + 2 * u ^ 3 + 6 * u ^ 4 + 24 * u ^ 5 + 120 * u ^ 6)
        ≤ ((2 : ℝ) ^ 2 + 2 * (2 : ℝ) ^ 3 + 6 * (2 : ℝ) ^ 4 + 24 * (2 : ℝ) ^ 5 + 120 * (2 : ℝ) ^ 6) := by
    gcongr
  have hB :
      ((log 2 ^ 2)⁻¹ + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5 + 120 / log 2 ^ 6) ≤ (9000 : ℝ) := by
    have huform :
        ((log 2 ^ 2)⁻¹ + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5 + 120 / log 2 ^ 6)
          = u ^ 2 + 2 * u ^ 3 + 6 * u ^ 4 + 24 * u ^ 5 + 120 * u ^ 6 := by
      dsimp [u]
      ring_nf
    rw [huform]
    have hnum : ((2 : ℝ) ^ 2 + 2 * (2 : ℝ) ^ 3 + 6 * (2 : ℝ) ^ 4 + 24 * (2 : ℝ) ^ 5 + 120 * (2 : ℝ) ^ 6) ≤ (9000 : ℝ) := by
      norm_num
    exact le_trans hBaux hnum
  have hdiv :
      2 * (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ)
      = 2 * (3914 : ℝ) ^ 6 * Real.exp (-(3914 : ℝ)) := by
    have he : (1 : ℝ) = Real.exp (3914 : ℝ) * Real.exp (-(3914 : ℝ)) := by
      rw [← Real.exp_add]
      norm_num
    field_simp
    rw [he]
  rw [hdiv]
  have hmul :
      2 * (3914 : ℝ) ^ 6 * Real.exp (-(3914 : ℝ)) *
        ((log 2 ^ 2)⁻¹ + 2 / log 2 ^ 3 + 6 / log 2 ^ 4 + 24 / log 2 ^ 5 + 120 / log 2 ^ 6)
      ≤ ((1 : ℝ) / 1000000) * (9000 : ℝ) := by
    exact mul_le_mul hA hB (by positivity) (by positivity)
  have hnum : ((1 : ℝ) / 1000000) * (9000 : ℝ) ≤ (1 : ℝ) := by
    norm_num
  exact le_trans hmul hnum

theorem C1_le_one_of
    {a : ℝ → ℝ} {xₐ : ℝ}
    (hxₐ : xₐ = Real.exp (3914 : ℝ))
    (h2xa : 2 ≤ xₐ)
    (h3870le : Real.exp 3870 ≤ xₐ)
    (ha_int : IntegrableOn (fun t ↦ a t / Real.log t ^ 7) (Set.Icc 2 xₐ) volume)
    (ha_le_low_huge : ∀ t ∈ Set.Icc 2 (Real.exp 3870), a t ≤ (100000000000000000000 : ℝ))
    (ha_mono_3000 : AntitoneOn a (Set.Ici (Real.exp 3000)))
    (ha_3870_upper : a (Real.exp 3870) ≤ (1800 : ℝ))
    (hJ3870 :
      ∫ t in Set.Icc 2 (Real.exp 3870), 1 / Real.log t ^ 7
        ≤ Real.exp 3870 / Real.log (Real.exp 3870) ^ 7
          + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8
            + 2 ^ 8 * Real.exp 3870 / Real.log (Real.exp 3870) ^ 8)) :
    Real.log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / Real.log t ^ 7 ≤ (1 : ℝ) := by
  let K : ℝ := (100000000000000000720 : ℝ)
  have hK_nonneg : 0 ≤ K := by
    dsimp [K]
    positivity
  let f : ℝ → ℝ := fun t ↦ (720 + a t) / Real.log t ^ 7
  have hJ_int : IntegrableOn (fun t : ℝ ↦ 1 / Real.log t ^ 7) (Set.Icc 2 xₐ) volume :=
    ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
      (continuousOn_log.mono <| by
        intro t ht
        exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
      intro t ht
      exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))
  have hconst_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / Real.log t ^ 7) (Set.Icc 2 xₐ) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) * (1 / Real.log t ^ 7)) (Set.Icc 2 xₐ) volume :=
      hJ_int.const_mul 720
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hadd_int : IntegrableOn (fun t : ℝ ↦ (720 : ℝ) / Real.log t ^ 7 + a t / Real.log t ^ 7) (Set.Icc 2 xₐ) volume :=
    hconst_int.add ha_int
  have hf_int : IntegrableOn f (Set.Icc 2 xₐ) volume := by
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 hadd_int
    intro t ht
    dsimp [f]
    ring
  have hsplit :
      ∫ t in Set.Icc 2 xₐ, f t
        = (∫ t in Set.Icc 2 (Real.exp 3870), f t)
          + (∫ t in Set.Icc (Real.exp 3870) xₐ, f t) :=
    integral_Icc_split (f := f) (a := 2) (b := Real.exp 3870) (c := xₐ)
      (by linarith [add_one_le_exp (3870 : ℝ)]) h3870le hf_int

  have hf_int_low : IntegrableOn f (Set.Icc 2 (Real.exp 3870)) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨ht.1, le_trans ht.2 h3870le⟩)
  have hlow_rhs_int : IntegrableOn (fun t : ℝ ↦ K / Real.log t ^ 7) (Set.Icc 2 (Real.exp 3870)) volume := by
    have htmp : IntegrableOn (fun t : ℝ ↦ K * (1 / Real.log t ^ 7)) (Set.Icc 2 (Real.exp 3870)) volume :=
      (ContinuousOn.integrableOn_Icc (continuousOn_const.div (ContinuousOn.pow
        (continuousOn_log.mono <| by
          intro t ht
          exact ne_of_gt (lt_of_lt_of_le (by norm_num) ht.1)) _) (by
        intro t ht
        exact pow_ne_zero _ <| ne_of_gt <| log_pos <| by linarith [ht.1]))).const_mul K
    refine (integrableOn_congr_fun ?_ measurableSet_Icc).2 htmp
    intro t ht
    ring
  have hlow_pt : ∀ t ∈ Set.Icc 2 (Real.exp 3870), f t ≤ K / Real.log t ^ 7 := by
    intro t ht
    have ha_le : a t ≤ (100000000000000000000 : ℝ) := ha_le_low_huge t ht
    have hnum_le : 720 + a t ≤ K := by
      dsimp [K]
      linarith
    have hlog_nonneg : 0 ≤ Real.log t := Real.log_nonneg (by linarith [ht.1])
    dsimp [f]
    exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
  have hlow_le_rhs :
      ∫ t in Set.Icc 2 (Real.exp 3870), f t
        ≤ ∫ t in Set.Icc 2 (Real.exp 3870), K / Real.log t ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_low hlow_rhs_int measurableSet_Icc hlow_pt
  have hlow_factor :
      ∫ t in Set.Icc 2 (Real.exp 3870), K / Real.log t ^ 7
        = K * ∫ t in Set.Icc 2 (Real.exp 3870), 1 / Real.log t ^ 7 := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc ?_
    intro t ht
    ring
  have hlow_le :
      ∫ t in Set.Icc 2 (Real.exp 3870), f t
        ≤ K * (Real.exp 3870 / Real.log (Real.exp 3870) ^ 7
          + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / Real.log (Real.exp 3870) ^ 8)) := by
    rw [hlow_factor] at hlow_le_rhs
    exact le_trans hlow_le_rhs (mul_le_mul_of_nonneg_left hJ3870 hK_nonneg)

  have hf_int_high : IntegrableOn f (Set.Icc (Real.exp 3870) xₐ) volume :=
    hf_int.mono_set (by intro t ht; exact ⟨le_trans (by linarith [add_one_le_exp (3870 : ℝ)]) ht.1, ht.2⟩)
  have hconst_high_int : IntegrableOn (fun _ : ℝ ↦ (2520 : ℝ) / (3870 : ℝ) ^ 7) (Set.Icc (Real.exp 3870) xₐ) volume := by
    exact ContinuousOn.integrableOn_Icc continuousOn_const
  have hhigh_pt : ∀ t ∈ Set.Icc (Real.exp 3870) xₐ, f t ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 := by
    intro t ht
    have ht3000 : Real.exp 3000 ≤ t :=
      le_trans (Real.exp_le_exp.mpr (by norm_num : (3000 : ℝ) ≤ 3870)) ht.1
    have hat3870 : a t ≤ a (Real.exp 3870) :=
      ha_mono_3000
        (Set.mem_Ici.mpr (Real.exp_le_exp.mpr (by norm_num : (3000 : ℝ) ≤ 3870)))
        (Set.mem_Ici.mpr ht3000) ht.1
    have hat : a t ≤ 1800 := le_trans hat3870 ha_3870_upper
    have hnum_le : 720 + a t ≤ 2520 := by linarith
    have hlog_ge : (3870 : ℝ) ≤ Real.log t := by
      have h := Real.log_le_log (by positivity : (0 : ℝ) < Real.exp 3870) ht.1
      simpa [Real.log_exp] using h
    have hpow : (3870 : ℝ) ^ 7 ≤ Real.log t ^ 7 := pow_le_pow_left₀ (by norm_num) hlog_ge 7
    have hlog_nonneg : 0 ≤ Real.log t := by linarith [hlog_ge]
    calc
      f t = (720 + a t) / Real.log t ^ 7 := rfl
      _ ≤ (2520 : ℝ) / Real.log t ^ 7 := by
        exact div_le_div_of_nonneg_right hnum_le (pow_nonneg hlog_nonneg 7)
      _ ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 := by
        exact div_le_div_of_nonneg_left (by norm_num : 0 ≤ (2520 : ℝ)) (by positivity) hpow
  have hhigh_le_const :
      ∫ t in Set.Icc (Real.exp 3870) xₐ, f t
        ≤ ∫ t in Set.Icc (Real.exp 3870) xₐ, (2520 : ℝ) / (3870 : ℝ) ^ 7 :=
    MeasureTheory.setIntegral_mono_on hf_int_high hconst_high_int measurableSet_Icc hhigh_pt
  have hhigh_const_eval :
      ∫ t in Set.Icc (Real.exp 3870) xₐ, (2520 : ℝ) / (3870 : ℝ) ^ 7
        = (2520 : ℝ) / (3870 : ℝ) ^ 7 * (xₐ - Real.exp 3870) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le h3870le,
      intervalIntegral.integral_const]
    simp [smul_eq_mul, mul_comm]
  have hhigh_le :
      ∫ t in Set.Icc (Real.exp 3870) xₐ, f t
        ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 * xₐ := by
    have htmp : ∫ t in Set.Icc (Real.exp 3870) xₐ, f t
        ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 * (xₐ - Real.exp 3870) := by
      simpa [hhigh_const_eval] using hhigh_le_const
    have hsub : xₐ - Real.exp 3870 ≤ xₐ := by
      have : 0 ≤ Real.exp 3870 := by positivity
      linarith
    have hcoeff_nonneg : 0 ≤ (2520 : ℝ) / (3870 : ℝ) ^ 7 := by positivity
    exact le_trans htmp (mul_le_mul_of_nonneg_left hsub hcoeff_nonneg)

  have hsum :
      (∫ t in Set.Icc 2 (Real.exp 3870), f t) + (∫ t in Set.Icc (Real.exp 3870) xₐ, f t)
        ≤ K * (Real.exp 3870 / Real.log (Real.exp 3870) ^ 7
          + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / Real.log (Real.exp 3870) ^ 8))
          + (2520 : ℝ) / (3870 : ℝ) ^ 7 * xₐ := by
    linarith [hlow_le, hhigh_le]
  have hcoef_nonneg : 0 ≤ Real.log xₐ ^ 6 / xₐ := by
    positivity
  have hmain :
      Real.log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (Real.exp 3870), f t) + (∫ t in Set.Icc (Real.exp 3870) xₐ, f t))
        ≤ Real.log xₐ ^ 6 / xₐ *
            (K * (Real.exp 3870 / Real.log (Real.exp 3870) ^ 7
              + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / Real.log (Real.exp 3870) ^ 8))
              + (2520 : ℝ) / (3870 : ℝ) ^ 7 * xₐ) := by
    exact mul_le_mul_of_nonneg_left hsum hcoef_nonneg
  have hmain' :
      (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          ((∫ t in Set.Icc 2 (Real.exp 3870), f t) + (∫ t in Set.Icc (Real.exp 3870) (Real.exp (3914 : ℝ)), f t))
        ≤ (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          (K * (Real.exp 3870 / (3870 : ℝ) ^ 7
            + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8))
            + (2520 : ℝ) / (3870 : ℝ) ^ 7 * Real.exp (3914 : ℝ)) := by
    simpa [hxₐ, Real.log_exp] using hmain
  have hdecomp :
      (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          (K * (Real.exp 3870 / (3870 : ℝ) ^ 7
            + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8))
            + (2520 : ℝ) / (3870 : ℝ) ^ 7 * Real.exp (3914 : ℝ))
        = (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
            (K * (Real.exp 3870 / (3870 : ℝ) ^ 7
              + 7 * (Real.sqrt (Real.exp 3870) / Real.log 2 ^ 8 + 2 ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8)))
          + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 := by
    field_simp
  rw [hdecomp] at hmain'
  dsimp [K] at hmain'
  have hlow_num :
      (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          ((100000000000000000720 : ℝ) *
            (Real.exp 3870 / (3870 : ℝ) ^ 7
              + 7 *
                (Real.sqrt (Real.exp 3870) / (Real.log 2) ^ 8
                  + (2 : ℝ) ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8)))
        ≤ (3 : ℝ) / 10 := low_contrib_raw_le_three_tenths
  have hhigh_num : (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 ≤ (7 : ℝ) / 10 := by
    norm_num
  have hfin :
      (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
          ((100000000000000000720 : ℝ) *
            (Real.exp 3870 / (3870 : ℝ) ^ 7
              + 7 *
                (Real.sqrt (Real.exp 3870) / (Real.log 2) ^ 8
                  + (2 : ℝ) ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8)))
          + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 ≤ 1 := by
    nlinarith [hlow_num, hhigh_num]
  have horig_split :
      Real.log xₐ ^ 6 / xₐ *
          ((∫ t in Set.Icc 2 (Real.exp 3870), f t) + (∫ t in Set.Icc (Real.exp 3870) xₐ, f t))
        ≤ (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
            ((100000000000000000720 : ℝ) *
              (Real.exp 3870 / (3870 : ℝ) ^ 7
                + 7 *
                  (Real.sqrt (Real.exp 3870) / (Real.log 2) ^ 8
                    + (2 : ℝ) ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8)))
            + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 := by
    simpa [f, hxₐ, Real.log_exp] using hmain'
  have horig :
      Real.log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / Real.log t ^ 7
        ≤ (3914 : ℝ) ^ 6 / Real.exp (3914 : ℝ) *
            ((100000000000000000720 : ℝ) *
              (Real.exp 3870 / (3870 : ℝ) ^ 7
                + 7 *
                  (Real.sqrt (Real.exp 3870) / (Real.log 2) ^ 8
                    + (2 : ℝ) ^ 8 * Real.exp 3870 / (3870 : ℝ) ^ 8)))
            + (2520 : ℝ) * (3914 : ℝ) ^ 6 / (3870 : ℝ) ^ 7 := by
    rw [hsplit]
    exact horig_split
  exact le_trans horig hfin

theorem m_upper_from_bounds
    {a_xa C1 C2 C3 B : ℝ}
    (hax0 : 0 ≤ a_xa)
    (hC3 : 0 ≤ C3)
    (hB0 : 0 ≤ B)
    (hC2abs : |C2| ≤ C1)
    (hC1 : C1 ≤ (1 : ℝ)) :
    120 - a_xa - (C2 + C3) - a_xa * B ≤ (121 : ℝ) := by
  have hC2C3 : -(C2 + C3) ≤ |C2| := by
    have h1 : -(C2 + C3) ≤ -C2 := by linarith
    have h2 : -C2 ≤ |C2| := by nlinarith [neg_abs_le C2]
    exact le_trans h1 h2
  have hmain :
      120 - a_xa - (C2 + C3) - a_xa * B ≤ 120 + |C2| := by
    nlinarith [hax0, hC3, hB0, hC2C3]
  have hmain2 : 120 + |C2| ≤ (121 : ℝ) := by
    nlinarith [hC2abs, hC1]
  exact le_trans hmain hmain2

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
    (hax0 : 0 ≤ a_xa)
    (hC1 : C1 ≤ (1 : ℝ))
    (hax : a_xa ≤ (1311 : ℝ))
    (haex : a_exa ≤ (13042 / 10 : ℝ))
    (hB : B ≤ (3 : ℝ) / 8000) :
    120 + a_exa + C1 + (720 + a_xa) * B ≤ (1426 : ℝ) := by
  have h720a : 720 + a_xa ≤ (2031 : ℝ) := by linarith
  have hterm_le : (720 + a_xa) * B ≤ (2031 : ℝ) * ((3 : ℝ) / 8000) := by
    have h1 :
        (720 + a_xa) * B ≤ (720 + a_xa) * ((3 : ℝ) / 8000) := by
      exact mul_le_mul_of_nonneg_left hB (by linarith [hax0])
    have h2 :
        (720 + a_xa) * ((3 : ℝ) / 8000) ≤ (2031 : ℝ) * ((3 : ℝ) / 8000) := by
      exact mul_le_mul_of_nonneg_right h720a (by positivity)
    exact le_trans h1 h2
  nlinarith [hC1, haex, hterm_le]

theorem m_lower_from_bounds
    {a_xa C1 C2 C3 B : ℝ}
    (hax0 : 0 ≤ a_xa)
    (hax : a_xa ≤ (1311 : ℝ))
    (hC1 : C1 ≤ (1 : ℝ))
    (hC2abs : |C2| ≤ C1)
    (hC3 : C3 ≤ (1 : ℝ))
    (hB : B ≤ (3 : ℝ) / 8000) :
    (-1194 : ℝ) ≤ 120 - a_xa - (C2 + C3) - a_xa * B := by
  have hC2abs1 : |C2| ≤ (1 : ℝ) := le_trans hC2abs hC1
  have hC2le : C2 ≤ (1 : ℝ) := (abs_le.mp hC2abs1).2
  have hC2C3_lower : (-2 : ℝ) ≤ -(C2 + C3) := by
    nlinarith [hC2le, hC3]
  have hprod_le : a_xa * B ≤ (1311 : ℝ) * ((3 : ℝ) / 8000) := by
    have h1 :
        a_xa * B ≤ a_xa * ((3 : ℝ) / 8000) := by
      exact mul_le_mul_of_nonneg_left hB hax0
    have h2 : a_xa * ((3 : ℝ) / 8000) ≤ (1311 : ℝ) * ((3 : ℝ) / 8000) := by
      exact mul_le_mul_of_nonneg_right hax (by positivity)
    exact le_trans h1 h2
  have hnegprod :
      -((1311 : ℝ) * ((3 : ℝ) / 8000)) ≤ -a_xa * B := by
    nlinarith [hprod_le]
  have hnega : (-(1311 : ℝ)) ≤ -a_xa := by
    nlinarith [hax]
  nlinarith [hnega, hC2C3_lower, hnegprod]

end Calculations

end Ramanujan
