import PrimeNumberTheoremAnd.IEANTN.FKS2Cor23

/-!
# FKS2 Corollary 23 — shared `B=3/2, C=2` tail source for rows 8 and 9

`mu_asymp_num_le_cor14` is the un-normalized analogue of `FKS2.mu_asymp_num_le`:
it bounds `μ_asymp` at the `corollary_14` parameters `(A=121.0961, B=3/2, C=2,
R=5.5666305, x₀=2, x₁=e^20000)` by `9e-5` (actual ≈ 5.016e-5), via the same
`dawson_le_sharp (w=0.117)` technique (`z = √20000 − 1/√R ≈ 140.99752`).

`cor14_tail` then applies `theorem_3` to `corollary_14`, yielding
`Eπ x ≤ admissible_bound 121.107 (3/2) 2 R x` for `x ≥ e^20000` (since
`121.0961·(1+μ_asymp) ≤ 121.107`).  This bound has EXACTLY the rate `2/√R` of
table-6 rows 8 and 9 (both have `C = 2`): it IS row 8's tail curve, and — because
`L^{3/2} ≤ const·L²` for large `L` — it DOMINATES row 9's `B = 2` curve.  This is
why neither row needs an `Eθ` `B = 2` source bound.
-/

namespace FKS2
open Real MeasureTheory Chebyshev

theorem mu_asymp_num_le_cor14 :
    μ_asymp 121.0961 1.5 2 5.5666305 2 (exp 20000) ≤ 9e-5 := by
  have hs_lo : (141.4213562 : ℝ) ≤ Real.sqrt 20000 := by interval_decide
  have hs_hi : Real.sqrt 20000 ≤ (141.4213563 : ℝ) := by
    have h := Real.sqrt_le_sqrt (show (20000:ℝ) ≤ 141.4213563 ^ 2 by norm_num)
    rwa [Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 141.4213563)] at h
  have hexp32 : Real.exp (-(32:ℝ)) ≤ (1.3e-14 : ℝ) :=
    (le_of_lt (LogTables.exp_neg_32_lt.trans_le (by norm_num)))
  have hexpw : Real.exp ((0.117:ℝ) ^ 2) ≤ (1.0138790 : ℝ) := by
    rw [show ((0.117:ℝ)) ^ 2 = 13689 / 1000000 by norm_num]
    interval_decide
  have hlog2_lo : (0.6931471803 : ℝ) < Real.log 2 := LogTables.log_2_gt_d9
  have hlog2_hi : Real.log 2 < (0.6931471808 : ℝ) := LogTables.log_2_lt_d9
  unfold μ_asymp
  rw [Real.log_exp]
  -- ===== Term 1 =====
  have hT1 : (2 * 20000) /
      (admissible_bound 121.0961 1.5 2 5.5666305 (exp 20000) * exp 20000 * Real.log 2)
      * δ 2 ≤ 1e-11 := by
    have hpc : Nat.primeCounting 2 = 1 := by decide
    have hpi2 : pi 2 = 1 := by
      unfold pi
      rw [show ⌊(2:ℝ)⌋₊ = 2 from by norm_num, hpc]
      norm_num
    have hLi2 : Li 2 = 0 := by
      unfold Li
      exact intervalIntegral.integral_same
    have hθ0 : (0:ℝ) ≤ θ 2 := Chebyshev.theta_nonneg 2
    have hθ3 : θ 2 ≤ 3 := by
      have h4 := theta_le_log4_mul_x (by norm_num : (0:ℝ) ≤ 2)
      have hlog4 : Real.log 4 ≤ 1.4 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        push_cast
        nlinarith [hlog2_hi]
      nlinarith [h4, hlog4]
    have hδ2 : δ 2 ≤ 2 := by
      unfold δ
      rw [hpi2, hLi2]
      have hlogne : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
      have hform : ((1:ℝ) - 0) / ((2:ℝ) / Real.log 2) = Real.log 2 / 2 := by
        field_simp
        norm_num
      rw [hform, abs_le]
      constructor
      · nlinarith [hθ0, hθ3, hlog2_lo, hlog2_hi]
      · nlinarith [hθ0, hθ3, hlog2_lo, hlog2_hi]
    have hδ0 : (0:ℝ) ≤ δ 2 := abs_nonneg _
    have hbig : (2:ℝ) ^ (60:ℕ) ≤
        admissible_bound 121.0961 1.5 2 5.5666305 (exp 20000) * exp 20000 := by
      unfold admissible_bound
      rw [Real.log_exp, ← Real.sqrt_eq_rpow]
      -- The "power" factor `(20000/5.5666305)^1.5 ≥ 1`.
      have hP : (1:ℝ) ≤ ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ) :=
        Real.one_le_rpow (by norm_num) (by norm_num)
      have hAP : (1:ℝ) ≤ 121.0961 * ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ) := by
        nlinarith [hP]
      -- `√(20000/5.5666305) ≤ 60`, so the exp argument exceeds `19880`.
      have hsqrtR : Real.sqrt ((20000:ℝ) / 5.5666305) ≤ 60 := by
        rw [show (60:ℝ) = Real.sqrt (60 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
        exact Real.sqrt_le_sqrt (by norm_num)
      have hsqrtRnn : (0:ℝ) ≤ Real.sqrt ((20000:ℝ) / 5.5666305) := Real.sqrt_nonneg _
      have hE : Real.exp (19880:ℝ) ≤
          Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000 := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        nlinarith [hsqrtR, hsqrtRnn]
      have hEpos : (0:ℝ) <
          Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000 :=
        mul_pos (Real.exp_pos _) (Real.exp_pos _)
      have hK : (2:ℝ) ^ (60:ℕ) ≤ Real.exp (19880:ℝ) := by
        have h1 : Real.exp (19880:ℝ) = Real.exp 1 ^ (19880:ℕ) := by
          rw [← Real.exp_nat_mul]
          norm_num
        rw [h1]
        calc (2:ℝ) ^ (60:ℕ) ≤ (2:ℝ) ^ (19880:ℕ) :=
              pow_le_pow_right₀ (by norm_num) (by norm_num)
          _ ≤ Real.exp 1 ^ (19880:ℕ) := by
              apply pow_le_pow_left₀ (by norm_num)
              nlinarith [Real.exp_one_gt_d9]
      have hstep :
          Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000 ≤
          (121.0961 * ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ)) *
            (Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000) := by
        nlinarith [mul_nonneg
          (by linarith [hAP] : (0:ℝ) ≤ 121.0961 * ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ) - 1)
          hEpos.le]
      calc (2:ℝ) ^ (60:ℕ) ≤ Real.exp (19880:ℝ) := hK
        _ ≤ Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000 := hE
        _ ≤ (121.0961 * ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ)) *
              (Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000) := hstep
        _ = 121.0961 * ((20000:ℝ) / 5.5666305) ^ (1.5:ℝ) *
              Real.exp (-2 * Real.sqrt ((20000:ℝ) / 5.5666305)) * Real.exp 20000 := by ring
    have hpow60 : ((2:ℝ) ^ (60:ℕ)) = 1152921504606846976 := by norm_num
    have hfrac : (2 * 20000) /
        (admissible_bound 121.0961 1.5 2 5.5666305 (exp 20000) * exp 20000 *
        Real.log 2) ≤ 40000 / (1152921504606846976 * 0.6931471803) := by
      gcongr
      · norm_num
      · nlinarith [hbig, hlog2_lo, hpow60]
    calc (2 * 20000) /
        (admissible_bound 121.0961 1.5 2 5.5666305 (exp 20000) * exp 20000 *
        Real.log 2) * δ 2
        ≤ 40000 / (1152921504606846976 * 0.6931471803) * 2 := by
          apply mul_le_mul hfrac hδ2 hδ0 (by positivity)
      _ ≤ 1e-11 := by norm_num
  -- ===== Term 2: the Dawson term =====
  -- `2 / (2 * √5.5666305) = 1 / √5.5666305 ∈ [0.4238403, 0.4238420]`.
  have hsR_lo : (2.359370 : ℝ) ≤ Real.sqrt 5.5666305 := by
    rw [show (2.359370:ℝ) = Real.sqrt (2.359370 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsR_hi : Real.sqrt 5.5666305 ≤ (2.359379 : ℝ) := by
    rw [show (2.359379:ℝ) = Real.sqrt (2.359379 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hsR_pos : (0:ℝ) < Real.sqrt 5.5666305 := by positivity
  have harg_hi : (2:ℝ) / (2 * Real.sqrt 5.5666305) ≤ 0.4238420 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hsR_lo, hsR_pos]
  have harg_lo : (0.4238403 : ℝ) ≤ 2 / (2 * Real.sqrt 5.5666305) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [hsR_hi, hsR_pos]
  set z := Real.sqrt 20000 - 2 / (2 * Real.sqrt 5.5666305) with hzdef
  have hz_lo : (140.997514 : ℝ) ≤ z := by rw [hzdef]; linarith
  have hz_hi : z ≤ (141 : ℝ) := by rw [hzdef]; linarith [Real.sqrt_nonneg (5.5666305:ℝ)]
  have hz_pos : (0:ℝ) < z := by linarith
  have hD := dawson_le_sharp (z := z) (w := 0.117) (by norm_num) (by linarith) hz_pos
  have b1 : 1 / (2 * z) ≤ 1 / (2 * 140.997514) := by
    gcongr
  have b2 : Real.exp ((0.117:ℝ) ^ 2) / (4 * z ^ 3) ≤
      1.0138790 / (4 * (140.997514:ℝ) ^ 3) := by
    gcongr
  have b3 : (z - 0.117) * Real.exp (-(0.117 * (2 * z - 0.117))) ≤
      141 * (1.3e-14 : ℝ) := by
    have hexpo : Real.exp (-(0.117 * (2 * z - 0.117))) ≤ Real.exp (-(32:ℝ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hz_lo]
    have hzw : z - 0.117 ≤ 141 := by linarith
    have hzw0 : (0:ℝ) ≤ z - 0.117 := by linarith
    calc (z - 0.117) * Real.exp (-(0.117 * (2 * z - 0.117)))
        ≤ 141 * Real.exp (-(32:ℝ)) := by
          apply mul_le_mul hzw hexpo (Real.exp_nonneg _) (by norm_num)
      _ ≤ 141 * 1.3e-14 := by nlinarith [hexp32]
  have hDb : dawson z ≤ 1 / (2 * 140.997514) + 1.0138790 / (4 * (140.997514:ℝ) ^ 3) +
      141 * 1.3e-14 := by linarith [hD, b1, b2, b3]
  have hD0 : (0:ℝ) ≤ dawson z := dawson_nonneg hz_pos.le
  have hT2 : 2 * dawson z / Real.sqrt 20000 ≤
      2 * (1 / (2 * 140.997514) + 1.0138790 / (4 * (140.997514:ℝ) ^ 3) + 141 * 1.3e-14) /
        141.4213562 := by
    gcongr
  linarith [hT1, hT2, show
    (2:ℝ) * (1 / (2 * 140.997514) + 1.0138790 / (4 * (140.997514:ℝ) ^ 3) + 141 * 1.3e-14) /
      141.4213562 + 1e-11 ≤ 9e-5 from by norm_num]

/-- Row-8/9 tail source: `theorem_3` applied to `corollary_14` (the un-normalized
`Eθ` `B=3/2`, `C=2`, `R=5.5666305` bound) at `x₁ = e^20000`.  Same rate as
rows 8/9 (`C = 2`); transported constant `121.0961·(1+μ_asymp) ≤ 121.107` by
`mu_asymp_num_le_cor14`.  This IS row 8's curve, and DOMINATES row 9's `B=2` curve. -/
theorem cor14_tail :
    ∀ x ≥ exp 20000, Eπ x ≤ admissible_bound 121.107 1.5 2 5.5666305 x := by
  have htail :=
    theorem_3 121.0961 (3 / 2) 2 5.5666305 2 (exp 20000)
      (by rw [ge_iff_le, max_le_iff]; constructor <;> norm_num)
      (by norm_num)
      corollary_14
      (by rw [ge_iff_le, max_le_iff]
          refine ⟨le_trans Real.exp_one_gt_two.le
            (Real.exp_le_exp.mpr (by norm_num : (1:ℝ) ≤ 20000)), ?_⟩
          apply Real.exp_le_exp.mpr
          have h1 : (2:ℝ) / (2 * Real.sqrt 5.5666305) ≤ 1 := by
            rw [div_le_iff₀ (by positivity)]; nlinarith [sqrtR5_lb]
          have h0 : (0:ℝ) ≤ 2 / (2 * Real.sqrt 5.5666305) := by positivity
          nlinarith [h1, h0])
      (by norm_num)
      (by norm_num)
      (by norm_num)
      (by have h1 : (2:ℝ) / (2 * Real.sqrt 5.5666305) ≤ 0.4239 := by
            rw [div_le_iff₀ (by positivity)]; nlinarith [sqrtR5_lb]
          have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
          have hsq : (0.8325 : ℝ) ^ 2 ≤ Real.log 2 := by nlinarith [hlog2]
          have hsqrt : (0.8325 : ℝ) ≤ Real.sqrt (Real.log 2) := by
            calc (0.8325 : ℝ) = Real.sqrt ((0.8325 : ℝ) ^ 2) :=
                  (Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 0.8325)).symm
              _ ≤ Real.sqrt (Real.log 2) := Real.sqrt_le_sqrt hsq
          linarith)
  intro x hx
  have hmain := htail x hx
  rw [show (3 / 2 : ℝ) = 1.5 by norm_num] at hmain
  have hμ : μ_asymp 121.0961 1.5 2 5.5666305 2 (exp 20000) ≤ 9e-5 := mu_asymp_num_le_cor14
  have hA :
      121.0961 * (1 + μ_asymp 121.0961 1.5 2 5.5666305 2 (exp 20000)) ≤ 121.107 := by
    nlinarith [hμ]
  refine le_trans hmain ?_
  have hlognn : 0 ≤ Real.log x := by
    have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num : (1 : ℝ) ≤ exp 20000) hx
    exact Real.log_nonneg hx1
  unfold admissible_bound
  have hP : (0:ℝ) ≤ (Real.log x / 5.5666305) ^ (1.5:ℝ) :=
    Real.rpow_nonneg (div_nonneg hlognn (by norm_num)) _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hP) (Real.exp_nonneg _)

end FKS2
