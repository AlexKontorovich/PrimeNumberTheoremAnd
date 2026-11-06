import TernaryGoldbach.Prelim.PNTMertens
import RSBounds.RS75MomentCalculus
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Abel transform of the first Mangoldt Mertens error

This identifies the Abel average of `E₁Λ` with the pole-subtracted logarithmic
derivative of zeta for every real `s>1`.  It uses the existing unconditional
boundedness of `E₁Λ`, Mathlib's L-series summatory-integral identity, and the
already checked logarithmic moment primitive. No limiting value of `E₁Λ`,
RH hypothesis, or quantitative prime-number estimate is assumed.
-/

open Real Complex Set Filter MeasureTheory Asymptotics
open scoped Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensAbelIdentity

open TernaryGoldbach.PNTMertens RS75MomentCalculus

theorem sum_Icc_mangoldt_div (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℝ) / n) = Real.log x + E₁Λ x := by
  have heq : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [heq, sum_mangoldt_div_eq]

theorem weighted_sum_isBigO_rpow {r : ℝ} (hr : 0 < r) :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (Λ k : ℝ) / k) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ r) := by
  have h := (sum_mangoldt_div_eq_log'.isBigO.trans
    (isLittleO_log_rpow_atTop hr).isBigO).comp_tendsto tendsto_natCast_atTop_atTop
  convert h using 1
  · funext n
    dsimp only [Function.comp_apply]
    simpa only [Nat.floor_natCast] using
      (sum_Icc_mangoldt_div (n : ℝ)).trans (sum_mangoldt_div_eq (n : ℝ)).symm
  · rfl

/-- Shifting the coefficients by `1/n` shifts the L-series variable by one. -/
theorem LSeries_mangoldt_div_shift (s : ℝ) :
    LSeries (fun n : ℕ => (((Λ n : ℝ) / n : ℝ) : ℂ)) ((s : ℂ) - 1) =
      LSeries (fun n : ℕ => (Λ n : ℂ)) (s : ℂ) := by
  unfold LSeries
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    push_cast
    rw [div_div]
    congr 1
    calc
      (n : ℂ) * (n : ℂ) ^ ((s : ℂ) - 1) =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((s : ℂ) - 1) := by rw [Complex.cpow_one]
      _ = (n : ℂ) ^ ((1 : ℂ) + ((s : ℂ) - 1)) :=
        (Complex.cpow_add _ _ (by exact_mod_cast hn)).symm
      _ = (n : ℂ) ^ (s : ℂ) := by congr 1; ring

theorem integrableOn_error_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => E₁Λ x * x ^ (-s)) (Ioi 1) := by
  obtain ⟨C, hC, hbound⟩ := E₁Λ.bounded'
  have hg : IntegrableOn (fun x : ℝ => C * x ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one).const_mul C
  have hm : Measurable E₁Λ := by fun_prop
  apply hg.mono' (hm.mul (measurable_id.pow_const (-s))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  change ‖E₁Λ x * x ^ (-s)‖ ≤ C * x ^ (-s)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  exact mul_le_mul_of_nonneg_right (hbound x hx.le) (Real.rpow_nonneg hx0.le _)

theorem integrableOn_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => Real.log x * x ^ (-s)) (Ioi 1) := by
  simpa only [momentFn, pow_one] using
    (integrableOn_Ioi_deriv_of_nonneg'
      (fun t ht => hasDerivAt_neg_tailPrimitive hs.ne' 1 (by norm_num)
        (lt_of_lt_of_le zero_lt_one ht))
      (fun t ht => momentFn_nonneg 1 ht.le)
      ((tendsto_tailPrimitive hs 1).neg))

theorem integral_log_mul_rpow {s : ℝ} (hs : 1 < s) :
    (∫ x in Ioi (1 : ℝ), Real.log x * x ^ (-s)) = 1 / (s - 1) ^ 2 := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun t ht => hasDerivAt_neg_tailPrimitive hs.ne' 1 (by norm_num)
      (lt_of_lt_of_le zero_lt_one ht))
    (by simpa only [momentFn, pow_one] using integrableOn_log_mul_rpow hs)
    ((tendsto_tailPrimitive hs 1).neg)
  simpa [tailPrimitive, momentFn] using h

/-- The real summatory-Mangoldt integral in the domain of absolute convergence. -/
theorem logDeriv_eq_integral {s : ℝ} (hs : 1 < s) :
    -(logDeriv riemannZeta (s : ℂ)).re =
      (s - 1) * ∫ x in Ioi (1 : ℝ), (Real.log x + E₁Λ x) * x ^ (-s) := by
  have h := LSeries_eq_mul_integral_of_nonneg
    (fun n : ℕ => (Λ n : ℝ) / n)
    (r := (s - 1) / 2) (s := (s : ℂ) - 1) (by linarith)
    (by simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]; linarith)
    (weighted_sum_isBigO_rpow (by linarith))
    (fun n => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _))
  rw [LSeries_mangoldt_div_shift,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)] at h
  have hi :
      (∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((Λ k : ℝ) / k : ℝ) : ℂ)) *
          (t : ℂ) ^ (-(((s : ℂ) - 1) + 1))) =
        ((∫ t in Ioi (1 : ℝ), (Real.log t + E₁Λ t) * t ^ (-s) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 ≤ t := (lt_trans zero_lt_one ht).le
    change (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (((Λ k : ℝ) / k : ℝ) : ℂ)) *
        (t : ℂ) ^ (-(((s : ℂ) - 1) + 1)) =
      (((Real.log t + E₁Λ t) * t ^ (-s) : ℝ) : ℂ)
    rw [show -(((s : ℂ) - 1) + 1) = ((-s : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0]
    rw [← Complex.ofReal_sum, ← Complex.ofReal_mul, sum_Icc_mangoldt_div]
  rw [hi] at h
  rw [neg_div, ← logDeriv_apply] at h
  have hr := congrArg Complex.re h
  simpa using hr

/-- The pole-subtracted Abel identity used to normalize a convergent `E₁Λ`. -/
theorem error_abel_identity {s : ℝ} (hs : 1 < s) :
    (s - 1) * (∫ x in Ioi (1 : ℝ), E₁Λ x * x ^ (-s)) =
      -(logDeriv riemannZeta (s : ℂ)).re - 1 / (s - 1) := by
  have h := logDeriv_eq_integral hs
  have hi : (∫ x in Ioi (1 : ℝ), (Real.log x + E₁Λ x) * x ^ (-s)) =
      1 / (s - 1) ^ 2 + ∫ x in Ioi (1 : ℝ), E₁Λ x * x ^ (-s) := by
    simp_rw [add_mul]
    rw [integral_add (integrableOn_log_mul_rpow hs) (integrableOn_error_mul_rpow hs),
      integral_log_mul_rpow hs]
  rw [hi] at h
  have hn : s - 1 ≠ 0 := by linarith
  have he : (s - 1) * (1 / (s - 1) ^ 2) = 1 / (s - 1) := by
    field_simp
  nlinarith [he]

end TernaryGoldbach.RSBounds.MertensAbelIdentity
