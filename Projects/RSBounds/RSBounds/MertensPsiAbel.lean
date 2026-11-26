import RSBounds.MertensAbelIdentity

/-!
# Abel averages of `ψ(x)/x` and the signed-integral normalization

Chebyshev's elementary `ψ(x)=O(x)` bound is enough for the summatory L-series
identity.  In particular, this module never assumes or proves `ψ(x)/x → 1`.
The final formula subtracts the psi average from the first Mertens error
average, so the Laurent expansion at one can normalize their difference.
-/

open Real Complex Set Filter MeasureTheory Asymptotics
open scoped Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensPsiAbel

open TernaryGoldbach.PNTMertens MertensAbelIdentity

noncomputable def D (x : ℝ) : ℝ := E₁Λ x - Chebyshev.psi x / x

theorem sum_Icc_mangoldt (x : ℝ) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (Λ n : ℝ)) = Chebyshev.psi x := by
  have heq : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_Ioc]
    omega
  rw [heq]
  rfl

theorem sum_mangoldt_isBigO :
    (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, (Λ k : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
  refine Asymptotics.isBigO_iff.mpr ⟨Real.log 4 + 4, Eventually.of_forall fun n => ?_⟩
  have heq : (∑ k ∈ Finset.Icc 1 n, (Λ k : ℝ)) = Chebyshev.psi (n : ℝ) := by
    simpa only [Nat.floor_natCast] using sum_Icc_mangoldt (n : ℝ)
  rw [heq, Real.rpow_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Chebyshev.psi_nonneg _), abs_of_nonneg (Nat.cast_nonneg _)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

theorem psi_ratio_bound {x : ℝ} (hx : 1 ≤ x) :
    |Chebyshev.psi x / x| ≤ Real.log 4 + 4 := by
  have hx0 : 0 < x := by linarith
  rw [abs_of_nonneg (div_nonneg (Chebyshev.psi_nonneg _) hx0.le), div_le_iff₀ hx0]
  exact Chebyshev.psi_le_const_mul_self hx0.le

theorem measurable_D : Measurable D := by
  unfold D Chebyshev.psi
  fun_prop

theorem D_bound {x : ℝ} (hx : 1 ≤ x) :
    |D x| ≤ 2 * (Real.log 4 + 4) := by
  have he : |E₁Λ x| ≤ Real.log 4 + 4 := sum_mangoldt_div_eq_log hx
  have hp := psi_ratio_bound hx
  unfold D
  calc
    _ ≤ |E₁Λ x| + |Chebyshev.psi x / x| := by
      simpa only [sub_eq_add_neg, abs_neg] using
        abs_add_le (E₁Λ x) (-(Chebyshev.psi x / x))
    _ ≤ 2 * (Real.log 4 + 4) := by linarith

theorem integrableOn_psi_ratio_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => (Chebyshev.psi x / x) * x ^ (-s)) (Ioi 1) := by
  have hg : IntegrableOn (fun x : ℝ => (Real.log 4 + 4) * x ^ (-s)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one).const_mul _
  have hm : Measurable (fun x : ℝ => Chebyshev.psi x / x) := by
    unfold Chebyshev.psi
    fun_prop
  apply hg.mono' (hm.mul (measurable_id.pow_const (-s))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  change ‖(Chebyshev.psi x / x) * x ^ (-s)‖ ≤ (Real.log 4 + 4) * x ^ (-s)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
  exact mul_le_mul_of_nonneg_right (psi_ratio_bound hx.le) (Real.rpow_nonneg hx0.le _)

theorem logDeriv_eq_psi_integral {s : ℝ} (hs : 1 < s) :
    -(logDeriv riemannZeta (s : ℂ)).re =
      s * ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x / x) * x ^ (-s) := by
  have h := LSeries_eq_mul_integral_of_nonneg (fun n : ℕ => (Λ n : ℝ))
    (r := 1) (s := (s : ℂ)) (by norm_num) (by simpa using hs)
    sum_mangoldt_isBigO (fun n => ArithmeticFunction.vonMangoldt_nonneg)
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (by simpa using hs)] at h
  have hi :
      (∫ t in Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (Λ k : ℂ)) * (t : ℂ) ^ (-((s : ℂ) + 1))) =
        ((∫ t in Ioi (1 : ℝ), (Chebyshev.psi t / t) * t ^ (-s) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    change (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, (Λ k : ℂ)) *
        (t : ℂ) ^ (-((s : ℂ) + 1)) =
      (((Chebyshev.psi t / t) * t ^ (-s) : ℝ) : ℂ)
    rw [show -((s : ℂ) + 1) = ((-s - 1 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow ht0.le, ← Complex.ofReal_sum, ← Complex.ofReal_mul,
      sum_Icc_mangoldt, Real.rpow_sub_one ht0.ne']
    congr 1
    ring
  rw [hi, neg_div, ← logDeriv_apply] at h
  have hr := congrArg Complex.re h
  simpa using hr

/-- This averaged psi identity requires only Chebyshev's upper bound. -/
theorem psi_abel_identity {s : ℝ} (hs : 1 < s) :
    (s - 1) * (∫ x in Ioi (1 : ℝ), (Chebyshev.psi x / x) * x ^ (-s)) =
      -((s - 1) / s) * (logDeriv riemannZeta (s : ℂ)).re := by
  have h := logDeriv_eq_psi_integral hs
  have hn : s ≠ 0 := by linarith
  have he : (∫ x in Ioi (1 : ℝ), (Chebyshev.psi x / x) * x ^ (-s)) =
      -(logDeriv riemannZeta (s : ℂ)).re / s := by
    apply (eq_div_iff hn).mpr
    nlinarith
  rw [he]
  ring

theorem integrableOn_D_mul_rpow {s : ℝ} (hs : 1 < s) :
    IntegrableOn (fun x : ℝ => D x * x ^ (-s)) (Ioi 1) := by
  have heq : (fun x : ℝ => D x * x ^ (-s)) =
      (fun x : ℝ => E₁Λ x * x ^ (-s)) -
        (fun x : ℝ => (Chebyshev.psi x / x) * x ^ (-s)) := by
    funext x
    change (E₁Λ x - Chebyshev.psi x / x) * x ^ (-s) =
      E₁Λ x * x ^ (-s) - (Chebyshev.psi x / x) * x ^ (-s)
    ring
  rw [heq]
  exact (integrableOn_error_mul_rpow hs).sub (integrableOn_psi_ratio_mul_rpow hs)

/-- Normalization-ready form: the Laurent remainder tends to `γ`, so the
right-hand side tends to `-γ-1`. No pointwise psi asymptotic is needed. -/
theorem D_abel_identity {s : ℝ} (hs : 1 < s) :
    (s - 1) * (∫ x in Ioi (1 : ℝ), D x * x ^ (-s)) =
      -((logDeriv riemannZeta (s : ℂ)).re + 1 / (s - 1) + 1) / s := by
  have he := error_abel_identity hs
  have hp := psi_abel_identity hs
  have hi : (∫ x in Ioi (1 : ℝ), D x * x ^ (-s)) =
      (∫ x in Ioi (1 : ℝ), E₁Λ x * x ^ (-s)) -
        ∫ x in Ioi (1 : ℝ), (Chebyshev.psi x / x) * x ^ (-s) := by
    have heq : (fun x : ℝ => D x * x ^ (-s)) =
        (fun x : ℝ => E₁Λ x * x ^ (-s) - (Chebyshev.psi x / x) * x ^ (-s)) := by
      funext x
      change (E₁Λ x - Chebyshev.psi x / x) * x ^ (-s) =
        E₁Λ x * x ^ (-s) - (Chebyshev.psi x / x) * x ^ (-s)
      ring
    rw [heq]
    exact integral_sub (integrableOn_error_mul_rpow hs) (integrableOn_psi_ratio_mul_rpow hs)
  rw [hi, mul_sub, he, hp]
  have hs0 : s ≠ 0 := by linarith
  have hs1 : s - 1 ≠ 0 := by linarith
  field_simp [hs0, hs1]
  ring

end TernaryGoldbach.RSBounds.MertensPsiAbel
