import RSBounds.RS75RealAxisLogDerivative
import RSBounds.SmallTotientProduct
import RSBounds.PolynomialZeroCountBridge
import TernaryGoldbach.Explicit.ZeroFreeRegion

/-!
# The reciprocal-square zero sum used by Schoenfeld's Theorem 11

Every finite sum below is over actual zeros and keeps their analytic
multiplicities. The proof uses the certified height-100 zero table, the
existing xi partial-fraction approximation and its exact value at one.
There is no finite-RH or zero-count hypothesis.

The elementary comparison factor `1.0013` allows for replacing the paired
xi kernel by the reciprocal square of the ordinate. Below height 100 all
zeros lie on the critical line; above it the full open critical strip
suffices. This gives the classical all-ordinate bound `0.0463`.
-/

open Complex Set Filter Finset
open scoped Real Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.SchoenfeldReciprocalSquare

open TernaryGoldbach.Explicit RS75XiIncrement BacklundCountIdentity
open PolynomialZeroCountBridge ZetaZeroTable

/-- The sum of the two nonnegative real kernels at the endpoints zero and one. -/
noncomputable def pairedKernel (ρ : ℂ) : ℝ := kernel 1 ρ - kernel 0 ρ

theorem pairedKernel_eq (ρ : ℂ) :
    pairedKernel ρ = (1 - ρ.re) / ((1 - ρ.re) ^ 2 + ρ.im ^ 2) +
      ρ.re / (ρ.re ^ 2 + ρ.im ^ 2) := by
  rw [pairedKernel, kernel_eq, kernel_eq]
  ring

theorem pairedKernel_nonneg {ρ : ℂ} (hρ : xiF ρ = 0) :
    0 ≤ pairedKernel ρ := by
  have hr := xiF_zero_re_strip hρ
  rw [pairedKernel_eq]
  exact add_nonneg (div_nonneg (by linarith) (by positivity))
    (div_nonneg hr.1.le (by positivity))

theorem xi_zero_re_eq_half_of_height_le100 {ρ : ℂ} (hρ : xiF ρ = 0)
    (h100 : |ρ.im| ≤ 100) : ρ.re = 1 / 2 := by
  have hpos : ∀ {z : ℂ}, xiF z = 0 → 0 < z.im → z.im ≤ 100 → z.re = 1 / 2 := by
    intro z hz hi hu
    have hs := xiF_zero_re_strip hz
    obtain ⟨i, he⟩ := first29.complete z ((xiF_eq_zero_iff hs.1 hs.2).mp hz) hi hu
    simp [he]
  rcases lt_or_gt_of_ne (xiF_zero_im_ne_zero hρ) with hn | hp
  · have hz : xiF (conj ρ) = 0 := by rw [xiF_conj, hρ, map_zero]
    have he := hpos hz (by simpa using neg_pos.mpr hn)
      (by simpa [abs_of_neg hn] using h100)
    simpa using he
  · exact hpos hρ hp (by simpa [abs_of_pos hp] using h100)

private theorem paired_fraction_lower {β t c : ℝ}
    (hb : 0 ≤ β) (hb1 : β ≤ 1) (ht : t ≠ 0)
    (hbc : β ^ 2 ≤ c) (h1c : (1 - β) ^ 2 ≤ c) :
    1 / (c + t ^ 2) ≤
      (1 - β) / ((1 - β) ^ 2 + t ^ 2) + β / (β ^ 2 + t ^ 2) := by
  have h1 : 0 < (1 - β) ^ 2 + t ^ 2 := by positivity
  have h0 : 0 < β ^ 2 + t ^ 2 := by positivity
  calc
    _ = (1 - β) / (c + t ^ 2) + β / (c + t ^ 2) := by ring
    _ ≤ _ := add_le_add
      (div_le_div_of_nonneg_left (by linarith) h1 (by linarith))
      (div_le_div_of_nonneg_left hb h0 (by linarith))

/-- The critical line is needed only through the already certified height 100. -/
theorem reciprocal_square_le_pairedKernel {ρ : ℂ} (hρ : xiF ρ = 0) :
    1 / ρ.im ^ 2 ≤ 1.0013 * pairedKernel ρ := by
  have hr := xiF_zero_re_strip hρ
  have ht := xi_zero_height_lower hρ
  have hn := xiF_zero_im_ne_zero hρ
  have ht2 : 14.13 ^ 2 < ρ.im ^ 2 := by nlinarith [sq_abs ρ.im]
  rw [pairedKernel_eq]
  by_cases h100 : |ρ.im| ≤ 100
  · have hb := xi_zero_re_eq_half_of_height_le100 hρ h100
    have hk := paired_fraction_lower hr.1.le hr.2.le hn
      (c := 1 / 4) (by rw [hb]; norm_num) (by rw [hb]; norm_num)
    calc
      _ ≤ 1.0013 * (1 / (1 / 4 + ρ.im ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (sq_pos_of_ne_zero hn) (by positivity)]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (by norm_num)
  · have ht100 : 10000 < ρ.im ^ 2 := by
      have ha : 100 < |ρ.im| := lt_of_not_ge h100
      nlinarith [sq_abs ρ.im]
    have hbprod : 0 ≤ ρ.re * (1 - ρ.re) :=
      mul_nonneg hr.1.le (by linarith)
    have hk := paired_fraction_lower hr.1.le hr.2.le hn
      (c := 1) (by nlinarith [hbprod]) (by nlinarith [hbprod])
    calc
      _ ≤ 1.0013 * (1 / (1 + ρ.im ^ 2)) := by
        rw [mul_one_div, div_le_div_iff₀ (sq_pos_of_ne_zero hn) (by positivity)]
        nlinarith
      _ ≤ _ := mul_le_mul_of_nonneg_left hk (by norm_num)

/-- Exact xi normalization, using Mathlib's digamma value at one half. -/
theorem twice_re_logDeriv_xi_one :
    2 * (logDeriv xiF 1).re =
      2 + Real.eulerMascheroniConstant - Real.log Real.pi - 2 * Real.log 2 := by
  have he := RS75RealAxisLogDerivative.re_logDeriv_xiF_real (s := 1) le_rfl
  rw [Complex.ofReal_one, RS75RealAxisLogDerivative.logDeriv_zetaF_one,
    Complex.ofReal_re] at he
  unfold RS75RealAxisGamma.gammaAxis at he
  rw [Complex.ofReal_one, Complex.digamma_one_half] at he
  have hlogtwo : Complex.log (2 : ℂ) = (Real.log (2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_ofNat] using
      (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlogtwo] at he
  norm_num [Complex.mul_re] at he
  have hrelogtwo := congrArg Complex.re hlogtwo
  simp only [Complex.ofReal_re] at hrelogtwo
  rw [hrelogtwo] at he
  linarith

theorem normalized_allowance_lt :
    1.0013 * (2 * (logDeriv xiF 1).re) < 0.0463 := by
  rw [twice_re_logDeriv_xi_one]
  have hg := SmallTotientProduct.gamma_bounds.2
  have hp := log_pi_ge
  have h2 := Real.log_two_gt_d9
  linarith

/-- The square approximation multiplicity is the actual analytic order. -/
theorem mult_sqZeros_eq_order {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ sqZeros T) :
    mult T ρ = (analyticOrderAt xiF ρ).toNat := by
  have hn := (mem_zerosIn (Finset.mem_filter.mp hρ).1).1
  have hm : ρ ∈ Metric.closedBall (1 / 2 : ℂ) (6 * T) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [norm_nonneg (ρ - 1 / 2)]
  rw [mult, divB, MeromorphicOn.AnalyticOnNhd.divisor_apply
    (fun z _ => differentiable_xiF.analyticAt z :
      AnalyticOnNhd ℂ xiF (Metric.closedBall (1 / 2) (6 * T))) hm]
  cases ho : analyticOrderAt xiF ρ <;> simp

/-- Any finite multiplicity-weighted paired-kernel sum is bounded by xi at one. -/
theorem finite_pairedKernel_sum_le (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, xiF ρ = 0) :
    (∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) * pairedKernel ρ) ≤
      2 * (logDeriv xiF 1).re := by
  classical
  let M : ℝ := 1 + ∑ ρ ∈ S, ‖ρ - 1 / 2‖
  have hM : 1 ≤ M := by
    have hn : 0 ≤ ∑ ρ ∈ S, ‖ρ - 1 / 2‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    dsimp [M]
    linarith
  have hnorm : ∀ ρ ∈ S, ‖ρ - 1 / 2‖ ≤ M := by
    intro ρ hρ
    have he : ‖ρ - 1 / 2‖ ≤ ∑ z ∈ S, ‖z - 1 / 2‖ :=
      Finset.single_le_sum (fun z _ => norm_nonneg (z - 1 / 2)) hρ
    dsimp [M]
    linarith
  apply le_of_forall_pos_lt_add
  intro ε hε
  obtain ⟨T, _, happrox, hmem, hzero⟩ :=
    xi_partial_approx (M := M) (ε := ε / 4) (by linarith) (by positivity)
  have ha1 := approx_re (s := 1) (happrox 1
    (by norm_num; linarith) (by rw [xiF_one]; norm_num))
  have ha0 := approx_re (s := 0) (happrox 0
    (by norm_num; linarith) (by rw [xiF_zero]; norm_num))
  have hsub : S ⊆ sqZeros T := fun ρ hρ => (hmem ρ (hS ρ hρ) (hnorm ρ hρ)).1
  have hw : (∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) * pairedKernel ρ) ≤
      ∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * pairedKernel ρ := by
    calc
      _ = ∑ ρ ∈ S, (mult T ρ : ℝ) * pairedKernel ρ := by
        apply Finset.sum_congr rfl
        intro ρ hρ
        rw [mult_sqZeros_eq_order (hsub hρ)]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun ρ hρ _ => mul_nonneg (Nat.cast_nonneg _) (pairedKernel_nonneg (hzero ρ hρ)))
  have he : (∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * pairedKernel ρ) =
      (∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * kernel 1 ρ) -
        ∑ ρ ∈ sqZeros T, (mult T ρ : ℝ) * kernel 0 ρ := by
    simp only [pairedKernel, mul_sub, Finset.sum_sub_distrib]
  rw [he] at hw
  have hzeroXi : logDeriv xiF 0 = -logDeriv xiF 1 := by
    simpa using logDeriv_xiF_one_sub 1
  simp only [Complex.ofReal_zero, Complex.ofReal_one] at ha0 ha1
  rw [hzeroXi, Complex.neg_re] at ha0
  have h1 := (abs_le.mp ha1).1
  have h0 := (abs_le.mp ha0).2
  linarith

/-- The common upper bound is independent of the chosen finite zero set. -/
theorem finite_xi_reciprocal_square_sum_le (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, xiF ρ = 0) :
    (∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) / ρ.im ^ 2) ≤
      1.0013 * (2 * (logDeriv xiF 1).re) := by
  have hc : (∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) / ρ.im ^ 2) ≤
      1.0013 * ∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) * pairedKernel ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    have hh := mul_le_mul_of_nonneg_left (reciprocal_square_le_pairedKernel (hS ρ hρ))
      (Nat.cast_nonneg (analyticOrderAt xiF ρ).toNat : (0 : ℝ) ≤ _)
    convert hh using 1 <;> ring
  exact hc.trans (mul_le_mul_of_nonneg_left (finite_pairedKernel_sum_le S hS)
    (by norm_num))

/-- Rosser's reciprocal-square allowance, for arbitrary actual finite zero sets. -/
theorem finite_xi_reciprocal_square_sum_lt (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, xiF ρ = 0) :
    (∑ ρ ∈ S, ((analyticOrderAt xiF ρ).toNat : ℝ) / ρ.im ^ 2) < 0.0463 :=
  (finite_xi_reciprocal_square_sum_le S hS).trans_lt normalized_allowance_lt

/-- The same finite bound, expressed using zeta's analytic multiplicity. -/
theorem finite_zeta_reciprocal_square_sum_lt (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, xiF ρ = 0) :
    (∑ ρ ∈ S, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) / ρ.im ^ 2) < 0.0463 := by
  convert finite_xi_reciprocal_square_sum_lt S hS using 1
  apply Finset.sum_congr rfl
  intro ρ hρ
  rw [analyticOrderAt_xi_eq_zeta (hS ρ hρ)]

end TernaryGoldbach.RSBounds.SchoenfeldReciprocalSquare
