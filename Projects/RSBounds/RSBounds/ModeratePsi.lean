import RSBounds.PolynomialZeroPairing
import RSBounds.PolynomialZeroMajorants
import RSBounds.RosserWeightedBounds
import RSBounds.RosserCubicTail
import RSBounds.ZeroWindowFiniteSum
import RSBounds.ZetaZeroHeadBound
import RSBounds.PolynomialPsiFromZeroSums
import RSBounds.BacklundLowScalarBase
import RSBounds.Targets

/-!
# A moderate-range psi estimate from the checked quartic formula

The final theorem has the explicit premise FiniteRH1894439 and holds for
all x≥100000. The smoothing step is .001. The analytic ingredients are
reused from the quartic formula, the proved Rosser count, and the certified
first29 zeros. No quantitative zero-free region or PNT premise occurs.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

open Complex Set MeasureTheory Finset Filter
open scoped Real Interval Topology ComplexConjugate

namespace TernaryGoldbach.RSBounds.PolynomialRemainderFlexibleStep

open TernaryGoldbach.Explicit PolynomialAveraged PolynomialLeftRemainder
open PolynomialRemainderIntegral PolynomialLeftKernel PolynomialRemainderMajorant

/- The fixed scalar majorant remains unchanged; only its application to the
actual smoothing step is parameterized. -/

theorem norm_averagedIntegrand_le_majorant {x y δ : ℝ} (hx : 0 < x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) (hcut : 1 / δ ≤ cutoff)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) (t : ℝ) :
    ‖logDeriv riemannZeta (leftLine t) *
        zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * majorant t := by
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hlo := norm_zeroCoefficient_left_low hx
    hδ hδ1
    hy0 hy1 (leftLine_re t)
  have hld := norm_logDeriv_zeta_left_log t
  change ‖logDeriv riemannZeta (leftLine t)‖ ≤
    340 + 80 * Real.log (max 1 |t|) at hld
  have hn0 : 0 < ‖leftLine t‖ := by
    have hh := Complex.abs_re_le_norm (leftLine t)
    rw [leftLine_re] at hh
    norm_num at hh
    linarith
  have hhalf : (1 / 2 : ℝ) ≤ ‖leftLine t‖ := by
    have hh := Complex.abs_re_le_norm (leftLine t)
    rw [leftLine_re] at hh
    norm_num at hh
    exact hh
  have htNorm : |t| ≤ ‖leftLine t‖ := by
    simpa [leftLine] using Complex.abs_im_le_norm (leftLine t)
  rw [norm_mul]
  by_cases ht1 : |t| ≤ 1
  · have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 340 := by
      simpa only [max_eq_left ht1, Real.log_one, mul_zero, add_zero] using hld
    have hk : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
        x ^ (-1 / 2 : ℝ) * 2.2 := by
      refine hlo.trans (mul_le_mul_of_nonneg_left ?_ hxp)
      rw [div_le_iff₀ hn0]
      nlinarith
    have he : majorant t = 748 := by simp [majorant, positiveMajorant, ht1]
    rw [he]
    calc
      _ ≤ 340 * (x ^ (-1 / 2 : ℝ) * 2.2) :=
        mul_le_mul hd hk (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  · have htpos : 0 < |t| := by linarith
    have htgt : 1 < |t| := lt_of_not_ge ht1
    rw [max_eq_right htgt.le] at hld
    by_cases htD : |t| ≤ cutoff
    · have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 1300 := by
        have hl := (Real.log_le_log htpos htD).trans log_cutoff_le
        linarith
      have hk : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
          x ^ (-1 / 2 : ℝ) * (1.1 / |t|) := by
        exact hlo.trans (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left (by norm_num) htpos htNorm) hxp)
      have he : majorant t = 1430 / |t| := by
        simp [majorant, positiveMajorant, ht1, htD]
      rw [he]
      calc
        _ ≤ 1300 * (x ^ (-1 / 2 : ℝ) * (1.1 / |t|)) :=
          mul_le_mul hd hk (norm_nonneg _) (by norm_num)
        _ = _ := by ring
    · have hD : (0 : ℝ) < cutoff := by norm_num [cutoff]
      have hratio : 0 < |t| / cutoff := div_pos htpos hD
      have hl : Real.log |t| ≤ 12 + |t| / cutoff := by
        have he := Real.log_div htpos.ne' hD.ne'
        have hh := Real.log_le_sub_one_of_pos hratio
        linarith [log_cutoff_le]
      have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 1300 + 80 * |t| / cutoff := by
        calc
          _ ≤ 340 + 80 * (12 + |t| / cutoff) := by linarith
          _ = _ := by ring
      have htim : (leftLine t).im ≠ 0 := by
        simpa [leftLine] using (abs_pos.mp htpos)
      have hi := norm_zeroCoefficient_left_high hx
        hδ hδ1
        hy0 hy1 (leftLine_re t) htim
      have hi' : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
          x ^ (-1 / 2 : ℝ) * (19 * cutoff ^ 4 / |t| ^ 5) := by
        have hc : (1 : ℝ) / δ ^ 4 ≤ cutoff ^ 4 := by
          simpa only [div_pow, one_pow] using pow_le_pow_left₀ (by positivity) hcut 4
        refine hi.trans (mul_le_mul_of_nonneg_left ?_ hxp)
        simp only [leftLine, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
          Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, zero_mul,
          add_zero, zero_add]
        calc
          19 / (δ ^ 4 * |t| ^ 5) =
              19 * (1 / δ ^ 4) / |t| ^ 5 := by ring
          _ ≤ 19 * cutoff ^ 4 / |t| ^ 5 := by gcongr
      have he : majorant t =
          19 * cutoff ^ 4 * (1300 + 80 * |t| / cutoff) / |t| ^ 5 := by
        simp [majorant, positiveMajorant, tail, ht1, htD]
      rw [he]
      calc
        _ ≤ (1300 + 80 * |t| / cutoff) *
            (x ^ (-1 / 2 : ℝ) * (19 * cutoff ^ 4 / |t| ^ 5)) :=
          mul_le_mul hd hi' (norm_nonneg _) (by positivity)
        _ = _ := by ring

theorem norm_leftRemainder_le {x y δ : ℝ} (hx : 0 < x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) (hcut : 1 / δ ≤ cutoff)
    (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤
      25000 / (Real.pi * x ^ (1 / 2 : ℝ)) := by
  have hy : 0 < y := by linarith
  have hh : 0 < δ * x := mul_pos hδ hx
  have hxp : 0 ≤ x ^ (-1 / 2 : ℝ) := Real.rpow_nonneg hx.le _
  have hi := integrable_averagedIntegrand (mul_pos hx hy) hh
  have hmaj := integrable_majorant.const_mul (x ^ (-1 / 2 : ℝ))
  have hnorm : ‖∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
      zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      x ^ (-1 / 2 : ℝ) * 50000 := by
    calc
      _ ≤ ∫ t : ℝ, ‖logDeriv riemannZeta (leftLine t) *
          zeroCoefficient (x * y) (δ * x) (leftLine t)‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ t : ℝ, x ^ (-1 / 2 : ℝ) * majorant t :=
        integral_mono hi.norm hmaj (norm_averagedIntegrand_le_majorant hx hδ hδ1 hcut hy0 hy1)
      _ = x ^ (-1 / 2 : ℝ) * ∫ t : ℝ, majorant t := integral_const_mul _ _
      _ ≤ x ^ (-1 / 2 : ℝ) * 50000 := mul_le_mul_of_nonneg_left integral_majorant_le hxp
  rw [leftRemainder_eq_integral (mul_pos hx hy) hh, norm_mul]
  have hfac : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hfac]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (x ^ (-1 / 2 : ℝ) * 50000) :=
      mul_le_mul_of_nonneg_left hnorm (by positivity)
    _ = 25000 / (Real.pi * x ^ (1 / 2 : ℝ)) := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le]
      ring


end TernaryGoldbach.RSBounds.PolynomialRemainderFlexibleStep

namespace TernaryGoldbach.RSBounds.ModeratePsiScalars

open BacklundLowScalar RosserWeightedBounds RosserTailIntegrals

private theorem certified_log_bounds (c : LogCert) (hc : c.Valid)
    {q l u : ℚ} (hq : c.ratio = q) (hl : l ≤ c.lower) (hu : c.upper ≤ u) :
    (l : ℝ) ≤ Real.log (q : ℝ) ∧ Real.log (q : ℝ) ≤ (u : ℝ) := by
  have hb := LogCert.log_bounds hc
  rw [hq] at hb
  have hl' : (l : ℝ) ≤ (c.lower : ℝ) := by exact_mod_cast hl
  have hu' : (c.upper : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
  exact ⟨hl'.trans hb.1, hb.2.trans hu'⟩

private theorem log_hundred_bounds :
    (4.6 : ℝ) ≤ Real.log (100 : ℝ) ∧ Real.log (100 : ℝ) ≤ 4.61 := by
  have h := certified_log_bounds (c := ⟨6, 16, 9⟩)
    (by decide) (q := 100) (l := 4.6) (u := 4.61)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_twothousand_bounds :
    (7.6 : ℝ) ≤ Real.log (2000 : ℝ) ∧ Real.log (2000 : ℝ) ≤ 7.61 := by
  have h := certified_log_bounds (c := ⟨10, 64, 61⟩)
    (by decide) (q := 2000) (l := 7.6) (u := 7.61)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_ratio_hundred_lower :
    (2.76 : ℝ) ≤ Real.log ((62500/3927) : ℝ) ∧ Real.log ((62500/3927) : ℝ) ≤ 2.77 := by
  have h := certified_log_bounds (c := ⟨3, 7854, 7771⟩)
    (by decide) (q := (62500/3927)) (l := 2.76) (u := 2.77)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_ratio_hundred_upper :
    (2.76 : ℝ) ≤ Real.log ((2500/157) : ℝ) ∧ Real.log ((2500/157) : ℝ) ≤ 2.77 := by
  have h := certified_log_bounds (c := ⟨3, 314, 311⟩)
    (by decide) (q := (2500/157)) (l := 2.76) (u := 2.77)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_ratio_twothousand_upper :
    (5.76 : ℝ) ≤ Real.log ((50000/157) : ℝ) ∧ Real.log ((50000/157) : ℝ) ≤ 5.77 := by
  have h := certified_log_bounds (c := ⟨8, 2512, 613⟩)
    (by decide) (q := (50000/157)) (l := 5.76) (u := 5.77)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_461_bounds :
    (1.52 : ℝ) ≤ Real.log (4.61 : ℝ) ∧ Real.log (4.61 : ℝ) ≤ 1.53 := by
  have h := certified_log_bounds (c := ⟨2, 400, 61⟩)
    (by decide) (q := 4.61) (l := 1.52) (u := 1.53)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

private theorem log_761_bounds :
    (2.02 : ℝ) ≤ Real.log (7.61 : ℝ) ∧ Real.log (7.61 : ℝ) ≤ 2.04 := by
  have h := certified_log_bounds (c := ⟨2, 400, 361⟩)
    (by decide) (q := 7.61) (l := 2.02) (u := 2.04)
    (by norm_num [LogCert.ratio]) (by decide +kernel) (by decide +kernel)
  convert h using 1 <;> norm_num

theorem log_hundred_two_pi_bounds :
    (2.76 : ℝ) ≤ Real.log (100 / (2 * Real.pi)) ∧
      Real.log (100 / (2 * Real.pi)) ≤ 2.77 := by
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · have h := Real.log_le_log (by norm_num : (0 : ℝ) < 100 / 6.2832)
      (div_le_div_of_nonneg_left (by norm_num) hp (by linarith [Real.pi_lt_d4]))
    have hh := log_ratio_hundred_lower.1
    norm_num at h hh ⊢
    exact hh.trans h
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < 100 / (2 * Real.pi))
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 6.28)
        (by linarith [Real.pi_gt_d2]))
    have hh := log_ratio_hundred_upper.2
    norm_num at h hh ⊢
    exact h.trans hh

theorem log_twothousand_two_pi_bounds :
    0 ≤ Real.log (2000 / (2 * Real.pi)) ∧
      Real.log (2000 / (2 * Real.pi)) ≤ 5.77 := by
  have hp : 0 < 2 * Real.pi := by positivity
  constructor
  · apply Real.log_nonneg
    rw [le_div_iff₀ hp]
    linarith [Real.pi_lt_four]
  · have h := Real.log_le_log (by positivity : (0 : ℝ) < 2000 / (2 * Real.pi))
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0 : ℝ) < 6.28)
        (by linarith [Real.pi_gt_d2]))
    have hh := log_ratio_twothousand_upper.2
    norm_num at h hh ⊢
    exact h.trans hh

theorem low_integral_le : I 100 2000 ≤ 2.1 := by
  have hD := log_hundred_two_pi_bounds
  have hY := log_twothousand_two_pi_bounds
  have hlog := log_hundred_bounds.1
  have hnum : Real.log (2000 / (2 * Real.pi)) ^ 2 -
      Real.log (100 / (2 * Real.pi)) ^ 2 ≤ (5.77 : ℝ) ^ 2 - 2.76 ^ 2 := by
    have hys := pow_le_pow_left₀ hY.1 hY.2 2
    have hds := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.76) hD.1 2
    linarith
  have hfirst :
      (Real.log (2000 / (2 * Real.pi)) ^ 2 - Real.log (100 / (2 * Real.pi)) ^ 2) /
        (4 * Real.pi) ≤ ((5.77 : ℝ) ^ 2 - 2.76 ^ 2) / (4 * 3.14) := by
    exact (div_le_div_of_nonneg_right hnum (by positivity)).trans
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by linarith [Real.pi_gt_d2]))
  have hc : (0.137 : ℝ) + 0.443 / Real.log 100 ≤ 0.137 + 0.443 / 4.6 := by
    exact add_le_add le_rfl
      (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog)
  have hsecond := mul_le_mul_of_nonneg_right hc
    (by norm_num : (0 : ℝ) ≤ 1 / 100 - 1 / 2000)
  unfold RosserWeightedBounds.I
  linarith

theorem head_correction_le : (G 100 - 29) / 100 ≤ 0.03 := by
  have hlog := log_hundred_bounds
  have hloglog : Real.log (Real.log (100 : ℝ)) ≤ 1.53 :=
    (Real.log_le_log (by linarith : 0 < Real.log (100 : ℝ)) hlog.2).trans
      (by simpa using log_461_bounds.2)
  have hR : rosserR 1.588 100 ≤ 0.137 * 4.61 + 0.443 * 1.53 + 1.588 := by
    unfold rosserR
    linarith
  have hl := log_hundred_two_pi_bounds
  have hq : (100 : ℝ) / (2 * Real.pi) ≤ 100 / (2 * 3.14) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_d2])
  have hF : rosserF 100 ≤ (100 / (2 * 3.14)) * (2.77 - 1) + 7 / 8 := by
    unfold rosserF
    calc
      _ = (100 / (2 * Real.pi)) * (Real.log (100 / (2 * Real.pi)) - 1) + 7 / 8 := by ring
      _ ≤ _ := add_le_add
        (mul_le_mul hq (sub_le_sub_right hl.2 1)
          (by linarith [hl.1]) (by norm_num : (0 : ℝ) ≤ 100 / (2 * 3.14))) le_rfl
  unfold G
  linarith

theorem middle_fifth_allowance_le :
    (17000000000000 : ℝ) * (J 2000 + 2 * rosserR 1.588 2000 / 2000 ^ 5) ≤ 0.27 := by
  have hlog := log_twothousand_bounds
  have hloglog : Real.log (Real.log (2000 : ℝ)) ≤ 2.04 :=
    (Real.log_le_log (by linarith : 0 < Real.log (2000 : ℝ)) hlog.2).trans
      (by simpa using log_761_bounds.2)
  have hR : rosserR 1.588 2000 ≤ 0.137 * 7.61 + 0.443 * 2.04 + 1.588 := by
    unfold rosserR
    linarith
  have hl := log_twothousand_two_pi_bounds
  have hJ : J 2000 ≤
      (5.77 / 4 + 1 / 16) / (2 * 3.14 * (2000 : ℝ) ^ 4) +
      0.137 / (5 * 2000 ^ 5) + 0.443 / (5 * 2000 ^ 5 * 7.6) := by
    unfold J
    apply add_le_add
    · apply add_le_add ?_ le_rfl
      exact (div_le_div_of_nonneg_right
        (by linarith : Real.log (2000 / (2 * Real.pi)) / 4 + 1 / 16 ≤ 5.77 / 4 + 1 / 16)
        (by positivity)).trans
        (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
          (by nlinarith [Real.pi_gt_d2]))
    · exact div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (by nlinarith [hlog.1])
  have ht := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num : (0 : ℝ) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 2000 ^ 5)
  nlinarith only [hJ, ht]

theorem log_two_pi_le_three : Real.log (2 * Real.pi) ≤ 3 := by
  have h := Real.log_le_log (by positivity : (0 : ℝ) < 2 * Real.pi)
    (by linarith [Real.pi_lt_four] : 2 * Real.pi ≤ (2 : ℝ) ^ 3)
  rw [Real.log_pow] at h
  have htwo := Real.log_two_lt_d9
  norm_num only [Nat.cast_ofNat] at h
  linarith

end TernaryGoldbach.RSBounds.ModeratePsiScalars

namespace TernaryGoldbach.RSBounds.ModeratePsi

open TernaryGoldbach.Explicit BacklundCountIdentity WeightedZetaZeros
open PolynomialExplicit PolynomialZeroKernel PolynomialAveraged PolynomialKernelScaling
open PolynomialLowerKernel RosserWeightedBounds

def delta : ℝ := 0.001

def C : ℝ := 17000000000000

theorem delta_pos : 0 < delta := by norm_num [delta]
theorem delta_small : delta ≤ 0.01 := by norm_num [delta]
theorem four_mul_delta_lt_one : 4 * delta < 1 := by norm_num [delta]
theorem C_nonneg : 0 ≤ C := by norm_num [C]
theorem kernel_constant_le : R4 delta / delta ^ 4 ≤ C := by norm_num [R4, delta, C]

noncomputable def coefficient (lower : Bool) (x : ℝ) (ρ : ℂ) : ℂ :=
  zeroCoefficient (if lower then x - 4 * (delta * x) else x) (delta * x) ρ

noncomputable def normalizedKernel (lower : Bool) (ρ : ℂ) : ℂ :=
  if lower then
    forwardDiff delta 4 (antiderivative ρ 4) (1 - 4 * delta) / (delta : ℂ) ^ 4
  else upperKernel delta ρ

theorem coefficient_eq (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    coefficient lower x ρ = (x : ℂ) ^ ρ * normalizedKernel lower ρ := by
  cases lower with
  | false => simpa [coefficient, normalizedKernel] using zeroCoefficient_upper hx delta_pos ρ
  | true => simpa [coefficient, normalizedKernel] using
      zeroCoefficient_lower hx delta_pos four_mul_delta_lt_one ρ

theorem norm_coefficient_conj (lower : Bool) {x : ℝ} (hx : 0 < x) (ρ : ℂ) :
    ‖coefficient lower x (conj ρ)‖ = ‖coefficient lower x ρ‖ := by
  have ht : 0 < (if lower then x - 4 * (delta * x) else x) := by
    split_ifs
    · have hp := mul_pos hx (sub_pos.mpr four_mul_delta_lt_one)
      nlinarith
    · exact hx
  unfold coefficient
  rw [PolynomialZeroMajorants.zeroCoefficient_conj ht
    (mul_nonneg delta_pos.le hx.le)]
  simp

theorem norm_coefficient_le_low (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * 1.002 / ‖ρ‖ := by
  have hn : ρ ≠ 0 := by intro h; simp [h] at hre
  have hk : ‖normalizedKernel lower ρ‖ ≤ (1 + 2 * delta) / ‖ρ‖ := by
    cases lower with
    | false =>
        exact norm_upperKernel_le_low delta_pos (by rw [hre]; norm_num)
          (by rw [hre]; norm_num)
    | true =>
        exact norm_lower_difference_le_low_common delta_pos four_mul_delta_lt_one
          (by rw [hre]; norm_num) hn
  rw [coefficient_eq lower hx, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
    hre, ← Real.sqrt_eq_rpow]
  have hh := mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg x)
  norm_num [delta] at hh
  convert hh using 1 <;> ring

theorem norm_coefficient_le_high_line (lower : Bool) {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ‖coefficient lower x ρ‖ ≤ Real.sqrt x * C / |ρ.im| ^ 5 := by
  have hk : ‖coefficient lower x ρ‖ ≤
      (R4 delta / delta ^ 4) * x ^ ρ.re / |ρ.im| ^ 5 := by
    cases lower with
    | false =>
        simpa [coefficient] using
          PolynomialZeroPairing.norm_zeroCoefficient_upper_le_high hx delta_pos
            (by rw [hre]; norm_num) him
    | true =>
        simpa [coefficient] using
          PolynomialZeroPairing.norm_zeroCoefficient_lower_le_high hx delta_pos
            four_mul_delta_lt_one (by rw [hre]; norm_num) him
  rw [hre, ← Real.sqrt_eq_rpow] at hk
  refine hk.trans ?_
  have hh := mul_le_mul_of_nonneg_right kernel_constant_le (Real.sqrt_nonneg x)
  have hd := div_le_div_of_nonneg_right hh (pow_nonneg (abs_nonneg ρ.im) 5)
  convert hd using 1 <;> ring

theorem low_zero_re {ρ : ℂ} (hRH : Goals.FiniteRH 1894439)
    (hρ : ρ ∈ closedPositiveZeros 1894439) : ρ.re = 1 / 2 := by
  obtain ⟨hz, him, hiA⟩ := (mem_closedPositiveZeros_iff (by norm_num : (0 : ℝ) < 1894439)).mp hρ
  obtain ⟨hr0, hr1⟩ := zeta_zero_re_strip hz him.ne'
  exact hRH ρ hz hr0 hr1 (by simpa only [abs_of_pos him] using hiA)

/-- A sufficient numerical bound for the actual positive-ordinate line sum. -/
theorem positive_low_sum_le (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894439) :
    (∑ ρ ∈ closedPositiveZeros 1894439,
      ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ‖coefficient lower x ρ‖) ≤ 3 * Real.sqrt x := by
  have hgeneric := ZeroWindowFiniteSum.sum_le_windows
    (D := 100) (L := 100) (U := 100) (Y := 2000) (A := 1894439)
    (s := Real.sqrt x) (k := 1.002) (C := C) (r := 1.002)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Real.sqrt_nonneg _) (by norm_num)
    (fun ρ => ‖coefficient lower x ρ‖)
    (fun ρ hρ => norm_coefficient_le_low lower hx (low_zero_re hRH hρ))
    (by
      intro ρ hρ _
      have him := ((mem_closedPositiveZeros_iff (by norm_num : (0 : ℝ) < 1894439)).mp hρ).2.1
      simpa only [abs_of_pos him] using norm_coefficient_le_high_line lower hx
        (low_zero_re hRH hρ) him.ne')
    (by intro ρ _ hlo hhi; linarith)
  simp only [sub_self, zero_mul, sub_zero] at hgeneric
  have hr := reciprocal_sum_le_head (a := 100) (b := 2000) (by norm_num) (by norm_num)
  rw [ZetaZeroTable.positiveZeroCount_hundred] at hr
  have hr' : weightedSum 100 2000 (fun t => 1 / t) ≤ 2.1 + 0.03 := by
    linarith [ModeratePsiScalars.low_integral_le, ModeratePsiScalars.head_correction_le]
  have hf := mul_le_mul_of_nonneg_left
    (fifth_sum_le (a := 2000) (b := 1894439) (by norm_num) (by norm_num)) C_nonneg
  have hf' : C * weightedSum 2000 1894439 (fun t => 1 / t ^ 5) ≤ 0.27 :=
    hf.trans ModeratePsiScalars.middle_fifth_allowance_le
  have hhead := ZetaZeroHeadBound.weighted_head_le
  change (∑ ρ ∈ closedPositiveZeros 1894439,
    ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * ‖coefficient lower x ρ‖) ≤ _ at hgeneric
  refine hgeneric.trans ?_
  have hbudget : 1.002 * (∑ ρ ∈ closedPositiveZeros 100,
        ZeroWindowFiniteSum.multiplicity ρ / ‖ρ‖) +
      1.002 * weightedSum 100 2000 (fun t => 1 / t) +
      C * weightedSum 2000 1894439 (fun t => 1 / t ^ 5) ≤ 3 := by
    change (∑ ρ ∈ closedPositiveZeros 100,
      ZeroWindowFiniteSum.multiplicity ρ / ‖ρ‖) ≤ 0.592316 at hhead
    linarith
  have hb := mul_le_mul_of_nonneg_left hbudget (Real.sqrt_nonneg x)
  convert hb using 1 <;> ring

private theorem weightedSum_const_mul (a b c : ℝ) (w : ℝ → ℝ) :
    weightedSum a b (fun t => c * w t) = c * weightedSum a b w := by
  classical
  unfold weightedSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  split_ifs <;> ring

/-- The already checked reciprocal-cube tail suffices for this fifth-power budget. -/
theorem high_fifth_le {T : ℝ} (hAT : 1894439 ≤ T) :
    C * weightedSum 1894439 T (fun t => 1 / t ^ 5) ≤ 2e-12 := by
  have hT : 0 < T := by linarith
  have hm := weightedSum_mono (a := 1894439) hT
    (φ := fun t => 1 / t ^ 5)
    (ψ := fun t => (1 / (1894439 : ℝ) ^ 2) * (1 / t ^ 3)) (by
      intro t ht
      have ht0 : 0 < t := by linarith [ht.1]
      have hsq : (1894439 : ℝ) ^ 2 ≤ t ^ 2 :=
        pow_le_pow_left₀ (by norm_num) ht.1.le 2
      calc
        1 / t ^ 5 = (1 / t ^ 3) / t ^ 2 := by field_simp [ht0.ne']
        _ ≤ (1 / t ^ 3) / (1894439 : ℝ) ^ 2 :=
          div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
        _ = _ := by ring)
  rw [weightedSum_const_mul] at hm
  have hc := RosserCubicTail.cubic_sum_A_lt hAT
  have hb := mul_le_mul_of_nonneg_left hm C_nonneg
  have hsmall := mul_le_mul_of_nonneg_left hc.le
    (show 0 ≤ C * (1 / (1894439 : ℝ) ^ 2) by unfold C; positivity)
  have hbound : C * weightedSum 1894439 T (fun t => 1 / t ^ 5) ≤
      C * (1 / (1894439 : ℝ) ^ 2) * 3e-13 := by nlinarith only [hb, hsmall]
  refine hbound.trans ?_
  norm_num [C]

private theorem fifth_nonneg {T : ℝ} (hT : 0 < T) :
    0 ≤ weightedSum 1894439 T (fun t => 1 / t ^ 5) := by
  classical
  unfold weightedSum
  apply Finset.sum_nonneg
  intro ρ hρ
  have him := ((mem_closedPositiveZeros_iff hT).mp hρ).2.1
  split_ifs <;> positivity

/-- The upper and lower high-zero contributions use no RH premise. -/
theorem norm_high_sum_le (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hAT : 1894439 < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤
      2e-12 * (x + 1) := by
  have hT : 0 < T := by linarith
  have hk :
      ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
        (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤
        (R4 delta / delta ^ 4) * (x + 1) * weightedSum 1894439 T (fun t => 1 / t ^ 5) := by
    cases lower with
    | false => simpa [coefficient] using
        PolynomialZeroPairing.norm_high_sum_upper_le hT hg hx delta_pos 1894439
    | true => simpa [coefficient] using
        PolynomialZeroPairing.norm_high_sum_lower_le hT hg hx delta_pos four_mul_delta_lt_one 1894439
  have hW := fifth_nonneg hT
  have hp : 0 ≤ x + 1 := by linarith
  have hc := mul_le_mul_of_nonneg_right kernel_constant_le (mul_nonneg hp hW)
  have hf := mul_le_mul_of_nonneg_right (high_fifth_le hAT.le) hp
  nlinarith only [hk, hc, hf]

theorem norm_low_sum_le (lower : Bool) {x T : ℝ} (hx : 0 < x)
    (hRH : Goals.FiniteRH 1894439) (hAT : 1894439 < T) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ 1894439),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ 6 * Real.sqrt x := by
  have hh := PolynomialZeroPairing.norm_low_sum_le_two_closed
    (by norm_num : (0 : ℝ) < 1894439) hAT (coefficient lower x)
    (fun ρ _ => norm_coefficient_conj lower hx ρ)
  have hp := positive_low_sum_le lower hx hRH
  linarith

/-- Uniform bounds for the actual finite complex sums, retaining all multiplicities. -/
theorem norm_sum_le (lower : Bool) {x T : ℝ} (hx : 1 ≤ x)
    (hRH : Goals.FiniteRH 1894439) (hAT : 1894439 < T) (hg : zetaGoodHeight T) :
    ‖∑ ρ ∈ zerosRectD zetaF T,
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤
      6 * Real.sqrt x + 2e-12 * (x + 1) := by
  classical
  have hlo := norm_low_sum_le lower (by linarith : 0 < x) hRH hAT
  have hhi := norm_high_sum_le lower hx hAT hg
  rw [← Finset.sum_filter_add_sum_filter_not (zerosRectD zetaF T)
    (fun ρ => |ρ.im| ≤ 1894439)]
  simp only [not_le]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

theorem norm_left_remainder_le (lower : Bool) {x : ℝ} (hx : 0 < x) :
    ‖leftRemainder (if lower then x - 4 * (delta * x) else x) (delta * x)‖ ≤
      25000 / (Real.pi * Real.sqrt x) := by
  have hcut : 1 / delta ≤ PolynomialRemainderMajorant.cutoff := by
    norm_num [delta, PolynomialRemainderMajorant.cutoff]
  cases lower with
  | false =>
      have h := PolynomialRemainderFlexibleStep.norm_leftRemainder_le
        (x := x) (y := 1) hx delta_pos delta_small hcut (by norm_num [delta]) le_rfl
      rw [← Real.sqrt_eq_rpow] at h
      simpa using h
  | true =>
      have h := PolynomialRemainderFlexibleStep.norm_leftRemainder_le
        (x := x) (y := 1 - 4 * delta) hx delta_pos delta_small hcut le_rfl (by norm_num [delta])
      rw [show x * (1 - 4 * delta) = x - 4 * (delta * x) by ring] at h
      rw [← Real.sqrt_eq_rpow] at h
      simpa using h

theorem remainder_and_log_le {x : ℝ} (hx : 100000 ≤ x) :
    25000 / (Real.pi * Real.sqrt x) + Real.log (2 * Real.pi) ≤ 0.000295 * x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 316 ≤ Real.sqrt x := (Real.le_sqrt (by norm_num) hx0).mpr (by nlinarith)
  have hden : (3 : ℝ) * 316 ≤ Real.pi * Real.sqrt x := by
    have hp := mul_le_mul (show (3 : ℝ) ≤ Real.pi by linarith [Real.pi_gt_three]) hs
      (by norm_num) Real.pi_pos.le
    exact hp
  have hb := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 25000)
    (by norm_num : (0 : ℝ) < 3 * 316) hden
  have hl := ModeratePsiScalars.log_two_pi_le_three
  linarith

/-- A moderate-error estimate for every x≥100000. The only hypothesis beyond
this range is finite RH through height1894439; no PNT/ZFR estimate is assumed. -/
theorem psi_error_le (hRH : Goals.FiniteRH 1894439) {x : ℝ} (hx : 100000 ≤ x) :
    |Chebyshev.psi x - x| ≤ 0.0023 * x + 6 * Real.sqrt x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hh : 0 < delta * x := mul_pos delta_pos hx0
  have hshift : 4 * (delta * x) < x := by norm_num [delta]; linarith
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  have hlarge : ∀ᶠ k : ℕ in atTop, (1894439 : ℝ) < T k := by
    filter_upwards [eventually_ge_atTop (1894439 : ℕ)] with k hk
    have hkR : (1894439 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have ht := (hT.mem k).1
    linarith
  have hnorm (lower : Bool) : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) ρ : ℂ) * coefficient lower x ρ‖ ≤
          6 * Real.sqrt x + 2e-12 * (x + 1) := by
    filter_upwards [hlarge] with k hk
    exact norm_sum_le lower hx1 hRH hk
      (PolynomialZeroCountBridge.zetaGoodHeight_of_goodHeights hT k)
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 4 * (delta * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hup := PolynomialPsiFromZeroSums.upper_error_of_eventually_bounded_zero_sums
    hT hx0 hh hN
    (by simpa [coefficient] using hnorm false)
    (by simpa using norm_left_remainder_le false hx0)
  have hlo := PolynomialPsiFromZeroSums.lower_error_of_eventually_bounded_zero_sums
    hT hshift hh hNx
    (by simpa [coefficient] using hnorm true)
    (by simpa using norm_left_remainder_le true hx0)
  have hpsi := PolynomialPsi.psi_error_of_polynomial_errors hx0.le hh hN hup hlo
  have hr := remainder_and_log_le hx
  have htail : (2e-12 : ℝ) * (x + 1) ≤ 0.000005 * x := by linarith
  norm_num [delta] at hpsi
  linarith

end TernaryGoldbach.RSBounds.ModeratePsi
