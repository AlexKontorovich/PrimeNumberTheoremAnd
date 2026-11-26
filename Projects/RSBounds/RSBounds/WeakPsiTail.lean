import RSBounds.RS75AdaptiveHighBudget
import RSBounds.SchoenfeldSquareCutoffs
import RSBounds.SchoenfeldCoefficientPairing
import RSBounds.MertensIntervalLeftBound
import RSBounds.PolynomialPsiFromZeroSums

/-!
# An auxiliary decaying psi bound for the global RS62 handoff

This deliberately coarse tail is used only beyond log x=2400. It does not
replace the exact Schoenfeld Theorem 11 target. The quartic formula, high-zero
budget, reciprocal-square allowance and left-line estimates are reused.
-/

open Complex Finset Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.WeakPsiTail

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open PolynomialExplicit PolynomialAveraged PolynomialZeroKernel PolynomialKernelScaling
open PolynomialLeftKernel PolynomialRemainderIntegral RS75AdaptiveHighBudget

noncomputable def coefficient (lower : Bool) (x : ℝ) (ρ : ℂ) : ℂ :=
  if lower then zeroCoefficient (x - 4 * (adaptiveDelta x * x)) (adaptiveDelta x * x) ρ
  else zeroCoefficient x (adaptiveDelta x * x) ρ

theorem norm_coefficient_low (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hL : 400 ≤ Real.log x) {ρ : ℂ} (hre : ρ.re = 1 / 2) (him : ρ.im ≠ 0) :
    ‖coefficient lower x ρ‖ ≤ 2 * Real.sqrt x / |ρ.im| := by
  have hδ := adaptiveDelta_pos hL
  have hδ4 := four_adaptiveDelta_lt_one hL
  have hd : 1 + 2 * adaptiveDelta x ≤ 2 := by linarith [adaptiveDelta_le hL]
  have hn : ρ ≠ 0 := by intro h; exact him (by simp [h])
  have hc : (1 + 2 * adaptiveDelta x) / ‖ρ‖ ≤ 2 / |ρ.im| := by
    exact (div_le_div_of_nonneg_right hd (norm_nonneg _)).trans
      (div_le_div_of_nonneg_left (by norm_num) (abs_pos.mpr him) (Complex.abs_im_le_norm _))
  cases lower with
  | false =>
      simp only [coefficient, Bool.false_eq_true, ↓reduceIte]
      rw [zeroCoefficient_upper hx hδ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx,
        hre, ← Real.sqrt_eq_rpow]
      have hk := (norm_upperKernel_le_low hδ (by rw [hre]; norm_num)
        (by rw [hre]; norm_num)).trans hc
      convert mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg x) using 1 <;> ring
  | true =>
      simp only [coefficient, ↓reduceIte]
      rw [zeroCoefficient_lower hx hδ hδ4, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, ← Real.sqrt_eq_rpow]
      have hk := (PolynomialLowerKernel.norm_lower_difference_le_low_common hδ hδ4
        (by rw [hre]; norm_num) hn).trans hc
      convert mul_le_mul_of_nonneg_left hk (Real.sqrt_nonneg x) using 1 <;> ring

/-- The all-zero square allowance makes a new low-head count calculation unnecessary. -/
theorem norm_low_sum_le (lower : Bool) (hRH : Goals.FiniteRH 1894439)
    {T x : ℝ} (hT : 0 < T) (hx : 0 < x) (hL : 400 ≤ Real.log x) :
    ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ 1894439),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ 200000 * Real.sqrt x := by
  classical
  let S := (zerosRectD zetaF T).filter (fun ρ => |ρ.im| ≤ 1894439)
  have hp : ‖∑ ρ ∈ S, (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤
      (2 * 1894439 * Real.sqrt x) * ∑ ρ ∈ S, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ρ hρ
    obtain ⟨hr, hA⟩ := Finset.mem_filter.mp hρ
    have hi := ((mem_zerosRectD_zetaF_iff hT).mp hr).2.1
    have hb := SchoenfeldCoefficientPairing.low_re_eq_half hRH hT hr hA
    have hk := norm_coefficient_low lower hx hL hb hi
    have hc : 1 / |ρ.im| ≤ 1894439 / ρ.im ^ 2 := by
      apply (div_le_div_iff₀ (abs_pos.mpr hi) (sq_pos_of_ne_zero hi)).mpr
      have hm := mul_le_mul_of_nonneg_right hA (abs_nonneg ρ.im)
      nlinarith only [sq_abs ρ.im, hm]
    rw [norm_mul, Complex.norm_natCast]
    have h1 := mul_le_mul_of_nonneg_left hk (Nat.cast_nonneg (multRectD zetaF T ρ))
    have h2 := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (multRectD zetaF T ρ : ℝ) * (2 * Real.sqrt x) by positivity)
    refine h1.trans ?_
    convert h2 using 1 <;> ring
  have hs : (∑ ρ ∈ S, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2) ≤
      ∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) / ρ.im ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (by
      intro ρ _ _
      positivity)
  have hq := SchoenfeldReciprocalSquare.rectangle_reciprocal_square_sum_lt hT
  have hh := mul_le_mul_of_nonneg_left (hs.trans hq.le)
    (show 0 ≤ 2 * 1894439 * Real.sqrt x by positivity)
  change ‖∑ ρ ∈ S, (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ _
  exact hp.trans (hh.trans (by nlinarith [Real.sqrt_nonneg x]))

theorem norm_sum_le (lower : Bool) (hRH : Goals.FiniteRH 1894439)
    {T x : ℝ} (hAT : 1894439 ≤ T) (hg : zetaGoodHeight T)
    (hx : 1 ≤ x) (hL : 400 ≤ Real.log x) :
    ‖∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤
      200000 * Real.sqrt x + 0.05 * x / Real.log x := by
  classical
  have hlo := norm_low_sum_le lower hRH (by linarith : 0 < T) (by linarith : 0 < x) hL
  have hhi : ‖∑ ρ ∈ (zerosRectD zetaF T).filter (fun ρ => 1894439 < |ρ.im|),
      (multRectD zetaF T ρ : ℂ) * coefficient lower x ρ‖ ≤ 0.05 * x / Real.log x := by
    cases lower with
    | false => simpa only [coefficient, Bool.false_eq_true, ↓reduceIte] using
        (RS75AdaptiveHighBudget.norm_high_sum_upper_lt hAT hg hx hL).le
    | true => simpa only [coefficient, ↓reduceIte] using
        (RS75AdaptiveHighBudget.norm_high_sum_lower_lt hAT hg hx hL).le
  rw [← Finset.sum_filter_add_sum_filter_not (zerosRectD zetaF T)
    (fun ρ => |ρ.im| ≤ 1894439)]
  simp only [not_le]
  exact (norm_add_le _ _).trans (add_le_add hlo hhi)

/-- Coarse fifth-power kernel decay makes the variable-step left integral harmless. -/
theorem norm_left_integrand_le {x y δ : ℝ} (hx : 0 < x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) (t : ℝ) :
    ‖logDeriv riemannZeta (leftLine t) * zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      (2308500 * x ^ (-1 / 2 : ℝ) / δ ^ 4) * (1 + |t|) ^ (-3 / 2 : ℝ) := by
  have hp : 0 < 1 + |t| := by positivity
  have hk := PolynomialQuartic.decayFive_kernel.line_bound (-1 / 2) (Or.inl rfl) t
  have he : ‖QuarticMellin.kernel (leftLine t)‖ = 1 / ‖rising (leftLine t) 4‖ := by
    norm_num [QuarticMellin.kernel, rising, norm_div, norm_one]
  change ‖QuarticMellin.kernel (leftLine t)‖ ≤ 243 / (1 + |t|) ^ 5 at hk
  rw [he] at hk
  have hc := norm_difference_left_high hδ hδ1 hy0 hy1 (leftLine_re t)
  have hc' : ‖zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      (4617 * x ^ (-1 / 2 : ℝ) / δ ^ 4) / (1 + |t|) ^ 5 := by
    rw [norm_zeroCoefficient_dilate hx (by linarith) hδ, leftLine_re]
    have hh := mul_le_mul_of_nonneg_left hk
      (show 0 ≤ x ^ (-1 / 2 : ℝ) * (19 / δ ^ 4) by positivity)
    have hc0 := mul_le_mul_of_nonneg_left hc (Real.rpow_nonneg hx.le (-1 / 2 : ℝ))
    refine hc0.trans ?_
    convert hh using 1 <;> ring
  have hd : ‖logDeriv riemannZeta (leftLine t)‖ ≤ 500 * (1 + |t|) ^ (1 / 2 : ℝ) :=
    MertensIntervalLeftBound.norm_logDeriv_zeta_left_le_sqrt t
  rw [norm_mul]
  have hm := mul_le_mul hd hc' (norm_nonneg _) (by positivity)
  have heq : (500 * (1 + |t|) ^ (1 / 2 : ℝ)) *
      ((4617 * x ^ (-1 / 2 : ℝ) / δ ^ 4) / (1 + |t|) ^ 5) =
      (2308500 * x ^ (-1 / 2 : ℝ) / δ ^ 4) * (1 + |t|) ^ (-9 / 2 : ℝ) := by
    rw [show (1 + |t|) ^ (5 : ℕ) = (1 + |t|) ^ (5 : ℝ) by rw [Real.rpow_ofNat]]
    rw [show (500 * (1 + |t|) ^ (1 / 2 : ℝ)) *
      ((4617 * x ^ (-1 / 2 : ℝ) / δ ^ 4) / (1 + |t|) ^ (5 : ℝ)) =
      (2308500 * x ^ (-1 / 2 : ℝ) / δ ^ 4) *
        ((1 + |t|) ^ (1 / 2 : ℝ) / (1 + |t|) ^ (5 : ℝ)) by ring]
    rw [← Real.rpow_sub hp]
    norm_num
  rw [heq] at hm
  exact hm.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg t]) (by norm_num))
    (by positivity))

theorem norm_leftRemainder_le {x y δ : ℝ} (hx : 0 < x)
    (hδ : 0 < δ) (hδ1 : δ ≤ 0.01) (hy0 : 1 - 4 * δ ≤ y) (hy1 : y ≤ 1) :
    ‖leftRemainder (x * y) (δ * x)‖ ≤ 2000000 / (δ ^ 4 * Real.sqrt x) := by
  have hy : 0 < y := by linarith
  have hi := integrable_averagedIntegrand (mul_pos hx hy) (mul_pos hδ hx)
  have hm := MertensIntervalLeftBound.integrable_one_add_abs_neg_three_halves.const_mul
    (2308500 * x ^ (-1 / 2 : ℝ) / δ ^ 4)
  have hn : ‖∫ t : ℝ, logDeriv riemannZeta (leftLine t) *
      zeroCoefficient (x * y) (δ * x) (leftLine t)‖ ≤
      9234000 * x ^ (-1 / 2 : ℝ) / δ ^ 4 := by
    refine (norm_integral_le_integral_norm _).trans ((integral_mono hi.norm hm
      (norm_left_integrand_le hx hδ hδ1 hy0 hy1)).trans_eq ?_)
    rw [integral_const_mul, MertensIntervalLeftBound.integral_one_add_abs_neg_three_halves]
    ring
  rw [leftRemainder_eq_integral (mul_pos hx hy) (mul_pos hδ hx), norm_mul]
  have hf : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Real.pi_pos.le]
  rw [hf]
  have hc : (1 / (2 * Real.pi)) * 9234000 ≤ 2000000 := by
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity)]
    linarith [Real.pi_gt_three]
  have hb := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ x ^ (-1 / 2 : ℝ) / δ ^ 4 by positivity)
  have hh := mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  have he : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hx.le,
      ← Real.sqrt_eq_rpow, one_div]
  calc
    _ ≤ (1 / (2 * Real.pi)) * (9234000 * x ^ (-1 / 2 : ℝ) / δ ^ 4) := hh
    _ ≤ 2000000 * (x ^ (-1 / 2 : ℝ) / δ ^ 4) := by
      convert hb using 1 <;> ring
    _ = _ := by rw [he]; ring

theorem sqrt_eq_exp_half_log {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
  congr 1
  ring

/-- A single sixth Taylor term is ample for the coarse low-zero allowance. -/
theorem sqrt_budget {x : ℝ} (hx : 1 ≤ x) (hL : 2400 ≤ Real.log x) :
    300000 * Real.sqrt x ≤ 0.001 * x / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2400) hL 5
  have hc : (300000000 : ℝ) ≤ (Real.log x) ^ 5 / 46080 := by
    calc
      _ ≤ (2400 : ℝ) ^ 5 / 46080 := by norm_num
      _ ≤ _ := div_le_div_of_nonneg_right hp (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hc hL0.le
  have ht := Real.pow_div_factorial_le_exp (Real.log x / 2) (by positivity) 6
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at ht
  have he : 300000000 * Real.log x ≤ Real.sqrt x := by
    rw [sqrt_eq_exp_half_log hx0]
    refine (show 300000000 * Real.log x ≤ (Real.log x / 2) ^ 6 / 720 from ?_).trans ht
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_right he (Real.sqrt_nonneg x)
  apply (le_div_iff₀ hL0).mpr
  nlinarith only [hmul, Real.sq_sqrt hx0.le]

/-- A single twelfth Taylor term bounds the variable-step left remainder. -/
theorem left_budget {x : ℝ} (hx : 1 ≤ x) (hL : 2400 ≤ Real.log x) :
    2000000 / ((adaptiveDelta x) ^ 4 * Real.sqrt x) ≤ 0.001 * x / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hs0 := Real.sqrt_pos.mpr hx0
  have hδ := adaptiveDelta_pos (by linarith : 400 ≤ Real.log x)
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2400) hL 7
  have hc : (2000000000 : ℝ) * 50 ^ 4 ≤
      ((3 / 2 : ℝ) ^ 12 / 479001600) * (Real.log x) ^ 7 := by
    calc
      _ ≤ ((3 / 2 : ℝ) ^ 12 / 479001600) * 2400 ^ 7 := by norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by norm_num)
  have hm := mul_le_mul_of_nonneg_right hc (pow_nonneg hL0.le 5)
  have ht := Real.pow_div_factorial_le_exp (3 * Real.log x / 2) (by positivity) 12
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.cast_ofNat] at ht
  have hpow : 2000000000 * 50 ^ 4 * (Real.log x) ^ 5 ≤
      Real.exp (3 * Real.log x / 2) := by
    refine (show 2000000000 * 50 ^ 4 * (Real.log x) ^ 5 ≤
      (3 * Real.log x / 2) ^ 12 / 479001600 from ?_).trans ht
    convert hm using 1 <;> ring
  have he : Real.exp (3 * Real.log x / 2) = x * Real.sqrt x := by
    calc
      _ = Real.exp (Real.log x + Real.log x / 2) := by congr 1; ring
      _ = Real.exp (Real.log x) * Real.exp (Real.log x / 2) := Real.exp_add _ _
      _ = _ := by rw [Real.exp_log hx0, ← sqrt_eq_exp_half_log hx0]
  rw [he] at hpow
  have hb : 2000000 * (50 ^ 4 * (Real.log x) ^ 5) ≤
      0.001 * x * Real.sqrt x := by nlinarith only [hpow]
  apply (div_le_iff₀ (mul_pos (pow_pos hδ 4) hs0)).mpr
  have heq : (0.001 * x / Real.log x) * ((adaptiveDelta x) ^ 4 * Real.sqrt x) =
      (0.001 * x * Real.sqrt x) / (50 ^ 4 * (Real.log x) ^ 5) := by
    unfold adaptiveDelta
    field_simp [hL0.ne'] <;> ring
  rw [heq]
  exact (le_div_iff₀ (by positivity : (0 : ℝ) < 50 ^ 4 * (Real.log x) ^ 5)).mpr hb

theorem norm_adaptive_left_le (lower : Bool) {x : ℝ} (hx : 0 < x)
    (hL : 2400 ≤ Real.log x) :
    ‖leftRemainder (if lower then x - 4 * (adaptiveDelta x * x) else x)
      (adaptiveDelta x * x)‖ ≤ 2000000 / ((adaptiveDelta x) ^ 4 * Real.sqrt x) := by
  have h400 : 400 ≤ Real.log x := by linarith
  have hδ := adaptiveDelta_pos h400
  have hδ1 : adaptiveDelta x ≤ 0.01 := by linarith [adaptiveDelta_le h400]
  cases lower with
  | false =>
      have hh := norm_leftRemainder_le (y := 1) hx hδ hδ1 (by linarith) le_rfl
      simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using hh
  | true =>
      have hh := norm_leftRemainder_le (y := 1 - 4 * adaptiveDelta x) hx hδ hδ1
        le_rfl (by linarith)
      rw [show x * (1 - 4 * adaptiveDelta x) = x - 4 * (adaptiveDelta x * x) by ring] at hh
      simpa only [↓reduceIte] using hh

/-- Auxiliary far-tail input for the RS62 handoff, not the exact Schoenfeld target. -/
theorem psi_error_le (hRH : Goals.FiniteRH 1894439) {x : ℝ} (hx : Real.exp 2400 ≤ x) :
    |Chebyshev.psi x - x| ≤ 0.1 * x / Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos _).trans_le hx
  have hx1 : 1 ≤ x := (Real.one_le_exp_iff.mpr (by norm_num : (0 : ℝ) ≤ 2400)).trans hx
  have hL : 2400 ≤ Real.log x := by
    have hh := Real.log_le_log (Real.exp_pos 2400) hx
    rwa [Real.log_exp] at hh
  have h400 : 400 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hδ := adaptiveDelta_pos h400
  have hh : 0 < adaptiveDelta x * x := mul_pos hδ hx0
  have hshift : 4 * (adaptiveDelta x * x) < x := by
    have hm := mul_lt_mul_of_pos_right (four_adaptiveDelta_lt_one h400) hx0
    nlinarith only [hm]
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta
  have hlarge : ∀ᶠ k : ℕ in atTop, (1894439 : ℝ) ≤ T k := by
    filter_upwards [eventually_ge_atTop (1894439 : ℕ)] with k hk
    have hkR : (1894439 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [(hT.mem k).1]
  have hnorm (lower : Bool) : ∀ᶠ k in atTop,
      ‖∑ ρ ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) ρ : ℂ) * coefficient lower x ρ‖ ≤
        200000 * Real.sqrt x + 0.05 * x / Real.log x := by
    filter_upwards [hlarge] with k hk
    exact norm_sum_le lower hRH hk (zetaGoodHeight_of_goodHeights hT k) hx1 h400
  obtain ⟨N, hN⟩ := exists_nat_ge (x + 4 * (adaptiveDelta x * x))
  have hNx : x ≤ (N : ℝ) := by linarith
  have hup := PolynomialPsiFromZeroSums.upper_error_of_eventually_bounded_zero_sums
    hT hx0 hh hN
    (by simpa only [coefficient, Bool.false_eq_true, ↓reduceIte] using hnorm false)
    (by simpa only [Bool.false_eq_true, ↓reduceIte] using norm_adaptive_left_le false hx0 hL)
  have hlo := PolynomialPsiFromZeroSums.lower_error_of_eventually_bounded_zero_sums
    hT hshift hh hNx
    (by simpa only [coefficient, ↓reduceIte] using hnorm true)
    (by simpa only [↓reduceIte] using norm_adaptive_left_le true hx0 hL)
  have hp := PolynomialPsi.psi_error_of_polynomial_errors hx0.le hh hN hup hlo
  have hlog : Real.log (2 * Real.pi) ≤ 10 := by
    have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
    linarith [Real.pi_lt_d4]
  have hs : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx1
  have hlows : 200000 * Real.sqrt x + Real.log (2 * Real.pi) ≤ 300000 * Real.sqrt x := by
    linarith
  have hmain : 2 * (adaptiveDelta x * x) = 0.04 * x / Real.log x := by
    unfold adaptiveDelta
    field_simp [hL0.ne']
    ring
  rw [hmain] at hp
  have hlow := sqrt_budget hx1 hL
  have hleft := left_budget hx1 hL
  have hquot : 0 ≤ x / Real.log x := (div_pos hx0 hL0).le
  simp only [div_eq_mul_inv] at hp hlow hleft hquot ⊢
  nlinarith only [hp, hlows, hlow, hleft, hquot]

end TernaryGoldbach.RSBounds.WeakPsiTail
