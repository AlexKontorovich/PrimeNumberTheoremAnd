import RSBounds.BacklundEulerMaclaurin
import RSBounds.BacklundZetaRegularization
import RSBounds.BacklundCenterNumericsBase
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.PSeriesComplex
import Mathlib.NumberTheory.LSeries.RiemannZeta
import TernaryGoldbach.Prelim.RamareHarm
import RSBounds.SmallTotientProduct

/-!
# The Euler--Maclaurin remainder used in Backlund's right-edge bound

The analytic remainder is proved from the second-order quadrature formula.
No prime-number theorem, zero-free region, or zero-count estimate is used.
-/

open Complex MeasureTheory Set Filter
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundZetaBoundary

/-- Absolute convergence compares zeta with its value on the real axis. -/
theorem zeta_norm_le_real_axis {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ ‖riemannZeta (s.re : ℂ)‖ := by
  rw [zeta_eq_tsum_one_div_nat_cpow hs, CenterNumerics.norm_zeta_eq_tsum_rpow hs]
  have hsum := Complex.summable_one_div_nat_cpow.mpr hs
  calc
    _ ≤ ∑' n : ℕ, ‖1 / (n : ℂ) ^ s‖ := norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s.re) := by
      congr 1
      funext n
      rw [one_div, ← Complex.cpow_neg,
        Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith), Complex.neg_re]

/-- Beyond `Re s = 3/2`, the elementary integral test already gives `3`. -/
theorem zeta_norm_le_three {s : ℂ} (hs : 3 / 2 ≤ s.re) : ‖riemannZeta s‖ ≤ 3 := by
  have hs1 : 1 < s.re := by linarith
  have hh := CenterNumerics.zeta_tail_upper hs1 (N := 1) (by norm_num)
  norm_num [CenterNumerics.rpowSum] at hh
  have hden : (0 : ℝ) < s.re - 1 := by linarith
  have hdiv : 1 / (s.re - 1) ≤ 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  simp only [one_div] at hdiv
  exact (zeta_norm_le_real_axis hs1).trans (by linarith)

theorem nat_cpow_tendsto_zero {a : ℂ} (ha : a.re < 0) :
    Tendsto (fun n : ℕ => (n : ℂ) ^ a) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [Complex.norm_natCast_cpow_of_re_ne_zero _ ha.ne]
  simpa only [neg_neg, Function.comp_def] using
    (tendsto_rpow_neg_atTop (by linarith : 0 < -a.re)).comp
      tendsto_natCast_atTop_atTop

/-- The second-order remainder, including the critical strip. Its convergence
uses the existing first-order regularization, not the Dirichlet series alone. -/
theorem zeta_second_order_remainder {s : ℂ} (hs : 0 < s.re) (hs_one : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2
        - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      (1 / 12 : ℝ) * ∫ x in Ioi (N : ℝ),
        ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖ := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.neg_re, Complex.zero_re] at this
    linarith
  have hs1 : -s - 1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hf (x : ℝ) (hx : (N : ℝ) ≤ x) :
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ (-s))
        (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs0
  have hg (x : ℝ) (hx : (N : ℝ) ≤ x) :
      HasDerivAt (fun y : ℝ => -s * (y : ℂ) ^ (-s - 1))
        (s * (s + 1) * (x : ℂ) ^ (-s - 2)) x := by
    convert (hasDerivAt_ofReal_cpow_const (hN0.trans_le hx).ne' hs1).const_mul (-s)
      using 1
    rw [show -s - 1 - 1 = -s - 2 by ring]
    ring
  have hc : ContinuousOn (fun x : ℝ => s * (s + 1) * (x : ℂ) ^ (-s - 2))
      (Ici (N : ℝ)) := by
    intro x hx
    exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (hN0.trans_le hx).ne'))).continuousWithinAt
  have hf0 := nat_cpow_tendsto_zero (a := -s) (by simp; linarith)
  have hg0 := (nat_cpow_tendsto_zero (a := -s - 1) (by simp; linarith)).const_mul (-s)
  simp only [mul_zero] at hg0
  have hhi := (integrableOn_Ioi_cpow_of_lt (a := -s - 2) (by simp; linarith)
    hN0).const_mul (s * (s + 1))
  have hh := BacklundEulerMaclaurin.regularized_infinite_error_le N hf hg hc
    (BacklundZetaRegularization.regularized_sum_tendsto hs hs_one hN) hf0 hg0 hhi
  push_cast at hh
  convert hh using 1
  congr 1
  ring

/-- The same remainder with the improper integral evaluated. -/
theorem zeta_second_order_remainder_explicit_of_pos {s : ℂ} (hs : 0 < s.re)
    (hs_one : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hIH : (∫ x in Ioi (N : ℝ), ‖s * (s + 1) * (x : ℂ) ^ (-s - 2)‖) =
      ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
    calc
      _ = ∫ x in Ioi (N : ℝ), ‖s * (s + 1)‖ * x ^ (-s.re - 2) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        dsimp only
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hN0.trans hx)]
        simp
      _ = ‖s * (s + 1)‖ * ((N : ℝ) ^ (-s.re - 1) / (s.re + 1)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) hN0]
        congr 1
        rw [show -s.re - 2 + 1 = -s.re - 1 by ring,
          show -s.re - 1 = -(s.re + 1) by ring, div_neg, neg_div, neg_neg]
  have hh := zeta_second_order_remainder hs hs_one hN
  rw [hIH] at hh
  convert hh using 1
  field_simp

theorem zeta_second_order_remainder_explicit {s : ℂ} (hs : 1 < s.re)
    {N : ℕ} (hN : 1 ≤ N) :
    ‖riemannZeta s - (∑ k ∈ Finset.range N, (k : ℂ) ^ (-s))
        - (N : ℂ) ^ (-s) / 2 - (N : ℂ) ^ (1 - s) / (s - 1)
        - s * (N : ℂ) ^ (-s - 1) / 12‖ ≤
      ‖s * (s + 1)‖ / (12 * (s.re + 1)) * (N : ℝ) ^ (-s.re - 1) :=
  zeta_second_order_remainder_explicit_of_pos (by linarith)
    (by intro he; simp [he] at hs) hN

theorem partial_sum_norm_le_harmonic {s : ℂ} (hs : 1 ≤ s.re) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), (k : ℂ) ^ (-s)‖ ≤ (harmonic n : ℚ) := by
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, Complex.zero_cpow hs0, add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range n, ‖((k + 1 : ℕ) : ℂ) ^ (-s)‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [Complex.norm_natCast_cpow_of_pos (Nat.succ_pos k), Complex.neg_re]
      have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast (Nat.succ_pos k)
      have hh := Real.rpow_le_rpow_of_exponent_le hk1 (show -s.re ≤ -1 by linarith)
      simpa only [Real.rpow_neg_one, Nat.cast_add, Nat.cast_one, Nat.cast_succ, one_div] using hh
    _ = (harmonic n : ℚ) := by simp [harmonic, Rat.cast_sum, one_div]

/-- A direct upper bound with the second-order tail and no hidden error term. -/
theorem zeta_norm_le_euler_maclaurin {s : ℂ} (hs : 1 < s.re) (n : ℕ) :
    ‖riemannZeta s‖ ≤ (harmonic n : ℚ) + ((n + 1 : ℕ) : ℝ) ^ (-s.re) / 2
      + ((n + 1 : ℕ) : ℝ) ^ (1 - s.re) / ‖s - 1‖
      + ‖s‖ * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) / 12
      + ‖s * (s + 1)‖ / (12 * (s.re + 1)) * ((n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  let N : ℕ := n + 1
  let P : ℂ := ∑ k ∈ Finset.range N, (k : ℂ) ^ (-s)
  let a : ℂ := (N : ℂ) ^ (-s) / 2
  let b : ℂ := (N : ℂ) ^ (1 - s) / (s - 1)
  let c : ℂ := s * (N : ℂ) ^ (-s - 1) / 12
  let R : ℂ := riemannZeta s - P - a - b - c
  have hN0 : 0 < N := Nat.succ_pos n
  have hR := zeta_second_order_remainder_explicit hs (N := N) (by omega)
  have hP := partial_sum_norm_le_harmonic hs.le n
  have ha : ‖a‖ = (N : ℝ) ^ (-s.re) / 2 := by
    simp [a, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
  have hb : ‖b‖ = (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
    simp [b, norm_div, Complex.norm_natCast_cpow_of_pos hN0]
  have hc : ‖c‖ = ‖s‖ * (N : ℝ) ^ (-s.re - 1) / 12 := by
    simp [c, norm_div, norm_mul, Complex.norm_natCast_cpow_of_pos hN0]
  have htri : ‖riemannZeta s‖ ≤ ‖P‖ + ‖a‖ + ‖b‖ + ‖c‖ + ‖R‖ := by
    calc
      _ = ‖P + a + b + c + R‖ := by congr 1; dsimp [R]; ring
      _ ≤ ‖P + a + b + c‖ + ‖R‖ := norm_add_le _ _
      _ ≤ (‖P + a + b‖ + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖P + a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
      _ ≤ ((‖P‖ + ‖a‖ + ‖b‖) + ‖c‖) + ‖R‖ := by gcongr; exact norm_add_le _ _
  rw [ha, hb, hc] at htri
  exact htri.trans (by dsimp [R, P, a, b, c, N] at *; linarith)

/-- The harmonic-number estimate is reused from the existing Ramaré work. -/
theorem harmonic_half_endpoint_le (n : ℕ) :
    (harmonic n : ℚ) + 1 / (2 * ((n + 1 : ℕ) : ℝ)) ≤
      Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant := by
  have hh := (TernaryGoldbach.Prelim.RamPf.harm_bounds
    (n := n + 1) (by omega)).2
  rw [harmonic_succ] at hh
  push_cast at hh ⊢
  have hden : (n : ℝ) + 1 ≠ 0 := by positivity
  have he : ((n : ℝ) + 1)⁻¹ = 2 * (1 / (2 * ((n : ℝ) + 1))) := by
    field_simp
  rw [he] at hh
  linarith

/-- Backlund's preliminary right-edge estimate, with the height and finite
cutoff still free. -/
theorem zeta_norm_le_log_cutoff {s : ℂ} (hs : 1 < s.re) (ht : 0 < s.im) (n : ℕ) :
    ‖riemannZeta s‖ ≤ Real.log ((n + 1 : ℕ) : ℝ) + Real.eulerMascheroniConstant
      + 1 / s.im + ‖s‖ / (12 * (((n + 1 : ℕ) : ℝ) ^ 2))
      + ‖s * (s + 1)‖ / (24 * (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have hN1 : 1 ≤ N := by dsimp [N]; exact_mod_cast Nat.succ_pos n
  have hN0 : 0 < N := by linarith
  have hp1 : N ^ (-s.re) ≤ 1 / N := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re ≤ -1 by linarith)
    simpa only [Real.rpow_neg_one, one_div] using hh
  have hp0 : N ^ (1 - s.re) ≤ 1 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - s.re ≤ 0 by linarith)
    simpa only [Real.rpow_zero] using hh
  have hp2 : N ^ (-s.re - 1) ≤ 1 / N ^ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le hN1 (show -s.re - 1 ≤ -2 by linarith)
    simpa only [Real.rpow_neg hN0.le, Real.rpow_two, one_div] using hh
  have hden : s.im ≤ ‖s - 1‖ := by
    simpa using (le_abs_self (s - 1).im).trans (Complex.abs_im_le_norm (s - 1))
  have hden0 : 0 < ‖s - 1‖ := ht.trans_le hden
  have hb : N ^ (1 - s.re) / ‖s - 1‖ ≤ 1 / s.im := by
    exact (div_le_div_of_nonneg_right hp0 hden0.le).trans
      (one_div_le_one_div_of_le ht hden)
  have hc : ‖s‖ * N ^ (-s.re - 1) / 12 ≤ ‖s‖ / (12 * N ^ 2) := by
    calc
      _ ≤ ‖s‖ * (1 / N ^ 2) / 12 := by gcongr
      _ = _ := by ring
  have hd0 : ‖s * (s + 1)‖ / (12 * (s.re + 1)) ≤ ‖s * (s + 1)‖ / 24 := by
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) (by linarith)
  have hd : ‖s * (s + 1)‖ / (12 * (s.re + 1)) * N ^ (-s.re - 1) ≤
      ‖s * (s + 1)‖ / (24 * N ^ 2) := by
    calc
      _ ≤ (‖s * (s + 1)‖ / 24) * (1 / N ^ 2) :=
        mul_le_mul hd0 hp2 (Real.rpow_nonneg hN0.le _) (by positivity)
      _ = _ := by ring
  have ha : (harmonic n : ℚ) + N ^ (-s.re) / 2 ≤
      Real.log N + Real.eulerMascheroniConstant := by
    calc
      _ ≤ (harmonic n : ℚ) + (1 / N) / 2 := by gcongr
      _ = (harmonic n : ℚ) + 1 / (2 * N) := by ring
      _ ≤ _ := harmonic_half_endpoint_le n
  have hz := zeta_norm_le_euler_maclaurin hs n
  change ‖riemannZeta s‖ ≤ _ at hz
  change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
    1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2)
  dsimp only [N] at ha hb hc hd
  linarith

theorem norm_height_bounds {s : ℂ} (hs0 : 1 ≤ s.re) (hs1 : s.re ≤ 3 / 2)
    (ht : 50 ≤ s.im) :
    ‖s‖ ≤ 1.001 * s.im ∧ ‖s * (s + 1)‖ ≤ 1.004 * s.im ^ 2 := by
  have ht0 : 0 ≤ s.im := by linarith
  have ht2 : 2500 ≤ s.im ^ 2 := by nlinarith
  have hs2 : s.re ^ 2 ≤ 9 / 4 := by nlinarith
  have hs3 : (s.re + 1) ^ 2 ≤ 25 / 4 := by nlinarith
  have hn1 := Complex.sq_norm_sub_sq_im s
  have hn2 := Complex.sq_norm_sub_sq_im (s + 1)
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero] at hn2
  have h1 : ‖s‖ ≤ 1.001 * s.im := by nlinarith [norm_nonneg s]
  have h2 : ‖s + 1‖ ≤ 1.002 * s.im := by nlinarith [norm_nonneg (s + 1)]
  refine ⟨h1, ?_⟩
  rw [norm_mul]
  have hp := mul_le_mul h1 h2 (norm_nonneg (s + 1)) (by positivity)
  nlinarith

theorem zeta_norm_le_log_sub_of_le_three_halves {s : ℂ}
    (hs : 1 < s.re) (hs1 : s.re ≤ 3 / 2) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  let n : ℕ := ⌊s.im / 3⌋₊
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  have ht0 : 0 < s.im := by linarith
  have hNlo : s.im / 3 ≤ N := by
    dsimp [N, n]
    simpa only [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (s.im / 3)).le
  have hNhi : N ≤ s.im / 3 + 1 := by
    dsimp [N, n]
    push_cast
    have hh := Nat.floor_le (show (0 : ℝ) ≤ s.im / 3 by positivity)
    linarith
  have hN0 : 0 < N := by linarith
  have hN2 : s.im ^ 2 ≤ 9 * N ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ s.im / 3) hNlo 2
    nlinarith
  have hlog : Real.log N ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
    have he : s.im / 3 + 1 = (s.im / 3) * (1 + 3 / s.im) := by field_simp
    calc
      _ ≤ Real.log (s.im / 3 + 1) := Real.log_le_log hN0 hNhi
      _ = Real.log s.im - Real.log 3 + Real.log (1 + 3 / s.im) := by
        rw [he, Real.log_mul (by positivity) (by positivity), Real.log_div ht0.ne' (by norm_num)]
      _ ≤ Real.log s.im - Real.log 3 + 3 / s.im := by
        have hh := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 3 / s.im)
        linarith
  obtain ⟨h1, h2⟩ := norm_height_bounds hs.le hs1 ht
  have hc : ‖s‖ / (12 * N ^ 2) ≤ 0.75075 / s.im := by
    apply (div_le_div_iff₀ (by positivity) ht0).mpr
    have hh := mul_le_mul_of_nonneg_right h1 ht0.le
    nlinarith
  have hd : ‖s * (s + 1)‖ / (24 * N ^ 2) ≤ 0.3765 := by
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hcorr : (4 + 0.75075) / s.im ≤ 0.095015 := by
    apply (div_le_iff₀ ht0).mpr
    nlinarith
  have hγ : Real.eulerMascheroniConstant ≤ 0.578 := by
    linarith [SmallTotientProduct.gamma_bounds.2]
  have hlog3 : 1.098 ≤ Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hz := zeta_norm_le_log_cutoff hs ht0 n
  change ‖riemannZeta s‖ ≤ Real.log N + Real.eulerMascheroniConstant +
    1 / s.im + ‖s‖ / (12 * N ^ 2) + ‖s * (s + 1)‖ / (24 * N ^ 2) at hz
  have he : 3 / s.im + 1 / s.im + 0.75075 / s.im = (4 + 0.75075) / s.im := by ring
  linarith

theorem zeta_norm_le_log_sub_on_one {s : ℂ} (hs : s.re = 1) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  let δ : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) / 2
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa only [zero_div, δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).div_const 2
  have hδpos (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  have hδle (n : ℕ) : δ n ≤ 1 / 2 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ (n : ℝ) + 1)
    dsimp [δ]
    norm_num at hh
    simp only [one_div]
    linarith
  have hzseq : Tendsto (fun n : ℕ => s + (δ n : ℂ)) atTop (𝓝 s) := by
    simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp hδ).const_add s
  have hsne : s ≠ 1 := by
    intro he
    have := congrArg Complex.im he
    simp at this
    linarith
  have hζlim := ((differentiableAt_riemannZeta hsne).continuousAt.tendsto.comp hzseq).norm
  apply le_of_tendsto hζlim
  filter_upwards with n
  have hh := zeta_norm_le_log_sub_of_le_three_halves (s := s + (δ n : ℂ))
    (by simp [hs]; exact hδpos n) (by simp [hs]; linarith [hδle n]) (by simpa using ht)
  simpa using hh

/-- Backlund (54), with its explicit saving. This is unconditional. -/
theorem zeta_norm_le_log_sub {s : ℂ} (hs : 1 ≤ s.re) (ht : 50 ≤ s.im) :
    ‖riemannZeta s‖ ≤ Real.log s.im - 0.048 := by
  rcases eq_or_lt_of_le hs with he | hs'
  · exact zeta_norm_le_log_sub_on_one he.symm ht
  by_cases hs1 : s.re ≤ 3 / 2
  · exact zeta_norm_le_log_sub_of_le_three_halves hs' hs1 ht
  have hz := zeta_norm_le_three (le_of_not_ge hs1)
  have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 27)
    (by linarith : (27 : ℝ) ≤ s.im)
  have he : Real.log (27 : ℝ) = 3 * Real.log 3 := by
    rw [show (27 : ℝ) = 3 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [he] at hlog
  linarith [Real.log_three_gt_d9]

end TernaryGoldbach.RSBounds.BacklundZetaBoundary
