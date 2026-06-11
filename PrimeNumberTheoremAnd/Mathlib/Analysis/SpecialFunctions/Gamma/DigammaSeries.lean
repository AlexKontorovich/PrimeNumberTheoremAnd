/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The series representation of the digamma function

This file proves the classical series representation of the digamma function:
for `z : ℂ` avoiding the poles of `Gamma`,
`digamma z = -γ + ∑' n : ℕ, (1 / (n + 1) - 1 / (n + z))`,
where `γ` is the Euler-Mascheroni constant.

The proof goes through the Euler limit form of the Gamma function. We introduce
`Complex.logGammaSeq`, the complex analogue of `Real.BohrMollerup.logGammaSeq`, show that
it converges pointwise on the right half-plane (to a logarithm of `Gamma`, via
`Complex.GammaSeq_tendsto_Gamma`), that its derivatives converge uniformly on bounded
substrips of the half-plane, and apply `hasDerivAt_of_tendstoUniformlyOn` to identify
`digamma` with the limit of the derivatives there. The recurrence
`Complex.digamma_apply_add_one` then propagates the identity from the half-plane to the
whole domain.

## Main statements

* `Complex.hasSum_digamma`: for `z` avoiding `-ℕ`, the series
  `∑ (1 / (n + 1) - 1 / (n + z))` sums to `digamma z + γ`.
* `Complex.digamma_eq_tsum`: the same identity, written as a formula for `digamma z`.
-/

@[expose] public section

open Filter Topology Finset Nat

namespace Complex

/-! ## Elementary helper lemmas -/

/-- The norm of `(n : ℂ) + 1` is `n + 1`. -/
lemma norm_natCast_add_one (n : ℕ) : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
  rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, norm_natCast]
  push_cast
  ring

/-- The partial sums of the series `∑ 1 / (m + 1)` are the harmonic numbers. -/
lemma sum_inv_natCast_add_one (n : ℕ) :
    ∑ m ∈ Finset.range n, ((m : ℂ) + 1)⁻¹ = ((harmonic n : ℚ) : ℂ) := by
  rw [harmonic]
  push_cast
  rfl

/-- The summand of the digamma series, in closed form. -/
lemma inv_add_one_sub_inv_eq {z : ℂ} {m : ℕ} (hzm : z + m ≠ 0) :
    ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹ = (z - 1) * (((m : ℂ) + 1) * (z + m))⁻¹ := by
  have hm : ((m : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero m
  field_simp
  ring

/-- The Weierstrass bound for the digamma series summand on a bounded substrip of the
right half-plane. -/
lemma norm_inv_add_one_sub_inv_le {a R : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) {z : ℂ}
    (hza : a ≤ z.re) (hzR : ‖z‖ ≤ R) (m : ℕ) :
    ‖((m : ℂ) + 1)⁻¹ - (z + m)⁻¹‖ ≤ (R + 1) / (a * ((m : ℝ) + 1) ^ 2) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hR0 : (0 : ℝ) ≤ R := le_trans (norm_nonneg z) hzR
  have hrepos : 0 < (z + m).re := by
    rw [add_re, natCast_re]
    linarith
  have hzm : z + m ≠ 0 := fun h => by simp [h] at hrepos
  have hnorm_zm : a * ((m : ℝ) + 1) ≤ ‖z + m‖ := by
    have h1 : (z + m).re ≤ ‖z + m‖ := re_le_norm _
    rw [add_re, natCast_re] at h1
    nlinarith
  have hz1 : ‖z - 1‖ ≤ R + 1 := le_trans (norm_sub_le z 1) (by rw [norm_one]; linarith)
  rw [inv_add_one_sub_inv_eq hzm, norm_mul, norm_inv, norm_mul, norm_natCast_add_one,
    ← div_eq_mul_inv]
  calc ‖z - 1‖ / (((m : ℝ) + 1) * ‖z + m‖)
      ≤ (R + 1) / (((m : ℝ) + 1) * (a * ((m : ℝ) + 1))) := by
        gcongr
    _ = (R + 1) / (a * ((m : ℝ) + 1) ^ 2) := by ring_nf

/-- Summability of the comparison series `∑ 1 / (m + 1) ^ 2`. -/
lemma summable_one_div_natCast_add_one_sq :
    Summable (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) := by
  have h := Real.summable_one_div_nat_pow.mpr (one_lt_two : (1 : ℕ) < 2)
  exact ((summable_nat_add_iff 1).mpr h).congr fun n => by push_cast; ring

/-- A summable telescoping series whose terms tend to zero sums to its first term. -/
lemma hasSum_sub_succ_of_tendsto_zero {a : ℕ → ℂ} (h0 : Tendsto a atTop (𝓝 0))
    (hs : Summable fun n => a n - a (n + 1)) :
    HasSum (fun n => a n - a (n + 1)) (a 0) := by
  have h1 : Tendsto (fun n => ∑ i ∈ Finset.range n, (a i - a (i + 1))) atTop (𝓝 (a 0)) := by
    have he : ∀ n, ∑ i ∈ Finset.range n, (a i - a (i + 1)) = a 0 - a n :=
      fun n => Finset.sum_range_sub' a n
    simp only [he]
    simpa using tendsto_const_nhds.sub h0
  have h2 := hs.hasSum
  rwa [tendsto_nhds_unique h2.tendsto_sum_nat h1] at h2

/-! ## The complex logarithmic Gamma sequence -/

/-- The sequence of approximations to a logarithm of `Gamma z`, the complex analogue of
`Real.BohrMollerup.logGammaSeq`. For `0 < z.re` it converges to a logarithm of `Gamma z`,
and its derivative sequence converges, uniformly on bounded substrips of the half-plane,
to `digamma z`. -/
noncomputable def logGammaSeq (z : ℂ) (n : ℕ) : ℂ :=
  z * (Real.log n : ℂ) + (Real.log (n !) : ℂ) - ∑ m ∈ Finset.range (n + 1), log (z + m)

/-- The increment of `logGammaSeq` in closed form. -/
lemma logGammaSeq_succ_sub {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    logGammaSeq z (n + 1) - logGammaSeq z n
      = z * ((Real.log ((n : ℝ) + 1) - Real.log n : ℝ) : ℂ) - log (1 + z / ((n : ℂ) + 1)) := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnC : ((n : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero n
  have hx : 1 + z / ((n : ℂ) + 1) ≠ 0 := by
    intro h
    have hzval : z = -((n : ℂ) + 1) := by
      field_simp at h
      linear_combination h
    rw [hzval] at hz
    simp only [neg_re, add_re, natCast_re, one_re] at hz
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hfacC : (Real.log ((n + 1)!) : ℂ)
      = (Real.log ((n : ℝ) + 1) : ℂ) + (Real.log (n !) : ℂ) := by
    have hfac : Real.log (((n + 1)! : ℕ) : ℝ)
        = Real.log ((n : ℝ) + 1) + Real.log ((n ! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      rw [Real.log_mul (by positivity) (by exact_mod_cast n.factorial_ne_zero)]
    rw [← ofReal_add]
    exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) hfac
  have hlog : log (z + ((n + 1 : ℕ) : ℂ))
      = (Real.log ((n : ℝ) + 1) : ℂ) + log (1 + z / ((n : ℂ) + 1)) := by
    have hxx : ((((n : ℝ) + 1) : ℝ) : ℂ) * (1 + z / ((n : ℂ) + 1)) = z + ((n + 1 : ℕ) : ℂ) := by
      push_cast
      field_simp
      ring
    rw [← hxx, log_ofReal_mul hn1 hx]
  unfold logGammaSeq
  rw [Finset.sum_range_succ, hfacC, hlog]
  push_cast
  ring

/-- For `0 < z.re`, the sequence `logGammaSeq z` is Cauchy. -/
lemma cauchySeq_logGammaSeq {z : ℂ} (hz : 0 < z.re) : CauchySeq (logGammaSeq z) := by
  apply cauchySeq_of_summable_dist
  apply Summable.of_norm_bounded_eventually_nat
    (g := fun n => (2 * ‖z‖ + ‖z‖ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2))
    (summable_one_div_natCast_add_one_sq.mul_left _)
  filter_upwards [eventually_ge_atTop 1, eventually_ge_atTop ⌈2 * ‖z‖⌉₊] with n hn1 hn2
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn2R : 2 * ‖z‖ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn2)
  have hw : ‖z / ((n : ℂ) + 1)‖ = ‖z‖ / ((n : ℝ) + 1) := by
    rw [norm_div, norm_natCast_add_one]
  have hw2 : ‖z / ((n : ℂ) + 1)‖ ≤ 1 / 2 := by
    rw [hw, div_le_iff₀ (by positivity)]
    linarith
  simp only [Nat.succ_eq_add_one]
  rw [Real.norm_of_nonneg dist_nonneg, dist_eq_norm, ← norm_neg, neg_sub,
    logGammaSeq_succ_sub hz n]
  have key : z * ((Real.log ((n : ℝ) + 1) - Real.log n : ℝ) : ℂ) - log (1 + z / ((n : ℂ) + 1))
      = z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
        + (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))) := by
    push_cast
    ring
  rw [key]
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog_est : |Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹|
      ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hdiv : Real.log ((n : ℝ) + 1) - Real.log n = Real.log (((n : ℝ) + 1) / n) :=
      (Real.log_div (by positivity) (by positivity)).symm
    have l1 : Real.log ((n : ℝ) + 1) - Real.log n ≤ 1 / n := by
      rw [hdiv]
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((n : ℝ) + 1) / n by positivity)
      have he : ((n : ℝ) + 1) / n - 1 = 1 / n := by
        field_simp
        ring
      linarith
    have l2 : ((n : ℝ) + 1)⁻¹ ≤ Real.log ((n : ℝ) + 1) - Real.log n := by
      have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) / ((n : ℝ) + 1) by positivity)
      rw [Real.log_div hn0.ne' (by positivity)] at h
      have he : (n : ℝ) / ((n : ℝ) + 1) - 1 = -((n : ℝ) + 1)⁻¹ := by
        field_simp
        ring
      rw [he] at h
      linarith
    have hcomp : 1 / (n : ℝ) - ((n : ℝ) + 1)⁻¹ ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
      have he : 1 / (n : ℝ) - ((n : ℝ) + 1)⁻¹ = 1 / ((n : ℝ) * ((n : ℝ) + 1)) := by
        field_simp
        ring
      rw [he, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by positivity
      linarith
    · linarith
  calc ‖z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)
        + (z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1)))‖
      ≤ ‖z * ((Real.log ((n : ℝ) + 1) - Real.log n - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ)‖
        + ‖z / ((n : ℂ) + 1) - log (1 + z / ((n : ℂ) + 1))‖ := norm_add_le _ _
    _ ≤ ‖z‖ * (2 * (1 / ((n : ℝ) + 1) ^ 2)) + ‖z‖ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
        apply _root_.add_le_add
        · rw [norm_mul, norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left hlog_est (norm_nonneg z)
        · have hlt : ‖z / ((n : ℂ) + 1)‖ < 1 := lt_of_le_of_lt hw2 (by norm_num)
          have hb := norm_log_one_add_sub_self_le hlt
          rw [← norm_neg, neg_sub]
          calc ‖log (1 + z / ((n : ℂ) + 1)) - z / ((n : ℂ) + 1)‖
              ≤ ‖z / ((n : ℂ) + 1)‖ ^ 2 * (1 - ‖z / ((n : ℂ) + 1)‖)⁻¹ / 2 := hb
            _ ≤ ‖z / ((n : ℂ) + 1)‖ ^ 2 * 2 / 2 := by
                have h2 : (1 - ‖z / ((n : ℂ) + 1)‖)⁻¹ ≤ 2 := by
                  rw [← one_div]
                  have h3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1 / 2)
                    (by linarith : (1 : ℝ) / 2 ≤ 1 - ‖z / ((n : ℂ) + 1)‖)
                  simpa using h3
                gcongr
            _ = ‖z / ((n : ℂ) + 1)‖ ^ 2 := by ring
            _ = ‖z‖ ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
                rw [hw, div_pow]
                ring
    _ = (2 * ‖z‖ + ‖z‖ ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by ring

/-- On the right half-plane, `exp (logGammaSeq z n) = GammaSeq z n` for `n ≠ 0`. -/
lemma exp_logGammaSeq {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : n ≠ 0) :
    exp (logGammaSeq z n) = GammaSeq z n := by
  have hne : ∀ m : ℕ, z + (m : ℂ) ≠ 0 := by
    intro m h
    have hpos : 0 < (z + (m : ℂ)).re := by
      rw [add_re, natCast_re]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    simp [h] at hpos
  unfold logGammaSeq GammaSeq
  rw [exp_sub, exp_add, exp_sum]
  congr 1
  · congr 1
    · rw [natCast_log, cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), mul_comm z (log (n : ℂ))]
    · rw [natCast_log, exp_log (by exact_mod_cast n.factorial_ne_zero)]
  · exact Finset.prod_congr rfl fun m _ => exp_log (hne m)

/-! ## The series on the right half-plane -/

/-- The digamma series on the right half-plane. -/
lemma hasSum_digamma_of_re_pos {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    HasSum (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)
      (digamma z₀ + Real.eulerMascheroniConstant) := by
  set a : ℝ := min (z₀.re / 2) 1 with ha_def
  set R : ℝ := ‖z₀‖ + 1 with hR_def
  have ha : 0 < a := lt_min (by linarith) one_pos
  have ha1 : a ≤ 1 := min_le_right _ _
  set s : Set ℂ := {w : ℂ | a < w.re} ∩ {w : ℂ | ‖w‖ < R} with hs_def
  have hs_open : IsOpen s :=
    (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_norm continuous_const)
  have haz : a < z₀.re := by
    rw [ha_def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hz₀R : ‖z₀‖ < R := by rw [hR_def]; linarith
  have hz₀s : z₀ ∈ s := ⟨haz, hz₀R⟩
  have hmem : ∀ w ∈ s, a ≤ w.re ∧ ‖w‖ ≤ R := fun w hw => ⟨le_of_lt hw.1, le_of_lt hw.2⟩
  have hre_pos : ∀ w ∈ s, 0 < w.re := fun w hw => lt_trans ha hw.1
  -- the Weierstrass majorant
  have hu : Summable (fun m : ℕ => (R + 1) / (a * ((m : ℝ) + 1) ^ 2)) := by
    refine (summable_one_div_natCast_add_one_sq.mul_left ((R + 1) / a)).congr fun m => ?_
    rw [mul_one_div, div_div]
  -- uniform convergence of the partial sums of the packet series
  have hM : TendstoUniformlyOn
      (fun (N : ℕ) (w : ℂ) => ∑ m ∈ Finset.range N, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s :=
    tendstoUniformlyOn_tsum_nat hu fun m w hw =>
      norm_inv_add_one_sub_inv_le ha ha1 (hmem w hw).1 (hmem w hw).2 m
  have hM1 : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => ∑ m ∈ Finset.range (n + 1), (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹))
      (fun (w : ℂ) => ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    intro u hu'
    exact (tendsto_add_atTop_nat 1).eventually (hM u hu')
  -- the constant part tends to `-γ`
  have hcR : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹) atTop
      (𝓝 (-Real.eulerMascheroniConstant)) := by
    have h1 : Tendsto (fun n : ℕ => Real.log n - (harmonic n : ℝ)) atTop
        (𝓝 (-Real.eulerMascheroniConstant)) :=
      Real.tendsto_harmonic_sub_log.neg.congr fun n => by ring
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) := by
      apply Filter.Tendsto.inv_tendsto_atTop
      exact tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa using h1.sub h2
  have hcC : Tendsto (fun n : ℕ => ((Real.log n - (harmonic n : ℝ) - ((n : ℝ) + 1)⁻¹ : ℝ) : ℂ))
      atTop (𝓝 (-(Real.eulerMascheroniConstant : ℂ))) := by
    have h := (continuous_ofReal.tendsto (-Real.eulerMascheroniConstant)).comp hcR
    have hval : ((-Real.eulerMascheroniConstant : ℝ) : ℂ) = -(Real.eulerMascheroniConstant : ℂ) := by
      push_cast
      ring
    rw [← hval]
    exact h
  have hcU := hcC.tendstoUniformlyOn_const s
  -- assemble: the derivative sequence converges uniformly on `s`
  have hF' : TendstoUniformlyOn
      (fun (n : ℕ) (w : ℂ) => (Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (w + m)⁻¹)
      (fun (w : ℂ) => -(Real.eulerMascheroniConstant : ℂ)
        + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (w + m)⁻¹)) atTop s := by
    have hadd := hcU.add hM1
    refine hadd.congr ?_
    filter_upwards with n
    intro w hw
    simp only [Pi.add_apply]
    rw [Finset.sum_sub_distrib, sum_inv_natCast_add_one (n + 1)]
    push_cast [harmonic_succ]
    ring
  -- the derivatives of `logGammaSeq`
  have hderiv : ∀ n : ℕ, ∀ x : ℂ, x ∈ s →
      HasDerivAt (fun w => logGammaSeq w n)
        ((Real.log n : ℂ) - ∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
    intro n x hx
    have hre : 0 < x.re := hre_pos x hx
    have h1 : HasDerivAt (fun w : ℂ => w * (Real.log n : ℂ) + (Real.log (n !) : ℂ))
        ((Real.log n : ℂ)) x := (hasDerivAt_mul_const _).add_const _
    have h2 : HasDerivAt (fun w : ℂ => ∑ m ∈ Finset.range (n + 1), log (w + m))
        (∑ m ∈ Finset.range (n + 1), (x + m)⁻¹) x := by
      apply HasDerivAt.fun_sum
        (A := fun (m : ℕ) (w : ℂ) => log (w + m)) (A' := fun m : ℕ => (x + m)⁻¹)
      intro m _
      have hmem : x + (m : ℂ) ∈ slitPlane := by
        rw [mem_slitPlane_iff]
        left
        rw [add_re, natCast_re]
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hinner : HasDerivAt (fun w : ℂ => w + (m : ℂ)) 1 x := (hasDerivAt_id x).add_const _
      simpa using (hasDerivAt_log hmem).comp x hinner
    simpa only [logGammaSeq] using h1.sub h2
  -- pointwise convergence to the limit function
  have hptw : ∀ x : ℂ, x ∈ s →
      Tendsto (fun n => logGammaSeq x n) atTop (𝓝 (limUnder atTop (logGammaSeq x))) :=
    fun x hx => (cauchySeq_logGammaSeq (hre_pos x hx)).tendsto_limUnder
  -- differentiate the limit
  have hkey : HasDerivAt (fun w => limUnder atTop (logGammaSeq w))
      (-(Real.eulerMascheroniConstant : ℂ)
        + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)) z₀ :=
    hasDerivAt_of_tendstoUniformlyOn hs_open hF'
      (Filter.Eventually.of_forall fun n x hx => hderiv n x hx) hptw hz₀s
  -- identify the exponential of the limit with `Gamma`
  have hEq : ∀ w ∈ s, exp (limUnder atTop (logGammaSeq w)) = Gamma w := by
    intro w hw
    have h2 := (continuous_exp.tendsto _).comp (hptw w hw)
    have h3 : Tendsto (fun n => GammaSeq w n) atTop
        (𝓝 (exp (limUnder atTop (logGammaSeq w)))) := by
      apply h2.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      exact exp_logGammaSeq (hre_pos w hw) hn
    exact tendsto_nhds_unique h3 (GammaSeq_tendsto_Gamma w)
  have hGd : HasDerivAt Gamma (Gamma z₀ * (-(Real.eulerMascheroniConstant : ℂ)
      + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹))) z₀ := by
    have hexp := hkey.cexp
    rw [hEq z₀ hz₀s] at hexp
    exact hexp.congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem (hs_open.mem_nhds hz₀s) fun w hw => (hEq w hw).symm)
  have hne : ∀ m : ℕ, z₀ ≠ -(m : ℂ) := by
    intro m h
    rw [h] at hz₀
    simp only [neg_re, natCast_re] at hz₀
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdig : digamma z₀ = -(Real.eulerMascheroniConstant : ℂ)
      + ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹) := by
    rw [digamma_def, logDeriv_apply, hGd.deriv, mul_div_cancel_left₀ _ (Gamma_ne_zero hne)]
  have hsm : Summable (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹) :=
    Summable.of_norm_bounded hu fun m =>
      norm_inv_add_one_sub_inv_le ha ha1 haz.le hz₀R.le m
  have ht : ∑' m : ℕ, (((m : ℂ) + 1)⁻¹ - (z₀ + m)⁻¹)
      = digamma z₀ + Real.eulerMascheroniConstant := by
    rw [hdig]
    ring
  exact ht ▸ hsm.hasSum

/-! ## The main statements -/

/-- The series representation of the digamma function: for `z` away from the poles of
`Gamma`, the series `∑ (1 / (n + 1) - 1 / (n + z))` sums to `digamma z + γ`, where `γ` is
the Euler-Mascheroni constant. -/
theorem hasSum_digamma {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
      (digamma z + Real.eulerMascheroniConstant) := by
  suffices h : HasSum (fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹)
      (digamma z + Real.eulerMascheroniConstant) by
    have e : (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))
        = fun m : ℕ => ((m : ℂ) + 1)⁻¹ - (z + m)⁻¹ := by
      funext m
      rw [one_div, one_div, add_comm (m : ℂ) z]
    rw [e]
    exact h
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -(N : ℝ) < z.re :=
    ⟨⌈-z.re⌉₊ + 1, by have := Nat.le_ceil (-z.re); push_cast; linarith⟩
  induction N generalizing z with
  | zero =>
    apply hasSum_digamma_of_re_pos
    simpa using hN
  | succ N ih =>
    by_cases hcase : -(N : ℝ) < z.re
    · exact ih hz hcase
    · -- shift by one and use the recurrence
      have hz1 : ∀ n : ℕ, z + 1 ≠ -(n : ℂ) := by
        intro n hcon
        apply hz (n + 1)
        push_cast
        linear_combination hcon
      have hre1 : -(N : ℝ) < (z + 1).re := by
        rw [add_re, one_re]
        push_cast at hN
        linarith
      have hih := ih hz1 hre1
      rw [digamma_apply_add_one z hz] at hih
      have hzm : ∀ n : ℕ, z + (n : ℂ) ≠ 0 := fun n hcon => hz n (by linear_combination hcon)
      have hnorm_lb : ∀ n : ℕ, (n : ℝ) - ‖z‖ ≤ ‖z + n‖ := by
        intro n
        have h := norm_sub_norm_le (n : ℂ) (-z)
        rw [sub_neg_eq_add, norm_neg, norm_natCast] at h
        rw [show z + (n : ℂ) = (n : ℂ) + z from add_comm _ _]
        exact h
      have ha0 : Tendsto (fun n : ℕ => (z + (n : ℂ))⁻¹) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        simp only [norm_inv]
        apply Filter.Tendsto.inv_tendsto_atTop
        apply tendsto_atTop_mono hnorm_lb
        have h := tendsto_atTop_add_const_right atTop (-‖z‖) tendsto_natCast_atTop_atTop
        exact h.congr fun n => by ring
      have hts : Summable (fun n : ℕ => (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹) := by
        apply Summable.of_norm_bounded_eventually_nat
          (g := fun n : ℕ => 4 * (1 / ((n : ℝ) + 1) ^ 2))
          (summable_one_div_natCast_add_one_sq.mul_left _)
        filter_upwards [eventually_ge_atTop ⌈2 * ‖z‖ + 1⌉₊] with n hn
        have hnR : 2 * ‖z‖ + 1 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
        have hz0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
        have hb1 : ((n : ℝ) + 1) / 2 ≤ ‖z + n‖ := le_trans (by linarith) (hnorm_lb n)
        have hb2 : ((n : ℝ) + 1) / 2 ≤ ‖z + ((n + 1 : ℕ) : ℂ)‖ := by
          refine le_trans ?_ (hnorm_lb (n + 1))
          push_cast
          linarith
        have hid : (z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹
            = ((z + n) * (z + ((n + 1 : ℕ) : ℂ)))⁻¹ := by
          have h1 := hzm n
          have h2 := hzm (n + 1)
          field_simp
          push_cast
          ring
        rw [hid, norm_inv, norm_mul,
          show (4 : ℝ) * (1 / ((n : ℝ) + 1) ^ 2)
            = ((((n : ℝ) + 1) / 2) * (((n : ℝ) + 1) / 2))⁻¹ by field_simp; ring]
        gcongr
      have htel := hasSum_sub_succ_of_tendsto_zero ha0 hts
      simp only [Nat.cast_zero, add_zero] at htel
      have hfin := hih.sub htel
      have e2 : (fun n : ℕ => (((n : ℂ) + 1)⁻¹ - (z + 1 + n)⁻¹)
            - ((z + (n : ℂ))⁻¹ - (z + ((n + 1 : ℕ) : ℂ))⁻¹))
          = fun n : ℕ => ((n : ℂ) + 1)⁻¹ - (z + n)⁻¹ := by
        funext n
        push_cast
        ring
      rw [e2] at hfin
      convert hfin using 1
      ring

/-- The series representation of the digamma function, written as a formula:
`digamma z = -γ + ∑' n, (1 / (n + 1) - 1 / (n + z))` for `z` away from the poles. -/
theorem digamma_eq_tsum {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    digamma z = -(Real.eulerMascheroniConstant : ℂ)
      + ∑' n : ℕ, (1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z)) := by
  rw [(hasSum_digamma hz).tsum_eq]
  ring

end Complex
