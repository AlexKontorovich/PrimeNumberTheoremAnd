import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.Algebra.Group.SubmonoidClosure
import Mathlib.Topology.Bases
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Algebra.Order.Field

/-!
# Phase alignment for Backlund's powers of the zeta function

Rosser's proof of Theorem 19 (1941, pp. 223–224) follows Backlund by choosing
powers whose phase at the center approaches one. This file supplies that
step for any nonzero complex number, independently of zeta estimates.
In particular it applies to the center value `ζ(5/4 + iT)` once its
nonvanishing is supplied by the Euler product.

This is a prerequisite for the sharp zero-count argument, not a proof of
the zero-count bound itself.
-/

open Filter Complex Metric
open scoped Topology

namespace TernaryGoldbach.RSBounds

/-- Every point of the unit circle has powers converging to one along a
strictly increasing sequence of exponents. -/
theorem circle_powers_subsequence_one (u : Circle) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (u : ℂ) ^ n j) atTop (𝓝 1) := by
  obtain ⟨n, hn, ht⟩ := (mapClusterPt_one_atTop_pow u).tendsto_subseq
  refine ⟨n, hn, ?_⟩
  have hc : Continuous ((↑) : Circle → ℂ) := continuous_subtype_val
  have h := (hc.tendsto (1 : Circle)).comp ht
  change Tendsto (fun j => ((u ^ n j : Circle) : ℂ)) atTop (𝓝 (1 : ℂ)) at h
  exact h

/-- Backlund's phase-aligned subsequence for an arbitrary nonzero center value. -/
theorem complex_powers_phase_subsequence {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) := by
  let u : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.2 (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr hz)])⟩
  exact circle_powers_subsequence_one u

/-- The real center value, normalized by the modulus of its power, tends to one. -/
theorem real_power_ratio_tendsto {z : ℂ} {n : ℕ → ℕ}
    (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
    Tendsto (fun j => (z ^ n j).re / ‖z‖ ^ n j) atTop (𝓝 (1 : ℝ)) := by
  have h := (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
  simpa only [Function.comp_def, div_pow, ← Complex.ofReal_pow,
    Complex.div_ofReal_re, Complex.one_re] using h

/-- Along a phase-aligned sequence, division by the exponent removes the
oscillating real-part factor from the logarithm. -/
theorem log_real_pow_div_tendsto {z : ℂ} (hz : z ≠ 0) {n : ℕ → ℕ}
    (hn : StrictMono n)
    (hp : Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1)) :
    Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
  let w : ℂ := z / (‖z‖ : ℂ)
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hrc : (‖z‖ : ℂ) ≠ 0 := by simpa using hr.ne'
  have hdecomp : z = (‖z‖ : ℂ) * w := (mul_div_cancel₀ z hrc).symm
  have hpow (m : ℕ) : (z ^ m).re = ‖z‖ ^ m * (w ^ m).re := by
    calc (z ^ m).re = (((‖z‖ : ℂ) * w) ^ m).re := congrArg (fun t : ℂ => (t ^ m).re) hdecomp
      _ = ‖z‖ ^ m * (w ^ m).re := by
        rw [mul_pow]
        have hc : (‖z‖ : ℂ) ^ m = ((‖z‖ ^ m : ℝ) : ℂ) :=
          (Complex.ofReal_pow ‖z‖ m).symm
        rw [hc]
        simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, sub_zero]
  have hre : Tendsto (fun j => (w ^ n j).re) atTop (𝓝 (1 : ℝ)) := by
    simpa only [Function.comp_def, Complex.one_re] using
      (Complex.continuous_re.tendsto (1 : ℂ)).comp hp
  have hlog : Tendsto (fun j => Real.log ((w ^ n j).re)) atTop (𝓝 0) := by
    simpa using hre.log (one_ne_zero : (1 : ℝ) ≠ 0)
  have hnTop : Tendsto (fun j => (n j : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hn.tendsto_atTop
  have hlim : Tendsto (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ))
      atTop (𝓝 (Real.log ‖z‖)) := by
    have hconst : Tendsto (fun _ : ℕ => Real.log ‖z‖) atTop (𝓝 (Real.log ‖z‖)) :=
      tendsto_const_nhds
    simpa using hconst.add (hlog.div_atTop hnTop)
  have heq : (fun j => Real.log |(z ^ n j).re| / (n j : ℝ)) =ᶠ[atTop]
      (fun j => Real.log ‖z‖ + Real.log ((w ^ n j).re) / (n j : ℝ)) := by
    filter_upwards [hre.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      hnTop.eventually (eventually_gt_atTop (0 : ℝ))] with j hj hnj
    rw [Real.log_abs, hpow, Real.log_mul (pow_ne_zero _ hr.ne') hj.ne', Real.log_pow]
    rw [add_div, mul_div_cancel_left₀ _ hnj.ne']
  exact (Filter.tendsto_congr' heq).2 hlim

/-- The phase and logarithmic conclusions used at the center of Backlund's
Jensen argument, with no assumptions beyond a nonzero center value. -/
theorem exists_backlund_phase_sequence {z : ℂ} (hz : z ≠ 0) :
    ∃ n : ℕ → ℕ, StrictMono n ∧
      Tendsto (fun j => (z / (‖z‖ : ℂ)) ^ n j) atTop (𝓝 1) ∧
      Tendsto (fun j => Real.log |(z ^ n j).re| / (n j : ℝ))
        atTop (𝓝 (Real.log ‖z‖)) := by
  obtain ⟨n, hn, hp⟩ := complex_powers_phase_subsequence hz
  exact ⟨n, hn, hp, log_real_pow_div_tendsto hz hn hp⟩

end TernaryGoldbach.RSBounds
