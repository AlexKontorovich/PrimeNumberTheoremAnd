import TernaryGoldbach.Prelim.PNTMertens
import TernaryGoldbach.Explicit.ZetaGrowth
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# A regularized Dirichlet-sum limit for `Re s > 0`

This reuses the first-order Euler--Maclaurin formula already ported from
PNT+/IEANTN and the analytic continuation of the sawtooth integral already
proved in `Explicit.ZetaGrowth`. It supplies the convergence hypothesis for
the second-order formula inside the critical strip.
-/

open Complex MeasureTheory Set Filter Finset
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundZetaRegularization

open TernaryGoldbach.Explicit

theorem zeta_eq_Izeta_of_pos {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    riemannZeta s = 1 + 1 / (s - 1) + s * Izeta s := by
  have hh := zetaF_eq hs
  rw [zetaF_of_ne hs1] at hh
  have hn : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  apply (mul_left_cancel₀ hn)
  calc
    (s - 1) * riemannZeta s = s + s * (s - 1) * Izeta s := hh
    _ = (s - 1) * (1 + 1 / (s - 1) + s * Izeta s) := by field_simp [hn]; ring

noncomputable def firstRemainder (s : ℂ) (x : ℝ) : ℂ :=
  (-s * (x : ℂ) ^ (-s - 1)) * (B1 x : ℝ)

theorem firstRemainder_eq (s : ℂ) (x : ℝ) :
    firstRemainder s x = s * (saw x * (x : ℂ) ^ (-(s + 1))) +
      (s / 2) * (x : ℂ) ^ (-s - 1) := by
  unfold firstRemainder B1 saw
  push_cast
  rw [show -(s + 1) = -s - 1 by ring]
  ring

theorem integrableOn_firstRemainder {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (firstRemainder s) (Ioi (1 : ℝ)) := by
  change IntegrableOn (fun x => firstRemainder s x) (Ioi (1 : ℝ))
  simp_rw [firstRemainder_eq]
  exact ((integrableOn_saw_integrand hs).const_mul s).add
    ((integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
      (by norm_num : (0 : ℝ) < 1)).const_mul (s / 2))

theorem integral_firstRemainder {s : ℂ} (hs : 0 < s.re) :
    (∫ x in Ioi (1 : ℝ), firstRemainder s x) = s * Izeta s + 1 / 2 := by
  have hs0 : s ≠ 0 := by intro he; simp [he] at hs
  have hfi := integrableOn_saw_integrand hs
  have hgi := integrableOn_Ioi_cpow_of_lt (a := -s - 1) (by simp; linarith)
    (by norm_num : (0 : ℝ) < 1)
  simp_rw [firstRemainder_eq]
  rw [integral_add (hfi.const_mul s) (hgi.const_mul (s / 2)),
    integral_const_mul, integral_const_mul,
    integral_Ioi_cpow_of_lt (by simp; linarith) (by norm_num : (0 : ℝ) < 1)]
  simp only [Complex.ofReal_one, Complex.one_cpow, Izeta]
  field_simp [hs0]
  ring

/-- A finite first-order identity, with both the sum and integral allowed to
diverge separately as the endpoint tends to infinity. -/
theorem finite_regularized_sum {s : ℂ} (hs : 0 < s.re) {M : ℕ} (hM : 1 ≤ M) :
    (∑ k ∈ range M, (k : ℂ) ^ (-s)) - (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s)) =
      (1 - (M : ℂ) ^ (-s)) / 2 + ∫ x in (1 : ℝ)..M, firstRemainder s x := by
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (-s)
  have hs0 : -s ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hderiv (x : ℝ) (hx : 1 ≤ x) :
      HasDerivAt f (-s * (x : ℂ) ^ (-s - 1)) x :=
    hasDerivAt_ofReal_cpow_const (by linarith) hs0
  have hc : ContinuousOn (deriv f) (uIcc (1 : ℝ) M) := by
    rw [uIcc_of_le hM']
    apply ContinuousOn.congr (f := fun x : ℝ => -s * (x : ℂ) ^ (-s - 1))
    · intro x hx
      exact (continuousAt_const.mul (Complex.continuousAt_ofReal_cpow_const _ _
        (Or.inr (by linarith [hx.1])))).continuousWithinAt
    · intro x hx
      exact (hderiv x hx.1).deriv
  have hh := sum_eq_integral_add_integral_deriv (f := f)
    (a := 1) (b := (M : ℝ)) (by norm_num) hM'
    (fun x hx => (hderiv x hx.1).differentiableAt) hc
  simp only [RCLike.ofReal_eq_complex_ofReal] at hh
  have hsets : Finset.Ioc 1 M = Finset.Ico 2 (M + 1) := by ext k; simp; omega
  have hint : (∫ x in (1 : ℝ)..M, deriv f x * (B1 x : ℝ)) =
      ∫ x in (1 : ℝ)..M, firstRemainder s x := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le hM'] at hx
    dsimp only
    rw [(hderiv x hx.1).deriv]
    rfl
  rw [hint] at hh
  simp only [Nat.floor_one, Nat.floor_natCast] at hh
  rw [hsets, sum_Ico_eq_sub _ (by omega)] at hh
  simp only [sum_range_succ, sum_range_zero, add_zero] at hh
  norm_num [f, B1, hs0] at hh
  linear_combination hh

theorem regularized_sum_from_one_tendsto {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun M : ℕ => (∑ k ∈ range M, (k : ℂ) ^ (-s)) -
      (∫ x in (1 : ℝ)..M, (x : ℂ) ^ (-s))) atTop (𝓝 (1 + s * Izeta s)) := by
  have hf0 : Tendsto (fun M : ℕ => (M : ℂ) ^ (-s)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    change Tendsto (fun M : ℕ => ‖(M : ℂ) ^ (-s)‖) atTop (𝓝 0)
    simp only [Complex.norm_natCast_cpow_of_re_ne_zero _
      (show (-s).re ≠ 0 by simp only [Complex.neg_re]; linarith), Complex.neg_re]
    exact (tendsto_rpow_neg_atTop hs).comp tendsto_natCast_atTop_atTop
  have hI := intervalIntegral_tendsto_integral_Ioi (1 : ℝ)
    (integrableOn_firstRemainder hs) tendsto_natCast_atTop_atTop
  have hlim := ((hf0.const_sub 1).div_const 2).add hI
  rw [integral_firstRemainder hs] at hlim
  have he : (1 - (0 : ℂ)) / 2 + (s * Izeta s + 1 / 2) = 1 + s * Izeta s := by ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with M hM
  exact (finite_regularized_sum hs hM).symm

theorem regularized_sum_tendsto {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {N : ℕ} (hN : 1 ≤ N) :
    Tendsto (fun M : ℕ => (∑ k ∈ Ico N M, (k : ℂ) ^ (-s)) -
      (∫ x in (N : ℝ)..M, (x : ℂ) ^ (-s))) atTop
      (𝓝 (riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
        (N : ℂ) ^ (1 - s) / (s - 1))) := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hint {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
      IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    intro x hx
    exact (Complex.continuousAt_ofReal_cpow_const _ _
      (Or.inr (by linarith [hx.1]))).continuousWithinAt
  have hIN : (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
      ((N : ℂ) ^ (1 - s) - 1) / (1 - s) := by
    rw [integral_cpow (Or.inr ⟨by intro he; exact hs1 (neg_inj.mp he),
      by rw [uIcc_of_le hN']; simp⟩), Complex.ofReal_one, Complex.one_cpow]
    push_cast
    congr 2 <;> ring
  have hlim := ((regularized_sum_from_one_tendsto hs).sub_const
    (∑ k ∈ range N, (k : ℂ) ^ (-s))).add_const
      (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s))
  have htarget : (1 + s * Izeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s))) +
      (∫ x in (1 : ℝ)..N, (x : ℂ) ^ (-s)) =
      riemannZeta s - (∑ k ∈ range N, (k : ℂ) ^ (-s)) -
        (N : ℂ) ^ (1 - s) / (s - 1) := by
    rw [hIN, zeta_eq_Izeta_of_pos hs hs1]
    field_simp [sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
    ring
  rw [htarget] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop N] with M hM
  have hM' : (N : ℝ) ≤ M := by exact_mod_cast hM
  have hcat := intervalIntegral.integral_add_adjacent_intervals
    (hint le_rfl hN') (hint hN' hM')
  rw [sum_Ico_eq_sub _ hM, ← hcat]
  ring

end TernaryGoldbach.RSBounds.BacklundZetaRegularization
