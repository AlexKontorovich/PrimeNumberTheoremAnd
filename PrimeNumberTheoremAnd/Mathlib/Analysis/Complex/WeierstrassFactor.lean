/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Weierstrass elementary factors

We define the Weierstrass elementary factors
`E_m(z) = (1 - z) * exp (∑_{k=1}^m z^k / k)` (as `Complex.weierstrassFactor`) and prove basic
properties and estimates

## Main definitions

* `Complex.partialLogSum m z`: the truncation of `-log (1 - z)`, defined via `Complex.logTaylor`
* `Complex.logTail m z`: the tail `∑_{k>m} z^k / k` as a `tsum` starting at `m + 1`
* `Complex.weierstrassFactor m z`: the elementary factor `E_m(z)`

## Main results

* `Complex.weierstrassFactor_sub_one_pow_bound`: `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)` for `‖z‖ ≤ 1 / 2`
* `Complex.weierstrassFactor_eq_exp_neg_tail`: on `‖z‖ < 1` with `z ≠ 1`,
  `E_m z = exp (-logTail m z)`
* `Complex.norm_partialLogSum_le_nat_mul_max_one_norm_pow`: a crude bound on the truncated
  logarithm series
* `Complex.log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow`: a crude lower
  bound for `log ‖E_m(z)‖` used in minimum-modulus arguments
-/

public section

noncomputable section

open scoped BigOperators
open Set

namespace Complex

/-! ## The Weierstrass factor -/

/-- The Weierstrass elementary factor `E_m`. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

lemma weierstrassFactor_def (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = (1 - z) * exp (partialLogSum m z) := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

@[simp]
lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum_at_zero]

@[simp]
lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    rw [weierstrassFactor] at hz
    rcases mul_eq_zero.mp hz with h1 | h2
    · exact (sub_eq_zero.mp h1).symm
    · exact absurd h2 (exp_ne_zero _)
  · rintro rfl
    simp [weierstrassFactor]

lemma weierstrassFactor_ne_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z ≠ 0 ↔ z ≠ 1 := by
  simpa [ne_eq] using (not_congr (weierstrassFactor_eq_zero_iff (m := m) (z := z)))

lemma weierstrassFactor_ne_zero_of_ne_one (m : ℕ) {z : ℂ} (hz : z ≠ 1) :
    weierstrassFactor m z ≠ 0 :=
  (weierstrassFactor_ne_zero_iff (m := m) (z := z)).2 hz

lemma weierstrassFactor_div_eq_zero_iff (m : ℕ) {a z : ℂ} (ha : a ≠ 0) :
    weierstrassFactor m (z / a) = 0 ↔ z = a := by
  rw [weierstrassFactor_eq_zero_iff]
  constructor
  · intro hz
    simpa using (div_eq_iff ha).mp hz
  · intro hz
    exact (div_eq_iff ha).mpr (by simpa only [one_mul] using hz)

lemma weierstrassFactor_div_ne_zero_iff (m : ℕ) {a z : ℂ} (ha : a ≠ 0) :
    weierstrassFactor m (z / a) ≠ 0 ↔ z ≠ a := by
  rw [not_iff_not]
  exact weierstrassFactor_div_eq_zero_iff m ha

lemma differentiable_weierstrassFactor (m : ℕ) :
    Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  simpa [weierstrassFactor] using!
    ((differentiable_const (c := (1 : ℂ))).sub differentiable_id).mul
      (differentiable_exp.comp (differentiable_partialLogSum m))

lemma hasDerivAt_weierstrassFactor_at_one (m : ℕ) :
    HasDerivAt (weierstrassFactor m) (-Complex.exp (partialLogSum m 1)) 1 := by
  have hsub : HasDerivAt (fun z : ℂ => 1 - z) (-1) 1 := by
    simpa using! (hasDerivAt_const (1 : ℂ) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hexp :
      HasDerivAt (fun z : ℂ => Complex.exp (partialLogSum m z))
        ((∑ j ∈ Finset.range m, (1 : ℂ) ^ j) * Complex.exp (partialLogSum m 1)) 1 := by
    simpa [mul_comm] using!
      (Complex.hasDerivAt_exp (partialLogSum m 1)).comp 1 (hasDerivAt_partialLogSum m 1)
  simpa [weierstrassFactor] using! hsub.mul hexp

@[simp]
lemma deriv_weierstrassFactor_at_one (m : ℕ) :
    deriv (weierstrassFactor m) 1 = -Complex.exp (partialLogSum m 1) :=
  (hasDerivAt_weierstrassFactor_at_one m).deriv

lemma deriv_weierstrassFactor_at_one_ne_zero (m : ℕ) :
    deriv (weierstrassFactor m) 1 ≠ 0 := by
  simp [deriv_weierstrassFactor_at_one]

lemma hasDerivAt_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ weierstrassFactor m (z / a))
      ((-Complex.exp (partialLogSum m 1)) / a) a := by
  have hcomp :
      HasDerivAt ((weierstrassFactor m) ∘ fun z : ℂ ↦ z / a)
        ((-Complex.exp (partialLogSum m 1)) * (1 / a)) a :=
    HasDerivAt.comp (x := a) (h := fun z : ℂ ↦ z / a) (h₂ := weierstrassFactor m)
      (by simpa [ha] using hasDerivAt_weierstrassFactor_at_one m)
      ((hasDerivAt_id a).div_const a)
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using! hcomp

@[simp]
lemma deriv_weierstrassFactor_div_at_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a =
      (-Complex.exp (partialLogSum m 1)) / a :=
  (hasDerivAt_weierstrassFactor_div_at_self m ha).deriv

lemma deriv_weierstrassFactor_div_at_self_ne_zero (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    deriv (fun z : ℂ ↦ weierstrassFactor m (z / a)) a ≠ 0 := by
  simp [deriv_weierstrassFactor_div_at_self, ha]

/-- The elementary factor `z ↦ E_m (z / a)` has a simple zero at `a`. -/
theorem analyticOrderAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassFactor m (z / a)) a = (1 : ℕ∞) := by
  set F : ℂ → ℂ := fun z => weierstrassFactor m (z / a)
  have hF : AnalyticAt ℂ F a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hdiff : Differentiable ℂ F := (differentiable_weierstrassFactor m).comp hdiv
    exact Differentiable.analyticAt (f := F) hdiff a
  let g : ℂ → ℂ := fun z => (-a⁻¹) * Complex.exp (partialLogSum m (z / a))
  have hg : AnalyticAt ℂ g a := by
    have hdiv : Differentiable ℂ (fun z : ℂ => z / a) := by
      simp [div_eq_mul_inv]
    have hpls : Differentiable ℂ (fun z : ℂ => partialLogSum m (z / a)) :=
      (differentiable_partialLogSum m).comp hdiv
    have hexp : Differentiable ℂ (fun z : ℂ => Complex.exp (partialLogSum m (z / a))) :=
      (Complex.differentiable_exp).comp hpls
    have hdiffg : Differentiable ℂ g := by
      simpa [g] using hexp.const_mul (-a⁻¹ : ℂ)
    exact Differentiable.analyticAt (f := g) hdiffg a
  have hg0 : g a ≠ 0 := by
    have hconst : (-a⁻¹ : ℂ) ≠ 0 := by simp [ha]
    have hexp0 : Complex.exp (partialLogSum m (a / a)) ≠ 0 :=
      Complex.exp_ne_zero (partialLogSum m (a / a))
    simpa [g] using mul_ne_zero hconst hexp0
  refine (hF.analyticOrderAt_eq_natCast (n := 1)).2 ?_
  refine ⟨g, hg, hg0, ?_⟩
  refine Filter.Eventually.of_forall ?_
  intro z
  have hlin : (1 - z / a) = (z - a) * (-a⁻¹) := by
    have h1 : (1 : ℂ) = a * a⁻¹ := by simp [ha]
    simp [div_eq_mul_inv, h1]
    ring
  simp only [F, g, pow_one, smul_eq_mul]
  rw [weierstrassFactor_def]
  simp [hlin, mul_assoc]

/-- The natural-valued analytic order of `z ↦ E_m (z / a)` at `a` is `1`. -/
theorem analyticOrderNatAt_weierstrassFactor_div_self (m : ℕ) {a : ℂ} (ha : a ≠ 0) :
    analyticOrderNatAt (fun z : ℂ => weierstrassFactor m (z / a)) a = 1 := by
  simp [analyticOrderNatAt, analyticOrderAt_weierstrassFactor_div_self (m := m) ha]

/-- For `‖z‖ < 1` and `z ≠ 1`, `E_m(z) = exp(-logTail_m(z))`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  rw [← exp_log hz_ne_1, ← Complex.exp_add]
  have hsum : log (1 - z) + partialLogSum m z = -logTail m z := by
    have hdecomp := neg_log_one_sub_eq_partialLogSum_add_logTail hz m
    calc
      log (1 - z) + partialLogSum m z
          = log (1 - z) + (partialLogSum m z + logTail m z) - logTail m z := by ring
      _ = log (1 - z) + (-log (1 - z)) - logTail m z := by rw [hdecomp]
      _ = -logTail m z := by ring
  simp [hsum]

/-! ## Power bound -/

/-- For `‖z‖ ≤ 1 / 2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^(m+1)`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  by_cases hm : m = 0
  · subst hm
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [weierstrassFactor] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound := norm_logTail_le_two_mul_norm_pow hz_lt hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by
          exact Nat.succ_le_succ (Nat.succ_le_iff.2 hm_pos)
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact (h_tail_bound.trans hmul).trans hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

/-!
## Lower bounds on `Real.log ‖weierstrassFactor m z‖`

Auxiliary inequalities for minimum-modulus / Cartan-type arguments in Hadamard factorization.
-/

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_sub (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - ‖partialLogSum m z‖ ≤ Real.log ‖weierstrassFactor m z‖ := by
  by_cases hz1 : z = (1 : ℂ)
  · subst hz1
    simp [weierstrassFactor]
  set S : ℂ := partialLogSum m z
  have hS : weierstrassFactor m z = (1 - z) * Complex.exp S := by
    simp [weierstrassFactor, S]
  have hnorm_pos : 0 < ‖(1 : ℂ) - z‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = Real.log ‖1 - z‖ + S.re := by
    have hne : ‖(1 : ℂ) - z‖ ≠ 0 := ne_of_gt hnorm_pos
    calc
      Real.log ‖weierstrassFactor m z‖
          = Real.log (‖(1 : ℂ) - z‖ * ‖Complex.exp S‖) := by
              simp [hS]
      _ = Real.log ‖(1 : ℂ) - z‖ + Real.log ‖Complex.exp S‖ := by
            simpa using (Real.log_mul hne (ne_of_gt (by simp)))
      _ = Real.log ‖(1 : ℂ) - z‖ + S.re := by
            simp [Complex.norm_exp, Real.log_exp]
      _ = Real.log ‖1 - z‖ + S.re := by simp [sub_eq_add_neg, add_comm]
  have hre : S.re ≥ -‖S‖ := Complex.neg_norm_le_re S
  have : Real.log ‖weierstrassFactor m z‖ ≥ Real.log ‖1 - z‖ - ‖S‖ := by
    linarith [hlog, hre]
  simpa [S] using this

lemma log_norm_weierstrassFactor_ge_neg_two_pow {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    (-2 : ℝ) * ‖z‖ ^ (m + 1) ≤ Real.log ‖weierstrassFactor m z‖ := by
  have hz_lt : ‖z‖ < (1 : ℝ) := lt_of_le_of_lt hz (by norm_num)
  have hz1 : z ≠ (1 : ℂ) := by
    intro h
    have : (1 : ℝ) ≤ (1 / 2 : ℝ) := by
      simpa [h] using hz
    norm_num at this
  have hEq : weierstrassFactor m z = Complex.exp (-logTail m z) :=
    weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
  have hlog :
      Real.log ‖weierstrassFactor m z‖ = (-logTail m z).re := by
    simp [hEq, Complex.norm_exp, Real.log_exp]
  have hre : (-logTail m z).re ≥ -‖logTail m z‖ := by
    simpa [norm_neg] using Complex.neg_norm_le_re (-logTail m z)
  have htail := norm_logTail_le_two_mul_norm_pow hz_lt hz m
  have : (-logTail m z).re ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
    calc
      (-logTail m z).re ≥ -‖logTail m z‖ := hre
      _ ≥ (-2 : ℝ) * ‖z‖ ^ (m + 1) := by
            nlinarith [htail]
  simpa [hlog, mul_assoc, mul_left_comm, mul_comm] using this

lemma log_norm_weierstrassFactor_ge_log_norm_one_sub_nat_mul_max_one_norm_pow
    (m : ℕ) (z : ℂ) :
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m) ≤ Real.log ‖weierstrassFactor m z‖ := by
  calc
    Real.log ‖1 - z‖ - (m : ℝ) * max 1 (‖z‖ ^ m)
        ≤ Real.log ‖1 - z‖ - ‖partialLogSum m z‖ := by
          gcongr
          exact norm_partialLogSum_le_nat_mul_max_one_norm_pow m z
    _ ≤ Real.log ‖weierstrassFactor m z‖ :=
      log_norm_weierstrassFactor_ge_log_norm_one_sub_sub m z

/-! ## Locally uniform convergence of products of scaled factors -/

private lemma eventually_le_norm_div_two_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2 := by
  intro R hR
  by_cases hR0 : R = 0
  · subst hR0
    exact Filter.Eventually.of_forall fun _ => by positivity
  have hRpos : 0 < R := lt_of_le_of_ne hR (by simpa [eq_comm] using hR0)
  have htend : Filter.Tendsto (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)) Filter.atTop (nhds (0 : ℝ)) := by
    simpa [Nat.cofinite_eq_atTop] using h_sum.tendsto_cofinite_zero
  have hεpos : 0 < (1 / (2 * R) : ℝ) ^ (m + 1) := by
    have : 0 < (1 / (2 * R) : ℝ) := by
      have : 0 < (2 * R : ℝ) := by positivity
      exact one_div_pos.mpr this
    exact pow_pos this _
  filter_upwards [htend.eventually (eventually_lt_nhds hεpos)] with n hn
  by_contra h
  have hlt : ‖a n‖ / 2 < R := lt_of_not_ge h
  have hle : ‖a n‖ ≤ 2 * R := by nlinarith
  have hanorm_pos : 0 < ‖a n‖ := norm_pos_iff.mpr (h_nonzero n)
  have hinv : (1 / (2 * R : ℝ)) ≤ ‖a n‖⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hanorm_pos hle)
  have hpow :
      (1 / (2 * R : ℝ)) ^ (m + 1) ≤ ‖a n‖⁻¹ ^ (m + 1) :=
    pow_le_pow_left₀ (by positivity) hinv _
  exact (not_lt_of_ge hpow) hn

private lemma summable_scaled_bound_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) :
    ∀ R ≥ 0, Summable (fun n : ℕ => 4 * R ^ (m + 1) / ‖a n‖ ^ (m + 1)) := by
  intro R _hR
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
    h_sum.mul_left (4 * R ^ (m + 1))

lemma continuousOn_weierstrassFactor_div (m : ℕ) (a : ℂ) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ ↦ weierstrassFactor m (z / a)) s := by
  simpa using! (differentiable_weierstrassFactor m).continuous.continuousOn.comp
    (continuous_id.div_const a).continuousOn (mapsTo_univ (fun z : ℂ ↦ z / a) s)

lemma norm_weierstrassFactor_div_sub_one_le_pow_div (m : ℕ) {a z : ℂ}
    (hza : ‖z‖ ≤ ‖a‖ / 2) :
    ‖weierstrassFactor m (z / a) - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by
  by_cases ha : a = 0
  · have hz : z = 0 := by
      apply norm_eq_zero.mp
      rw [ha] at hza
      simpa using hza
    subst z
    simp [ha]
  · have ha' : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hza' : ‖z / a‖ ≤ 1 / 2 := by
      rw [Complex.norm_div, div_le_iff₀ ha']
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hza
    have hbase := weierstrassFactor_sub_one_pow_bound (m := m) (z := z / a) hza'
    calc
      ‖weierstrassFactor m (z / a) - 1‖ ≤ ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) * 4 := by
        simpa [Complex.norm_div, div_pow, mul_comm, mul_left_comm, mul_assoc] using hbase
      _ = 4 * ‖z‖ ^ (m + 1) / ‖a‖ ^ (m + 1) := by ring

lemma summable_norm_weierstrassFactor_div_sub_one_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) (z : ℂ) :
    Summable (fun n : ℕ ↦ ‖weierstrassFactor m (z / a n) - 1‖) := by
  refine Summable.of_norm_bounded_eventually_nat
    (summable_scaled_bound_of_summable_inv_pow h_sum ‖z‖ (norm_nonneg z)) ?_
  filter_upwards
    [eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero ‖z‖ (norm_nonneg z)]
    with n hn
  simpa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
    norm_weierstrassFactor_div_sub_one_le_pow_div (m := m) (a := a n) (z := z) hn

lemma hasProdUniformlyOn_weierstrassFactor_div_of_bound {K : Set ℂ} (hK : IsCompact K)
    {m : ℕ → ℕ} {a : ℕ → ℂ} {R : ℝ}
    (hR : ∀ z ∈ K, ‖z‖ ≤ R) (hsmall : ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) K := by
  have hbound :
      ∀ᶠ n in Filter.atTop,
        ∀ z ∈ K,
          ‖weierstrassFactor (m n) (z / a n) - 1‖ ≤ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1) := by
    filter_upwards [hsmall] with n hn z hz
    refine (norm_weierstrassFactor_div_sub_one_le_pow_div (m := m n) ?_).trans ?_
    · exact (hR z hz).trans hn
    · have hpow : ‖z‖ ^ (m n + 1) ≤ R ^ (m n + 1) :=
        pow_le_pow_left₀ (norm_nonneg z) (hR z hz) (m n + 1)
      refine div_le_div_of_nonneg_right ?_ (pow_nonneg (norm_nonneg (a n)) _)
      exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hcts :
      ∀ n, ContinuousOn (fun z ↦ weierstrassFactor (m n) (z / a n) - 1) K := by
    intro n
    exact (continuousOn_weierstrassFactor_div (m n) (a n) K).fun_sub continuousOn_const
  simpa using hsumm.hasProdUniformlyOn_nat_one_add (K := K)
    (f := fun n z ↦ weierstrassFactor (m n) (z / a n) - 1) hK hbound hcts

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor (m n) (z / a n)) s := by
  apply hasProdLocallyUniformlyOn_of_forall_compact hs
  intro K hKs hK
  obtain ⟨R, hR⟩ : ∃ R, ∀ z ∈ K, ‖z‖ ≤ R := by
    by_cases hKe : K.Nonempty
    · obtain ⟨z, hzK, hzmax⟩ := hK.exists_isMaxOn hKe continuous_norm.continuousOn
      exact ⟨‖z‖, fun w hw ↦ (isMaxOn_iff.mp hzmax) w hw⟩
    · exact ⟨0, fun z hz ↦ False.elim <| hKe ⟨z, hz⟩⟩
  let R' := max R 0
  have hR'0 : 0 ≤ R' := le_max_right _ _
  have hR' : ∀ z ∈ K, ‖z‖ ≤ R' := by
    intro z hz
    exact (hR z hz).trans (le_max_left _ _)
  exact hasProdUniformlyOn_weierstrassFactor_div_of_bound hK hR'
    (hsmall R' hR'0) (hsumm R' hR'0)

lemma hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ} {a : ℕ → ℂ}
    (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1))) (h_nonzero : ∀ n, a n ≠ 0) :
    HasProdLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n))
      (fun z ↦ ∏' n, weierstrassFactor m (z / a n)) Set.univ := by
  simpa using
    hasProdLocallyUniformlyOn_weierstrassFactor_div (s := (Set.univ : Set ℂ)) isOpen_univ
      (m := fun _ => m) (a := a)
      (eventually_le_norm_div_two_of_summable_inv_pow h_sum h_nonzero)
      (summable_scaled_bound_of_summable_inv_pow h_sum)

lemma multipliableLocallyUniformlyOn_weierstrassFactor_div {s : Set ℂ} (hs : IsOpen s)
    {m : ℕ → ℕ} {a : ℕ → ℂ}
    (hsmall : ∀ R ≥ 0, ∀ᶠ n in Filter.atTop, R ≤ ‖a n‖ / 2)
    (hsumm : ∀ R ≥ 0, Summable (fun n : ℕ ↦ 4 * R ^ (m n + 1) / ‖a n‖ ^ (m n + 1))) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor (m n) (z / a n)) s :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactor_div hs hsmall hsumm⟩

lemma multipliableLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow {m : ℕ}
    {a : ℕ → ℂ} (h_sum : Summable (fun n : ℕ => ‖a n‖⁻¹ ^ (m + 1)))
    (h_nonzero : ∀ n, a n ≠ 0) :
    MultipliableLocallyUniformlyOn (fun n z ↦ weierstrassFactor m (z / a n)) Set.univ :=
  ⟨_, hasProdLocallyUniformlyOn_weierstrassFactor_div_of_summable_inv_pow h_sum h_nonzero⟩

end Complex
