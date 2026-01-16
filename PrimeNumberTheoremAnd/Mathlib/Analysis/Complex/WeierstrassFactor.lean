import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Power bound for Weierstrass elementary factors

This file is **PR 1** in the upstream refactoring roadmap.

It provides a self-contained, sequence-friendly API for Weierstrass elementary factors,
independent of any external zero-enumeration structure (no `ZeroData`, no padding conventions).

The key analytic estimate is:

`‖E_m(z) - 1‖ ≤ 4 * ‖z‖^(m+1)` for `‖z‖ ≤ 1/2`.
-/

noncomputable section

open Complex Real Set Filter Topology
open scoped BigOperators Topology

namespace Complex.Hadamard

/-! ## Partial logarithm series -/

/-- The partial sum `P_m(z) = ∑_{k=1}^m z^k/k`. -/
def partialLogSum (m : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)

/-- `partialLogSum 0 z = 0`. -/
@[simp] lemma partialLogSum_range_zero (z : ℂ) : partialLogSum 0 z = 0 := by
  simp [partialLogSum]

/-- The tail of the log series: `-log(1-z) - P_m(z) = ∑_{k>m} z^k/k`. -/
def logTail (m : ℕ) (z : ℂ) : ℂ :=
  ∑' k, z ^ (m + 1 + k) / (m + 1 + k)

/-- For `‖z‖ < 1`, `-log(1-z) = ∑_{k≥1} z^k/k`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ < 1) :
    -log (1 - z) = ∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
  have h := Complex.hasSum_taylorSeries_neg_log hz
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add, Nat.cast_add, Nat.cast_one]

/-- The log tail converges for `‖z‖ < 1`. -/
lemma summable_logTail {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Summable (fun k => z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)) := by
  have h_geom : Summable (fun k : ℕ => ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz
  refine Summable.of_norm_bounded (g := fun k => ‖z‖ ^ k) h_geom ?_
  intro k
  rw [norm_div, norm_pow]
  have h1 : (1 : ℝ) ≤ (m + 1 + k : ℝ) := by
    have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
    nlinarith
  have h_denom : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
    have : (↑m + 1 + ↑k : ℂ) = ((m + 1 + k : ℕ) : ℂ) := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [this, Complex.norm_natCast]
    simp
  rw [h_denom]
  calc
    ‖z‖ ^ (m + 1 + k) / (m + 1 + k : ℝ)
        ≤ ‖z‖ ^ (m + 1 + k) := by
              exact div_le_self (pow_nonneg (norm_nonneg z) _) h1
    _ = ‖z‖ ^ (m + 1) * ‖z‖ ^ k := by rw [pow_add]
    _ ≤ 1 * ‖z‖ ^ k := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) k)
          exact pow_le_one₀ (norm_nonneg z) (le_of_lt hz)
    _ = ‖z‖ ^ k := one_mul _

/-- Bound on the log tail: `‖∑_{k>m} z^k/k‖ ≤ ‖z‖^{m+1}/(1-‖z‖)`. -/
lemma norm_logTail_le {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    ‖logTail m z‖ ≤ ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
  unfold logTail
  have h1mr_pos : 0 < 1 - ‖z‖ := sub_pos.mpr hz
  have h_summable := summable_logTail hz m
  calc
    ‖∑' k, z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖
        ≤ ∑' k, ‖z ^ (m + 1 + k) / ((m + 1 + k) : ℂ)‖ :=
          norm_tsum_le_tsum_norm h_summable.norm
    _ ≤ ∑' k, ‖z‖ ^ (m + 1 + k) := by
          have h_rhs_summable : Summable (fun k => ‖z‖ ^ (m + 1 + k)) := by
            simpa [pow_add] using (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ (m + 1))
          refine h_summable.norm.tsum_le_tsum ?_ h_rhs_summable
          intro k
          rw [norm_div, norm_pow]
          have hm : 1 ≤ (m + 1 + k : ℝ) := by
            have : (0 : ℝ) ≤ (m + k : ℝ) := by positivity
            nlinarith
          have h_denom : ‖(↑m + 1 + ↑k : ℂ)‖ = (m + 1 + k : ℝ) := by
            have : (↑m + 1 + ↑k : ℂ) = ((m + 1 + k : ℕ) : ℂ) := by
              simp only [Nat.cast_add, Nat.cast_one]
            rw [this, Complex.norm_natCast]
            simp
          rw [h_denom]
          exact div_le_self (pow_nonneg (norm_nonneg z) _) hm
    _ = ‖z‖ ^ (m + 1) / (1 - ‖z‖) := by
          have h_eq : (fun k => ‖z‖ ^ (m + 1 + k)) = (fun k => ‖z‖ ^ (m + 1) * ‖z‖ ^ k) := by
            ext k; rw [pow_add]
          rw [h_eq, tsum_mul_left]
          have h_geom := hasSum_geometric_of_lt_one (norm_nonneg z) hz
          rw [h_geom.tsum_eq, div_eq_mul_inv]

/-- For `‖z‖ ≤ 1/2`: `‖z‖^{m+1}/(1-‖z‖) ≤ 2‖z‖^{m+1}`. -/
lemma norm_pow_div_one_sub_le_two {z : ℂ} (hz : ‖z‖ ≤ 1/2) (m : ℕ) :
    ‖z‖ ^ (m + 1) / (1 - ‖z‖) ≤ 2 * ‖z‖ ^ (m + 1) := by
  have h1mr_pos : 0 < 1 - ‖z‖ := by linarith [norm_nonneg z]
  have h1mr_ge_half : 1 - ‖z‖ ≥ 1/2 := by linarith
  rw [div_le_iff₀ h1mr_pos]
  calc
    ‖z‖ ^ (m + 1) = 1 * ‖z‖ ^ (m + 1) := by ring
    _ ≤ 2 * (1 - ‖z‖) * ‖z‖ ^ (m + 1) := by
          refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg z) _)
          nlinarith
    _ = 2 * ‖z‖ ^ (m + 1) * (1 - ‖z‖) := by ring

/-! ## The Weierstrass factor representation -/

/-- The Weierstrass elementary factor. -/
def weierstrassFactor (m : ℕ) (z : ℂ) : ℂ :=
  (1 - z) * exp (partialLogSum m z)

/-- The elementary factor `E₀(z) = 1 - z`. -/
@[simp] lemma weierstrassFactor_zero (z : ℂ) : weierstrassFactor 0 z = 1 - z := by
  simp [weierstrassFactor]

/-- The elementary factor at `z = 0` equals `1`. -/
@[simp] lemma weierstrassFactor_at_zero (m : ℕ) : weierstrassFactor m 0 = 1 := by
  simp [weierstrassFactor, partialLogSum]

/-- The elementary factor vanishes at `z = 1`. -/
@[simp] lemma weierstrassFactor_at_one (m : ℕ) : weierstrassFactor m 1 = 0 := by
  simp [weierstrassFactor]

/-- The Weierstrass factor vanishes exactly at `z = 1`. -/
lemma weierstrassFactor_eq_zero_iff (m : ℕ) (z : ℂ) :
    weierstrassFactor m z = 0 ↔ z = 1 := by
  constructor
  · intro hz
    -- `exp _` never vanishes, so the zero comes from the factor `1 - z`.
    have : (1 - z) = 0 := by
      have hexp : Complex.exp (partialLogSum m z) ≠ 0 := Complex.exp_ne_zero _
      -- from `a * b = 0` and `b ≠ 0`, infer `a = 0`
      exact mul_eq_zero.mp (by simpa [weierstrassFactor] using hz) |>.resolve_right hexp
    have hz' : (1 : ℂ) = z := by
      simpa [sub_eq_zero] using this
    simpa using hz'.symm
  · rintro rfl
    simp [weierstrassFactor]

lemma differentiable_partialLogSum (m : ℕ) : Differentiable ℂ (fun z : ℂ => partialLogSum m z) := by
  classical
  -- rewrite as a finite sum of differentiable functions
  -- (we keep the `∑ k ∈ ...` syntax, but treat it as a `Finset.sum` of functions)
  have :
      Differentiable ℂ (∑ k ∈ Finset.range m, fun z : ℂ => z ^ (k + 1) / (k + 1)) := by
    refine Differentiable.sum (u := Finset.range m) ?_
    intro k hk
    have hpow : Differentiable ℂ (fun z : ℂ => z ^ (k + 1)) := differentiable_pow (k + 1)
    -- `z ↦ z^(k+1) / (k+1) = z^(k+1) * (k+1)⁻¹`
    have hmul : Differentiable ℂ (fun z : ℂ => z ^ (k + 1) * ((k + 1 : ℂ)⁻¹)) :=
      hpow.mul_const ((k + 1 : ℂ)⁻¹)
    -- rewrite the goal and finish
    convert hmul using 1
  -- now unfold `partialLogSum`
  have hsum :
      (∑ k ∈ Finset.range m, fun z : ℂ => z ^ (k + 1) / (k + 1))
        = (fun z : ℂ => ∑ k ∈ Finset.range m, z ^ (k + 1) / (k + 1)) := by
    funext z
    simp
  simp [hsum] at this
  exact this

lemma differentiable_weierstrassFactor (m : ℕ) : Differentiable ℂ (fun z : ℂ => weierstrassFactor m z) := by
  have hsub : Differentiable ℂ (fun z : ℂ => (1 : ℂ) - z) :=
    ((differentiable_const (c := (1 : ℂ)) : Differentiable ℂ (fun _ : ℂ => (1 : ℂ)))).sub differentiable_id
  have hexp : Differentiable ℂ (fun z : ℂ => exp (partialLogSum m z)) :=
    differentiable_exp.comp (differentiable_partialLogSum m)
  simpa [weierstrassFactor] using hsub.mul hexp

/-- `E_m(z) = exp(-logTail_m(z))` for `‖z‖ < 1` with `z ≠ 1`. -/
lemma weierstrassFactor_eq_exp_neg_tail (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) (hz1 : z ≠ 1) :
    weierstrassFactor m z = exp (-logTail m z) := by
  unfold weierstrassFactor partialLogSum logTail
  have hz_ne_1 : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  have h_log : log (1 - z) = -∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
    -- from `-log(1-z) = S` we get `log(1-z) = -S`
    simpa using (congrArg Neg.neg (neg_log_one_sub_eq_tsum (z := z) hz))
  -- Convert `1 - z` to `exp(log(1-z))`.
  rw [← exp_log hz_ne_1, ← Complex.exp_add, h_log]
  congr 1
  rw [add_comm, ← sub_eq_add_neg, ← neg_sub, neg_inj]
  let f : ℕ → ℂ := fun k => z ^ (k + 1) / ((k : ℂ) + 1)
  have h_summable : Summable f := by
    have h_geom := summable_geometric_of_lt_one (norm_nonneg z) hz
    refine Summable.of_norm_bounded (g := fun (k : ℕ) => ‖z‖ * ‖z‖ ^ k) (h_geom.mul_left ‖z‖) (fun k => ?_)
    simp only [f, norm_div, norm_mul, norm_pow, pow_succ, mul_comm ‖z‖]
    have hk : 1 ≤ (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    have h_norm : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
      have h1 : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_natCast]; simp
    rw [h_norm]
    exact div_le_self (mul_nonneg (pow_nonneg (norm_nonneg z) k) (norm_nonneg z)) hk
  have h_decomp := h_summable.sum_add_tsum_nat_add m
  rw [← h_decomp, add_sub_cancel_left]
  congr 1
  ext k
  simp only [f, Nat.cast_add]
  ring_nf

/-! ## The power bound -/

/-- For `‖z‖ ≤ 1/2`, `‖E_m(z) - 1‖ ≤ 4‖z‖^{m+1}`. -/
theorem weierstrassFactor_sub_one_pow_bound {m : ℕ} {z : ℂ} (hz : ‖z‖ ≤ 1/2) :
    ‖weierstrassFactor m z - 1‖ ≤ 4 * ‖z‖ ^ (m + 1) := by
  classical
  by_cases hm : m = 0
  · subst hm
    have hE0 : weierstrassFactor 0 z = 1 - z := by
      simp [weierstrassFactor, partialLogSum, Finset.range_zero]
    -- reduce to a simple norm computation
    have hmain : ‖(1 - z) - 1‖ ≤ 4 * ‖z‖ ^ 1 := by
      have h : (1 - z) - 1 = -z := by ring
      calc
        ‖(1 - z) - 1‖ = ‖-z‖ := by simp [h]
        _ = ‖z‖ := norm_neg z
        _ = ‖z‖ ^ 1 := by simp
        _ ≤ 4 * ‖z‖ ^ 1 := by nlinarith [pow_nonneg (norm_nonneg z) 1]
    simpa [hE0] using hmain
  · have hz_lt : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
    by_cases hz1 : z = 1
    · exfalso; rw [hz1] at hz; norm_num at hz
    have h_eq : weierstrassFactor m z = exp (-logTail m z) :=
      weierstrassFactor_eq_exp_neg_tail m hz_lt hz1
    rw [h_eq]
    have h_tail_bound : ‖logTail m z‖ ≤ 2 * ‖z‖ ^ (m + 1) := by
      refine le_trans (norm_logTail_le hz_lt m) ?_
      exact norm_pow_div_one_sub_le_two hz m
    have hw_le_one : ‖-logTail m z‖ ≤ 1 := by
      simp only [norm_neg]
      have : ‖logTail m z‖ ≤ 1 := by
        -- crude but sufficient: `‖logTail‖ ≤ 2‖z‖^{m+1} ≤ 2(1/2)^2 = 1/2`
        have hm_pos : 0 < m := Nat.pos_of_ne_zero hm
        have h2 : 2 ≤ m + 1 := by omega
        have hpow : (‖z‖ ^ (m + 1)) ≤ (‖z‖ ^ 2) := by
          have hz1' : ‖z‖ ≤ 1 := by nlinarith [hz]
          have hz0' : 0 ≤ ‖z‖ := norm_nonneg z
          exact pow_le_pow_of_le_one hz0' hz1' h2
        have hmul : 2 * ‖z‖ ^ (m + 1) ≤ 2 * ‖z‖ ^ 2 := by gcongr
        have hsq : 2 * ‖z‖ ^ 2 ≤ 1 := by
          -- from `‖z‖ ≤ 1/2` we get `‖z‖^2 ≤ 1/4`
          have hz0 : 0 ≤ ‖z‖ := norm_nonneg z
          have hz_sq : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz 2
          nlinarith
        exact le_trans (le_trans h_tail_bound hmul) hsq
      linarith
    have h_exp_sub_one : ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖-logTail m z‖ :=
      Complex.norm_exp_sub_one_le hw_le_one
    simp only [norm_neg] at h_exp_sub_one
    calc
      ‖exp (-logTail m z) - 1‖ ≤ 2 * ‖logTail m z‖ := h_exp_sub_one
      _ ≤ 2 * (2 * ‖z‖ ^ (m + 1)) := by gcongr
      _ = 4 * ‖z‖ ^ (m + 1) := by ring

end Complex.Hadamard
