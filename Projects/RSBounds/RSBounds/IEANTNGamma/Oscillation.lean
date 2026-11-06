/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNGamma.Recurrence
import RSBounds.IEANTNGamma.ComplexToReal

/-!
# Stage 2f: `E = ψ - G` varies by `O(1/n)` across a unit interval

The third and last hypothesis of `eq_zero_of_periodic_of_nat_of_oscillation`. For `a, b ≥ n ≥ 1`
at distance at most one,

  `‖E a - E b‖ ≤ 5/n`.

The two sides are bounded quite differently:

* **the `ψ` side, `≤ 3/n`**, comes from Stage 1. Writing
  `ψ(a) - ψ(b) = (ψ(a) - log a) + (log a - log b) - (ψ(b) - log b)`, the two outer brackets are at
  most `1/a` and `1/b` by `abs_deriv_log_Gamma_sub_log_le`, and `|log a - log b| ≤ |a - b| / n`
  from `log(1 + t) ≤ t`.
* **the `G` side, `≤ 2/n`**, is a series computation. Termwise
  `gaussTerm a k - gaussTerm b k = (a - b) / ((k+a)(k+b))`, so the `1/(k+1)` that carries the
  divergence cancels and what is left is `O(1/k²)`, summing to `O(1/n)` rather than `O(1)`. The
  comparison used is `1/((k+a)(k+b)) ≤ 2/((k+n)(k+n+1))`, whose right side telescopes to `2/n`
  exactly — no `p`-series constant survives into the answer, and the same `hasSum_sub_succ` from
  `Recurrence.lean` does the work one type down, which is why that lemma is stated over an
  arbitrary complete normed group.

Note which direction the difficulty runs. The `O(1/n)` is not a refinement for its own sake: a
bound of `O(1)` on either side would leave `E` merely bounded, which no amount of periodicity
turns into `E = 0`. The whole argument turns on the oscillation shrinking.
-/

namespace GammaSolution

open Complex

/-! ### The telescoping sum, over `ℝ` -/

/-- The differences `1/(k+t) - 1/(k+t+1) = 1/((k+t)(k+t+1))` are summable, by comparison with
`1/k²` past `k = 1`. -/
theorem summable_telescope {t : ℝ} (ht : 1 ≤ t) :
    Summable (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) := by
  have hcomp : Summable (fun k : ℕ ↦ 1 / (k : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  refine Summable.of_norm_bounded_eventually_nat hcomp ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with k hk
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsq : (0 : ℝ) < (k : ℝ) ^ 2 := by nlinarith
  have hpos : (0 : ℝ) < ((k : ℝ) + t) * ((k : ℝ) + t + 1) := by nlinarith
  rw [Real.norm_of_nonneg (by positivity), inv_eq_one_div, div_le_div_iff₀ hpos hsq]
  nlinarith

/-- **The telescoping value**: `∑ₖ 1/((k+t)(k+t+1)) = 1/t`.

This is what replaces a `p`-series constant in the bound below: the comparison series can be
summed exactly, so the final `2/n` carries no anonymous constant. -/
theorem tsum_telescope {t : ℝ} (ht : 1 ≤ t) :
    ∑' k : ℕ, (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ = t⁻¹ := by
  set f : ℕ → ℝ := fun k ↦ ((k : ℝ) + t)⁻¹ with hf
  have hne : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + t := fun k ↦ by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hdiff : ∀ k : ℕ, f k - f (k + 1) = (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹ := by
    intro k
    have h1 : ((k : ℝ) + t) ≠ 0 := (hne k).ne'
    have h2 : (((k : ℕ) + 1 : ℕ) : ℝ) + t ≠ 0 := (hne (k + 1)).ne'
    simp only [hf]
    push_cast at h2 ⊢
    field_simp
    ring
  have hsum : Summable (fun k : ℕ ↦ f k - f (k + 1)) := by
    simpa only [hdiff] using summable_telescope ht
  have hlim : Filter.Tendsto f Filter.atTop (nhds 0) := by
    simp only [hf]
    exact Filter.Tendsto.inv_tendsto_atTop
      (Filter.tendsto_atTop_add_const_right _ t tendsto_natCast_atTop_atTop)
  have h := hasSum_sub_succ hsum hlim
  have hf0 : f 0 = t⁻¹ := by simp [hf]
  rw [hf0] at h
  simpa only [hdiff] using h.tsum_eq

/-- The comparison series, with its sum: `∑ₖ |a-b| * 2/((k+n)(k+n+1)) = |a-b| * (2/n)`. -/
theorem hasSum_comparison {t : ℝ} (ht : 1 ≤ t) (c : ℝ) :
    HasSum (fun k : ℕ ↦ c * (2 * (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹)) (c * (2 * t⁻¹)) := by
  have h : HasSum (fun k : ℕ ↦ (((k : ℝ) + t) * ((k : ℝ) + t + 1))⁻¹) t⁻¹ := by
    rw [← tsum_telescope ht]
    exact (summable_telescope ht).hasSum
  exact (h.mul_left 2).mul_left c

/-! ### The `G` side -/

/-- Termwise, `gaussTerm a k - gaussTerm b k = (a - b)/((k+a)(k+b))`: the divergent `1/(k+1)`
cancels, which is the whole reason the difference is `O(1/n)` and each series alone is not. -/
theorem gaussTerm_sub {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k
      = ((a : ℂ) - b) / (((k : ℂ) + a) * ((k : ℂ) + b)) := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : ((k : ℂ) + a) ≠ 0 := by
    intro h
    have : (k : ℝ) + a = 0 := by exact_mod_cast congrArg Complex.re h
    linarith
  have h2 : ((k : ℂ) + b) ≠ 0 := by
    intro h
    have : (k : ℝ) + b = 0 := by exact_mod_cast congrArg Complex.re h
    linarith
  simp only [gaussTerm]
  field_simp
  ring

/-- **The `G` side of the oscillation**: `‖G a - G b‖ ≤ |a - b| * (2/n)`.

The comparison is `1/((k+a)(k+b)) ≤ 2/((k+n)(k+n+1))`, valid because `a, b ≥ n ≥ 1` makes
`(k+a)(k+b) ≥ (k+n)²` and `(k+n+1) ≤ 2(k+n)`. -/
theorem norm_gaussSum_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) :
    ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ |a - b| * (2 / n) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have habs : (0 : ℝ) ≤ |a - b| := abs_nonneg _
  have hsa : ∀ m : ℕ, (a : ℂ) ≠ -m := fun m h ↦ by
    have h' : a = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hsb : ∀ m : ℕ, (b : ℂ) ≠ -m := fun m h ↦ by
    have h' : b = -(m : ℝ) := by exact_mod_cast h
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  -- The difference of the two series, term by term.
  have hHS : HasSum (fun k ↦ gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k)
      (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by
    have h := (summable_gaussTerm hsa).hasSum.sub (summable_gaussTerm hsb).hasSum
    simpa only [gaussSum, add_sub_add_left_eq_sub] using h
  -- Each term, bounded by the telescoping comparison scaled by `|a - b|`.
  have hbound : ∀ k : ℕ, ‖gaussTerm (a : ℂ) k - gaussTerm (b : ℂ) k‖
      ≤ |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by
    intro k
    have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hka : (0 : ℝ) < (k : ℝ) + a := by linarith
    have hkb : (0 : ℝ) < (k : ℝ) + b := by linarith
    have hknpos : (0 : ℝ) < (k : ℝ) + n := by linarith
    have hprod : (0 : ℝ) < ((k : ℝ) + a) * ((k : ℝ) + b) := mul_pos hka hkb
    have hnprod : (0 : ℝ) < ((k : ℝ) + n) * ((k : ℝ) + n + 1) := by positivity
    rw [gaussTerm_sub hapos hbpos k, norm_div, norm_mul]
    have hna : ‖((k : ℂ) + a)‖ = (k : ℝ) + a := by
      have hc : ((k : ℂ) + a) = (((k : ℝ) + a : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hka.le]
    have hnb : ‖((k : ℂ) + b)‖ = (k : ℝ) + b := by
      have hc : ((k : ℂ) + b) = (((k : ℝ) + b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_of_nonneg hkb.le]
    have hnum : ‖((a : ℂ) - b)‖ = |a - b| := by
      have hc : ((a : ℂ) - b) = ((a - b : ℝ) : ℂ) := by push_cast; ring
      rw [hc, Complex.norm_real, Real.norm_eq_abs]
    rw [hna, hnb, hnum]
    have hcmp : 1 / (((k : ℝ) + a) * ((k : ℝ) + b))
        ≤ 2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1)) := by
      rw [div_le_div_iff₀ hprod hnprod]
      nlinarith
    calc |a - b| / (((k : ℝ) + a) * ((k : ℝ) + b))
        = |a - b| * (1 / (((k : ℝ) + a) * ((k : ℝ) + b))) := by ring
      _ ≤ |a - b| * (2 / (((k : ℝ) + n) * ((k : ℝ) + n + 1))) :=
          mul_le_mul_of_nonneg_left hcmp habs
      _ = |a - b| * (2 * (((k : ℝ) + n) * ((k : ℝ) + n + 1))⁻¹) := by ring
  have hle := hHS.norm_le_of_bounded (hasSum_comparison hn1 |a - b|) hbound
  refine hle.trans_eq ?_
  field_simp

/-! ### The `ψ` side -/

/-- `|log a - log b| ≤ |a - b| / n` for `a, b ≥ n > 0`, from `log(1 + t) ≤ t`. -/
theorem abs_log_sub_log_le {n : ℝ} (hn : 0 < n) {a b : ℝ} (ha : n ≤ a) (hb : n ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / n := by
  -- Symmetric in `a` and `b`, so it is enough to do the case `b ≤ a`.
  have key : ∀ u v : ℝ, n ≤ u → n ≤ v → v ≤ u → Real.log u - Real.log v ≤ (u - v) / n := by
    intro u v hu hv hvu
    have hvpos : (0 : ℝ) < v := lt_of_lt_of_le hn hv
    have hupos : (0 : ℝ) < u := lt_of_lt_of_le hn hu
    rw [← Real.log_div hupos.ne' hvpos.ne']
    have h1 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h2 : u / v - 1 = (u - v) / v := by field_simp
    have h3 : (u - v) / v ≤ (u - v) / n := by gcongr
    linarith
  rcases le_total b a with h | h
  · have hlog : Real.log b ≤ Real.log a := Real.log_le_log (lt_of_lt_of_le hn hb) h
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    exact key a b ha hb h
  · have hlog : Real.log a ≤ Real.log b := Real.log_le_log (lt_of_lt_of_le hn ha) h
    rw [abs_sub_comm, abs_sub_comm a b, abs_of_nonneg (by linarith),
      abs_of_nonneg (by linarith)]
    exact key b a hb ha h

/-- **The `ψ` side of the oscillation**: `|ψ a - ψ b| ≤ 3/n`, from Stage 1. -/
theorem abs_deriv_log_Gamma_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    |deriv (fun t ↦ Real.log (Real.Gamma t)) a - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
      ≤ 3 / n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  have h1 := abs_deriv_log_Gamma_sub_log_le hapos
  have h2 := abs_deriv_log_Gamma_sub_log_le hbpos
  have h3 := abs_log_sub_log_le hnpos ha hb
  have h1n : (1 : ℝ) / a ≤ 1 / n := by gcongr
  have h2n : (1 : ℝ) / b ≤ 1 / n := by gcongr
  have h3n : |a - b| / n ≤ 1 / n := by gcongr
  -- Two triangle inequalities through `log a` and `log b`.
  have t1 := abs_sub_le (deriv (fun t ↦ Real.log (Real.Gamma t)) a) (Real.log a)
    (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
  have t2 := abs_sub_le (Real.log a) (Real.log b)
    (deriv (fun t ↦ Real.log (Real.Gamma t)) b)
  have t3 : |Real.log b - deriv (fun t ↦ Real.log (Real.Gamma t)) b|
      = |deriv (fun t ↦ Real.log (Real.Gamma t)) b - Real.log b| := abs_sub_comm _ _
  have hthree : (3 : ℝ) / n = 1 / n + 1 / n + 1 / n := by ring
  linarith

/-! ### The two sides together -/

/-- **Stage 2f**: `E = ψ - G` varies by at most `5/n` across a unit interval to the right of `n`.

This is the third and last hypothesis of `eq_zero_of_periodic_of_nat_of_oscillation`, with
`C = 5`. -/
theorem norm_error_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    ‖(Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
        - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))‖ ≤ 5 / n := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hapos : (0 : ℝ) < a := by linarith
  have hbpos : (0 : ℝ) < b := by linarith
  -- Split into the `ψ` difference and the `G` difference.
  have hsplit : (Complex.digamma (a : ℂ) - gaussSum (a : ℂ))
      - (Complex.digamma (b : ℂ) - gaussSum (b : ℂ))
      = (Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ))
        - (gaussSum (a : ℂ) - gaussSum (b : ℂ)) := by ring
  -- The `ψ` difference is real, and Stage 1 bounds it.
  have hpsi : ‖Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ)‖ ≤ 3 / n := by
    rw [digamma_ofReal hapos, digamma_ofReal hbpos, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    exact abs_deriv_log_Gamma_sub_le hn ha hb hab
  have hG : ‖gaussSum (a : ℂ) - gaussSum (b : ℂ)‖ ≤ 2 / n := by
    refine (norm_gaussSum_sub_le hn ha hb).trans ?_
    have hle : |a - b| * (2 / n) ≤ 1 * (2 / n) := by gcongr
    simpa using hle
  have hfive : (5 : ℝ) / n = 3 / n + 2 / n := by ring
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  linarith

end GammaSolution
