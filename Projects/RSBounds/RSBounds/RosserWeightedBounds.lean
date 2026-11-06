import RSBounds.WeightedZetaZeros
import RSBounds.RosserTailIntegrals

/-!
# Explicit reciprocal and fifth-power sums over actual zeta zeros

The sums use analytic multiplicities and the interval `(a,b]`. All zero-count
bounds are the proved unconditional Rosser theorem. Only endpoint-range
conditions occur in the final estimates; no RH or count hypothesis is needed.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.RosserWeightedBounds
open Rosser1941 WeightedZetaZeros RosserTailIntegrals BacklundCountIdentity

noncomputable def G (t : ℝ) : ℝ := rosserF t + rosserR 1.588 t

/-- Explicit low-weight integral allowance. -/
noncomputable def I (a b : ℝ) : ℝ :=
  (Real.log (b / (2 * Real.pi)) ^ 2 - Real.log (a / (2 * Real.pi)) ^ 2) /
    (4 * Real.pi) + (0.137 + 0.443 / Real.log a) * (1 / a - 1 / b)

theorem hasDerivAt_reciprocal {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 / t) (-1 / t ^ 2) t := by
  simpa only [one_div, neg_div, neg_mul, one_mul] using hasDerivAt_inv ht.ne'

theorem hasDerivAt_reciprocal_fifth {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 5) (-5 / t ^ 6) t := by
  have hp : (fun t : ℝ => t ^ 5) t ≠ 0 := pow_ne_zero 5 ht.ne'
  have hh := (hasDerivAt_const t (1 : ℝ)).div ((hasDerivAt_id t).pow 5) hp
  convert hh using 1
  · rfl
  · dsimp only [id_eq, Pi.pow_apply]
    field_simp [ht.ne']
    <;> ring

private theorem derivative_reciprocal_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => -1 / t ^ 2) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : 0 < t := ha.trans_le ht.1
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

private theorem derivative_fifth_integrable {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => -5 / t ^ 6) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hab] at ht
  have ht0 : 0 < t := ha.trans_le ht.1
  exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))

/-- The reciprocal estimate with both signed endpoint corrections preserved. -/
theorem reciprocal_sum_le_endpoints {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t) ≤ I a b +
      (positiveZeroCount b - G b) / b + (G a - positiveZeroCount a) / a := by
  have ha0 : 0 < a := by linarith
  have he := weightedSum_le_decreasing (by linarith : 2 ≤ a) hab
    (fun t ht => hasDerivAt_reciprocal (ha0.trans_le ht.1))
    (derivative_reciprocal_integrable ha0 hab)
    (fun t _ => div_nonpos_of_nonpos_of_nonneg (by norm_num) (sq_nonneg t))
  have hi := integral_density_div_le ha hab
  change (∫ t in a..b, density t / t) ≤ I a b at hi
  have he' : weightedSum a b (fun t => 1 / t) ≤
      (∫ t in a..b, density t / t) +
      (positiveZeroCount b - G b) / b + (G a - positiveZeroCount a) / a := by
    convert he using 1 <;> simp only [density, G, mul_one_div] <;> ring
  linarith

/-- Discard the nonpositive upper-endpoint term in the reciprocal estimate. -/
theorem reciprocal_sum_le_head {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t) ≤ I a b + (G a - positiveZeroCount a) / a := by
  have he := reciprocal_sum_le_endpoints ha hab
  have hb0 : 0 < b := by linarith
  have hc := zero_count_bounds b (by linarith)
  change |positiveZeroCount b - rosserF b| < rosserR 1.588 b at hc
  have hn : positiveZeroCount b - G b ≤ 0 := by
    unfold G
    linarith [(abs_lt.mp hc).2]
  have hp := div_nonpos_of_nonpos_of_nonneg hn hb0.le
  linarith

/-- The fifth-power estimate with both signed endpoint corrections. -/
theorem fifth_sum_le_endpoints {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 5) ≤ J a +
      (positiveZeroCount b - G b) / b ^ 5 +
      (G a - positiveZeroCount a) / a ^ 5 := by
  have ha0 : 0 < a := by linarith
  have he := weightedSum_le_decreasing (by linarith : 2 ≤ a) hab
    (fun t ht => hasDerivAt_reciprocal_fifth (ha0.trans_le ht.1))
    (derivative_fifth_integrable ha0 hab)
    (fun t _ => div_nonpos_of_nonpos_of_nonneg (by norm_num) (by positivity))
  have hi := integral_density_div_pow_five_le ha hab
  have he' : weightedSum a b (fun t => 1 / t ^ 5) ≤
      (∫ t in a..b, density t / t ^ 5) +
      (positiveZeroCount b - G b) / b ^ 5 +
      (G a - positiveZeroCount a) / a ^ 5 := by
    convert he using 1 <;> simp only [density, G, mul_one_div] <;> ring
  linarith

/-- Uniform finite tail estimate retaining the exact lower count. -/
theorem fifth_sum_le_head {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 5) ≤
      J a + (G a - positiveZeroCount a) / a ^ 5 := by
  have he := fifth_sum_le_endpoints ha hab
  have hb0 : 0 < b := by linarith
  have hc := zero_count_bounds b (by linarith)
  change |positiveZeroCount b - rosserF b| < rosserR 1.588 b at hc
  have hn : positiveZeroCount b - G b ≤ 0 := by
    unfold G
    linarith [(abs_lt.mp hc).2]
  have hp := div_nonpos_of_nonpos_of_nonneg hn (pow_nonneg hb0.le 5)
  linarith

/-- The actual upper-envelope correction is nonnegative. -/
theorem head_correction_nonneg {a : ℝ} (ha : 2 ≤ a) :
    0 ≤ G a - positiveZeroCount a := by
  have hc := zero_count_bounds a ha
  change |positiveZeroCount a - rosserF a| < rosserR 1.588 a at hc
  unfold G
  linarith [(abs_lt.mp hc).2]

/-- The lower endpoint correction is at most twice Rosser's error allowance. -/
theorem head_correction_le {a : ℝ} (ha : 2 ≤ a) :
    G a - positiveZeroCount a ≤ 2 * rosserR 1.588 a := by
  have hc := zero_count_bounds a ha
  change |positiveZeroCount a - rosserF a| < rosserR 1.588 a at hc
  unfold G
  linarith [(abs_lt.mp hc).1]

/-- A completely explicit finite fifth-power tail bound. -/
theorem fifth_sum_le {a b : ℝ} (ha : 7 ≤ a) (hab : a ≤ b) :
    weightedSum a b (fun t => 1 / t ^ 5) ≤ J a + 2 * rosserR 1.588 a / a ^ 5 := by
  have ha0 : 0 ≤ a := by linarith
  have hc : (G a - positiveZeroCount a) / a ^ 5 ≤
      2 * rosserR 1.588 a / a ^ 5 :=
    div_le_div_of_nonneg_right (head_correction_le (by linarith : 2 ≤ a))
      (pow_nonneg ha0 5)
  have he := fifth_sum_le_head ha hab
  linarith

/-- Constant-weight sums recover the difference of the actual inclusive counts. -/
theorem weightedSum_const_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (c : ℝ) :
    weightedSum a b (fun _ => c) = (positiveZeroCount b - positiveZeroCount a) * c := by
  have he := weightedSum_eq ha hab (fun t _ => hasDerivAt_const t c)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume a b)
  simpa only [mul_zero, intervalIntegral.integral_zero, sub_zero, sub_mul] using he

/-- Pointwise comparison on the actual zero window, retaining analytic multiplicity. -/
theorem weightedSum_mono {a b : ℝ} (hb : 0 < b) {φ ψ : ℝ → ℝ}
    (h : ∀ t ∈ Ioc a b, φ t ≤ ψ t) : weightedSum a b φ ≤ weightedSum a b ψ := by
  classical
  unfold weightedSum
  apply Finset.sum_le_sum
  intro ρ hρ
  by_cases hρa : a < ρ.im
  · simp only [if_pos hρa]
    apply mul_le_mul_of_nonneg_left
    · exact h ρ.im ⟨hρa, ((mem_closedPositiveZeros_iff hb).mp hρ).2.2⟩
    · exact Nat.cast_nonneg _
  · simp only [if_neg hρa, le_refl]

/-- Each zero in a reciprocal band contributes at least the reciprocal upper height. -/
theorem reciprocal_sum_ge_count {l u : ℝ} (hl : 2 ≤ l) (hlu : l ≤ u) :
    (positiveZeroCount u - positiveZeroCount l) / u ≤
      weightedSum l u (fun t => 1 / t) := by
  have hl0 : 0 < l := by linarith
  have hu0 : 0 < u := hl0.trans_le hlu
  have hm := weightedSum_mono (a := l) hu0
    (φ := fun _ => 1 / u) (ψ := fun t => 1 / t)
    (fun t ht => one_div_le_one_div_of_le (hl0.trans ht.1) ht.2)
  rw [weightedSum_const_eq hl0 hlu] at hm
  simpa only [mul_one_div] using hm

/-- A reciprocal-band lower bound with no zero-count or RH assumption. -/
theorem reciprocal_sum_ge_rosser {l u : ℝ} (hl : 2 ≤ l) (hlu : l ≤ u) :
    (rosserF u - rosserR 1.588 u - rosserF l - rosserR 1.588 l) / u ≤
      weightedSum l u (fun t => 1 / t) := by
  have hu0 : 0 < u := by linarith
  have hcl := zero_count_bounds l hl
  have hcu := zero_count_bounds u (hl.trans hlu)
  change |positiveZeroCount l - rosserF l| < rosserR 1.588 l at hcl
  change |positiveZeroCount u - rosserF u| < rosserR 1.588 u at hcu
  have hcount : rosserF u - rosserR 1.588 u - rosserF l - rosserR 1.588 l ≤
      positiveZeroCount u - positiveZeroCount l := by
    linarith [(abs_lt.mp hcl).2, (abs_lt.mp hcu).1]
  exact (div_le_div_of_nonneg_right hcount hu0.le).trans (reciprocal_sum_ge_count hl hlu)

end TernaryGoldbach.RSBounds.RosserWeightedBounds
