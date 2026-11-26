import RSBounds.WeightedZeroSums
import RSBounds.Rosser1941
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Partial summation for the actual zeta zeros

Analytic multiplicities are represented by a finite set of copies of each
actual zero, then the existing finite-ordinate partial-summation theorem is
applied. The copied counting function is proved equal to the public inclusive
zeta zero count. The decreasing-weight bound uses the proved Rosser theorem,
with no RH or zero-count-envelope premise.
-/

open Complex Set MeasureTheory
open scoped BigOperators Interval

namespace TernaryGoldbach.RSBounds.WeightedZetaZeros
open BacklundCountIdentity Rosser1941

/-- Each actual zero occurs as many times as its analytic multiplicity. -/
noncomputable def zeroCopies (B : ℝ) : Finset (Σ _ : ℂ, ℕ) := by
  classical
  exact (closedPositiveZeros B).sigma
    (fun ρ => Finset.range (analyticOrderAt riemannZeta ρ).toNat)

/-- The multiplicity-weighted sum over actual zeros with `a < Im rho <= b`.
The finite zero set supplies the inclusive upper endpoint. -/
noncomputable def weightedSum (a b : ℝ) (φ : ℝ → ℝ) : ℝ :=
  ∑ ρ ∈ closedPositiveZeros b,
    if a < ρ.im then ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * φ ρ.im else 0

/-- Expanding multiplicity into finite copies leaves every weighted sum unchanged. -/
theorem sum_zeroCopies (B : ℝ) (W : ℂ → ℝ) :
    (∑ z ∈ zeroCopies B, W z.1) =
      ∑ ρ ∈ closedPositiveZeros B, ((analyticOrderAt riemannZeta ρ).toNat : ℝ) * W ρ := by
  classical
  simp [zeroCopies, Finset.sum_sigma, nsmul_eq_mul]

/-- Restricting a taller actual-zero set gives the exact smaller zero set. -/
theorem filter_closedPositiveZeros {t B : ℝ} (ht : 0 < t) (htB : t ≤ B) :
    (closedPositiveZeros B).filter (fun ρ => ρ.im ≤ t) = closedPositiveZeros t := by
  classical
  ext ρ
  rw [Finset.mem_filter, mem_closedPositiveZeros_iff (ht.trans_le htB),
    mem_closedPositiveZeros_iff ht]
  constructor
  · rintro ⟨⟨hz, h0, _⟩, hle⟩
    exact ⟨hz, h0, hle⟩
  · rintro ⟨hz, h0, hle⟩
    exact ⟨⟨hz, h0, hle.trans htB⟩, hle⟩

/-- The finite copied count is the actual inclusive count, not an assumed envelope. -/
theorem ordinateCount_zeroCopies {t B : ℝ} (ht : 0 < t) (htB : t ≤ B) :
    ordinateCount (zeroCopies B) (fun z => z.1.im) t = positiveZeroCount t := by
  classical
  unfold ordinateCount
  dsimp only
  rw [sum_zeroCopies B (fun ρ => if ρ.im ≤ t then (1 : ℝ) else 0)]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, filter_closedPositiveZeros ht htB, positiveZeroCount_eq ht]
  simp [N_le]

/-- The copied window sum is the actual multiplicity-weighted zero sum. -/
theorem window_sum_zeroCopies {a b : ℝ} (hb : 0 < b) (φ : ℝ → ℝ) :
    (∑ z ∈ zeroCopies b, if a < z.1.im ∧ z.1.im ≤ b then φ z.1.im else 0) =
      weightedSum a b φ := by
  classical
  rw [sum_zeroCopies b (fun ρ => if a < ρ.im ∧ ρ.im ≤ b then φ ρ.im else 0)]
  unfold weightedSum
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hi := ((mem_closedPositiveZeros_iff hb).mp hρ).2.2
  simp only [hi, and_true, mul_ite, mul_zero]

/-- Exact finite partial summation for the actual zeta zeros, with multiplicity.
Both endpoint counts are inclusive, so the summation window is `(a,b]`. -/
theorem weightedSum_eq {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume a b) :
    weightedSum a b φ = positiveZeroCount b * φ b - positiveZeroCount a * φ a -
      ∫ t in a..b, positiveZeroCount t * φ' t := by
  have he := weighted_ordinate_sum_eq (zeroCopies b) (fun z => z.1.im) hab hφ hφ'
  rw [window_sum_zeroCopies (ha.trans_le hab),
    ordinateCount_zeroCopies (ha.trans_le hab) le_rfl,
    ordinateCount_zeroCopies ha hab] at he
  have hi : (∫ t in a..b, ordinateCount (zeroCopies b) (fun z => z.1.im) t * φ' t) =
      ∫ t in a..b, positiveZeroCount t * φ' t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hab] at ht
    dsimp only
    rw [ordinateCount_zeroCopies (ha.trans_le ht.1) ht.2]
  rwa [hi] at he

/-- The actual count times an integrable function is integrable on each
positive finite interval. -/
theorem intervalIntegrable_count_mul {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    {f : ℝ → ℝ} (hf : IntervalIntegrable f volume a b) :
    IntervalIntegrable (fun t => positiveZeroCount t * f t) volume a b := by
  have hi := intervalIntegrable_ordinateCount_mul (zeroCopies b) (fun z => z.1.im) hf
  apply hi.congr
  intro t ht
  rw [uIoc_of_le hab] at ht
  dsimp only
  rw [ordinateCount_zeroCopies (ha.trans ht.1) ht.2]

/-- Rosser's proved envelope gives a decreasing-weight bound for actual zeros.
The signed endpoint corrections are retained, allowing a certified finite head
to be used later. No zero-count or RH hypothesis is present. -/
theorem weightedSum_le_decreasing {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hdec : ∀ t ∈ Ioo a b, φ' t ≤ 0) :
    weightedSum a b φ ≤
      (∫ t in a..b, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) +
        (0.137 + 0.443 / Real.log t) / t) * φ t) +
      (positiveZeroCount b - rosserF b - rosserR 1.588 b) * φ b -
      (positiveZeroCount a - rosserF a - rosserR 1.588 a) * φ a := by
  have ha0 : 0 < a := by linarith
  have hF' : IntervalIntegrable
      (fun t => Real.log (t / (2 * Real.pi)) / (2 * Real.pi)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha0.trans_le ht.1
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have hR' : IntervalIntegrable
      (fun t => (0.137 + 0.443 / Real.log t) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht1 : 1 < t := by linarith [ht.1]
    have ht0 : 0 < t := by linarith
    have hl : 0 < Real.log t := Real.log_pos ht1
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := positivity))
  have he := weighted_ordinate_sum_le_decreasing (zeroCopies b) (fun z => z.1.im) hab hφ
    (fun t ht => hasDerivAt_rosserF (ha0.trans_le ht.1))
    (fun t ht => hasDerivAt_rosserR 1.588 (by linarith [ht.1]))
    hφ' hF' hR' hdec (fun t ht => by
      rw [ordinateCount_zeroCopies (ha0.trans_le ht.1) ht.2]
      have hc := zero_count_bounds t (ha.trans ht.1)
      change |positiveZeroCount t - rosserF t| < rosserR 1.588 t at hc
      linarith [(abs_lt.mp hc).2])
  rw [window_sum_zeroCopies (ha0.trans_le hab),
    ordinateCount_zeroCopies (ha0.trans_le hab) le_rfl,
    ordinateCount_zeroCopies ha0 hab] at he
  exact he

/-- For a nonnegative upper-endpoint weight, the negative upper-endpoint
correction can be discarded while retaining the exact lower zero count. -/
theorem weightedSum_le_decreasing_head {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b)
    {φ φ' : ℝ → ℝ}
    (hφ : ∀ t ∈ Icc a b, HasDerivAt φ (φ' t) t)
    (hφ' : IntervalIntegrable φ' volume a b)
    (hdec : ∀ t ∈ Ioo a b, φ' t ≤ 0) (hb : 0 ≤ φ b) :
    weightedSum a b φ ≤
      (∫ t in a..b, (Real.log (t / (2 * Real.pi)) / (2 * Real.pi) +
        (0.137 + 0.443 / Real.log t) / t) * φ t) +
      (rosserF a + rosserR 1.588 a - positiveZeroCount a) * φ a := by
  have he := weightedSum_le_decreasing ha hab hφ hφ' hdec
  have hc := zero_count_bounds b (ha.trans hab)
  change |positiveZeroCount b - rosserF b| < rosserR 1.588 b at hc
  have hn : positiveZeroCount b - rosserF b - rosserR 1.588 b ≤ 0 := by
    linarith [(abs_lt.mp hc).2]
  have hp := mul_nonpos_of_nonpos_of_nonneg hn hb
  nlinarith

end TernaryGoldbach.RSBounds.WeightedZetaZeros
