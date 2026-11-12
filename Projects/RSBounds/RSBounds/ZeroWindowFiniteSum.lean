import RSBounds.WeightedZetaZeros

/-! Finite-window assembly of low, tail and cancellation-band majorants.
All sums run over actual zeros and retain analytic multiplicities. -/

open Complex
open scoped BigOperators
namespace TernaryGoldbach.RSBounds.ZeroWindowFiniteSum
open BacklundCountIdentity WeightedZetaZeros

noncomputable def multiplicity (ρ : ℂ) : ℝ :=
  (analyticOrderAt riemannZeta ρ).toNat

theorem weightedSum_lift {a b B : ℝ} (hb : 0 < b) (hbB : b ≤ B)
    (φ : ℝ → ℝ) :
    weightedSum a b φ = ∑ ρ ∈ closedPositiveZeros B,
      if a < ρ.im ∧ ρ.im ≤ b then multiplicity ρ * φ ρ.im else 0 := by
  classical
  unfold weightedSum
  rw [← filter_closedPositiveZeros hb hbB, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ρ hρ
  by_cases h : ρ.im ≤ b <;> simp [h, multiplicity]

/-- Simultaneously retain the short head, the reciprocal tail, the fifth-power
 tail, and the improvement on a middle cancellation band. -/
theorem sum_le_windows {D L U Y A s k C r : ℝ}
    (hD : 0 < D) (hDL : D ≤ L) (hLU : L ≤ U)
    (hUY : U ≤ Y) (hYA : Y ≤ A) (hs : 0 ≤ s) (hk : 0 ≤ k)
    (w : ℂ → ℝ)
    (hlo : ∀ ρ ∈ closedPositiveZeros A, w ρ ≤ s * k / ‖ρ‖)
    (hhi : ∀ ρ ∈ closedPositiveZeros A, Y < ρ.im → w ρ ≤ s * C / ρ.im ^ 5)
    (hband : ∀ ρ ∈ closedPositiveZeros A, L < ρ.im → ρ.im ≤ U →
      w ρ ≤ s * r / ρ.im) :
    (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * w ρ) ≤
      s * (k * (∑ ρ ∈ closedPositiveZeros D, multiplicity ρ / ‖ρ‖) +
        k * weightedSum D Y (fun t => 1 / t) +
        C * weightedSum Y A (fun t => 1 / t ^ 5) -
        (k - r) * weightedSum L U (fun t => 1 / t)) := by
  classical
  have hDY := hDL.trans (hLU.trans hUY)
  have hDA := hDY.trans hYA
  have hU := hD.trans_le (hDL.trans hLU)
  have hY := hD.trans_le hDY
  have hA := hD.trans_le hDA
  let H (ρ : ℂ) : ℝ := if ρ.im ≤ D then 1 / ‖ρ‖ else 0
  let M (ρ : ℂ) : ℝ := if D < ρ.im ∧ ρ.im ≤ Y then 1 / ρ.im else 0
  let Q (ρ : ℂ) : ℝ := if Y < ρ.im then 1 / ρ.im ^ 5 else 0
  let B (ρ : ℂ) : ℝ := if L < ρ.im ∧ ρ.im ≤ U then 1 / ρ.im else 0
  have hp : ∀ ρ ∈ closedPositiveZeros A,
      w ρ ≤ s * (k * H ρ + k * M ρ + C * Q ρ - (k - r) * B ρ) := by
    intro ρ hρ
    have him := ((mem_closedPositiveZeros_iff hA).mp hρ).2.1
    by_cases hd : ρ.im ≤ D
    · have hm : ¬ D < ρ.im := not_lt.mpr hd
      have hy : ¬ Y < ρ.im := not_lt.mpr (hd.trans hDY)
      have hb : ¬ L < ρ.im := not_lt.mpr (hd.trans hDL)
      simpa [H, M, Q, B, hd, hm, hy, hb, div_eq_mul_inv, mul_assoc] using hlo ρ hρ
    · have hd' : D < ρ.im := lt_of_not_ge hd
      by_cases hy : ρ.im ≤ Y
      · have hq : ¬ Y < ρ.im := not_lt.mpr hy
        by_cases hb : L < ρ.im ∧ ρ.im ≤ U
        · have h := hband ρ hρ hb.1 hb.2
          simp only [H, M, Q, B, hd, hd', hy, hb, hq, ite_true, ite_false,
            and_self, mul_zero, zero_add, add_zero]
          convert h using 1; ring
        · have hn : ρ.im ≤ ‖ρ‖ := (le_abs_self ρ.im).trans (Complex.abs_im_le_norm ρ)
          have h := (hlo ρ hρ).trans (div_le_div_of_nonneg_left (mul_nonneg hs hk) him hn)
          simpa [H, M, Q, B, hd, hd', hy, hb, hq, div_eq_mul_inv, mul_assoc] using h
      · have hy' : Y < ρ.im := lt_of_not_ge hy
        have hb : ¬ (L < ρ.im ∧ ρ.im ≤ U) := by
          intro hb; exact hy (hb.2.trans hUY)
        simpa [H, M, Q, B, hd, hy, hy', hb, div_eq_mul_inv, mul_assoc] using hhi ρ hρ hy'
  have hh : (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * H ρ) =
      ∑ ρ ∈ closedPositiveZeros D, multiplicity ρ / ‖ρ‖ := by
    rw [← filter_closedPositiveZeros hD hDA, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ρ _
    simp [H, mul_ite, div_eq_mul_inv]
  have hm : (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * M ρ) =
      weightedSum D Y (fun t => 1 / t) := by
    rw [weightedSum_lift hY hYA]
    apply Finset.sum_congr rfl
    intro ρ _
    simp [M, mul_ite]
  have hq : (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * Q ρ) =
      weightedSum Y A (fun t => 1 / t ^ 5) := by
    unfold weightedSum
    apply Finset.sum_congr rfl
    intro ρ _
    simp [Q, multiplicity, mul_ite]
  have hb : (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * B ρ) =
      weightedSum L U (fun t => 1 / t) := by
    rw [weightedSum_lift hU (hUY.trans hYA)]
    apply Finset.sum_congr rfl
    intro ρ _
    simp [B, mul_ite]
  calc
    _ ≤ ∑ ρ ∈ closedPositiveZeros A,
        multiplicity ρ * (s * (k * H ρ + k * M ρ + C * Q ρ - (k-r) * B ρ)) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact mul_le_mul_of_nonneg_left (hp ρ hρ) (Nat.cast_nonneg _)
    _ = s * (k * (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * H ρ) +
        k * (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * M ρ) +
        C * (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * Q ρ) -
        (k-r) * (∑ ρ ∈ closedPositiveZeros A, multiplicity ρ * B ρ)) := by
      calc
        _ = ∑ ρ ∈ closedPositiveZeros A,
            (s * k * (multiplicity ρ * H ρ) + s * k * (multiplicity ρ * M ρ) +
            s * C * (multiplicity ρ * Q ρ) - s * (k-r) * (multiplicity ρ * B ρ)) := by
          apply Finset.sum_congr rfl
          intro ρ _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          ring
    _ = _ := by rw [hh, hm, hq, hb]
end TernaryGoldbach.RSBounds.ZeroWindowFiniteSum
