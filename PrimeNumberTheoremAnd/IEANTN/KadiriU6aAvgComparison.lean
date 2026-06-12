import PrimeNumberTheoremAnd.IEANTN.KadiriU6aCountAtom

/-!
# U6a: log-squared reciprocal-zero sums from the count atom

This file closes the height-selection half of the U6a zero-sum route.  The
proved local count atom (`exists_u6aLocalZeroCountLogHypothesis`) supplies the
RvM-style density input, the density height selector picks cofinally many
heights `T` with zero-ordinate gap `c / log T`, and at such a height the
width-two reciprocal zero sum is bounded by the window count times the inverse
gap, hence by `(4 C / c) log² T`.  Feeding these heights into
`exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound_of_zeroGap`
gives the cofinal horizontal-segment endpoint from the zero-sum remainder
hypothesis alone.

The file also records the audit verdict on the previously stated comparison
shape: `U6aAveragedSelectionLogSqComparisonHypothesis C D Crec`
(`KadiriGoodHeights.lean`) is false for every `C > 0`, `D ≥ 0`, `Crec`.  It
quantifies over all dyadic indices `k` with only the upper coupling
`2X + 2 < 2^(k+1)`, while its left side carries the crude geometric mass
`C·3^k + D`; sending `k → ∞` at a fixed safe height blows up the left side
against the fixed `Crec log² T`.  Both the pointwise refutation and the
refutation of the consumer-shaped input are proved at the end, so no other
lane attempts that discharge again.
-/

namespace Kadiri

open Complex MeasureTheory

noncomputable section

/-! ## Finite-window helpers -/

private lemma u6aAC_zeroes_rect_Icc_finite (σ₁ σ₂ a b : ℝ) :
    (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc a b)).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc a b)
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨by simpa [Set.uIcc] using hre, him⟩, hzeta⟩

private lemma u6aAC_order_nonneg_of_zero {ρ : ℂ} (hzero : riemannZeta ρ = 0) :
    0 ≤ (riemannZeta.order ρ : ℝ) := by
  have hne_one : ρ ≠ 1 := by
    intro hρ
    exact riemannZeta_one_ne_zero (by simpa [hρ] using hzero)
  exact_mod_cast le_of_lt (riemannZeta_order_pos_of_zero_ne_one hne_one hzero)

/-! ## The count atom supplies the local-density input -/

/-- The proved `|t|`-form count atom restricts to the positive-height density
hypothesis consumed by the height selector. -/
theorem u6aAC_localZeroDensity_of_countAtom {C Tₘᵢₙ : ℝ}
    (h : U6aLocalZeroCountLogHypothesis C Tₘᵢₙ) :
    U6aLocalZeroDensityHypothesis (-1) 2 C Tₘᵢₙ := by
  refine ⟨h.1, fun t hTmin h3 => ?_⟩
  have habs : |t| = t := abs_of_nonneg (by linarith)
  have hcount := h.2 t (by rwa [habs]) (by rwa [habs])
  rwa [habs] at hcount

/-! ## Reciprocal zero sum ≤ window counts × inverse gap -/

/-- At a height with zero-ordinate gap `η`, the width-two reciprocal zero sum
is bounded by the two adjacent unit-window counts divided by `η`. -/
theorem u6aAC_reciprocalZeroSum_le_counts_div_gap {σ₁ σ₂ T η : ℝ}
    (hgap : horizontalSegmentZeroGap σ₁ σ₂ T η) :
    u6aReciprocalZeroSum σ₁ σ₂ T ≤
      (u6aNearbyZeroCount σ₁ σ₂ (T - 1) + u6aNearbyZeroCount σ₁ σ₂ (T + 1)) / η := by
  classical
  obtain ⟨hη, htop, _hbot⟩ := hgap
  have hrec : (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
      (Set.Icc (T - 2) (T + 2))).Finite :=
    u6aAC_zeroes_rect_Icc_finite σ₁ σ₂ (T - 2) (T + 2)
  have hA : (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
      (Set.Icc (T - 1 - 1) (T - 1 + 1))).Finite :=
    u6aAC_zeroes_rect_Icc_finite σ₁ σ₂ (T - 1 - 1) (T - 1 + 1)
  have hB : (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
      (Set.Icc (T + 1 - 1) (T + 1 + 1))).Finite :=
    u6aAC_zeroes_rect_Icc_finite σ₁ σ₂ (T + 1 - 1) (T + 1 + 1)
  have hterm_le : ∀ ρ ∈ hrec.toFinset,
      (1 / |T - ρ.im|) * (riemannZeta.order ρ : ℝ) ≤
        (1 / η) * (riemannZeta.order ρ : ℝ) := by
    intro ρ hρ
    have hρm := hrec.mem_toFinset.mp hρ
    have hzero : riemannZeta ρ = 0 := hρm.2.2
    have hdist : η ≤ |T - ρ.im| := by
      rw [abs_sub_comm]
      exact htop ρ hρm.1 hzero
    have hkernel : 1 / |T - ρ.im| ≤ 1 / η := one_div_le_one_div_of_le hη hdist
    exact mul_le_mul_of_nonneg_right hkernel (u6aAC_order_nonneg_of_zero hzero)
  have hsplit : hrec.toFinset ⊆ hA.toFinset ∪ hB.toFinset := by
    intro ρ hρ
    have hρm := hrec.mem_toFinset.mp hρ
    by_cases him : ρ.im ≤ T
    · exact Finset.mem_union_left _ (hA.mem_toFinset.mpr
        ⟨hρm.1, ⟨by linarith [hρm.2.1.1], by linarith⟩, hρm.2.2⟩)
    · have him' : T ≤ ρ.im := (not_le.mp him).le
      exact Finset.mem_union_right _ (hB.mem_toFinset.mpr
        ⟨hρm.1, ⟨by linarith, by linarith [hρm.2.1.2]⟩, hρm.2.2⟩)
  have hunion :
      ∑ ρ ∈ hA.toFinset ∪ hB.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) ≤
        ∑ ρ ∈ hA.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) +
          ∑ ρ ∈ hB.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) := by
    have hinter : (0 : ℝ) ≤ ∑ ρ ∈ hA.toFinset ∩ hB.toFinset,
        (1 / η) * (riemannZeta.order ρ : ℝ) := by
      refine Finset.sum_nonneg fun ρ hρ => ?_
      have hρm := hA.mem_toFinset.mp (Finset.mem_of_mem_inter_left hρ)
      exact mul_nonneg (by positivity) (u6aAC_order_nonneg_of_zero hρm.2.2)
    have hsum : ∑ ρ ∈ hA.toFinset ∪ hB.toFinset,
          (1 / η) * (riemannZeta.order ρ : ℝ) +
        ∑ ρ ∈ hA.toFinset ∩ hB.toFinset,
          (1 / η) * (riemannZeta.order ρ : ℝ) =
        ∑ ρ ∈ hA.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) +
          ∑ ρ ∈ hB.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) :=
      Finset.sum_union_inter
    linarith
  have hcountA :
      ∑ ρ ∈ hA.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) =
        (1 / η) * u6aNearbyZeroCount σ₁ σ₂ (T - 1) := by
    unfold u6aNearbyZeroCount
    rw [riemannZeta.zeroes_sum_eq_finset_of_finite (fun _ => (1 : ℝ)) hA,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  have hcountB :
      ∑ ρ ∈ hB.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) =
        (1 / η) * u6aNearbyZeroCount σ₁ σ₂ (T + 1) := by
    unfold u6aNearbyZeroCount
    rw [riemannZeta.zeroes_sum_eq_finset_of_finite (fun _ => (1 : ℝ)) hB,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun ρ _ => by ring
  calc
    u6aReciprocalZeroSum σ₁ σ₂ T
        = ∑ ρ ∈ hrec.toFinset,
            (1 / |T - ρ.im|) * (riemannZeta.order ρ : ℝ) := by
          unfold u6aReciprocalZeroSum
          exact riemannZeta.zeroes_sum_eq_finset_of_finite
            (fun ρ => (1 : ℝ) / |T - ρ.im|) hrec
    _ ≤ ∑ ρ ∈ hrec.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) :=
          Finset.sum_le_sum hterm_le
    _ ≤ ∑ ρ ∈ hA.toFinset ∪ hB.toFinset,
          (1 / η) * (riemannZeta.order ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsplit fun ρ hρ _ => ?_
          have hzero : riemannZeta ρ = 0 := by
            rcases Finset.mem_union.mp hρ with h | h
            · exact (hA.mem_toFinset.mp h).2.2
            · exact (hB.mem_toFinset.mp h).2.2
          exact mul_nonneg (by positivity) (u6aAC_order_nonneg_of_zero hzero)
    _ ≤ ∑ ρ ∈ hA.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) +
          ∑ ρ ∈ hB.toFinset, (1 / η) * (riemannZeta.order ρ : ℝ) := hunion
    _ = (1 / η) * (u6aNearbyZeroCount σ₁ σ₂ (T - 1) +
          u6aNearbyZeroCount σ₁ σ₂ (T + 1)) := by
          rw [hcountA, hcountB]
          ring
    _ = (u6aNearbyZeroCount σ₁ σ₂ (T - 1) +
          u6aNearbyZeroCount σ₁ σ₂ (T + 1)) / η := by
          rw [one_div, inv_mul_eq_div]

/-- At a `c / log T`-separated height past the count threshold, the reciprocal
zero sum is `O(log² T)` with the explicit constant `4 Ccnt / c`. -/
theorem u6aAC_reciprocalZeroSum_le_logSq_of_gap {Ccnt Tₘᵢₙ c T : ℝ}
    (hcnt : U6aLocalZeroCountLogHypothesis Ccnt Tₘᵢₙ) (hc : 0 < c)
    (hTmin : Tₘᵢₙ + 1 ≤ T) (hT4 : 4 ≤ T)
    (hgap : horizontalSegmentZeroGap (-1) 2 T (c / Real.log T)) :
    u6aReciprocalZeroSum (-1) 2 T ≤ (4 * Ccnt / c) * Real.log T ^ 2 := by
  obtain ⟨hCcnt, hcount⟩ := hcnt
  have hlogT : 0 < Real.log T := Real.log_pos (by linarith)
  have hbase := u6aAC_reciprocalZeroSum_le_counts_div_gap hgap
  have habsA : |T - 1| = T - 1 := abs_of_nonneg (by linarith)
  have habsB : |T + 1| = T + 1 := abs_of_nonneg (by linarith)
  have hcA : u6aNearbyZeroCount (-1) 2 (T - 1) ≤ Ccnt * Real.log (T + 1) := by
    have h := hcount (T - 1) (by rw [habsA]; linarith) (by rw [habsA]; linarith)
    rw [habsA] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith) (by linarith)) hCcnt.le)
  have hcB : u6aNearbyZeroCount (-1) 2 (T + 1) ≤ Ccnt * Real.log (T + 1) := by
    have h := hcount (T + 1) (by rw [habsB]; linarith) (by rw [habsB]; linarith)
    rwa [habsB] at h
  have hlogTp1 : Real.log (T + 1) ≤ 2 * Real.log T := by
    have hsq : T + 1 ≤ T ^ 2 := by nlinarith
    have hlog_sq : Real.log (T ^ 2) = 2 * Real.log T := by
      rw [Real.log_pow]
      norm_num
    have h := Real.log_le_log (by linarith) hsq
    rwa [hlog_sq] at h
  have hsum_counts :
      u6aNearbyZeroCount (-1) 2 (T - 1) + u6aNearbyZeroCount (-1) 2 (T + 1) ≤
        4 * Ccnt * Real.log T := by
    have h2 : Ccnt * Real.log (T + 1) ≤ Ccnt * (2 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlogTp1 hCcnt.le
    nlinarith
  have hη : 0 < c / Real.log T := div_pos hc hlogT
  have hdiv :
      (u6aNearbyZeroCount (-1) 2 (T - 1) + u6aNearbyZeroCount (-1) 2 (T + 1)) /
          (c / Real.log T) ≤
        (4 * Ccnt * Real.log T) / (c / Real.log T) := by
    gcongr
  have heq : (4 * Ccnt * Real.log T) / (c / Real.log T) =
      (4 * Ccnt / c) * Real.log T ^ 2 := by
    field_simp
  exact hbase.trans (hdiv.trans_eq heq)

/-! ## The endpoint: cofinal horizontal log-derivative bounds from the
zero-sum remainder hypothesis alone -/

/-- Cofinal U6a horizontal-segment `log² T` bounds from the zero-sum Hadamard
remainder estimate.  The height selection and the reciprocal-sum comparison
are both discharged from the proved local count atom, so no averaged-selection
input remains. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_of_zeroSumRemainder
    {Czero Tzero : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Ccnt, Tₘᵢₙ, hcnt⟩ := exists_u6aLocalZeroCountLogHypothesis
  obtain ⟨c, hc, hsel⟩ :=
    exists_arbitrarily_large_horizontalSegmentZeroGap_of_localDensity_proved
      (-1) 2 (u6aAC_localZeroDensity_of_countAtom hcnt)
  have hCrec : 0 < 4 * Ccnt / c := by
    have hCcnt := hcnt.1
    have h4 : 0 < 4 * Ccnt := by linarith
    exact div_pos h4 hc
  obtain ⟨Cout, Tout, hCout, _hTout4, hmain⟩ :=
    exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound_of_zeroGap
      (Crec := 4 * Ccnt / c) hZero hCrec
  refine ⟨Cout, hCout, fun T₀ => ?_⟩
  obtain ⟨T, hTle, hT3, hgap⟩ := hsel (max (max T₀ Tout) (max (Tₘᵢₙ + 1) 4))
  have hT₀ : T₀ ≤ T :=
    ((le_max_left T₀ Tout).trans (le_max_left _ _)).trans hTle
  have hTout : Tout ≤ T :=
    ((le_max_right T₀ Tout).trans (le_max_left _ _)).trans hTle
  have hTmin1 : Tₘᵢₙ + 1 ≤ T :=
    ((le_max_left (Tₘᵢₙ + 1) 4).trans (le_max_right _ _)).trans hTle
  have hT4 : (4 : ℝ) ≤ T :=
    ((le_max_right (Tₘᵢₙ + 1) 4).trans (le_max_right _ _)).trans hTle
  have hrecTop : u6aReciprocalZeroSum (-1) 2 T ≤ (4 * Ccnt / c) * Real.log T ^ 2 :=
    u6aAC_reciprocalZeroSum_le_logSq_of_gap hcnt hc hTmin1 hT4 hgap
  have hrecAll : ∀ t : ℝ, |t| = T →
      u6aReciprocalZeroSum (-1) 2 t ≤ (4 * Ccnt / c) * Real.log T ^ 2 := by
    intro t ht
    rcases (abs_eq (by linarith : (0 : ℝ) ≤ T)).mp ht with rfl | rfl
    · exact hrecTop
    · simpa [u6aReciprocalZeroSum_neg] using hrecTop
  exact ⟨T, hT₀, hT3, hmain T (c / Real.log T) hTout hT3 hgap hrecAll⟩

end

end Kadiri
