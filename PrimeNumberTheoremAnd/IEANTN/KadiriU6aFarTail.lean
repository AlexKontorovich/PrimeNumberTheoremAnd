import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights
import PrimeNumberTheoremAnd.IEANTN.KadiriContourShift
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard

/-!
# U6a far-tail lane: the zero-sum remainder from a single local-count atom

This file reorganizes the open partial-fraction estimate
`U6aZeroSumRemainderBoundHypothesis` around one named analytic atom, the
classical unit-window zero count `N(t+1) - N(t) = O(log t)`
(`U6aLocalZeroCountLogHypothesis`).  Every count-free piece is composed here:
the global xi Hadamard sum splits into the finite nearby fiber plus the far
remainder, the nearby residue is the already-proved convergence-factor bound,
and the triangle inequality assembles the target estimate from the far-tail
bound and the count atom.

The analytic discharge of the atom (and of the far tail, which follows from
the atom at shifted heights through the anchor-difference argument) requires
strip growth of `(s-1) * zeta s` left of `Re = 0`, which in turn rides
Stirling-grade decay of the complex Gamma function — the named upstream arc.
Until that lands, this file isolates exactly what remains.
-/

namespace Kadiri

open Complex MeasureTheory
open scoped Topology

noncomputable section

/-- The single remaining analytic atom of the U6a partial-fraction route: the
classical local zero count `N(t+1) - N(t) = O(log t)` over Kadiri's nearby
window, multiplicity-weighted.  Classically true (Backlund / Davenport
paragraph 15); its in-tree discharge is gated on strip growth of the completed
zeta function, hence on complex Stirling decay. -/
def U6aLocalZeroCountLogHypothesis (C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, Tₘᵢₙ ≤ |t| → 3 ≤ |t| →
    u6aNearbyZeroCount (-1) 2 t ≤ C * Real.log |t|

/-- The far part of the global xi Hadamard zero sum: everything outside the
finite nearby fiber. -/
noncomputable def u6aXiFarHadamardRemainder (t : ℝ) (s : ℂ) : ℂ :=
  u6aXiHadamardZeroSum s - u6aXiFiberNearbyHadamardSum t s

/-- The far-tail estimate, the second count-gated input: classically it
follows from the count atom at shifted heights through the anchor-difference
argument at `2 + i t`. -/
def U6aFarTailBoundHypothesis (C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc (-1 : ℝ) 2 → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖u6aXiFarHadamardRemainder s.im s‖ ≤ C * Real.log |s.im|

/-- Exact decomposition: the zero-sum remainder is the far tail plus the
nearby fiber residue. -/
theorem u6aXiHadamardZeroSum_sub_nearbyPrincipal_eq (t : ℝ) (s : ℂ) :
    u6aXiHadamardZeroSum s - u6aNearbyZeroPrincipalSum (-1) 2 t s =
      u6aXiFarHadamardRemainder t s +
        (u6aXiFiberNearbyHadamardSum t s - u6aNearbyZeroPrincipalSum (-1) 2 t s) := by
  unfold u6aXiFarHadamardRemainder
  ring

/-- The open `U6aZeroSumRemainderBoundHypothesis` composes from the far-tail
bound and the local-count atom: the count-free content of the partial-fraction
zero-sum estimate. -/
theorem U6aZeroSumRemainderBoundHypothesis_of_farTail_and_count
    {Cfar Ccnt Tₘᵢₙ : ℝ}
    (hfar : U6aFarTailBoundHypothesis Cfar Tₘᵢₙ)
    (hcnt : U6aLocalZeroCountLogHypothesis Ccnt Tₘᵢₙ) :
    U6aZeroSumRemainderBoundHypothesis (-1) 2 (Cfar + Ccnt) Tₘᵢₙ := by
  obtain ⟨hCfar, hfar⟩ := hfar
  obtain ⟨hCcnt, hcnt⟩ := hcnt
  refine ⟨by linarith, fun s hre hT h3 => ?_⟩
  rw [u6aXiHadamardZeroSum_sub_nearbyPrincipal_eq s.im s]
  have h1 := hfar s hre hT h3
  have h2 := norm_u6aXiFiberNearbyHadamardSum_sub_nearbyZeroPrincipalSum_le_nearbyZeroCount
    (t := s.im) s (by linarith)
  have h3' := hcnt s.im hT h3
  calc ‖u6aXiFarHadamardRemainder s.im s +
        (u6aXiFiberNearbyHadamardSum s.im s - u6aNearbyZeroPrincipalSum (-1) 2 s.im s)‖
      ≤ ‖u6aXiFarHadamardRemainder s.im s‖ +
        ‖u6aXiFiberNearbyHadamardSum s.im s - u6aNearbyZeroPrincipalSum (-1) 2 s.im s‖ :=
        norm_add_le _ _
    _ ≤ Cfar * Real.log |s.im| + Ccnt * Real.log |s.im| := by
        have := le_trans h2 h3'
        linarith
    _ = (Cfar + Ccnt) * Real.log |s.im| := by ring

/-! ## The finite/global bridge: splitting the Hadamard tsum at the window -/

/-- The nearby window of zeta zeros, as a set. -/
def u6aFTNearbyWindow (t : ℝ) : Set ℂ :=
  riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1))

theorem u6aFTNearbyWindow_finite (t : ℝ) : (u6aFTNearbyWindow t).Finite := by
  have h := zeroes_rect_uIcc_finite ((-1 : ℂ) + (t - 1) * I) ((2 : ℂ) + (t + 1) * I)
  have hre1 : ((-1 : ℂ) + (t - 1) * I).re = -1 := by simp
  have hre2 : ((2 : ℂ) + (t + 1) * I).re = 2 := by simp
  have him1 : ((-1 : ℂ) + (t - 1) * I).im = t - 1 := by simp
  have him2 : ((2 : ℂ) + (t + 1) * I).im = t + 1 := by simp
  rw [hre1, hre2, him1, him2, Set.uIcc_of_le (by linarith : t - 1 ≤ t + 1)] at h
  exact h

/-- The nearby window pulled back to the xi divisor index: the union of the
finite fibers over the windowed zeros. -/
noncomputable def u6aXiNearbyIndexFinset (t : ℝ) :
    Finset (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  (u6aFTNearbyWindow_finite t).toFinset.biUnion
    fun ρ => Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ

/-- Membership in the pulled-back window is membership of the value in the
window. -/
theorem mem_u6aXiNearbyIndexFinset_iff (t : ℝ)
    (p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :
    p ∈ u6aXiNearbyIndexFinset t ↔
      Complex.Hadamard.divisorZeroIndex₀_val p ∈ u6aFTNearbyWindow t := by
  unfold u6aXiNearbyIndexFinset
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨ρ, hρ, hp⟩
    rw [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp
    rw [hp]
    exact (Set.Finite.mem_toFinset _).mp hρ
  · intro hval
    exact ⟨Complex.Hadamard.divisorZeroIndex₀_val p, (Set.Finite.mem_toFinset _).mpr hval,
      (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset _ _ _).mpr rfl⟩

/-- The nearby fiber double sum is the single sum over the pulled-back window. -/
theorem u6aXiFiberNearbyHadamardSum_eq_indexFinset_sum (t : ℝ) (s : ℂ) :
    u6aXiFiberNearbyHadamardSum t s =
      ∑ p ∈ u6aXiNearbyIndexFinset t,
        ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p) := by
  letI : DecidableEq (Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ)) :=
    Classical.decEq _
  unfold u6aXiFiberNearbyHadamardSum u6aXiNearbyIndexFinset
  rw [Finset.sum_biUnion (by
    intro ρ₁ _ ρ₂ _ hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp1 hp2
    rw [Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset] at hp1 hp2
    exact hne (hp1 ▸ hp2))]
  refine Finset.sum_congr ?_ fun ρ _ => rfl
  ext ρ
  simp only [Set.Finite.mem_toFinset]
  rfl

/-- The finite/global bridge: at any point off the indexed zero set, the
global xi Hadamard sum splits into the nearby fiber sum plus the far-tail
tsum over the complement of the pulled-back window. -/
theorem u6aXiHadamardZeroSum_eq_nearby_add_farTail (t : ℝ) {s : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    u6aXiHadamardZeroSum s =
      u6aXiFiberNearbyHadamardSum t s +
        ∑' p : {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
            p ∉ u6aXiNearbyIndexFinset t},
          ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p.val) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p.val) := by
  have hsum := summable_riemannXi_logDerivTerms_divisorZeroIndex₀ (z := s) hz
  have hsplit := hsum.sum_add_tsum_subtype_compl (u6aXiNearbyIndexFinset t)
  unfold u6aXiHadamardZeroSum
  rw [← hsplit, u6aXiFiberNearbyHadamardSum_eq_indexFinset_sum]

/-- The far remainder is exactly the complement tsum: the analytic far-tail
estimate may now be attacked termwise. -/
theorem u6aXiFarHadamardRemainder_eq_tsum_compl (t : ℝ) {s : ℂ}
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    u6aXiFarHadamardRemainder t s =
      ∑' p : {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
          p ∉ u6aXiNearbyIndexFinset t},
        ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p.val) +
          1 / Complex.Hadamard.divisorZeroIndex₀_val p.val) := by
  unfold u6aXiFarHadamardRemainder
  linear_combination u6aXiHadamardZeroSum_eq_nearby_add_farTail t hz

end

end Kadiri
