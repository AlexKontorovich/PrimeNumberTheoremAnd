import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights

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

end

end Kadiri
