import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Zero-free horizontal heights for Kadiri contour shifts

This file packages the finite-avoidance selector used to choose horizontal
contour heights away from zeta zeros.
-/

namespace Kadiri

open Complex
open MeasureTheory

noncomputable section

/-- Both horizontal sides of the rectangle strip between `σ₁` and `σ₂` avoid
zeta zeros, and the pole point `1`. -/
def horizontalSegmentZeroFree (σ₁ σ₂ T : ℝ) : Prop :=
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → z.im = T →
    riemannZeta z ≠ 0 ∧ z ≠ 1) ∧
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → z.im = -T →
    riemannZeta z ≠ 0 ∧ z ≠ 1)

/-- The lane U6a horizontal-segment bound: both horizontal sides avoid zeros
and the pole, and `ζ'/ζ` is `O(log² T)` along the strip.  This matches
`56e3a7d:KadiriContourPull.lean:313-317`. -/
def horizontalSegmentLogDerivBound (σ₁ σ₂ T C : ℝ) : Prop :=
  horizontalSegmentZeroFree σ₁ σ₂ T ∧
  ∀ x ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
    ‖deriv riemannZeta ((x : ℂ) + t * I) / riemannZeta ((x : ℂ) + t * I)‖
      ≤ C * Real.log T ^ 2

/-- A quantitative zero-ordinate gap for both horizontal sides. -/
def horizontalSegmentZeroGap (σ₁ σ₂ T η : ℝ) : Prop :=
  0 < η ∧
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → riemannZeta z = 0 →
    η ≤ |z.im - T|) ∧
  (∀ z : ℂ, z.re ∈ Set.uIcc σ₁ σ₂ → riemannZeta z = 0 →
    η ≤ |z.im + T|)

/-- A positive zero-ordinate gap implies the zero-free horizontal condition. -/
theorem horizontalSegmentZeroFree_of_zeroGap {σ₁ σ₂ T η : ℝ}
    (hT : 0 < T) (hgap : horizontalSegmentZeroGap σ₁ σ₂ T η) :
    horizontalSegmentZeroFree σ₁ σ₂ T := by
  rcases hgap with ⟨hη, htop, hbot⟩
  constructor
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hdist := htop z hzre hzeta
      rw [hzim] at hdist
      norm_num at hdist
      linarith
    · intro hz1
      rw [hz1] at hzim
      norm_num at hzim
      linarith
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hdist := hbot z hzre hzeta
      rw [hzim] at hdist
      norm_num at hdist
      linarith
    · intro hz1
      rw [hz1] at hzim
      norm_num at hzim
      linarith

/-- The order-weighted nearby-zero principal part in the partial-fraction
formula, summing zeros with `|Im ρ - t| ≤ 1`. -/
noncomputable def u6aNearbyZeroPrincipalSum (σ₁ σ₂ t : ℝ) (s : ℂ) : ℂ :=
  riemannZeta.zeroes_sum (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
    fun ρ => (1 : ℂ) / (s - ρ)

/-- The order-weighted local zero count in a unit-height box. -/
noncomputable def u6aNearbyZeroCount (σ₁ σ₂ t : ℝ) : ℝ :=
  riemannZeta.zeroes_sum (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
    fun _ => (1 : ℝ)

/-- The panel-revised U6a reciprocal zero sum
`S₂(t) = Σ_{|γ - t| ≤ 2} 1 / |t - γ|`, multiplicity-weighted through
`zeroes_sum`. -/
noncomputable def u6aReciprocalZeroSum (σ₁ σ₂ t : ℝ) : ℝ :=
  riemannZeta.zeroes_sum (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))
    fun ρ => 1 / |t - ρ.im|

/-- Safe heights in the dyadic interval `[X, 2X]`, with both horizontal sides
at least `δ` away from zero ordinates. -/
def u6aSafeHeightSet (σ₁ σ₂ X δ : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc X (2 * X) ∧ horizontalSegmentZeroGap σ₁ σ₂ t δ}

/-- The explicit panel bound selected from the averaged reciprocal-zero sum. -/
noncomputable def u6aAveragedSelectionBound (X δ M : ℝ) : ℝ :=
  4 * M * Real.log (2 / δ) / X

/-- Named local-density hypothesis for the conditional U6a route.  This is the
RvM-style input `N(t+1)-N(t) ≤ C log t` used by the sprint panel. -/
def U6aLocalZeroDensityHypothesis (σ₁ σ₂ C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, Tₘᵢₙ ≤ t → 3 ≤ t →
    u6aNearbyZeroCount σ₁ σ₂ t ≤ C * Real.log t

/-- Named partial-fraction approximation hypothesis.  The Hadamard input is
`logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` in
`RiemannZetaHadamard.lean:244`, with the zeta bridge in
`HadamardLogDerivative.lean`. -/
def U6aPartialFractionApproximationHypothesis (σ₁ σ₂ C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc σ₁ σ₂ → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖deriv riemannZeta s / riemannZeta s -
        u6aNearbyZeroPrincipalSum σ₁ σ₂ s.im s‖ ≤ C * Real.log |s.im|

/-- Named height-selection output from the local-density pigeonhole argument:
cofinally many heights stay at least `c / log T` away from zero ordinates. -/
def U6aHeightSelectionHypothesis (σ₁ σ₂ Cdens Tdens c : ℝ) : Prop :=
  U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens →
    0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T)

/-- Named consequence of the partial-fraction formula plus local density and
the `c/log T` zero gap: a uniform `log² T` bound on the horizontal segment. -/
def U6aPartialFractionLogSqBoundHypothesis
    (σ₁ σ₂ Cpf Tpf Cdens Tdens c : ℝ) : Prop :=
  U6aPartialFractionApproximationHypothesis σ₁ σ₂ Cpf Tpf →
    U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens →
      ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
        horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T) →
          ∀ x ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
            ‖deriv riemannZeta ((x : ℂ) + t * I) /
                riemannZeta ((x : ℂ) + t * I)‖ ≤ C * Real.log T ^ 2

/-- Consume the named local-density height selector and expose its cofinal
`c/log T` zero-gap conclusion. -/
theorem exists_arbitrarily_large_horizontalSegmentZeroGap_of_localDensity
    (σ₁ σ₂ : ℝ) {Cdens Tdens c : ℝ}
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens)
    (hHeight : U6aHeightSelectionHypothesis σ₁ σ₂ Cdens Tdens c) :
    0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T) :=
  hHeight hDensity

/-- Consume the named partial-fraction and local-density inputs and expose the
uniform `log² T` horizontal estimate at separated heights. -/
theorem exists_logSq_horizontal_bound_of_partialFraction
    (σ₁ σ₂ : ℝ) {Cdens Tdens c Cpf Tpf : ℝ}
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens)
    (hPartialFraction : U6aPartialFractionApproximationHypothesis σ₁ σ₂ Cpf Tpf)
    (hLogSq : U6aPartialFractionLogSqBoundHypothesis σ₁ σ₂ Cpf Tpf Cdens Tdens c) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T) →
        ∀ x ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
          ‖deriv riemannZeta ((x : ℂ) + t * I) /
              riemannZeta ((x : ℂ) + t * I)‖ ≤ C * Real.log T ^ 2 :=
  hLogSq hPartialFraction hDensity

/-- Compose a quantitative zero gap with the partial-fraction `log²` bound to
obtain the lane's horizontal-segment bound predicate. -/
theorem horizontalSegmentLogDerivBound_of_zeroGap_and_partialFraction
    {σ₁ σ₂ T c C : ℝ}
    (hT : 3 ≤ T)
    (hgap : horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T))
    (hbound : ∀ x ∈ Set.uIcc σ₁ σ₂, ∀ t : ℝ, |t| = T →
      ‖deriv riemannZeta ((x : ℂ) + t * I) /
          riemannZeta ((x : ℂ) + t * I)‖ ≤ C * Real.log T ^ 2) :
    horizontalSegmentLogDerivBound σ₁ σ₂ T C := by
  have hTpos : 0 < T := by linarith
  exact ⟨horizontalSegmentZeroFree_of_zeroGap hTpos hgap, hbound⟩

/-- Conditional U6a endpoint matching the conclusion of
`56e3a7d:KadiriContourPull.lean:329-331`, with the local-density,
height-selection, and partial-fraction layers carried as named hypotheses. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_conditional
    (σ₁ σ₂ : ℝ) {Cdens Tdens c Cpf Tpf : ℝ}
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens)
    (hHeight : U6aHeightSelectionHypothesis σ₁ σ₂ Cdens Tdens c)
    (hPartialFraction : U6aPartialFractionApproximationHypothesis σ₁ σ₂ Cpf Tpf)
    (hLogSq : U6aPartialFractionLogSqBoundHypothesis σ₁ σ₂ Cpf Tpf Cdens Tdens c) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound σ₁ σ₂ T C := by
  rcases hHeight hDensity with ⟨hc, hselect⟩
  rcases hLogSq hPartialFraction hDensity with ⟨C, hCpos, hC⟩
  refine ⟨C, hCpos, ?_⟩
  intro T₀
  obtain ⟨T, hT₀, hT3, hgap⟩ := hselect T₀
  exact ⟨T, hT₀, hT3,
    horizontalSegmentLogDerivBound_of_zeroGap_and_partialFraction hT3 hgap
      (hC T hT3 hgap)⟩

/-- Mean-value extraction for the panel-revised averaged selector.  Once the
safe-set integral of `S₂` is below the safe-set integral of the boxed constant,
some safe height realizes the pointwise bound. -/
theorem exists_height_with_small_reciprocalZeroSum_of_indicator_average
    {σ₁ σ₂ X δ M : ℝ}
    (hX : 0 < X)
    (hEpos :
      (volume.restrict (Set.Ioc X (2 * X)))
        (u6aSafeHeightSet σ₁ σ₂ X δ) ≠ 0)
    (hSInt : IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (u6aReciprocalZeroSum σ₁ σ₂)) volume X (2 * X))
    (hBInt : IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        fun _ : ℝ => u6aAveragedSelectionBound X δ M) volume X (2 * X))
    (hAvg :
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
            (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
        ∫ t in X..(2 * X),
          (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
            (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume) :
    ∃ T : ℝ, T ∈ u6aSafeHeightSet σ₁ σ₂ X δ ∧
      u6aReciprocalZeroSum σ₁ σ₂ T ≤ u6aAveragedSelectionBound X δ M := by
  by_contra hnone
  push Not at hnone
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let B : ℝ := u6aAveragedSelectionBound X δ M
  let f : ℝ → ℝ := E.indicator fun _ : ℝ => B
  let g : ℝ → ℝ := E.indicator (u6aReciprocalZeroSum σ₁ σ₂)
  have hle : f ≤ᶠ[ae (volume.restrict (Set.Ioc X (2 * X)))] g := by
    filter_upwards with t
    by_cases ht : t ∈ E
    · have hlt : B < u6aReciprocalZeroSum σ₁ σ₂ t := hnone t ht
      simp [f, g, E, B, ht, le_of_lt hlt]
    · simp [f, g, ht]
  have hlt_set : (volume.restrict (Set.Ioc X (2 * X))) {t | f t < g t} ≠ 0 := by
    have hsub : E ⊆ {t | f t < g t} := by
      intro t ht
      have hlt : B < u6aReciprocalZeroSum σ₁ σ₂ t := hnone t ht
      simp [f, g, ht, hlt]
    have hle_measure :
        (volume.restrict (Set.Ioc X (2 * X))) E ≤
          (volume.restrict (Set.Ioc X (2 * X))) {t | f t < g t} :=
      measure_mono hsub
    intro hzero
    have hEzero : (volume.restrict (Set.Ioc X (2 * X))) E = 0 :=
      le_antisymm (hle_measure.trans (le_of_eq hzero)) (by positivity)
    exact hEpos (by simpa [E] using hEzero)
  have hlt_int :
      (∫ t in X..(2 * X), f t ∂volume) <
        ∫ t in X..(2 * X), g t ∂volume := by
    have hXX : X ≤ 2 * X := by nlinarith [hX]
    exact intervalIntegral.integral_lt_integral_of_ae_le_of_measure_setOf_lt_ne_zero
      (μ := volume) (a := X) (b := 2 * X) hXX
      (by simpa [f, E, B] using hBInt)
      (by simpa [g, E] using hSInt)
      hle hlt_set
  exact not_lt_of_ge (by simpa [f, g, E, B] using hAvg)
    (by simpa [f, g, E, B] using hlt_int)

private lemma mem_Icc_min_max_of_mem_uIcc {σ₁ σ₂ x : ℝ}
    (hx : x ∈ Set.uIcc σ₁ σ₂) :
    x ∈ Set.Icc (min σ₁ σ₂) (max σ₁ σ₂) := by
  simpa [Set.uIcc] using hx

private lemma horizontal_height_selector_core (σ₁ σ₂ T₀ : ℝ) :
    ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧ horizontalSegmentZeroFree σ₁ σ₂ T := by
  classical
  let B : ℝ := max T₀ 0
  let R : ℝ := B + 1
  let rect : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc (-R) R)
  have hrect_compact : IsCompact rect := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  have hzeros_fin : (rect ∩ riemannZeta.zeroes : Set ℂ).Finite :=
    riemannZeta.zeroes_on_Compact_finite' hrect_compact
  let badHeights : Set ℝ := (fun z : ℂ => |z.im|) '' (rect ∩ riemannZeta.zeroes) ∪ {0}
  have hbad_fin : badHeights.Finite :=
    (hzeros_fin.image fun z : ℂ => |z.im|).union (Set.finite_singleton 0)
  have hBR : B < R := by
    dsimp [R]
    linarith
  obtain ⟨T, hT_interval, hT_not_bad⟩ :=
    (Set.Ioo_infinite hBR).exists_notMem_finite hbad_fin
  have hT_ge_T₀ : T₀ ≤ T := by
    exact (le_max_left T₀ 0).trans hT_interval.1.le
  have hT_pos : 0 < T := by
    exact lt_of_le_of_lt (le_max_right T₀ 0) hT_interval.1
  have hR_pos : 0 < R := by
    linarith [le_max_right T₀ 0]
  refine ⟨T, hT_ge_T₀, hT_pos, ?_⟩
  constructor
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hz_rect : z ∈ rect := by
        refine ⟨mem_Icc_min_max_of_mem_uIcc hzre, ?_⟩
        change z.im ∈ Set.Icc (-R) R
        rw [Set.mem_Icc, hzim]
        constructor
        · linarith
        · exact hT_interval.2.le
      have hz_zero : z ∈ riemannZeta.zeroes := by
        simpa [riemannZeta.zeroes] using hzeta
      have hT_bad : T ∈ badHeights := by
        left
        refine ⟨z, ⟨hz_rect, hz_zero⟩, ?_⟩
        change |z.im| = T
        rw [hzim, abs_of_pos hT_pos]
      exact hT_not_bad hT_bad
    · intro hz_one
      have hT_zero : T = 0 := by
        rw [hz_one] at hzim
        simpa using hzim.symm
      exact hT_pos.ne' hT_zero
  · intro z hzre hzim
    constructor
    · intro hzeta
      have hz_rect : z ∈ rect := by
        refine ⟨mem_Icc_min_max_of_mem_uIcc hzre, ?_⟩
        change z.im ∈ Set.Icc (-R) R
        rw [Set.mem_Icc, hzim]
        constructor
        · linarith [hT_interval.2]
        · linarith
      have hz_zero : z ∈ riemannZeta.zeroes := by
        simpa [riemannZeta.zeroes] using hzeta
      have hT_bad : T ∈ badHeights := by
        left
        refine ⟨z, ⟨hz_rect, hz_zero⟩, ?_⟩
        change |z.im| = T
        rw [hzim, abs_neg, abs_of_pos hT_pos]
      exact hT_not_bad hT_bad
    · intro hz_one
      rw [hz_one] at hzim
      simp at hzim
      linarith

/-- Cofinal zero-free horizontal heights for the two sides of a Kadiri
rectangle.  This is the selector shape used before pulling contours at a
sequence of large heights. -/
theorem exists_arbitrarily_large_horizontalSegmentZeroFree (σ₁ σ₂ : ℝ) :
    ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 0 < T ∧ horizontalSegmentZeroFree σ₁ σ₂ T :=
  horizontal_height_selector_core σ₁ σ₂

end

end Kadiri
