import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
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

private lemma reciprocalKernelPositiveIntegral_eq {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    (∫ u in (γ + δ)..(γ + 2), (1 / |u - γ| : ℝ) ∂volume) =
      ∫ v in δ..2, (1 / v : ℝ) ∂volume := by
  rw [← intervalIntegral.integral_comp_add_left
    (fun u : ℝ => (1 / |u - γ| : ℝ)) γ]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc δ 2 := by
    simpa [Set.uIcc_of_le hδ2] using hv
  have hv_nonneg : 0 ≤ v := by linarith [hvIcc.1, hδ0]
  simp [abs_of_nonneg hv_nonneg]

private lemma reciprocalKernelNegativeIntegral_eq {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    (∫ u in (γ - 2)..(γ - δ), (1 / |u - γ| : ℝ) ∂volume) =
      ∫ v in δ..2, (1 / v : ℝ) ∂volume := by
  rw [← intervalIntegral.integral_comp_sub_left
    (fun u : ℝ => (1 / |u - γ| : ℝ)) γ]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc δ 2 := by
    simpa [Set.uIcc_of_le hδ2] using hv
  have hv_nonneg : 0 ≤ v := by linarith [hvIcc.1, hδ0]
  simp [abs_of_nonneg hv_nonneg]

/-- Per-zero reciprocal-kernel integral used by the panel-revised U6a
averaging argument. -/
theorem reciprocalKernelTwoSidedIntegral_le {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    (∫ u in (γ - 2)..(γ - δ), (1 / |u - γ| : ℝ) ∂volume) +
      (∫ u in (γ + δ)..(γ + 2), (1 / |u - γ| : ℝ) ∂volume) ≤
        2 * Real.log (2 / δ) := by
  rw [reciprocalKernelNegativeIntegral_eq hδ0 hδ2,
    reciprocalKernelPositiveIntegral_eq hδ0 hδ2]
  have hpos :
      (∫ v in δ..2, (1 / v : ℝ) ∂volume) = Real.log (2 / δ) := by
    simp only [one_div]
    rw [integral_inv_of_pos, Real.log_div]
    all_goals positivity
  rw [hpos]
  linarith

/-- Removing finitely many closed `δ`-balls from `(X, 2X]` leaves at least
`X / 2` measure once their total length is at most `X / 2`. -/
theorem volume_Ioc_diff_closedBalls_ge (A : Finset ℝ) {X δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : 2 * δ * (A.card : ℝ) ≤ X / 2) :
    ENNReal.ofReal (X / 2) ≤
      (volume : Measure ℝ) (Set.diff (Set.Ioc X (2 * X))
        (⋃ a ∈ A, Metric.closedBall a δ)) := by
  classical
  let s : Set ℝ := Set.Ioc X (2 * X)
  let bad : Set ℝ := ⋃ a ∈ A, Metric.closedBall a δ
  have hs_meas : MeasurableSet s := measurableSet_Ioc
  have hbad_meas : MeasurableSet bad := by
    dsimp [bad]
    exact Finset.measurableSet_biUnion A (fun _ _ => measurableSet_closedBall)
  have hinter_meas : NullMeasurableSet (s ∩ bad) (volume : Measure ℝ) :=
    (hs_meas.inter hbad_meas).nullMeasurableSet
  have hinter_fin : (volume : Measure ℝ) (s ∩ bad) ≠ ⊤ := by
    have hle : (volume : Measure ℝ) (s ∩ bad) ≤ (volume : Measure ℝ) s :=
      measure_mono Set.inter_subset_left
    have hs_ne_top : (volume : Measure ℝ) s ≠ ⊤ := by
      simp [s, Real.volume_Ioc]
    exact ne_top_of_le_ne_top hs_ne_top hle
  have hdiff :
      (volume : Measure ℝ) (Set.diff s bad) =
        (volume : Measure ℝ) s - (volume : Measure ℝ) (s ∩ bad) := by
    have h := MeasureTheory.measure_diff (μ := (volume : Measure ℝ))
      (s₁ := s) (s₂ := s ∩ bad) Set.inter_subset_left hinter_meas hinter_fin
    have hset : Set.diff s (s ∩ bad) = Set.diff s bad := by
      ext x
      constructor
      · intro hx
        exact ⟨hx.1, fun hb => hx.2 ⟨hx.1, hb⟩⟩
      · intro hx
        exact ⟨hx.1, fun hsb => hx.2 hsb.2⟩
    simpa [hset] using h
  have hbad_le :
      (volume : Measure ℝ) (s ∩ bad) ≤ ENNReal.ofReal (2 * δ * (A.card : ℝ)) := by
    have hle1 : (volume : Measure ℝ) (s ∩ bad) ≤ (volume : Measure ℝ) bad :=
      measure_mono Set.inter_subset_right
    have hle2 :
        (volume : Measure ℝ) bad ≤
          ∑ a ∈ A, (volume : Measure ℝ) (Metric.closedBall a δ) := by
      dsimp [bad]
      exact measure_biUnion_finset_le A (fun a => Metric.closedBall a δ)
    have hsum :
        (∑ a ∈ A, (volume : Measure ℝ) (Metric.closedBall a δ)) =
          (A.card : ENNReal) * ENNReal.ofReal (2 * δ) := by
      simp [Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
    calc
      (volume : Measure ℝ) (s ∩ bad) ≤ (volume : Measure ℝ) bad := hle1
      _ ≤ ∑ a ∈ A, (volume : Measure ℝ) (Metric.closedBall a δ) := hle2
      _ = (A.card : ENNReal) * ENNReal.ofReal (2 * δ) := hsum
      _ = ENNReal.ofReal (2 * δ * (A.card : ℝ)) := by
        rw [← ENNReal.ofReal_natCast A.card, ← ENNReal.ofReal_mul]
        · ring_nf
        · positivity
  have htarget_sub :
      ENNReal.ofReal (X / 2) ≤
        ENNReal.ofReal X - ENNReal.ofReal (2 * δ * (A.card : ℝ)) := by
    rw [← ENNReal.ofReal_sub]
    · exact ENNReal.ofReal_le_ofReal (by linarith)
    · positivity
  have hsub_mono :
      ENNReal.ofReal X - ENNReal.ofReal (2 * δ * (A.card : ℝ)) ≤
        ENNReal.ofReal X - (volume : Measure ℝ) (s ∩ bad) :=
    tsub_le_tsub_left hbad_le (ENNReal.ofReal X)
  have hs_vol : (volume : Measure ℝ) s = ENNReal.ofReal X := by
    simp [s, Real.volume_Ioc]
    ring_nf
  calc
    ENNReal.ofReal (X / 2)
        ≤ ENNReal.ofReal X - ENNReal.ofReal (2 * δ * (A.card : ℝ)) := htarget_sub
    _ ≤ ENNReal.ofReal X - (volume : Measure ℝ) (s ∩ bad) := hsub_mono
    _ = (volume : Measure ℝ) (Set.diff s bad) := by rw [hdiff, hs_vol]
    _ = (volume : Measure ℝ) (Set.diff (Set.Ioc X (2 * X))
        (⋃ a ∈ A, Metric.closedBall a δ)) := by rfl

private lemma u6aZeroWindowSet_finite (σ₁ σ₂ X δ : ℝ) :
    (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
      (Set.Icc (-(2 * X + δ)) (2 * X + δ))).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc (-(2 * X + δ)) (2 * X + δ))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨by simpa [Set.uIcc] using hre, him⟩, hzeta⟩

/-- The finite zero window whose ordinates can affect `δ`-separation in
`(X, 2X]`. -/
noncomputable def u6aZeroWindowFinset (σ₁ σ₂ X δ : ℝ) : Finset ℂ :=
  (u6aZeroWindowSet_finite σ₁ σ₂ X δ).toFinset

/-- Finite set of heights that can violate the top or bottom `δ`-gap inside
`(X, 2X]`.  It contains both zero ordinates and their negatives. -/
noncomputable def u6aBadHeightFinset (σ₁ σ₂ X δ : ℝ) : Finset ℝ :=
  (u6aZeroWindowFinset σ₁ σ₂ X δ).image Complex.im ∪
    (u6aZeroWindowFinset σ₁ σ₂ X δ).image (fun z : ℂ => -z.im)

/-- The bad-height set has at most two images of each zero in the underlying
window. -/
theorem u6aBadHeightFinset_card_le_two_zeroWindow
    (σ₁ σ₂ X δ : ℝ) :
    (u6aBadHeightFinset σ₁ σ₂ X δ).card ≤
      2 * (u6aZeroWindowFinset σ₁ σ₂ X δ).card := by
  classical
  let Z := u6aZeroWindowFinset σ₁ σ₂ X δ
  have h₁ : (Z.image Complex.im ∪ Z.image (fun z : ℂ => -z.im)).card ≤
      (Z.image Complex.im).card + (Z.image (fun z : ℂ => -z.im)).card :=
    Finset.card_union_le _ _
  have h₂ : (Z.image Complex.im).card + (Z.image (fun z : ℂ => -z.im)).card ≤
      Z.card + Z.card :=
    Nat.add_le_add Finset.card_image_le Finset.card_image_le
  calc
    (u6aBadHeightFinset σ₁ σ₂ X δ).card
        = (Z.image Complex.im ∪ Z.image (fun z : ℂ => -z.im)).card := by
          rfl
    _ ≤ (Z.image Complex.im).card + (Z.image (fun z : ℂ => -z.im)).card := h₁
    _ ≤ Z.card + Z.card := h₂
    _ = 2 * Z.card := by omega

/-- The finite bad-height set really covers every way the horizontal segment
can fail the `δ`-gap condition. -/
theorem u6aSafeHeightSet_contains_diff_badHeightFinset
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    Set.diff (Set.Ioc X (2 * X))
        (⋃ a ∈ u6aBadHeightFinset σ₁ σ₂ X δ, Metric.closedBall a δ) ⊆
      u6aSafeHeightSet σ₁ σ₂ X δ := by
  classical
  intro t ht
  rcases ht with ⟨htIoc, htbad⟩
  refine ⟨htIoc, hδ, ?_, ?_⟩
  · intro z hzre hzeta
    by_contra hnot
    have hclose : |z.im - t| < δ := lt_of_not_ge hnot
    have hdist := abs_lt.mp hclose
    have him_low : -(2 * X + δ) ≤ z.im := by
      nlinarith [htIoc.1, hdist.1, hX.le, hδ.le]
    have him_high : z.im ≤ 2 * X + δ := by
      nlinarith [htIoc.2, hdist.2]
    have hzZ : z ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
        (Set.Icc (-(2 * X + δ)) (2 * X + δ)) :=
      ⟨hzre, ⟨him_low, him_high⟩, hzeta⟩
    have hzFin : z ∈ u6aZeroWindowFinset σ₁ σ₂ X δ := by
      unfold u6aZeroWindowFinset
      exact (u6aZeroWindowSet_finite σ₁ σ₂ X δ).mem_toFinset.mpr hzZ
    have hzbad : z.im ∈ u6aBadHeightFinset σ₁ σ₂ X δ := by
      unfold u6aBadHeightFinset
      simp only [Finset.mem_union, Finset.mem_image]
      exact Or.inl ⟨z, hzFin, rfl⟩
    have htball : t ∈ Metric.closedBall z.im δ := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      exact le_of_lt (by simpa [abs_sub_comm] using hclose)
    exact htbad (by
      rw [Set.mem_iUnion]
      exact ⟨z.im, by rw [Set.mem_iUnion]; exact ⟨hzbad, htball⟩⟩)
  · intro z hzre hzeta
    by_contra hnot
    have hclose : |z.im + t| < δ := lt_of_not_ge hnot
    have hdist := abs_lt.mp hclose
    have him_low : -(2 * X + δ) ≤ z.im := by
      nlinarith [htIoc.2, hdist.1]
    have him_high : z.im ≤ 2 * X + δ := by
      nlinarith [htIoc.1, hdist.2, hX.le, hδ.le]
    have hzZ : z ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
        (Set.Icc (-(2 * X + δ)) (2 * X + δ)) :=
      ⟨hzre, ⟨him_low, him_high⟩, hzeta⟩
    have hzFin : z ∈ u6aZeroWindowFinset σ₁ σ₂ X δ := by
      unfold u6aZeroWindowFinset
      exact (u6aZeroWindowSet_finite σ₁ σ₂ X δ).mem_toFinset.mpr hzZ
    have hzbad : -z.im ∈ u6aBadHeightFinset σ₁ σ₂ X δ := by
      unfold u6aBadHeightFinset
      simp only [Finset.mem_union, Finset.mem_image, neg_inj]
      exact Or.inr ⟨z, hzFin, rfl⟩
    have htball : t ∈ Metric.closedBall (-z.im) δ := by
      rw [Metric.mem_closedBall, Real.dist_eq]
      have hclose' : |t + z.im| < δ := by
        simpa [add_comm] using hclose
      exact le_of_lt (by simpa using hclose')
    exact htbad (by
      rw [Set.mem_iUnion]
      exact ⟨-z.im, by rw [Set.mem_iUnion]; exact ⟨hzbad, htball⟩⟩)

/-- Safe heights have measure at least `X / 2` once the finite bad-height
cover has total length at most `X / 2`. -/
theorem u6aSafeHeightSet_measure_ge_of_badHeightFinset
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ)
    (hsmall : 2 * δ * ((u6aBadHeightFinset σ₁ σ₂ X δ).card : ℝ) ≤ X / 2) :
    ENNReal.ofReal (X / 2) ≤
      (volume.restrict (Set.Ioc X (2 * X))) (u6aSafeHeightSet σ₁ σ₂ X δ) := by
  classical
  let A := u6aBadHeightFinset σ₁ σ₂ X δ
  let G : Set ℝ := Set.diff (Set.Ioc X (2 * X))
    (⋃ a ∈ A, Metric.closedBall a δ)
  have hG_meas : MeasurableSet G := by
    have hbad_meas : MeasurableSet (⋃ a ∈ A, Metric.closedBall a δ) :=
      Finset.measurableSet_biUnion A (fun _ _ => measurableSet_closedBall)
    exact measurableSet_Ioc.diff hbad_meas
  have hG_subset_Ioc : G ⊆ Set.Ioc X (2 * X) := by
    intro t ht
    exact ht.1
  have hG_subset_safe : G ⊆ u6aSafeHeightSet σ₁ σ₂ X δ := by
    simpa [G, A] using
      (u6aSafeHeightSet_contains_diff_badHeightFinset (σ₁ := σ₁) (σ₂ := σ₂)
        (X := X) (δ := δ) hX hδ)
  have hmeasure_mono :
      (volume.restrict (Set.Ioc X (2 * X))) G ≤
        (volume.restrict (Set.Ioc X (2 * X))) (u6aSafeHeightSet σ₁ σ₂ X δ) :=
    measure_mono hG_subset_safe
  have hrestrictG :
      (volume.restrict (Set.Ioc X (2 * X))) G = (volume : Measure ℝ) G := by
    have hinter : G ∩ Set.Ioc X (2 * X) = G := Set.inter_eq_left.mpr hG_subset_Ioc
    simp [Measure.restrict_apply, hG_meas, hinter]
  exact (volume_Ioc_diff_closedBalls_ge A hδ.le hsmall).trans
    (by simpa [G, A, hrestrictG] using hmeasure_mono)

/-- The bad-height length condition gives the nonzero safe-set measure needed
by the averaged mean-value extraction. -/
theorem u6aSafeHeightSet_restrict_measure_ne_zero_of_badHeightFinset
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ)
    (hsmall : 2 * δ * ((u6aBadHeightFinset σ₁ σ₂ X δ).card : ℝ) ≤ X / 2) :
    (volume.restrict (Set.Ioc X (2 * X)))
      (u6aSafeHeightSet σ₁ σ₂ X δ) ≠ 0 := by
  have hmeasure := u6aSafeHeightSet_measure_ge_of_badHeightFinset
    (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) hX hδ hsmall
  have hpos : 0 < ENNReal.ofReal (X / 2) := ENNReal.ofReal_pos.2 (by linarith)
  exact ne_of_gt (lt_of_lt_of_le hpos hmeasure)

private lemma u6aNearbyZeroSet_finite (σ₁ σ₂ t : ℝ) :
    (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc (t - 1) (t + 1))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨by simpa [Set.uIcc] using hre, him⟩, hzeta⟩

private lemma u6aNearbyZeroCount_toFinset_card_le (σ₁ σ₂ t : ℝ) (ht : 3 ≤ t) :
    let Z := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
    let hfin : Z.Finite := u6aNearbyZeroSet_finite σ₁ σ₂ t
    (hfin.toFinset.card : ℝ) ≤ u6aNearbyZeroCount σ₁ σ₂ t := by
  classical
  dsimp
  let Z := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
  let hfin : Z.Finite := u6aNearbyZeroSet_finite σ₁ σ₂ t
  unfold u6aNearbyZeroCount
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite (fun _ => (1 : ℝ)) hfin]
  calc
    (hfin.toFinset.card : ℝ)
        = ∑ rho ∈ hfin.toFinset, (1 : ℝ) := by simp
    _ ≤ ∑ rho ∈ hfin.toFinset, (1 : ℝ) * (riemannZeta.order rho : ℝ) := by
      refine Finset.sum_le_sum fun rho hρ => ?_
      have hmem : rho ∈ Z := hfin.mem_toFinset.mp hρ
      have him_low : t - 1 ≤ rho.im := hmem.2.1.1
      have him_high : rho.im ≤ t + 1 := hmem.2.1.2
      let rhoPos : riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 (t + 2)) :=
        ⟨rho, Set.mem_univ _, by constructor <;> linarith, hmem.2.2⟩
      have horder : (1 : ℤ) ≤ riemannZeta.order rho :=
        riemannZeta_one_le_order_positiveHeightZero rhoPos
      have horderR : (1 : ℝ) ≤ (riemannZeta.order rho : ℝ) := by
        exact_mod_cast horder
      simpa using horderR

private lemma exists_avoids_finset_intervals
    (A : Finset ℝ) {L U η : ℝ} (hη : 0 < η)
    (hsmall : 2 * η * (A.card : ℝ) < U - L) :
    ∃ T : ℝ, T ∈ Set.Ioo L U ∧ ∀ a : ℝ, a ∈ A → η ≤ |T - a| := by
  by_contra hnone
  push Not at hnone
  have hsubset :
      Set.Ioo L U ⊆ ⋃ a ∈ A, Metric.closedBall a η := by
    intro T hT
    obtain ⟨a, ha, hbad⟩ := hnone T hT
    rw [Set.mem_iUnion]
    refine ⟨a, ?_⟩
    rw [Set.mem_iUnion]
    refine ⟨ha, ?_⟩
    rw [Metric.mem_closedBall, Real.dist_eq]
    exact le_of_lt hbad
  have hle₁ : volume (Set.Ioo L U) ≤ volume (⋃ a ∈ A, Metric.closedBall a η) :=
    measure_mono hsubset
  have hle₂ :
      volume (⋃ a ∈ A, Metric.closedBall a η) ≤
        ∑ a ∈ A, volume (Metric.closedBall a η) :=
    measure_biUnion_finset_le A (fun a => Metric.closedBall a η)
  have hle : volume (Set.Ioo L U) ≤
      ∑ a ∈ A, volume (Metric.closedBall a η) :=
    hle₁.trans hle₂
  have hsum :
      (∑ a ∈ A, volume (Metric.closedBall a η)) =
        (A.card : ENNReal) * ENNReal.ofReal (2 * η) := by
    simp [Real.volume_closedBall, Finset.sum_const, nsmul_eq_mul]
  have hUpos : 0 < U - L := by
    have hnonneg : 0 ≤ 2 * η * (A.card : ℝ) := by positivity
    linarith
  have hstrict :
      (∑ a ∈ A, volume (Metric.closedBall a η)) <
        volume (Set.Ioo L U) := by
    rw [hsum, Real.volume_Ioo]
    have hcard_nonneg : 0 ≤ (A.card : ℝ) := by positivity
    have hmul :
        (A.card : ENNReal) * ENNReal.ofReal (2 * η) =
          ENNReal.ofReal ((A.card : ℝ) * (2 * η)) := by
      rw [← ENNReal.ofReal_natCast A.card, ← ENNReal.ofReal_mul hcard_nonneg]
    rw [hmul]
    have hcomm : (A.card : ℝ) * (2 * η) = 2 * η * (A.card : ℝ) := by ring
    rw [hcomm]
    exact (ENNReal.ofReal_lt_ofReal_iff hUpos).2 hsmall
  exact (not_lt_of_ge hle) hstrict

/-- Finite real-set interval avoidance by the elementary length pigeonhole
argument. -/
theorem exists_avoids_finite_set_intervals {A : Set ℝ} (hA : A.Finite)
    {L U η : ℝ} (hη : 0 < η)
    (hsmall : 2 * η * (hA.toFinset.card : ℝ) < U - L) :
    ∃ T : ℝ, T ∈ Set.Ioo L U ∧ ∀ a : ℝ, a ∈ A → η ≤ |T - a| := by
  obtain ⟨T, hT, havoid⟩ :=
    exists_avoids_finset_intervals hA.toFinset hη hsmall
  exact ⟨T, hT, fun a ha => havoid a (hA.mem_toFinset.mpr ha)⟩

private lemma u6aEta_lt_quarter {C L c η : ℝ}
    (hC : 0 < C) (hL : 1 < L) (hc : c = 1 / (16 * (C + 1)))
    (hη : η = 2 * c / L) :
    η < 1 / 4 := by
  subst c
  subst η
  have hden_pos : 0 < 8 * (C + 1) * L := by positivity
  have hden_gt_four : 4 < 8 * (C + 1) * L := by nlinarith
  have hrewrite : 2 * (1 / (16 * (C + 1))) / L =
      1 / (8 * (C + 1) * L) := by
    field_simp [show 16 * (C + 1) ≠ 0 by positivity, show L ≠ 0 by positivity]
    ring
  rw [hrewrite]
  field_simp [hden_pos.ne']
  linarith

private lemma u6aSmall_for_avoidance {C L c η card : ℝ}
    (hC : 0 < C) (hL : 0 < L) (hc : c = 1 / (16 * (C + 1)))
    (hη : η = 2 * c / L) (hcard : card ≤ C * L) :
    2 * η * card < 1 / 2 := by
  subst c
  subst η
  have hcoef_nonneg : 0 ≤ 2 * (2 * (1 / (16 * (C + 1))) / L) := by positivity
  have hbound :
      2 * (2 * (1 / (16 * (C + 1))) / L) * card ≤
        2 * (2 * (1 / (16 * (C + 1))) / L) * (C * L) := by
    exact mul_le_mul_of_nonneg_left hcard hcoef_nonneg
  have hcalc :
      2 * (2 * (1 / (16 * (C + 1))) / L) * (C * L) =
        C / (4 * (C + 1)) := by
    field_simp [show 16 * (C + 1) ≠ 0 by positivity, hL.ne']
    ring
  have hfrac : C / (4 * (C + 1)) < 1 / 2 := by
    field_simp [show 4 * (C + 1) ≠ 0 by positivity]
    nlinarith
  linarith

private lemma u6aScale_gap {B T c η : ℝ}
    (hc : 0 ≤ c) (hBlog : 0 < Real.log (B + 1))
    (hlog : Real.log (B + 1) ≤ 2 * Real.log T)
    (hη : η = 2 * c / Real.log (B + 1)) :
    c / Real.log T ≤ η := by
  subst η
  calc
    c / Real.log T = (2 * c) / (2 * Real.log T) := by ring
    _ ≤ (2 * c) / Real.log (B + 1) := by
      exact div_le_div_of_nonneg_left (by positivity) hBlog hlog

/-- Named local-density hypothesis for the conditional U6a route.  This is the
RvM-style input `N(t+1)-N(t) ≤ C log t` used by the sprint panel. -/
def U6aLocalZeroDensityHypothesis (σ₁ σ₂ C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ t : ℝ, Tₘᵢₙ ≤ t → 3 ≤ t →
    u6aNearbyZeroCount σ₁ σ₂ t ≤ C * Real.log t

private theorem exists_good_height_in_half_unit_of_localDensity
    (σ₁ σ₂ Cdens Tdens B : ℝ)
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens)
    (hBdens : Tdens ≤ B) (hB4 : 4 ≤ B) :
    let c : ℝ := 1 / (16 * (Cdens + 1))
    ∃ T : ℝ, B + 1 / 4 < T ∧ T < B + 3 / 4 ∧
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T) := by
  classical
  let center : ℝ := B + 1 / 2
  let c : ℝ := 1 / (16 * (Cdens + 1))
  let η : ℝ := 2 * c / Real.log (B + 1)
  let Z := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
    (Set.Icc (center - 1) (center + 1))
  have hfin : Z.Finite := by
    simpa [Z, center] using u6aNearbyZeroSet_finite σ₁ σ₂ center
  let A : Finset ℝ := hfin.toFinset.image Complex.im
  have hcenter3 : 3 ≤ center := by
    dsimp [center]
    linarith
  have hcenter_dens : Tdens ≤ center := by
    dsimp [center]
    linarith
  have hcenter_pos : 0 < center := by
    dsimp [center]
    linarith
  have hcenter_le_B1 : center ≤ B + 1 := by
    dsimp [center]
    linarith
  have hB1_pos : 0 < B + 1 := by linarith
  have hlog_center_le_B1 : Real.log center ≤ Real.log (B + 1) :=
    Real.log_le_log hcenter_pos hcenter_le_B1
  have hcard_window :
      (hfin.toFinset.card : ℝ) ≤ u6aNearbyZeroCount σ₁ σ₂ center := by
    simpa [Z, center] using u6aNearbyZeroCount_toFinset_card_le σ₁ σ₂ center hcenter3
  have hcard_A_to_window : (A.card : ℝ) ≤ (hfin.toFinset.card : ℝ) := by
    exact_mod_cast (Finset.card_image_le (s := hfin.toFinset) (f := Complex.im))
  have hcard_A_center : (A.card : ℝ) ≤ Cdens * Real.log center :=
    hcard_A_to_window.trans
      (hcard_window.trans (hDensity.2 center hcenter_dens hcenter3))
  have hcard_A_B1 : (A.card : ℝ) ≤ Cdens * Real.log (B + 1) := by
    exact hcard_A_center.trans
      (mul_le_mul_of_nonneg_left hlog_center_le_B1 (le_of_lt hDensity.1))
  have hlogB1_gt_one : 1 < Real.log (B + 1) := by
    rw [Real.lt_log_iff_exp_lt hB1_pos]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < B + 1 := by norm_num; linarith
  have hlogB1_pos : 0 < Real.log (B + 1) := lt_trans zero_lt_one hlogB1_gt_one
  have hcpos : 0 < c := by
    dsimp [c]
    exact one_div_pos.mpr (by nlinarith [hDensity.1])
  have hηpos : 0 < η := by
    dsimp [η]
    positivity
  have hη_lt_quarter : η < 1 / 4 :=
    u6aEta_lt_quarter hDensity.1 hlogB1_gt_one (by rfl : c = 1 / (16 * (Cdens + 1)))
      (by rfl : η = 2 * c / Real.log (B + 1))
  have hsmall : 2 * η * (A.card : ℝ) < (B + 3 / 4) - (B + 1 / 4) := by
    have hhalf : 2 * η * (A.card : ℝ) < 1 / 2 :=
      u6aSmall_for_avoidance hDensity.1 hlogB1_pos
        (by rfl : c = 1 / (16 * (Cdens + 1)))
        (by rfl : η = 2 * c / Real.log (B + 1)) hcard_A_B1
    calc
      2 * η * (A.card : ℝ) < (1 / 2 : ℝ) := hhalf
      _ = (B + 3 / 4) - (B + 1 / 4) := by ring
  obtain ⟨T, hTinterval, hAvoid⟩ :=
    exists_avoids_finset_intervals A hηpos hsmall
  have hTpos : 0 < T := by linarith [hTinterval.1, hB4]
  have hT_gt_one : 1 < T := by linarith [hTinterval.1, hB4]
  have hlogT_pos : 0 < Real.log T := Real.log_pos hT_gt_one
  have hlogB1_le_two_logT : Real.log (B + 1) ≤ 2 * Real.log T := by
    have hB1_le_Tsq : B + 1 ≤ T ^ 2 := by nlinarith [hTinterval.1, hB4]
    have hlog_le_sq : Real.log (B + 1) ≤ Real.log (T ^ 2) :=
      Real.log_le_log hB1_pos hB1_le_Tsq
    simpa [Real.log_pow] using hlog_le_sq
  have hscale : c / Real.log T ≤ η :=
    u6aScale_gap (le_of_lt hcpos) hlogB1_pos hlogB1_le_two_logT
      (by rfl : η = 2 * c / Real.log (B + 1))
  refine ⟨T, hTinterval.1, hTinterval.2, ?_⟩
  refine ⟨div_pos hcpos hlogT_pos, ?_, ?_⟩
  · intro z hzre hzeta
    by_contra hnot
    have hclose_final : |z.im - T| < c / Real.log T := lt_of_not_ge hnot
    have hclose_eta : |z.im - T| < η := hclose_final.trans_le hscale
    have hdist := abs_lt.mp hclose_eta
    have him_low : center - 1 ≤ z.im := by
      dsimp [center]
      nlinarith [hdist.1, hTinterval.1, hη_lt_quarter]
    have him_high : z.im ≤ center + 1 := by
      dsimp [center]
      nlinarith [hdist.2, hTinterval.2, hη_lt_quarter]
    have hzZ : z ∈ Z := by
      exact ⟨hzre, ⟨him_low, him_high⟩, hzeta⟩
    have hzA : z.im ∈ A := by
      dsimp [A]
      rw [Finset.mem_image]
      exact ⟨z, hfin.mem_toFinset.2 hzZ, rfl⟩
    have havoid_abs : η ≤ |z.im - T| := by
      have := hAvoid z.im hzA
      rwa [abs_sub_comm] at this
    exact not_lt_of_ge havoid_abs hclose_eta
  · intro z hzre hzeta
    by_contra hnot
    have hclose_final : |z.im + T| < c / Real.log T := lt_of_not_ge hnot
    have hclose_eta : |z.im + T| < η := hclose_final.trans_le hscale
    let zc : ℂ := (starRingEnd ℂ) z
    have hzc_re : zc.re ∈ Set.uIcc σ₁ σ₂ := by
      dsimp [zc]
      simpa [Complex.conj_re] using hzre
    have hzc_zeta : riemannZeta zc = 0 := by
      dsimp [zc]
      exact riemannZetaConjZeroSource_of_riemannZeta_conj z hzeta
    have hzc_close_eta : |zc.im - T| < η := by
      have hdist_eq : |zc.im - T| = |z.im + T| := by
        calc
          |zc.im - T| = |-z.im - T| := by
            simp [zc, Complex.conj_im]
          _ = |-(z.im + T)| := by ring_nf
          _ = |z.im + T| := by rw [abs_neg]
      simpa [hdist_eq] using hclose_eta
    have hdist := abs_lt.mp hzc_close_eta
    have him_low : center - 1 ≤ zc.im := by
      dsimp [center]
      nlinarith [hdist.1, hTinterval.1, hη_lt_quarter]
    have him_high : zc.im ≤ center + 1 := by
      dsimp [center]
      nlinarith [hdist.2, hTinterval.2, hη_lt_quarter]
    have hzcZ : zc ∈ Z := by
      exact ⟨hzc_re, ⟨him_low, him_high⟩, hzc_zeta⟩
    have hzcA : zc.im ∈ A := by
      dsimp [A]
      rw [Finset.mem_image]
      exact ⟨zc, hfin.mem_toFinset.2 hzcZ, rfl⟩
    have havoid_abs : η ≤ |zc.im - T| := by
      have := hAvoid zc.im hzcA
      rwa [abs_sub_comm] at this
    exact not_lt_of_ge havoid_abs hzc_close_eta

private theorem u6aHeightSelection_fixedC_of_localDensity
    (σ₁ σ₂ : ℝ) {Cdens Tdens : ℝ}
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens) :
    0 < 1 / (16 * (Cdens + 1)) ∧
      ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
        horizontalSegmentZeroGap σ₁ σ₂ T
          ((1 / (16 * (Cdens + 1))) / Real.log T) := by
  constructor
  · exact one_div_pos.mpr (by nlinarith [hDensity.1])
  intro T₀
  let B : ℝ := max (max T₀ Tdens) 4
  have hT₀B : T₀ ≤ B := by
    exact (le_max_left T₀ Tdens).trans (le_max_left (max T₀ Tdens) 4)
  have hTdensB : Tdens ≤ B := by
    exact (le_max_right T₀ Tdens).trans (le_max_left (max T₀ Tdens) 4)
  have hB4 : 4 ≤ B := le_max_right (max T₀ Tdens) 4
  obtain ⟨T, hTB_low, _hTB_high, hgap⟩ :=
    exists_good_height_in_half_unit_of_localDensity σ₁ σ₂ Cdens Tdens B
      hDensity hTdensB hB4
  refine ⟨T, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · simpa using hgap

/-- Named partial-fraction approximation hypothesis.  The Hadamard input is
`logDeriv_riemannXi_eq_polynomial_derivative_add_tsum` in
`RiemannZetaHadamard.lean:244`, with the zeta bridge in
`HadamardLogDerivative.lean`. -/
def U6aPartialFractionApproximationHypothesis (σ₁ σ₂ C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc σ₁ σ₂ → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖deriv riemannZeta s / riemannZeta s -
        u6aNearbyZeroPrincipalSum σ₁ σ₂ s.im s‖ ≤ C * Real.log |s.im|

/-- The global xi-zero contribution supplied by Mathlib's genus-one Hadamard
logarithmic derivative formula. -/
noncomputable def u6aXiHadamardZeroSum (s : ℂ) : ℂ :=
  ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
    (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
      1 / Complex.Hadamard.divisorZeroIndex₀_val p)

/-- The exact remainder after subtracting the local Kadiri principal part from
the xi-Hadamard expression for `ζ'/ζ`.  Bounding this term is the analytic
piece left for the partial-fraction disk argument. -/
noncomputable def u6aHadamardPartialFractionRemainder
    (σ₁ σ₂ t : ℝ) (P : Polynomial ℂ) (s : ℂ) : ℂ :=
  Polynomial.eval s P.derivative
    + u6aXiHadamardZeroSum s
    - u6aNearbyZeroPrincipalSum σ₁ σ₂ t s
    - 1 / (s - 1)
    + (1 / 2 : ℂ) * Real.log Real.pi
    - (1 / 2 : ℂ) * digamma (s / 2 + 1)

/-- Named analytic-estimate input for the Hadamard partial-fraction route. -/
def U6aHadamardRemainderBoundHypothesis
    (σ₁ σ₂ C Tₘᵢₙ : ℝ) (P : Polynomial ℂ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc σ₁ σ₂ → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖u6aHadamardPartialFractionRemainder σ₁ σ₂ s.im P s‖ ≤ C * Real.log |s.im|

/-- Exact pointwise reduction of `ζ'/ζ` minus Kadiri's nearby-zero principal
part to the xi-Hadamard remainder. -/
theorem zeta_logDeriv_sub_nearby_eq_hadamardRemainder
    {P : Polynomial ℂ} {σ₁ σ₂ t : ℝ} {s : ℂ}
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hs0 : s ≠ 0)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    deriv riemannZeta s / riemannZeta s - u6aNearbyZeroPrincipalSum σ₁ σ₂ t s =
      u6aHadamardPartialFractionRemainder σ₁ σ₂ t P s := by
  have hneg :=
    neg_zeta_logDeriv_eq_of_riemannXi_hadamard
      (P := P) (s := s) hfac hz hs0 hs1 hΓdiff hΓ hζ
  have hpos : deriv riemannZeta s / riemannZeta s =
      Polynomial.eval s P.derivative
        + u6aXiHadamardZeroSum s
        - 1 / (s - 1)
        + (1 / 2 : ℂ) * Real.log Real.pi
        - (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
    unfold u6aXiHadamardZeroSum
    calc
      deriv riemannZeta s / riemannZeta s =
          -(-deriv riemannZeta s / riemannZeta s) := by ring
      _ = -(-Polynomial.eval s P.derivative
          - (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
              (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
                1 / Complex.Hadamard.divisorZeroIndex₀_val p))
          + 1 / (s - 1)
          - (1 / 2 : ℂ) * Real.log Real.pi
          + (1 / 2 : ℂ) * digamma (s / 2 + 1)) := by rw [hneg]
      _ = Polynomial.eval s P.derivative
          + (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
              (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
                1 / Complex.Hadamard.divisorZeroIndex₀_val p))
          - 1 / (s - 1)
          + (1 / 2 : ℂ) * Real.log Real.pi
          - (1 / 2 : ℂ) * digamma (s / 2 + 1) := by ring
  rw [hpos]
  unfold u6aHadamardPartialFractionRemainder
  ring

/-- A named Hadamard remainder bound gives the pointwise partial-fraction
approximation wherever the exact xi-Hadamard bridge is legal. -/
theorem u6aPartialFractionApproximation_at_of_hadamardRemainderBound
    {P : Polynomial ℂ} {σ₁ σ₂ C Tₘᵢₙ : ℝ} {s : ℂ}
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p)
    (hs0 : s ≠ 0)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hR : U6aHadamardRemainderBoundHypothesis σ₁ σ₂ C Tₘᵢₙ P)
    (hre : s.re ∈ Set.uIcc σ₁ σ₂)
    (hT : Tₘᵢₙ ≤ |s.im|)
    (hT3 : 3 ≤ |s.im|) :
    ‖deriv riemannZeta s / riemannZeta s -
        u6aNearbyZeroPrincipalSum σ₁ σ₂ s.im s‖ ≤ C * Real.log |s.im| := by
  rw [zeta_logDeriv_sub_nearby_eq_hadamardRemainder
    (P := P) (σ₁ := σ₁) (σ₂ := σ₂) (t := s.im) (s := s)
    hfac hz hs0 hs1 hΓdiff hΓ hζ]
  exact hR.2 s hre hT hT3

/-- Named height-selection output from the local-density pigeonhole argument:
cofinally many heights stay at least `c / log T` away from zero ordinates. -/
def U6aHeightSelectionHypothesis (σ₁ σ₂ Cdens Tdens c : ℝ) : Prop :=
  U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens →
    0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T)

/-- The local-density hypothesis alone supplies the `c / log T` height selector
with explicit `c = 1 / (16 * (C + 1))`. -/
theorem U6aHeightSelectionHypothesis_of_localDensity
    (σ₁ σ₂ Cdens Tdens : ℝ) :
    U6aHeightSelectionHypothesis σ₁ σ₂ Cdens Tdens
      (1 / (16 * (Cdens + 1))) := by
  intro hDensity
  exact u6aHeightSelection_fixedC_of_localDensity σ₁ σ₂ hDensity

/-- Cofinal quantitative zero gaps obtained from the local-density hypothesis,
with the explicit selector constant exposed existentially. -/
theorem exists_arbitrarily_large_horizontalSegmentZeroGap_of_localDensity_proved
    (σ₁ σ₂ : ℝ) {Cdens Tdens : ℝ}
    (hDensity : U6aLocalZeroDensityHypothesis σ₁ σ₂ Cdens Tdens) :
    ∃ c : ℝ, 0 < c ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentZeroGap σ₁ σ₂ T (c / Real.log T) := by
  exact ⟨1 / (16 * (Cdens + 1)),
    u6aHeightSelection_fixedC_of_localDensity σ₁ σ₂ hDensity⟩

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

/-- Averaged-selection input for the unconditional U6a height-selection route.
This packages the safe-set measure, integrability, and averaged `S₂` estimate
after the crude zero-counting and zero-gap work has supplied them. -/
structure U6aAveragedSelectionInput (σ₁ σ₂ X δ M : ℝ) : Prop where
  hX : 0 < X
  hEpos :
    (volume.restrict (Set.Ioc X (2 * X)))
      (u6aSafeHeightSet σ₁ σ₂ X δ) ≠ 0
  hSInt : IntervalIntegrable
    ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
      (u6aReciprocalZeroSum σ₁ σ₂)) volume X (2 * X)
  hBInt : IntervalIntegrable
    ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
      fun _ : ℝ => u6aAveragedSelectionBound X δ M) volume X (2 * X)
  hAvg :
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
      ∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume

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

/-- Consumer-facing averaged height selector.  The selection layer has no
local-density or `c / log T` height-selector hypothesis; those are replaced by
the averaged safe-set input. -/
theorem exists_height_with_small_reciprocalZeroSum_of_averaging
    {σ₁ σ₂ X δ M : ℝ}
    (hAvgSel : U6aAveragedSelectionInput σ₁ σ₂ X δ M) :
    ∃ T : ℝ, T ∈ u6aSafeHeightSet σ₁ σ₂ X δ ∧
      u6aReciprocalZeroSum σ₁ σ₂ T ≤ u6aAveragedSelectionBound X δ M :=
  exists_height_with_small_reciprocalZeroSum_of_indicator_average
    hAvgSel.hX hAvgSel.hEpos hAvgSel.hSInt hAvgSel.hBInt hAvgSel.hAvg

/-- Averaged selector with the safe-set nonzero-measure hypothesis discharged
from the finite bad-height length estimate. -/
theorem exists_height_with_small_reciprocalZeroSum_of_badHeightFinset_average
    {σ₁ σ₂ X δ M : ℝ}
    (hX : 0 < X) (hδ : 0 < δ)
    (hsmall : 2 * δ * ((u6aBadHeightFinset σ₁ σ₂ X δ).card : ℝ) ≤ X / 2)
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
      u6aReciprocalZeroSum σ₁ σ₂ T ≤ u6aAveragedSelectionBound X δ M :=
  exists_height_with_small_reciprocalZeroSum_of_indicator_average hX
    (u6aSafeHeightSet_restrict_measure_ne_zero_of_badHeightFinset hX hδ hsmall)
    hSInt hBInt hAvg

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
