import PrimeNumberTheoremAnd.IEANTN.KadiriZeroCounting
import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.IEANTN.CH2.CH2
import PrimeNumberTheoremAnd.Mathlib.Analysis.Calculus.Deriv.Polynomial
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFiniteOrder
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.DigammaSeries
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

private lemma u6aNearbyZeroSet_subset_reciprocalZeroSet
    (σ₁ σ₂ t : ℝ) :
    riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1)) ⊆
      riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2)) := by
  intro ρ hρ
  rcases hρ with ⟨hρre, hρim, hρzero⟩
  refine ⟨hρre, ?_, hρzero⟩
  exact ⟨by linarith [hρim.1], by linarith [hρim.2]⟩

/-- Safe heights in the dyadic interval `[X, 2X]`, with both horizontal sides
at least `δ` away from zero ordinates. -/
def u6aSafeHeightSet (σ₁ σ₂ X δ : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc X (2 * X) ∧ horizontalSegmentZeroGap σ₁ σ₂ t δ}

/-- The explicit panel bound selected from the averaged reciprocal-zero sum. -/
noncomputable def u6aAveragedSelectionBound (X δ M : ℝ) : ℝ :=
  4 * M * Real.log (2 / δ) / X

private lemma u6a_riemannZeta_eventually_ne_zero_punctured_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    ∀ᶠ z in nhdsWithin s ({s}ᶜ), riemannZeta z ≠ 0 := by
  have hmem_compl_one : s ∈ ({1} : Set ℂ)ᶜ := by
    simpa [Set.mem_compl_iff] using hs
  have hdisj : Disjoint (nhdsWithin s ({s}ᶜ))
      (Filter.principal (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)) := by
    exact (mem_codiscreteWithin.mp riemannZeta.zeroes_codiscreteWithin_compl_one)
      s hmem_compl_one
  have hnot_zeroes : (({1} : Set ℂ)ᶜ \ riemannZeta.zeroesᶜ)ᶜ ∈
      nhdsWithin s ({s}ᶜ) :=
    Filter.disjoint_principal_right.mp hdisj
  have heventually_compl_one : ∀ᶠ z in nhdsWithin s ({s}ᶜ),
      z ∈ ({1} : Set ℂ)ᶜ := by
    exact nhdsWithin_le_nhds (isOpen_compl_singleton.mem_nhds hmem_compl_one)
  filter_upwards [hnot_zeroes, heventually_compl_one] with z hznot hz_compl_one hzero
  have hz_zero : z ∈ riemannZeta.zeroes := by
    simpa [riemannZeta.zeroes] using hzero
  exact hznot ⟨hz_compl_one, by simpa using hz_zero⟩

private lemma u6a_riemannZeta_meromorphicOrderAt_ne_top_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    meromorphicOrderAt riemannZeta s ≠ ⊤ := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  exact (meromorphicOrderAt_ne_top_iff_eventually_ne_zero han.meromorphicAt).2
    (u6a_riemannZeta_eventually_ne_zero_punctured_of_ne_one hs)

private lemma u6a_riemannZeta_order_pos_of_zero_ne_one {s : ℂ} (hs : s ≠ 1)
    (hzero : riemannZeta s = 0) :
    0 < riemannZeta.order s := by
  have han := riemannZeta_analyticOn_compl_one s (by simpa [Set.mem_compl_iff] using hs)
  have horder_ne_top : meromorphicOrderAt riemannZeta s ≠ ⊤ :=
    u6a_riemannZeta_meromorphicOrderAt_ne_top_of_ne_one hs
  have hanOrder_ne_zero : analyticOrderAt riemannZeta s ≠ 0 := by
    intro h
    exact (han.analyticOrderAt_eq_zero.mp h) hzero
  unfold riemannZeta.order
  cases hO : analyticOrderAt riemannZeta s with
  | top =>
      exfalso
      exact horder_ne_top (by simp [han.meromorphicOrderAt_eq, hO])
  | coe n =>
      have hn_pos : 0 < n := by
        exact Nat.pos_of_ne_zero (by
          intro hn
          exact hanOrder_ne_zero (by simp [hO, hn]))
      rw [han.meromorphicOrderAt_eq, hO, ENat.map_coe, WithTop.untopD_coe]
      exact_mod_cast hn_pos

private lemma u6a_zeta_zero_order_nonneg_of_zero {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) :
    0 ≤ (riemannZeta.order ρ : ℝ) := by
  have hne_one : ρ ≠ 1 := by
    intro hρ
    exact riemannZeta_one_ne_zero (by simpa [hρ] using hzero)
  exact_mod_cast le_of_lt (u6a_riemannZeta_order_pos_of_zero_ne_one hne_one hzero)

private lemma u6a_riemannZeta_order_star (z : ℂ) :
    riemannZeta.order ((starRingEnd ℂ) z) = riemannZeta.order z := by
  have hsymm : CH2.ConjSymm riemannZeta := by
    intro s
    exact riemannZeta_conj s
  unfold riemannZeta.order
  rw [← CH2.meromorphicOrderAt_starRingEnd (F := riemannZeta) (z := z) (Or.inl hsymm)]

/-- Any non-real zeta zero is a non-trivial zero in the project's
`NontrivialZeros` representation. -/
theorem u6a_zeta_zero_mem_nontrivial_of_im_ne_zero {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (him : ρ.im ≠ 0) : ρ ∈ NontrivialZeros := by
  have hnot_re_nonpos : ¬ ρ.re ≤ 0 := by
    intro hre
    exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him) hzero
  have hre_pos : 0 < ρ.re := lt_of_not_ge hnot_re_nonpos
  have hnot_re_one_le : ¬ 1 ≤ ρ.re := by
    intro hre
    exact (riemannZeta_ne_zero_of_one_le_re hre) hzero
  have hre_lt_one : ρ.re < 1 := lt_of_not_ge hnot_re_one_le
  exact ⟨⟨hre_pos, hre_lt_one⟩, Set.mem_univ ρ.im, hzero⟩

/-- A unit-height window centered at height `t` with `|t| ≥ 2` contains no
real-axis zeta zeros; hence every zeta zero in the U6a strip window is
non-trivial. -/
theorem u6a_zeroes_rect_high_window_subset_nontrivial {t : ℝ}
    (ht : 2 ≤ |t|) :
    ∀ ρ : ℂ, ρ ∈ riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (t - 1) (t + 1)) →
      ρ ∈ NontrivialZeros := by
  intro ρ hρ
  exact u6a_zeta_zero_mem_nontrivial_of_im_ne_zero hρ.2.2 (by
    intro him0
    have him_abs : |t| ≤ 1 := by
      have himI := hρ.2.1
      rw [him0] at himI
      have ht_le : t ≤ 1 := by linarith [himI.1]
      have hneg_le : -1 ≤ t := by linarith [himI.2]
      exact abs_le.mpr ⟨hneg_le, ht_le⟩
    linarith)

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

private lemma intervalIntegrable_reciprocalKernel_left {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    IntervalIntegrable (fun u : ℝ => (1 / |u - γ| : ℝ)) volume (γ - 2) (γ - δ) := by
  have hle : γ - 2 ≤ γ - δ := by linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
  intro u hu
  have hne : |u - γ| ≠ 0 := by
    have hu_le : u ≤ γ - δ := hu.2
    have hlt : u < γ := by linarith
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hlt.ne)
  simpa [one_div] using
    (ContinuousAt.inv₀ ((continuousAt_id.sub continuousAt_const).abs) hne).continuousWithinAt

private lemma intervalIntegrable_reciprocalKernel_right {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    IntervalIntegrable (fun u : ℝ => (1 / |u - γ| : ℝ)) volume (γ + δ) (γ + 2) := by
  have hle : γ + δ ≤ γ + 2 := by linarith
  refine ContinuousOn.intervalIntegrable_of_Icc hle ?_
  intro u hu
  have hne : |u - γ| ≠ 0 := by
    have hu_ge : γ + δ ≤ u := hu.1
    have hgt : γ < u := by linarith
    exact abs_ne_zero.mpr (sub_ne_zero.mpr hgt.ne')
  simpa [one_div] using
    (ContinuousAt.inv₀ ((continuousAt_id.sub continuousAt_const).abs) hne).continuousWithinAt

private lemma integrable_puncturedReciprocalKernel {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    Integrable
      ((Set.Icc (γ - 2) (γ - δ) ∪ Set.Icc (γ + δ) (γ + 2)).indicator
        (fun u : ℝ => (1 / |u - γ| : ℝ))) volume := by
  let k : ℝ → ℝ := fun u => (1 / |u - γ| : ℝ)
  let L : Set ℝ := Set.Icc (γ - 2) (γ - δ)
  let R : Set ℝ := Set.Icc (γ + δ) (γ + 2)
  have hL_ioc : IntegrableOn k (Set.Ioc (γ - 2) (γ - δ)) volume := by
    simpa [k, L] using
      (intervalIntegrable_reciprocalKernel_left (γ := γ) hδ0 hδ2).1
  have hR_ioc : IntegrableOn k (Set.Ioc (γ + δ) (γ + 2)) volume := by
    simpa [k, R] using
      (intervalIntegrable_reciprocalKernel_right (γ := γ) hδ0 hδ2).1
  have hL : IntegrableOn k L volume := by
    simpa [L] using hL_ioc.congr_set_ae (Ioc_ae_eq_Icc (μ := volume)).symm
  have hR : IntegrableOn k R volume := by
    simpa [R] using hR_ioc.congr_set_ae (Ioc_ae_eq_Icc (μ := volume)).symm
  have hLR : IntegrableOn k (L ∪ R) volume := hL.union hR
  exact hLR.integrable_indicator (measurableSet_Icc.union measurableSet_Icc)

private lemma integral_puncturedReciprocalKernel_eq {δ γ : ℝ}
    (hδ0 : 0 < δ) (hδ2 : δ ≤ 2) :
    ∫ u, (Set.Icc (γ - 2) (γ - δ) ∪ Set.Icc (γ + δ) (γ + 2)).indicator
        (fun u : ℝ => (1 / |u - γ| : ℝ)) u ∂volume =
      (∫ u in (γ - 2)..(γ - δ), (1 / |u - γ| : ℝ) ∂volume) +
        ∫ u in (γ + δ)..(γ + 2), (1 / |u - γ| : ℝ) ∂volume := by
  let k : ℝ → ℝ := fun u => (1 / |u - γ| : ℝ)
  let L : Set ℝ := Set.Icc (γ - 2) (γ - δ)
  let R : Set ℝ := Set.Icc (γ + δ) (γ + 2)
  have hL_ioc : IntegrableOn k (Set.Ioc (γ - 2) (γ - δ)) volume := by
    simpa [k] using
      (intervalIntegrable_reciprocalKernel_left (γ := γ) hδ0 hδ2).1
  have hR_ioc : IntegrableOn k (Set.Ioc (γ + δ) (γ + 2)) volume := by
    simpa [k] using
      (intervalIntegrable_reciprocalKernel_right (γ := γ) hδ0 hδ2).1
  have hL : IntegrableOn k L volume := by
    simpa [L] using hL_ioc.congr_set_ae (Ioc_ae_eq_Icc (μ := volume)).symm
  have hR : IntegrableOn k R volume := by
    simpa [R] using hR_ioc.congr_set_ae (Ioc_ae_eq_Icc (μ := volume)).symm
  have hdisj : Disjoint L R := by
    rw [Set.disjoint_left]
    intro u huL huR
    have hle_left : u ≤ γ - δ := huL.2
    have hge_right : γ + δ ≤ u := huR.1
    linarith
  have haedisj : AEDisjoint volume L R := hdisj.aedisjoint
  rw [MeasureTheory.integral_indicator (measurableSet_Icc.union measurableSet_Icc)]
  rw [MeasureTheory.setIntegral_union₀ haedisj measurableSet_Icc.nullMeasurableSet hL hR]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [intervalIntegral.integral_of_le (by linarith : γ - 2 ≤ γ - δ)]
  rw [intervalIntegral.integral_of_le (by linarith : γ + δ ≤ γ + 2)]

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

/-- Fixed finite window that contains every zero contributing to `S₂(t)` when
`t ∈ (X, 2X]`. -/
noncomputable def u6aFixedWindowReciprocalSum (σ₁ σ₂ X t : ℝ) : ℝ :=
  ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2,
    (1 / |t - ρ.im|) * (riemannZeta.order ρ : ℝ)

/-- Fixed finite window with the per-zero kernel localized to
`|t - Im ρ| ≤ 2`, matching the support of `S₂(t)`. -/
noncomputable def u6aFixedWindowLocalizedReciprocalSum (σ₁ σ₂ X t : ℝ) : ℝ :=
  ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2,
    (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
      (fun u : ℝ => 1 / |u - ρ.im|) t *
      (riemannZeta.order ρ : ℝ)

/-- Order-weighted zero mass in the fixed dyadic window used by the
averaging argument. -/
noncomputable def u6aFixedWindowZeroMass (σ₁ σ₂ X : ℝ) : ℝ :=
  ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2, (riemannZeta.order ρ : ℝ)

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

/-- Possible real-axis zeros in the U6a strip, kept as a finite additive
bucket instead of being asserted away. -/
abbrev u6aStripZeroHeightZeros : Type :=
  riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc 0 0)

lemma u6aStripZeroHeightZeros_finite : Finite u6aStripZeroHeightZeros := by
  have hfin : (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc 0 0)).Finite := by
    rw [riemannZeta.zeroes_rect_eq]
    let S : Set ℂ :=
      (Complex.re ⁻¹' Set.Icc (-1 : ℝ) 2) ∩
        (Complex.im ⁻¹' Set.Icc (0 : ℝ) 0)
    have hS : IsCompact S := by
      exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
        (isCompact_Icc.prod isCompact_Icc)
    refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
    intro z hz
    rcases hz with ⟨⟨hre, him⟩, hzeta⟩
    have hle : (-1 : ℝ) ≤ 2 := by norm_num
    exact ⟨⟨by simpa [Set.uIcc_of_le hle] using hre, him⟩, hzeta⟩
  exact Set.finite_coe_iff.mpr hfin

/-- Order-weighted real-axis zero bucket in the U6a strip.  This remains
finite and additive rather than asserting those zeros away. -/
noncomputable def u6aStripZeroHeightZeroMass : ℝ :=
  riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2) (Set.Icc 0 0) (fun _ => (1 : ℝ))

/-- The order-weighted fixed window is controlled by the positive-height
zero-counting function twice, plus the finite real-axis order bucket.  Negative
heights are transferred to positive heights by conjugation, preserving order. -/
theorem u6aFixedWindowZeroMass_le_two_N_add_zeroHeightMass {k : ℕ} {X : ℝ}
    (hT : 2 * X + 2 < (2 : ℝ) ^ (k + 1)) :
    u6aFixedWindowZeroMass (-1) 2 X ≤
      2 * riemannZeta.N ((2 : ℝ) ^ (k + 1)) + u6aStripZeroHeightZeroMass := by
  classical
  let T : ℝ := (2 : ℝ) ^ (k + 1)
  let Win : Type := {z : ℂ // z ∈ u6aZeroWindowFinset (-1) 2 X 2}
  let Pos : Type := riemannZeta.zeroes_rect (.univ : Set ℝ) (.Ioo 0 T)
  let Zero : Type := u6aStripZeroHeightZeros
  haveI : Finite Pos :=
    Set.finite_coe_iff.mpr (zeroes_rect_univ_positive_height_finite T)
  haveI : Fintype Pos := Fintype.ofFinite Pos
  haveI : Finite Zero := u6aStripZeroHeightZeros_finite
  haveI : Fintype Zero := Fintype.ofFinite Zero
  haveI : Fintype Win := Finset.fintypeCoeSort (u6aZeroWindowFinset (-1) 2 X 2)
  let Bucket : Type := Pos ⊕ (Pos ⊕ Zero)
  let weightWin : Win → ℝ := fun z => (riemannZeta.order (z : ℂ) : ℝ)
  let weightBucket : Bucket → ℝ
    | Sum.inl ρ => (riemannZeta.order (ρ : ℂ) : ℝ)
    | Sum.inr (Sum.inl ρ) => (riemannZeta.order (ρ : ℂ) : ℝ)
    | Sum.inr (Sum.inr ρ) => (riemannZeta.order (ρ : ℂ) : ℝ)
  let toBucket : Win → Bucket := fun z =>
    have hzwin : (z : ℂ) ∈ riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (-(2 * X + 2)) (2 * X + 2)) := by
      simpa [u6aZeroWindowFinset] using z.property
    if hpos : 0 < (z : ℂ).im then
      Sum.inl
        ⟨(z : ℂ), Set.mem_univ _, by
          constructor
          · exact hpos
          · have him_le : (z : ℂ).im ≤ 2 * X + 2 := hzwin.2.1.2
            exact lt_of_le_of_lt him_le hT,
          hzwin.2.2⟩
    else if hzero : (z : ℂ).im = 0 then
      Sum.inr (Sum.inr ⟨(z : ℂ), hzwin.1, by simp [hzero], hzwin.2.2⟩)
    else
      Sum.inr (Sum.inl
        ⟨((starRingEnd ℂ) (z : ℂ)), Set.mem_univ _, by
          have hneg : (z : ℂ).im < 0 := lt_of_le_of_ne (not_lt.mp hpos) hzero
          constructor
          · simpa [Complex.conj_im] using neg_pos.mpr hneg
          · have him_abs_le : |(z : ℂ).im| ≤ 2 * X + 2 :=
              abs_le.mpr ⟨hzwin.2.1.1, hzwin.2.1.2⟩
            have him_neg : -((z : ℂ).im) = |(z : ℂ).im| := by
              rw [abs_of_neg hneg]
            rw [Complex.conj_im, him_neg]
            exact lt_of_le_of_lt him_abs_le hT,
          by
            exact riemannZetaConjZeroSource_of_riemannZeta_conj (z : ℂ) hzwin.2.2⟩)
  let recover : Bucket → ℂ
    | Sum.inl ρ => (ρ : ℂ)
    | Sum.inr (Sum.inl ρ) => (starRingEnd ℂ) (ρ : ℂ)
    | Sum.inr (Sum.inr ρ) => (ρ : ℂ)
  have hrecover : ∀ z : Win, recover (toBucket z) = (z : ℂ) := by
    intro z
    dsimp [toBucket, recover]
    by_cases hpos : 0 < (z : ℂ).im
    · simp [hpos]
    · by_cases hzero : (z : ℂ).im = 0
      · simp [hzero]
      · simp [hpos, hzero]
  have hinj : Function.Injective toBucket := by
    intro z w hzw
    apply Subtype.ext
    calc
      (z : ℂ) = recover (toBucket z) := (hrecover z).symm
      _ = recover (toBucket w) := by rw [hzw]
      _ = (w : ℂ) := hrecover w
  have hweight : ∀ z : Win, weightBucket (toBucket z) = weightWin z := by
    intro z
    dsimp [toBucket, weightBucket, weightWin]
    by_cases hpos : 0 < (z : ℂ).im
    · simp [hpos]
    · by_cases hzero : (z : ℂ).im = 0
      · simp [hzero]
      · simp [hpos, hzero, u6a_riemannZeta_order_star]
  have hbucket_nonneg : ∀ b : Bucket, 0 ≤ weightBucket b := by
    intro b
    rcases b with ρ | ρz
    · dsimp [weightBucket]
      have horder : (0 : ℤ) ≤ riemannZeta.order (ρ : ℂ) :=
        le_of_lt (riemannZeta_order_pos_positiveHeightZero ρ)
      exact_mod_cast horder
    · rcases ρz with ρ | ρ
      · dsimp [weightBucket]
        have horder : (0 : ℤ) ≤ riemannZeta.order (ρ : ℂ) :=
          le_of_lt (riemannZeta_order_pos_positiveHeightZero ρ)
        exact_mod_cast horder
      · dsimp [weightBucket]
        exact_mod_cast le_of_lt
          (u6a_riemannZeta_order_pos_of_zero_ne_one
            (by
              intro h
              have hzeta : riemannZeta ((ρ : ℂ)) = 0 := ρ.property.2.2
              exact riemannZeta_one_ne_zero (by simpa [h] using hzeta))
            ρ.property.2.2)
  have hbucket_summable : Summable weightBucket := by
    exact Summable.of_finite
  let emb : Win ↪ Bucket := ⟨toBucket, hinj⟩
  have hwin_sum_eq_bucket :
      (∑ z : Win, weightWin z) =
        ∑ b ∈ Finset.univ.map emb, weightBucket b := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl (fun z _ => (hweight z).symm)
  have hsum_le_tsum :
      (∑ z : Win, weightWin z) ≤ ∑' b : Bucket, weightBucket b := by
    rw [hwin_sum_eq_bucket]
    exact Summable.sum_le_tsum (Finset.univ.map emb)
      (fun b _ => hbucket_nonneg b) hbucket_summable
  have hmass_eq :
      u6aFixedWindowZeroMass (-1) 2 X = ∑ z : Win, weightWin z := by
    unfold u6aFixedWindowZeroMass
    let Z : Finset ℂ := u6aZeroWindowFinset (-1) 2 X 2
    have huniv : (Finset.univ : Finset Win) = Z.attach := by
      ext z
      simp [Win, Z]
    change (∑ ρ ∈ Z, (riemannZeta.order ρ : ℝ)) =
      ∑ z : Win, weightWin z
    rw [show (∑ z : Win, weightWin z) =
        ∑ z ∈ (Finset.univ : Finset Win), weightWin z by rfl]
    rw [huniv]
    simpa [Win, Z, weightWin] using
      (Finset.sum_attach (s := Z)
        (f := fun z : ℂ => (riemannZeta.order z : ℝ))).symm
  have hbucket_tsum :
      (∑' b : Bucket, weightBucket b) =
        2 * riemannZeta.N T + u6aStripZeroHeightZeroMass := by
    have hN_eq : (∑' ρ : Pos, (riemannZeta.order (ρ : ℂ) : ℝ)) = riemannZeta.N T := by
      unfold riemannZeta.N riemannZeta.zeroes_sum
      simp [Pos]
    have hzero_eq :
        (∑' ρ : Zero, (riemannZeta.order (ρ : ℂ) : ℝ)) =
          u6aStripZeroHeightZeroMass := by
      simp [u6aStripZeroHeightZeroMass, riemannZeta.zeroes_sum, Zero]
    rw [Summable.tsum_sum (Summable.of_finite) (Summable.of_finite)]
    simp only [weightBucket]
    rw [Summable.tsum_sum (Summable.of_finite) (Summable.of_finite)]
    change (∑' ρ : Pos, (riemannZeta.order (ρ : ℂ) : ℝ)) +
        ((∑' ρ : Pos, (riemannZeta.order (ρ : ℂ) : ℝ)) +
          ∑' ρ : Zero, (riemannZeta.order (ρ : ℂ) : ℝ)) =
      2 * riemannZeta.N T + u6aStripZeroHeightZeroMass
    rw [hzero_eq]
    rw [hN_eq]
    ring_nf
  calc
    u6aFixedWindowZeroMass (-1) 2 X = ∑ z : Win, weightWin z := hmass_eq
    _ ≤ ∑' b : Bucket, weightBucket b := hsum_le_tsum
    _ = 2 * riemannZeta.N T + u6aStripZeroHeightZeroMass := hbucket_tsum
    _ = 2 * riemannZeta.N ((2 : ℝ) ^ (k + 1)) +
        u6aStripZeroHeightZeroMass := by rfl

theorem u6aStripZeroHeightZeroMass_nonneg :
    0 ≤ u6aStripZeroHeightZeroMass := by
  unfold u6aStripZeroHeightZeroMass riemannZeta.zeroes_sum
  exact tsum_nonneg fun ρ => by
    have horder : 0 ≤ (riemannZeta.order (ρ : ℂ) : ℝ) := by
      exact_mod_cast le_of_lt
        (u6a_riemannZeta_order_pos_of_zero_ne_one
          (by
            intro h
            exact riemannZeta_one_ne_zero (by simpa [h] using ρ.property.2.2))
          ρ.property.2.2)
    simpa using horder

/-- Crude-majorant bound for the order-weighted fixed U6a zero window. -/
theorem u6aFixedWindowZeroMass_le_crude_geometric :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X : ℝ,
      2 * X + 2 < (2 : ℝ) ^ (k + 1) →
        u6aFixedWindowZeroMass (-1) 2 X ≤ C * 3 ^ k + D := by
  obtain ⟨E, hE, hN⟩ := zetaCountingDyadic_abs_N_le_geometric
  let C : ℝ := max 1 (2 * E)
  let D : ℝ := u6aStripZeroHeightZeroMass
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (2 * E))
  refine ⟨C, D, hC, u6aStripZeroHeightZeroMass_nonneg, ?_⟩
  intro k X hT
  have hbase := u6aFixedWindowZeroMass_le_two_N_add_zeroHeightMass
    (k := k) (X := X) hT
  have hNabs :
      riemannZeta.N ((2 : ℝ) ^ (k + 1)) ≤
        |riemannZeta.N ((2 : ℝ) ^ (k + 1))| := le_abs_self _
  have hNbound := hN k
  have htwoN :
      2 * riemannZeta.N ((2 : ℝ) ^ (k + 1)) ≤ 2 * (E * 3 ^ k) := by
    exact mul_le_mul_of_nonneg_left (hNabs.trans hNbound) (by norm_num)
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hcoef : 2 * E ≤ C := le_max_right 1 (2 * E)
  have hCmul : 2 * (E * 3 ^ k) ≤ C * 3 ^ k := by
    calc
      2 * (E * 3 ^ k) = (2 * E) * 3 ^ k := by ring
      _ ≤ C * 3 ^ k := mul_le_mul_of_nonneg_right hcoef hpow_nonneg
  calc
    u6aFixedWindowZeroMass (-1) 2 X
        ≤ 2 * riemannZeta.N ((2 : ℝ) ^ (k + 1)) + D := by
          simpa [D] using hbase
    _ ≤ 2 * (E * 3 ^ k) + D := by
          simpa [add_comm] using add_le_add_right htwoN D
    _ ≤ C * 3 ^ k + D := by
          simpa [add_comm] using add_le_add_right hCmul D

/-- In the actual U6a strip `[-1, 2]`, every non-real zero in the finite
height window injects into the non-trivial zero count by absolute height; the
only extra bucket is the finite real-axis strip set. -/
theorem u6aZeroWindowFinset_card_le_nontrivial_abs_count {X δ T : ℝ}
    (hT : 2 * X + δ < T) :
    (u6aZeroWindowFinset (-1) 2 X δ).card ≤
      Nat.card {rho : NontrivialZeros // |(rho : ℂ).im| < T} +
        Nat.card u6aStripZeroHeightZeros := by
  classical
  let Win : Type := {z : ℂ // z ∈ u6aZeroWindowFinset (-1) 2 X δ}
  let Abs : Type := {rho : NontrivialZeros // |(rho : ℂ).im| < T}
  let Zero : Type := u6aStripZeroHeightZeros
  haveI : Finite Abs :=
    Set.finite_coe_iff.mpr (nontrivialZeros_abs_im_lt_finite T)
  haveI : Finite Zero := u6aStripZeroHeightZeros_finite
  let toBucket : Win → Abs ⊕ Zero := fun z =>
    have hzwin : (z : ℂ) ∈ riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
        (Set.Icc (-(2 * X + δ)) (2 * X + δ)) := by
      have hzfin : (z : ℂ) ∈ u6aZeroWindowFinset (-1) 2 X δ := z.property
      unfold u6aZeroWindowFinset at hzfin
      exact (u6aZeroWindowSet_finite (-1) 2 X δ).mem_toFinset.mp hzfin
    if him : (z : ℂ).im = 0 then
      Sum.inr
        ⟨(z : ℂ), hzwin.1, by simp [him], hzwin.2.2⟩
    else
      have hre_nontrivial : (z : ℂ).re ∈ Set.Ioo (0 : ℝ) 1 := by
        have hzeta : riemannZeta (z : ℂ) = 0 := hzwin.2.2
        have hnot_nonpos : ¬ (z : ℂ).re ≤ 0 := by
          intro hre
          exact (riemannZeta_ne_zero_of_re_nonpos_im_ne_zero hre him) hzeta
        have hnot_one_le : ¬ 1 ≤ (z : ℂ).re := by
          intro hre
          exact (riemannZeta_ne_zero_of_one_le_re hre) hzeta
        exact ⟨lt_of_not_ge hnot_nonpos, lt_of_not_ge hnot_one_le⟩
      have habs_lt : |(z : ℂ).im| < T := by
        have habs_le : |(z : ℂ).im| ≤ 2 * X + δ :=
          abs_le.mpr ⟨hzwin.2.1.1, hzwin.2.1.2⟩
        exact lt_of_le_of_lt habs_le hT
      Sum.inl
        ⟨⟨(z : ℂ), hre_nontrivial, Set.mem_univ _, hzwin.2.2⟩, habs_lt⟩
  let recover : Abs ⊕ Zero → ℂ := fun bucket =>
    match bucket with
    | Sum.inl rho => (rho.1 : ℂ)
    | Sum.inr rho => (rho : ℂ)
  have hrecover : ∀ z : Win, recover (toBucket z) = (z : ℂ) := by
    intro z
    dsimp [toBucket, recover]
    by_cases him : (z : ℂ).im = 0
    · simp [him]
    · simp [him]
  have hinj : Function.Injective toBucket := by
    intro z w hzw
    apply Subtype.ext
    calc
      (z : ℂ) = recover (toBucket z) := (hrecover z).symm
      _ = recover (toBucket w) := by rw [hzw]
      _ = (w : ℂ) := hrecover w
  have hcard : Nat.card Win ≤ Nat.card (Abs ⊕ Zero) :=
    Nat.card_le_card_of_injective toBucket hinj
  have hsum : Nat.card (Abs ⊕ Zero) = Nat.card Abs + Nat.card Zero := by
    rw [Nat.card_sum]
  have hwin : Nat.card Win = (u6aZeroWindowFinset (-1) 2 X δ).card := by
    simp [Win]
  simpa [Abs, Zero, hwin, hsum] using hcard

/-- The U6a zero-window count in the actual strip is bounded by the project
zero-counting function, with the real-axis bucket absorbed as an additive
constant. -/
theorem u6aZeroWindowFinset_card_le_countByN_with_zero_height :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ : ℝ,
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
        ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) ≤
          A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D := by
  classical
  obtain ⟨A, D, hA, hD, hcount⟩ :=
    zeroImagDyadicCumulativeCountByNWithZeroHeightSource_of_conj_and_positive_height_zero_free
  refine ⟨A, D + (Nat.card u6aStripZeroHeightZeros : ℝ), hA,
    add_nonneg hD (by positivity), ?_⟩
  intro k X δ hT
  have hwin :=
    u6aZeroWindowFinset_card_le_nontrivial_abs_count
      (X := X) (δ := δ) (T := (2 : ℝ) ^ (k + 1)) hT
  have hwinR :
      ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) ≤
        (Nat.card {rho : NontrivialZeros //
            |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) +
          (Nat.card u6aStripZeroHeightZeros : ℝ) := by
    exact_mod_cast hwin
  have hcountk := hcount k
  calc
    ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ)
        ≤ (Nat.card {rho : NontrivialZeros //
            |(rho : ℂ).im| < (2 : ℝ) ^ (k + 1)} : ℝ) +
          (Nat.card u6aStripZeroHeightZeros : ℝ) := hwinR
    _ ≤ A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D +
          (Nat.card u6aStripZeroHeightZeros : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hcountk (Nat.card u6aStripZeroHeightZeros : ℝ)
    _ = A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| +
          (D + (Nat.card u6aStripZeroHeightZeros : ℝ)) := by ring

/-- Crude-majorant form of the U6a zero-window count.  The growth is geometric
in the dyadic scale because it consumes `Backlund.zetaCounting_crude_majorant`. -/
theorem u6aZeroWindowFinset_card_le_crude_geometric :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ : ℝ,
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
        ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) ≤ C * 3 ^ k + D := by
  obtain ⟨A, D, hA, hD, hcount⟩ :=
    u6aZeroWindowFinset_card_le_countByN_with_zero_height
  obtain ⟨E, hE, hN⟩ := zetaCountingDyadic_abs_N_le_geometric
  let C : ℝ := max 1 (A * E)
  have hC : 0 < C := by
    exact lt_of_lt_of_le zero_lt_one (le_max_left 1 (A * E))
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X δ hT
  have hbase := hcount k X δ hT
  have hNbound := hN k
  have hmul :
      A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| ≤ A * (E * 3 ^ k) := by
    exact mul_le_mul_of_nonneg_left hNbound hA
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hCmul : A * E * 3 ^ k ≤ C * 3 ^ k := by
    exact mul_le_mul_of_nonneg_right (le_max_right 1 (A * E)) hpow_nonneg
  calc
    ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ)
        ≤ A * |riemannZeta.N ((2 : ℝ) ^ (k + 1))| + D := hbase
    _ ≤ A * (E * 3 ^ k) + D := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hmul D
    _ = A * E * 3 ^ k + D := by ring
    _ ≤ C * 3 ^ k + D := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right hCmul D

/-- Crude-majorant form of the finite bad-height count used in the safe-set
length estimate. -/
theorem u6aBadHeightFinset_card_le_crude_geometric :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ : ℝ,
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
        ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ) ≤ C * 3 ^ k + D := by
  obtain ⟨C, D, hC, hD, hcount⟩ := u6aZeroWindowFinset_card_le_crude_geometric
  refine ⟨2 * C, 2 * D, by positivity, by positivity, ?_⟩
  intro k X δ hT
  have hbad :=
    u6aBadHeightFinset_card_le_two_zeroWindow (-1) 2 X δ
  have hbadR :
      ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ) ≤
        2 * ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) := by
    exact_mod_cast hbad
  have hcountk := hcount k X δ hT
  have hmul :
      2 * ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) ≤
        2 * (C * 3 ^ k + D) := by
    exact mul_le_mul_of_nonneg_left hcountk (by norm_num)
  calc
    ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ)
        ≤ 2 * ((u6aZeroWindowFinset (-1) 2 X δ).card : ℝ) := hbadR
    _ ≤ 2 * (C * 3 ^ k + D) := hmul
    _ = (2 * C) * 3 ^ k + 2 * D := by ring

/-- Explicit small radius for the crude-majorant safe-height selector. -/
noncomputable def u6aCrudeDelta (C D X : ℝ) (k : ℕ) : ℝ :=
  min 1 (X / (8 * (C * 3 ^ k + D + 1)))

theorem u6aCrudeDelta_pos {C D X : ℝ} (k : ℕ)
    (hX : 0 < X) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    0 < u6aCrudeDelta C D X k := by
  unfold u6aCrudeDelta
  apply lt_min
  · norm_num
  · positivity

/-- The explicit `δ_X` choice makes the bad-height cover short enough for
the `X / 2` safe-set measure lower bound. -/
theorem u6aCrudeDelta_small {C D X : ℝ} (k : ℕ)
    (hX : 0 < X) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    2 * u6aCrudeDelta C D X k * (C * 3 ^ k + D) ≤ X / 2 := by
  let B : ℝ := C * 3 ^ k + D
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hdelta_le : u6aCrudeDelta C D X k ≤ X / (8 * (B + 1)) := by
    unfold u6aCrudeDelta
    dsimp [B]
    exact min_le_right _ _
  have hcoef : 0 ≤ 2 * B := by positivity
  have hstep :
      u6aCrudeDelta C D X k * (2 * B) ≤
        (X / (8 * (B + 1))) * (2 * B) :=
    mul_le_mul_of_nonneg_right hdelta_le hcoef
  have htarget : (X / (8 * (B + 1))) * (2 * B) ≤ X / 2 := by
    have hden_pos : 0 < 8 * (B + 1) := by positivity
    field_simp [hden_pos.ne']
    nlinarith [hX.le, hB]
  calc
    2 * u6aCrudeDelta C D X k * (C * 3 ^ k + D)
        = u6aCrudeDelta C D X k * (2 * B) := by
          dsimp [B]
          ring
    _ ≤ (X / (8 * (B + 1))) * (2 * B) := hstep
    _ ≤ X / 2 := htarget

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

/-- The open bad-height cover is exactly the complement of the safe-height set
inside `(X, 2X]`. -/
theorem u6aSafeHeightSet_contains_diff_badHeightOpenBalls
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    Set.diff (Set.Ioc X (2 * X))
        (⋃ a ∈ u6aBadHeightFinset σ₁ σ₂ X δ, Metric.ball a δ) ⊆
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
    have htball : t ∈ Metric.ball z.im δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      simpa [abs_sub_comm] using hclose
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
    have htball : t ∈ Metric.ball (-z.im) δ := by
      rw [Metric.mem_ball, Real.dist_eq]
      have hclose' : |t + z.im| < δ := by
        simpa [add_comm] using hclose
      simpa using hclose'
    exact htbad (by
      rw [Set.mem_iUnion]
      exact ⟨-z.im, by rw [Set.mem_iUnion]; exact ⟨hzbad, htball⟩⟩)

/-- Safe heights are exactly `(X, 2X]` after deleting the open `δ`-balls around
the finitely many bad heights. -/
theorem u6aSafeHeightSet_eq_diff_badHeightOpenBalls
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    u6aSafeHeightSet σ₁ σ₂ X δ =
      Set.diff (Set.Ioc X (2 * X))
        (⋃ a ∈ u6aBadHeightFinset σ₁ σ₂ X δ, Metric.ball a δ) := by
  classical
  apply Set.Subset.antisymm
  · intro t ht
    refine ⟨ht.1, ?_⟩
    intro htbad
    rcases Set.mem_iUnion.mp htbad with ⟨a, ha'⟩
    rcases Set.mem_iUnion.mp ha' with ⟨ha, htball⟩
    unfold u6aBadHeightFinset at ha
    simp only [Finset.mem_union, Finset.mem_image] at ha
    rcases ha with ha | ha
    · rcases ha with ⟨z, hzFin, hza⟩
      have hzZ : z ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
          (Set.Icc (-(2 * X + δ)) (2 * X + δ)) := by
        unfold u6aZeroWindowFinset at hzFin
        exact (u6aZeroWindowSet_finite σ₁ σ₂ X δ).mem_toFinset.mp hzFin
      have htop := ht.2.2.1 z hzZ.1 hzZ.2.2
      rw [← hza, Metric.mem_ball, Real.dist_eq] at htball
      have hclose : |z.im - t| < δ := by
        simpa [abs_sub_comm] using htball
      exact not_le_of_gt hclose htop
    · rcases ha with ⟨z, hzFin, hza⟩
      have hzZ : z ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
          (Set.Icc (-(2 * X + δ)) (2 * X + δ)) := by
        unfold u6aZeroWindowFinset at hzFin
        exact (u6aZeroWindowSet_finite σ₁ σ₂ X δ).mem_toFinset.mp hzFin
      have hbot := ht.2.2.2 z hzZ.1 hzZ.2.2
      rw [← hza, Metric.mem_ball, Real.dist_eq] at htball
      have hclose : |z.im + t| < δ := by
        simpa [sub_neg_eq_add, add_comm] using htball
      exact not_le_of_gt hclose hbot
  · exact u6aSafeHeightSet_contains_diff_badHeightOpenBalls hX hδ

/-- The safe-height set is measurable because the bad heights are finite. -/
theorem measurableSet_u6aSafeHeightSet
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    MeasurableSet (u6aSafeHeightSet σ₁ σ₂ X δ) := by
  rw [u6aSafeHeightSet_eq_diff_badHeightOpenBalls hX hδ]
  have hbad_meas :
      MeasurableSet (⋃ a ∈ u6aBadHeightFinset σ₁ σ₂ X δ, Metric.ball a δ) :=
    Finset.measurableSet_biUnion (u6aBadHeightFinset σ₁ σ₂ X δ)
      (fun _ _ => measurableSet_ball)
  exact measurableSet_Ioc.diff hbad_meas

/-- The constant side of the averaged selector is interval-integrable once the
safe set has been identified as a finite open-ball deletion. -/
theorem intervalIntegrable_u6aAveragedSelectionBound_indicator
    {σ₁ σ₂ X δ M : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        fun _ : ℝ => u6aAveragedSelectionBound X δ M) volume X (2 * X) := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let B : ℝ := u6aAveragedSelectionBound X δ M
  have hE_meas : MeasurableSet E := by
    simpa [E] using measurableSet_u6aSafeHeightSet (σ₁ := σ₁) (σ₂ := σ₂)
      (X := X) (δ := δ) hX hδ
  have hE_subset : E ⊆ Set.Ioc X (2 * X) := by
    intro t ht
    exact ht.1
  have hIoc_ne_top : (volume : Measure ℝ) (Set.Ioc X (2 * X)) ≠ ⊤ := by
    simp [Real.volume_Ioc]
  have hE_ne_top : (volume : Measure ℝ) E ≠ ⊤ :=
    ne_top_of_le_ne_top hIoc_ne_top (measure_mono hE_subset)
  have hConst : IntegrableOn (fun _ : ℝ => B) E (volume : Measure ℝ) :=
    integrableOn_const hE_ne_top
  simpa [E, B] using hConst.integrable_indicator hE_meas |>.intervalIntegrable

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

/-- Crude-majorant safe-set measure lower bound in the actual U6a strip.  The
smallness condition is now expressed through the geometric count source rather
than the concrete finite bad-height set. -/
theorem u6aSafeHeightSet_measure_ge_of_crude_geometric :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ : ℝ,
      0 < X → 0 < δ →
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
      2 * δ * (C * 3 ^ k + D) ≤ X / 2 →
        ENNReal.ofReal (X / 2) ≤
          (volume.restrict (Set.Ioc X (2 * X)))
            (u6aSafeHeightSet (-1) 2 X δ) := by
  obtain ⟨C, D, hC, hD, hcount⟩ := u6aBadHeightFinset_card_le_crude_geometric
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X δ hX hδ hT hsmall
  have hbad := hcount k X δ hT
  have hcoef : 0 ≤ 2 * δ := by positivity
  have hsmall_bad :
      2 * δ * ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ) ≤ X / 2 := by
    calc
      2 * δ * ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ)
          ≤ 2 * δ * (C * 3 ^ k + D) := by
            exact mul_le_mul_of_nonneg_left hbad hcoef
      _ ≤ X / 2 := hsmall
  exact u6aSafeHeightSet_measure_ge_of_badHeightFinset hX hδ hsmall_bad

/-- Safe-set measure lower bound with the explicit crude-majorant
`δ_X` choice. -/
theorem u6aSafeHeightSet_measure_ge_of_crude_delta :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X : ℝ,
      0 < X →
      2 * X + u6aCrudeDelta C D X k < (2 : ℝ) ^ (k + 1) →
        ENNReal.ofReal (X / 2) ≤
          (volume.restrict (Set.Ioc X (2 * X)))
            (u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k)) := by
  obtain ⟨C, D, hC, hD, hmeasure⟩ := u6aSafeHeightSet_measure_ge_of_crude_geometric
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X hX hT
  exact hmeasure k X (u6aCrudeDelta C D X k) hX
    (u6aCrudeDelta_pos k hX hC.le hD) hT
    (u6aCrudeDelta_small k hX hC.le hD)

/-- Nonzero safe-set measure from the crude-majorant geometric count source. -/
theorem u6aSafeHeightSet_restrict_measure_ne_zero_of_crude_geometric :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ : ℝ,
      0 < X → 0 < δ →
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
      2 * δ * (C * 3 ^ k + D) ≤ X / 2 →
        (volume.restrict (Set.Ioc X (2 * X)))
          (u6aSafeHeightSet (-1) 2 X δ) ≠ 0 := by
  obtain ⟨C, D, hC, hD, hmeasure⟩ := u6aSafeHeightSet_measure_ge_of_crude_geometric
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X δ hX hδ hT hsmall
  have hmeasurek := hmeasure k X δ hX hδ hT hsmall
  have hpos : 0 < ENNReal.ofReal (X / 2) := ENNReal.ofReal_pos.2 (by linarith)
  exact ne_of_gt (lt_of_lt_of_le hpos hmeasurek)

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

private lemma u6aReciprocalZeroSet_finite (σ₁ σ₂ t : ℝ) :
    (riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))).Finite := by
  rw [riemannZeta.zeroes_rect_eq]
  let S : Set ℂ :=
    (Complex.re ⁻¹' Set.Icc (min σ₁ σ₂) (max σ₁ σ₂)) ∩
      (Complex.im ⁻¹' Set.Icc (t - 2) (t + 2))
  have hS : IsCompact S := by
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  refine (riemannZeta.zeroes_on_Compact_finite' (S := S) hS).subset ?_
  intro z hz
  rcases hz with ⟨⟨hre, him⟩, hzeta⟩
  exact ⟨⟨by simpa [Set.uIcc] using hre, him⟩, hzeta⟩

private lemma u6aZeroWindow_order_nonneg {σ₁ σ₂ X δ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X δ) :
    0 ≤ (riemannZeta.order ρ : ℝ) := by
  have hρmem : ρ ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
      (Set.Icc (-(2 * X + δ)) (2 * X + δ)) := by
    unfold u6aZeroWindowFinset at hρ
    exact (u6aZeroWindowSet_finite σ₁ σ₂ X δ).mem_toFinset.mp hρ
  have hzero : riemannZeta ρ = 0 := hρmem.2.2
  have hne_one : ρ ≠ 1 := by
    intro hρone
    exact riemannZeta_one_ne_zero (by simpa [hρone] using hzero)
  exact_mod_cast le_of_lt (u6a_riemannZeta_order_pos_of_zero_ne_one hne_one hzero)

/-- For `t ∈ (X, 2X]`, the moving width-two reciprocal zero sum is bounded by
the fixed zero window used in the dyadic averaging argument. -/
theorem u6aReciprocalZeroSum_le_fixedWindowReciprocalSum
    {σ₁ σ₂ X δ t : ℝ} (hX : 0 < X) (ht : t ∈ u6aSafeHeightSet σ₁ σ₂ X δ) :
    u6aReciprocalZeroSum σ₁ σ₂ t ≤ u6aFixedWindowReciprocalSum σ₁ σ₂ X t := by
  classical
  let Zmove := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))
  let hmove : Zmove.Finite := u6aReciprocalZeroSet_finite σ₁ σ₂ t
  let Zfixed := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
    (Set.Icc (-(2 * X + 2)) (2 * X + 2))
  have hsubset : hmove.toFinset ⊆ u6aZeroWindowFinset σ₁ σ₂ X 2 := by
    intro ρ hρ
    have hρmove : ρ ∈ Zmove := hmove.mem_toFinset.mp hρ
    have hρfixed : ρ ∈ Zfixed := by
      refine ⟨hρmove.1, ?_, hρmove.2.2⟩
      constructor
      · have ht_low : X < t := ht.1.1
        have him_low : t - 2 ≤ ρ.im := hρmove.2.1.1
        linarith
      · have ht_high : t ≤ 2 * X := ht.1.2
        have him_high : ρ.im ≤ t + 2 := hρmove.2.1.2
        linarith
    unfold u6aZeroWindowFinset
    exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mpr hρfixed
  unfold u6aReciprocalZeroSum u6aFixedWindowReciprocalSum
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
    (fun ρ => (1 / |t - ρ.im| : ℝ)) hmove]
  refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
  intro ρ hρfixed hρnot_move
  have hρfixed_mem : ρ ∈ Zfixed := by
    unfold u6aZeroWindowFinset at hρfixed
    exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mp hρfixed
  have hzero : riemannZeta ρ = 0 := hρfixed_mem.2.2
  have hne_one : ρ ≠ 1 := by
    intro hρone
    exact riemannZeta_one_ne_zero (by simpa [hρone] using hzero)
  have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) := by
    exact_mod_cast le_of_lt (u6a_riemannZeta_order_pos_of_zero_ne_one hne_one hzero)
  exact mul_nonneg (by positivity) horder_nonneg

/-- Localized fixed-window comparison: every term of `S₂(t)` appears in the
fixed dyadic zero window with its width-two support indicator turned on. -/
theorem u6aReciprocalZeroSum_le_fixedWindowLocalizedReciprocalSum
    {σ₁ σ₂ X δ t : ℝ} (hX : 0 < X) (ht : t ∈ u6aSafeHeightSet σ₁ σ₂ X δ) :
    u6aReciprocalZeroSum σ₁ σ₂ t ≤
      u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X t := by
  classical
  let Zmove := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))
  let hmove : Zmove.Finite := u6aReciprocalZeroSet_finite σ₁ σ₂ t
  let Zfixed := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
    (Set.Icc (-(2 * X + 2)) (2 * X + 2))
  let f : ℂ → ℝ := fun ρ =>
    (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
      (fun u : ℝ => 1 / |u - ρ.im|) t *
      (riemannZeta.order ρ : ℝ)
  have hsubset : hmove.toFinset ⊆ u6aZeroWindowFinset σ₁ σ₂ X 2 := by
    intro ρ hρ
    have hρmove : ρ ∈ Zmove := hmove.mem_toFinset.mp hρ
    have hρfixed : ρ ∈ Zfixed := by
      refine ⟨hρmove.1, ?_, hρmove.2.2⟩
      constructor
      · have ht_low : X < t := ht.1.1
        have him_low : t - 2 ≤ ρ.im := hρmove.2.1.1
        linarith
      · have ht_high : t ≤ 2 * X := ht.1.2
        have him_high : ρ.im ≤ t + 2 := hρmove.2.1.2
        linarith
    unfold u6aZeroWindowFinset
    exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mpr hρfixed
  unfold u6aReciprocalZeroSum
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
    (fun ρ => (1 / |t - ρ.im| : ℝ)) hmove]
  calc
    ∑ ρ ∈ hmove.toFinset, (1 / |t - ρ.im| : ℝ) * (riemannZeta.order ρ : ℝ)
        = ∑ ρ ∈ hmove.toFinset, f ρ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hρmove : ρ ∈ Zmove := hmove.mem_toFinset.mp hρ
          have htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2) := by
            constructor
            · have him_high : ρ.im ≤ t + 2 := hρmove.2.1.2
              linarith
            · have him_low : t - 2 ≤ ρ.im := hρmove.2.1.1
              linarith
          simp [f, htlocal]
    _ ≤ ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2, f ρ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro ρ hρfixed hρnot_move
          by_cases htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2)
          · have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) :=
              u6aZeroWindow_order_nonneg hρfixed
            have hkernel_nonneg : 0 ≤ |t - ρ.im|⁻¹ :=
              inv_nonneg.mpr (abs_nonneg _)
            simpa [f, htlocal] using mul_nonneg hkernel_nonneg horder_nonneg
          · simp [f, htlocal]
    _ = u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X t := by
          rfl

/-- On a safe dyadic height, the moving width-two reciprocal sum is exactly the
fixed finite-window sum with each kernel restricted to its own width-two
support. -/
theorem u6aReciprocalZeroSum_eq_fixedWindowLocalizedReciprocalSum
    {σ₁ σ₂ X δ t : ℝ} (hX : 0 < X) (ht : t ∈ u6aSafeHeightSet σ₁ σ₂ X δ) :
    u6aReciprocalZeroSum σ₁ σ₂ t =
      u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X t := by
  classical
  let Zmove := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))
  let hmove : Zmove.Finite := u6aReciprocalZeroSet_finite σ₁ σ₂ t
  let Zfixed := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
    (Set.Icc (-(2 * X + 2)) (2 * X + 2))
  let f : ℂ → ℝ := fun ρ =>
    (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
      (fun u : ℝ => 1 / |u - ρ.im|) t *
      (riemannZeta.order ρ : ℝ)
  have hsubset : hmove.toFinset ⊆ u6aZeroWindowFinset σ₁ σ₂ X 2 := by
    intro ρ hρ
    have hρmove : ρ ∈ Zmove := hmove.mem_toFinset.mp hρ
    have hρfixed : ρ ∈ Zfixed := by
      refine ⟨hρmove.1, ?_, hρmove.2.2⟩
      constructor
      · have ht_low : X < t := ht.1.1
        have him_low : t - 2 ≤ ρ.im := hρmove.2.1.1
        linarith
      · have ht_high : t ≤ 2 * X := ht.1.2
        have him_high : ρ.im ≤ t + 2 := hρmove.2.1.2
        linarith
    unfold u6aZeroWindowFinset
    exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mpr hρfixed
  have hzero_out :
      ∀ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2, ρ ∉ hmove.toFinset → f ρ = 0 := by
    intro ρ hρfixed hρnot_move
    by_cases htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2)
    · have hρfixed_mem : ρ ∈ Zfixed := by
        unfold u6aZeroWindowFinset at hρfixed
        exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mp hρfixed
      have hρmove : ρ ∈ Zmove := by
        refine ⟨hρfixed_mem.1, ?_, hρfixed_mem.2.2⟩
        constructor
        · linarith [htlocal.2]
        · linarith [htlocal.1]
      exact False.elim (hρnot_move (hmove.mem_toFinset.mpr hρmove))
    · simp [f, htlocal]
  unfold u6aReciprocalZeroSum
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
    (fun ρ => (1 / |t - ρ.im| : ℝ)) hmove]
  calc
    ∑ ρ ∈ hmove.toFinset, (1 / |t - ρ.im| : ℝ) * (riemannZeta.order ρ : ℝ)
        = ∑ ρ ∈ hmove.toFinset, f ρ := by
          refine Finset.sum_congr rfl ?_
          intro ρ hρ
          have hρmove : ρ ∈ Zmove := hmove.mem_toFinset.mp hρ
          have htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2) := by
            constructor
            · have him_high : ρ.im ≤ t + 2 := hρmove.2.1.2
              linarith
            · have him_low : t - 2 ≤ ρ.im := hρmove.2.1.1
              linarith
          simp [f, htlocal]
    _ = ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2, f ρ := by
          exact Finset.sum_subset hsubset hzero_out
    _ = u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X t := by
          rfl

theorem measurable_u6aFixedWindowLocalizedReciprocalSum (σ₁ σ₂ X : ℝ) :
    Measurable (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X) := by
  classical
  unfold u6aFixedWindowLocalizedReciprocalSum
  refine Finset.measurable_sum _ fun ρ _ => ?_
  have hkernel : Measurable fun u : ℝ => (1 / |u - ρ.im| : ℝ) := by
    fun_prop
  exact ((hkernel.indicator measurableSet_Icc).mul measurable_const)

private lemma norm_u6aFixedWindowLocalizedReciprocalSum_indicator_le
    {σ₁ σ₂ X δ t : ℝ} (hδ : 0 < δ) :
    ‖(u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X) t‖ ≤
      ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2,
        (1 / δ) * (riemannZeta.order ρ : ℝ) := by
  classical
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let Z := u6aZeroWindowFinset σ₁ σ₂ X 2
  let term : ℂ → ℝ := fun ρ =>
    (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
      (fun u : ℝ => 1 / |u - ρ.im|) t *
      (riemannZeta.order ρ : ℝ)
  by_cases ht : t ∈ E
  · have hterm :
        ∀ ρ ∈ Z, |term ρ| ≤ (1 / δ) * (riemannZeta.order ρ : ℝ) := by
      intro ρ hρ
      by_cases htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2)
      · have hρmem : ρ ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
            (Set.Icc (-(2 * X + 2)) (2 * X + 2)) := by
          unfold Z u6aZeroWindowFinset at hρ
          exact (u6aZeroWindowSet_finite σ₁ σ₂ X 2).mem_toFinset.mp hρ
        have hgap : δ ≤ |t - ρ.im| := by
          have h := ht.2.2.1 ρ hρmem.1 hρmem.2.2
          simpa [E, abs_sub_comm] using h
        have hinv : 1 / |t - ρ.im| ≤ 1 / δ :=
          one_div_le_one_div_of_le hδ hgap
        have horder : 0 ≤ (riemannZeta.order ρ : ℝ) :=
          u6aZeroWindow_order_nonneg (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
            (δ := 2) (ρ := ρ) hρ
        have hnonneg : 0 ≤ term ρ := by
          have hkernel_nonneg : 0 ≤ (1 / |t - ρ.im| : ℝ) := by positivity
          simpa [term, htlocal] using mul_nonneg hkernel_nonneg horder
        have hmul := mul_le_mul_of_nonneg_right hinv horder
        simpa [term, htlocal, abs_of_nonneg hnonneg, abs_of_nonneg horder] using hmul
      · have horder : 0 ≤ (riemannZeta.order ρ : ℝ) :=
          u6aZeroWindow_order_nonneg (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
            (δ := 2) (ρ := ρ) hρ
        have hrhs : 0 ≤ (1 / δ) * (riemannZeta.order ρ : ℝ) := by positivity
        simpa [term, htlocal] using hrhs
    calc
      ‖(u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X) t‖
          = |∑ ρ ∈ Z, term ρ| := by
            simp [E, Z, term, ht, u6aFixedWindowLocalizedReciprocalSum, Real.norm_eq_abs]
      _ ≤ ∑ ρ ∈ Z, |term ρ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ ρ ∈ Z, (1 / δ) * (riemannZeta.order ρ : ℝ) :=
            Finset.sum_le_sum hterm
  · have hsum_nonneg :
        0 ≤ ∑ ρ ∈ Z, (1 / δ) * (riemannZeta.order ρ : ℝ) := by
      refine Finset.sum_nonneg fun ρ hρ => ?_
      have horder : 0 ≤ (riemannZeta.order ρ : ℝ) :=
        u6aZeroWindow_order_nonneg (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
          (δ := 2) (ρ := ρ) hρ
      positivity
    simpa [E, ht] using hsum_nonneg

theorem intervalIntegrable_u6aFixedWindowLocalizedReciprocalSum_indicator
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X)) volume X (2 * X) := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  have hE_meas : MeasurableSet E := by
    simpa [E] using measurableSet_u6aSafeHeightSet (σ₁ := σ₁) (σ₂ := σ₂)
      (X := X) (δ := δ) hX hδ
  have hmeas :
      Measurable
        (E.indicator (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X)) := by
    exact (measurable_u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X).indicator hE_meas
  let B : ℝ := ∑ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2,
    (1 / δ) * (riemannZeta.order ρ : ℝ)
  have hB : IntervalIntegrable (fun _ : ℝ => B) volume X (2 * X) :=
    continuous_const.intervalIntegrable X (2 * X)
  exact hB.mono_fun' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t =>
      by simpa [B, E] using
        (norm_u6aFixedWindowLocalizedReciprocalSum_indicator_le
          (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (t := t) hδ))

theorem intervalIntegrable_u6aReciprocalZeroSum_indicator
    {σ₁ σ₂ X δ : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (u6aReciprocalZeroSum σ₁ σ₂)) volume X (2 * X) := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let g : ℝ → ℝ := E.indicator (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X)
  let f : ℝ → ℝ := E.indicator (u6aReciprocalZeroSum σ₁ σ₂)
  have hg : IntervalIntegrable g volume X (2 * X) := by
    simpa [g, E] using
      intervalIntegrable_u6aFixedWindowLocalizedReciprocalSum_indicator
        (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) hX hδ
  have hfg : g =ᵐ[volume.restrict (Set.uIoc X (2 * X))] f := by
    filter_upwards with t
    by_cases ht : t ∈ E
    · have heq :=
        u6aReciprocalZeroSum_eq_fixedWindowLocalizedReciprocalSum
          (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (t := t) hX (by simpa [E] using ht)
      simp [f, g, ht, heq]
    · simp [f, g, ht]
  exact hg.congr_ae hfg

private lemma norm_safe_localizedReciprocalKernel_le
    {σ₁ σ₂ X δ : ℝ} {ρ : ℂ} (hδ : 0 < δ)
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2) :
    ∀ t : ℝ,
      ‖(u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun u : ℝ =>
            (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
              (fun v : ℝ => 1 / |v - ρ.im|) u) t‖ ≤
        1 / δ := by
  intro t
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  by_cases htE : t ∈ E
  · by_cases htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2)
    · have hρmem : ρ ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
          (Set.Icc (-(2 * X + 2)) (2 * X + 2)) := by
        simpa [u6aZeroWindowFinset] using hρ
      have hgap : δ ≤ |t - ρ.im| := by
        have h := htE.2.2.1 ρ hρmem.1 hρmem.2.2
        simpa [E, abs_sub_comm] using h
      have hinv : 1 / |t - ρ.im| ≤ 1 / δ :=
        one_div_le_one_div_of_le hδ hgap
      have hnonneg : 0 ≤ (1 / |t - ρ.im| : ℝ) := by positivity
      simpa [E, htE, htlocal, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hinv
    · have hδ_nonneg : 0 ≤ 1 / δ := by positivity
      simpa [E, htE, htlocal, Real.norm_eq_abs] using hδ_nonneg
  · have hδ_nonneg : 0 ≤ 1 / δ := by positivity
    simpa [E, htE, Real.norm_eq_abs] using hδ_nonneg

private lemma intervalIntegrable_safe_localizedReciprocalKernel
    {σ₁ σ₂ X δ : ℝ} {ρ : ℂ}
    (hX : 0 < X) (hδ : 0 < δ)
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2) :
    IntervalIntegrable
      ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (fun u : ℝ =>
          (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
            (fun v : ℝ => 1 / |v - ρ.im|) u)) volume X (2 * X) := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  have hE_meas : MeasurableSet E := by
    simpa [E] using measurableSet_u6aSafeHeightSet (σ₁ := σ₁) (σ₂ := σ₂)
      (X := X) (δ := δ) hX hδ
  have hmeas :
      Measurable
        (E.indicator
          (fun u : ℝ =>
            (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
              (fun v : ℝ => 1 / |v - ρ.im|) u)) := by
    have hkernel : Measurable fun v : ℝ => (1 / |v - ρ.im| : ℝ) := by
      fun_prop
    exact ((hkernel.indicator measurableSet_Icc).indicator hE_meas)
  have hB : IntervalIntegrable (fun _ : ℝ => 1 / δ) volume X (2 * X) :=
    continuous_const.intervalIntegrable X (2 * X)
  exact hB.mono_fun' hmeas.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t =>
      norm_safe_localizedReciprocalKernel_le (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
        (δ := δ) (ρ := ρ) hδ hρ t)

private lemma safe_localizedReciprocalKernel_le_puncturedKernel
    {σ₁ σ₂ X δ : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2) :
    ∀ t : ℝ,
      (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun u : ℝ =>
            (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
              (fun v : ℝ => 1 / |v - ρ.im|) u) t ≤
        (Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
          Set.Icc (ρ.im + δ) (ρ.im + 2)).indicator
            (fun u : ℝ => 1 / |u - ρ.im|) t := by
  intro t
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  by_cases htE : t ∈ E
  · by_cases htlocal : t ∈ Set.Icc (ρ.im - 2) (ρ.im + 2)
    · have hρmem : ρ ∈ riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂)
          (Set.Icc (-(2 * X + 2)) (2 * X + 2)) := by
        simpa [u6aZeroWindowFinset] using hρ
      have hgap : δ ≤ |t - ρ.im| := by
        have h := htE.2.2.1 ρ hρmem.1 hρmem.2.2
        simpa [E, abs_sub_comm] using h
      have hpunct :
          t ∈ Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
            Set.Icc (ρ.im + δ) (ρ.im + 2) := by
        by_cases hle : t ≤ ρ.im
        · have habs : |t - ρ.im| = ρ.im - t := by
            have hsub_nonpos : t - ρ.im ≤ 0 := by linarith
            rw [abs_of_nonpos hsub_nonpos]
            ring
          have ht_upper : t ≤ ρ.im - δ := by
            rw [habs] at hgap
            linarith
          exact Or.inl ⟨htlocal.1, ht_upper⟩
        · have hge : ρ.im ≤ t := le_of_not_ge hle
          have habs : |t - ρ.im| = t - ρ.im := by
            rw [abs_of_nonneg]
            linarith
          have ht_lower : ρ.im + δ ≤ t := by
            rw [habs] at hgap
            linarith
          exact Or.inr ⟨ht_lower, htlocal.2⟩
      simp [E, htE, htlocal, hpunct]
    · have hpunct_nonneg :
          0 ≤ (Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
            Set.Icc (ρ.im + δ) (ρ.im + 2)).indicator
              (fun u : ℝ => 1 / |u - ρ.im|) t := by
        by_cases hp : t ∈ Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
            Set.Icc (ρ.im + δ) (ρ.im + 2)
        · simp [hp]
        · simp [hp]
      simpa [E, htE, htlocal] using hpunct_nonneg
  · have hpunct_nonneg :
        0 ≤ (Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
          Set.Icc (ρ.im + δ) (ρ.im + 2)).indicator
            (fun u : ℝ => 1 / |u - ρ.im|) t := by
      by_cases hp : t ∈ Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
          Set.Icc (ρ.im + δ) (ρ.im + 2)
      · simp [hp]
      · simp [hp]
    simpa [E, htE] using hpunct_nonneg

private lemma integral_safe_localizedReciprocalKernel_le
    {σ₁ σ₂ X δ : ℝ} {ρ : ℂ}
    (hX : 0 < X) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2) :
    (∫ t in X..(2 * X),
      (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
        (fun u : ℝ =>
          (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
            (fun v : ℝ => 1 / |v - ρ.im|) u) t ∂volume) ≤
      2 * Real.log (2 / δ) := by
  let base : ℝ → ℝ :=
    (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
      (fun u : ℝ =>
        (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
          (fun v : ℝ => 1 / |v - ρ.im|) u)
  let punctured : ℝ → ℝ :=
    (Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
      Set.Icc (ρ.im + δ) (ρ.im + 2)).indicator
        (fun u : ℝ => 1 / |u - ρ.im|)
  have hXX : X ≤ 2 * X := by nlinarith [hX]
  have hbase_int_interval :
      IntervalIntegrable base volume X (2 * X) := by
    simpa [base] using
      intervalIntegrable_safe_localizedReciprocalKernel (σ₁ := σ₁) (σ₂ := σ₂)
        (X := X) (δ := δ) (ρ := ρ) hX hδ hρ
  have hbase_int_global :
      Integrable ((Set.Ioc X (2 * X)).indicator base) volume := by
    exact hbase_int_interval.1.integrable_indicator measurableSet_Ioc
  have hpunct_int_global : Integrable punctured volume := by
    simpa [punctured] using
      integrable_puncturedReciprocalKernel (δ := δ) (γ := ρ.im) hδ hδ2
  have hmono :
      (Set.Ioc X (2 * X)).indicator base ≤ punctured := by
    intro t
    by_cases htI : t ∈ Set.Ioc X (2 * X)
    · have hbp := safe_localizedReciprocalKernel_le_puncturedKernel
        (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (ρ := ρ) hρ t
      simpa [base, punctured, htI] using hbp
    · have hnonneg : 0 ≤ punctured t := by
        by_cases hp : t ∈ Set.Icc (ρ.im - 2) (ρ.im - δ) ∪
            Set.Icc (ρ.im + δ) (ρ.im + 2)
        · simp [punctured, hp]
        · simp [punctured, hp]
      simpa [htI] using hnonneg
  have hglobal :
      (∫ t, (Set.Ioc X (2 * X)).indicator base t ∂volume) ≤
        ∫ t, punctured t ∂volume :=
    MeasureTheory.integral_mono hbase_int_global hpunct_int_global hmono
  have hinterval_global :
      (∫ t in X..(2 * X), base t ∂volume) =
        ∫ t, (Set.Ioc X (2 * X)).indicator base t ∂volume := by
    rw [intervalIntegral.integral_of_le hXX]
    rw [MeasureTheory.integral_indicator measurableSet_Ioc]
  have hpunct_eq :
      (∫ t, punctured t ∂volume) =
        (∫ u in (ρ.im - 2)..(ρ.im - δ), (1 / |u - ρ.im| : ℝ) ∂volume) +
          ∫ u in (ρ.im + δ)..(ρ.im + 2), (1 / |u - ρ.im| : ℝ) ∂volume := by
    simpa [punctured] using
      integral_puncturedReciprocalKernel_eq (δ := δ) (γ := ρ.im) hδ hδ2
  calc
    (∫ t in X..(2 * X), base t ∂volume)
        = ∫ t, (Set.Ioc X (2 * X)).indicator base t ∂volume := hinterval_global
    _ ≤ ∫ t, punctured t ∂volume := hglobal
    _ = (∫ u in (ρ.im - 2)..(ρ.im - δ), (1 / |u - ρ.im| : ℝ) ∂volume) +
          ∫ u in (ρ.im + δ)..(ρ.im + 2), (1 / |u - ρ.im| : ℝ) ∂volume := hpunct_eq
    _ ≤ 2 * Real.log (2 / δ) :=
          reciprocalKernelTwoSidedIntegral_le (γ := ρ.im) hδ hδ2

private lemma integral_safe_localizedReciprocalKernel_mul_order_le
    {σ₁ σ₂ X δ : ℝ} {ρ : ℂ}
    (hX : 0 < X) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hρ : ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2) :
    IntervalIntegrable
        ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun u : ℝ =>
            (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
              (fun v : ℝ => 1 / |v - ρ.im|) u *
            (riemannZeta.order ρ : ℝ))) volume X (2 * X) ∧
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
            (fun u : ℝ =>
              (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
                (fun v : ℝ => 1 / |v - ρ.im|) u *
              (riemannZeta.order ρ : ℝ)) t ∂volume) ≤
        (2 * Real.log (2 / δ)) * (riemannZeta.order ρ : ℝ) := by
  let scalar : ℝ → ℝ :=
    (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
      (fun u : ℝ =>
        (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
          (fun v : ℝ => 1 / |v - ρ.im|) u)
  let target : ℝ → ℝ :=
    (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
      (fun u : ℝ =>
        (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
          (fun v : ℝ => 1 / |v - ρ.im|) u *
        (riemannZeta.order ρ : ℝ))
  have htarget_eq :
      target = fun t : ℝ => scalar t * (riemannZeta.order ρ : ℝ) := by
    funext t
    by_cases ht : t ∈ u6aSafeHeightSet σ₁ σ₂ X δ
    · simp [target, scalar, ht]
    · simp [target, scalar, ht]
  have hscalar_int :
      IntervalIntegrable scalar volume X (2 * X) := by
    simpa [scalar] using
      intervalIntegrable_safe_localizedReciprocalKernel (σ₁ := σ₁) (σ₂ := σ₂)
        (X := X) (δ := δ) (ρ := ρ) hX hδ hρ
  have hscalar_bound :
      (∫ t in X..(2 * X), scalar t ∂volume) ≤ 2 * Real.log (2 / δ) := by
    simpa [scalar] using
      integral_safe_localizedReciprocalKernel_le (σ₁ := σ₁) (σ₂ := σ₂)
        (X := X) (δ := δ) (ρ := ρ) hX hδ hδ2 hρ
  have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) :=
    u6aZeroWindow_order_nonneg (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
      (δ := 2) (ρ := ρ) hρ
  constructor
  · change IntervalIntegrable target volume X (2 * X)
    rw [htarget_eq]
    exact hscalar_int.mul_const (riemannZeta.order ρ : ℝ)
  · change (∫ t in X..(2 * X), target t ∂volume) ≤
        (2 * Real.log (2 / δ)) * (riemannZeta.order ρ : ℝ)
    rw [htarget_eq, intervalIntegral.integral_mul_const]
    exact mul_le_mul_of_nonneg_right hscalar_bound horder_nonneg

/-- Fixed-window summation step for the averaged route: if each localized
reciprocal kernel has the stated integral bound, the order-weighted sum has
the corresponding fixed-window mass bound. -/
theorem integral_u6aReciprocalZeroSum_indicator_le_of_fixedWindowTermBounds
    {σ₁ σ₂ X δ B : ℝ}
    (hX : 0 < X)
    (hTerm : ∀ ρ ∈ u6aZeroWindowFinset σ₁ σ₂ X 2,
      IntervalIntegrable
          ((u6aSafeHeightSet σ₁ σ₂ X δ).indicator
            (fun u : ℝ =>
              (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
                (fun v : ℝ => 1 / |v - ρ.im|) u *
              (riemannZeta.order ρ : ℝ))) volume X (2 * X) ∧
        (∫ t in X..(2 * X),
            (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
              (fun u : ℝ =>
                (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
                  (fun v : ℝ => 1 / |v - ρ.im|) u *
                (riemannZeta.order ρ : ℝ)) t ∂volume) ≤
          B * (riemannZeta.order ρ : ℝ)) :
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
      B * u6aFixedWindowZeroMass σ₁ σ₂ X := by
  classical
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let Z : Finset ℂ := u6aZeroWindowFinset σ₁ σ₂ X 2
  let term : ℂ → ℝ → ℝ := fun ρ u =>
    (Set.Icc (ρ.im - 2) (ρ.im + 2)).indicator
      (fun v : ℝ => 1 / |v - ρ.im|) u *
    (riemannZeta.order ρ : ℝ)
  have hleft_eq :
      (∫ t in X..(2 * X),
          E.indicator (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) =
        ∫ t in X..(2 * X),
          E.indicator (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X) t ∂volume := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    by_cases htE : t ∈ E
    · have heq :=
        u6aReciprocalZeroSum_eq_fixedWindowLocalizedReciprocalSum
          (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (t := t) hX
          (by simpa [E] using htE)
      simp [E, htE, heq]
    · simp [E, htE]
  have hfixed_eq_sum :
      (∫ t in X..(2 * X),
          E.indicator (u6aFixedWindowLocalizedReciprocalSum σ₁ σ₂ X) t ∂volume) =
        ∫ t in X..(2 * X), ∑ ρ ∈ Z, E.indicator (term ρ) t ∂volume := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards with t ht
    by_cases htE : t ∈ E
    · simp [E, Z, term, htE, u6aFixedWindowLocalizedReciprocalSum]
    · simp [E, Z, term, htE]
  have hterm_int :
      ∀ ρ ∈ Z, IntervalIntegrable (fun t : ℝ => E.indicator (term ρ) t)
        volume X (2 * X) := by
    intro ρ hρ
    simpa [E, term, Z] using (hTerm ρ hρ).1
  calc
    (∫ t in X..(2 * X),
        E.indicator (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume)
        = ∫ t in X..(2 * X),
            ∑ ρ ∈ Z, E.indicator (term ρ) t ∂volume := by
          rw [hleft_eq, hfixed_eq_sum]
    _ = ∑ ρ ∈ Z, ∫ t in X..(2 * X), E.indicator (term ρ) t ∂volume := by
          rw [intervalIntegral.integral_finsetSum hterm_int]
    _ ≤ ∑ ρ ∈ Z, B * (riemannZeta.order ρ : ℝ) := by
          exact Finset.sum_le_sum fun ρ hρ => by
            simpa [E, term, Z] using (hTerm ρ hρ).2
    _ = B * u6aFixedWindowZeroMass σ₁ σ₂ X := by
          rw [u6aFixedWindowZeroMass, Finset.mul_sum]

/-- Integrating the fixed-window reciprocal sum over the safe set gives the
panel bound `2 log(2 / δ)` times the order-weighted fixed-window mass. -/
theorem integral_u6aReciprocalZeroSum_indicator_le_fixedWindowZeroMass
    {σ₁ σ₂ X δ : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hδ2 : δ ≤ 2) :
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
      (2 * Real.log (2 / δ)) * u6aFixedWindowZeroMass σ₁ σ₂ X :=
  integral_u6aReciprocalZeroSum_indicator_le_of_fixedWindowTermBounds hX
    (fun ρ hρ =>
      integral_safe_localizedReciprocalKernel_mul_order_le
        (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (ρ := ρ)
        hX hδ hδ2 hρ)

private lemma integral_u6aAveragedSelectionBound_indicator_eq_measureReal
    {σ₁ σ₂ X δ M : ℝ} (hX : 0 < X) (hδ : 0 < δ) :
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume) =
      (volume.restrict (Set.Ioc X (2 * X))).real
          (u6aSafeHeightSet σ₁ σ₂ X δ) *
        u6aAveragedSelectionBound X δ M := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let B : ℝ := u6aAveragedSelectionBound X δ M
  have hXX : X ≤ 2 * X := by nlinarith [hX]
  have hE_meas : MeasurableSet E := by
    simpa [E] using measurableSet_u6aSafeHeightSet (σ₁ := σ₁) (σ₂ := σ₂)
      (X := X) (δ := δ) hX hδ
  have hE_subset : E ⊆ Set.Ioc X (2 * X) := by
    intro t ht
    exact ht.1
  rw [intervalIntegral.integral_of_le hXX]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  have hindicator :
      (Set.Ioc X (2 * X)).indicator (E.indicator (fun _ : ℝ => B)) =
        E.indicator (fun _ : ℝ => B) := by
    funext t
    by_cases htE : t ∈ E
    · have htI := hE_subset htE
      simp [htE, htI]
    · simp [htE]
  rw [hindicator]
  rw [MeasureTheory.integral_indicator hE_meas]
  rw [MeasureTheory.setIntegral_const]
  rw [MeasureTheory.measureReal_restrict_apply hE_meas]
  have hinter : E ∩ Set.Ioc X (2 * X) = E := Set.inter_eq_left.mpr hE_subset
  simp [E, B, smul_eq_mul, hinter]

/-- The averaged `S₂` estimate follows from a fixed-window mass bound and the
safe-set measure lower bound. -/
theorem integral_u6aReciprocalZeroSum_indicator_le_averagedSelectionBound_indicator_of_fixedWindowMass
    {σ₁ σ₂ X δ M : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hδ2 : δ ≤ 2)
    (hMass : u6aFixedWindowZeroMass σ₁ σ₂ X ≤ M)
    (hMeasure :
      ENNReal.ofReal (X / 2) ≤
        (volume.restrict (Set.Ioc X (2 * X)))
          (u6aSafeHeightSet σ₁ σ₂ X δ)) :
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
      ∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume := by
  let E : Set ℝ := u6aSafeHeightSet σ₁ σ₂ X δ
  let μ : Measure ℝ := volume.restrict (Set.Ioc X (2 * X))
  let L : ℝ := Real.log (2 / δ)
  have hmass_nonneg : 0 ≤ u6aFixedWindowZeroMass σ₁ σ₂ X := by
    unfold u6aFixedWindowZeroMass
    exact Finset.sum_nonneg fun ρ hρ =>
      u6aZeroWindow_order_nonneg (σ₁ := σ₁) (σ₂ := σ₂) (X := X)
        (δ := 2) (ρ := ρ) hρ
  have hM_nonneg : 0 ≤ M := hmass_nonneg.trans hMass
  have hratio : 1 ≤ 2 / δ := by
    field_simp [hδ.ne']
    linarith
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg hratio
  have hA_nonneg : 0 ≤ 2 * L := by positivity
  have hleft_mass :=
    integral_u6aReciprocalZeroSum_indicator_le_fixedWindowZeroMass
      (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) hX hδ hδ2
  have hleft_M :
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
            (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume) ≤
        (2 * L) * M := by
    have hmass_step :
        (2 * L) * u6aFixedWindowZeroMass σ₁ σ₂ X ≤ (2 * L) * M :=
      mul_le_mul_of_nonneg_left hMass hA_nonneg
    exact hleft_mass.trans (by simpa [L, mul_assoc] using hmass_step)
  have hE_subset : E ⊆ Set.Ioc X (2 * X) := by
    intro t ht
    exact ht.1
  have hμE_ne_top : μ E ≠ ⊤ := by
    have hμ_univ_ne_top : μ Set.univ ≠ ⊤ := by
      dsimp [μ]
      simp [Real.volume_Ioc]
    exact ne_top_of_le_ne_top hμ_univ_ne_top (measure_mono (Set.subset_univ E))
  have hmeas_real : X / 2 ≤ μ.real E := by
    rw [MeasureTheory.measureReal_def]
    have hleft_ne_top : ENNReal.ofReal (X / 2) ≠ ⊤ := by simp
    have htoReal :=
      (ENNReal.toReal_le_toReal hleft_ne_top hμE_ne_top).2 hMeasure
    simpa [ENNReal.toReal_ofReal (by linarith : 0 ≤ X / 2)] using htoReal
  have hB_nonneg : 0 ≤ u6aAveragedSelectionBound X δ M := by
    unfold u6aAveragedSelectionBound
    positivity
  have hright_lower :
      (2 * L) * M ≤
        μ.real E * u6aAveragedSelectionBound X δ M := by
    have hmul :=
      mul_le_mul_of_nonneg_right hmeas_real hB_nonneg
    have hcalc :
        (X / 2) * u6aAveragedSelectionBound X δ M = (2 * L) * M := by
      unfold u6aAveragedSelectionBound
      field_simp [hX.ne']
      ring
    simpa [μ, E, L, hcalc] using hmul
  calc
    (∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (u6aReciprocalZeroSum σ₁ σ₂) t ∂volume)
        ≤ (2 * L) * M := hleft_M
    _ ≤ μ.real E * u6aAveragedSelectionBound X δ M := hright_lower
    _ = ∫ t in X..(2 * X),
        (u6aSafeHeightSet σ₁ σ₂ X δ).indicator
          (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume := by
        rw [integral_u6aAveragedSelectionBound_indicator_eq_measureReal
          (σ₁ := σ₁) (σ₂ := σ₂) (X := X) (δ := δ) (M := M) hX hδ]

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

/-- On a horizontal line separated from zero ordinates, the nearby principal
part is bounded by the width-two reciprocal zero sum at the same height. -/
theorem norm_u6aNearbyZeroPrincipalSum_le_reciprocalZeroSum_of_im_gap
    {σ₁ σ₂ t : ℝ} {s : ℂ}
    (hsim : s.im = t)
    (hsep : ∀ ρ : ℂ, ρ.re ∈ Set.uIcc σ₁ σ₂ → riemannZeta ρ = 0 →
      0 < |t - ρ.im|) :
    ‖u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ ≤
      u6aReciprocalZeroSum σ₁ σ₂ t := by
  classical
  let Znear := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 1) (t + 1))
  let Zrec := riemannZeta.zeroes_rect (Set.uIcc σ₁ σ₂) (Set.Icc (t - 2) (t + 2))
  let hnear : Znear.Finite := u6aNearbyZeroSet_finite σ₁ σ₂ t
  let hrec : Zrec.Finite := u6aReciprocalZeroSet_finite σ₁ σ₂ t
  have hsubset : hnear.toFinset ⊆ hrec.toFinset := by
    intro ρ hρ
    have hρnear : ρ ∈ Znear := hnear.mem_toFinset.mp hρ
    exact hrec.mem_toFinset.mpr
      (u6aNearbyZeroSet_subset_reciprocalZeroSet σ₁ σ₂ t hρnear)
  have hterm_le : ∀ ρ ∈ hnear.toFinset,
      ‖((1 : ℂ) / (s - ρ)) * (riemannZeta.order ρ : ℂ)‖ ≤
        (1 / |t - ρ.im|) * (riemannZeta.order ρ : ℝ) := by
    intro ρ hρ
    have hρnear : ρ ∈ Znear := hnear.mem_toFinset.mp hρ
    have hzero : riemannZeta ρ = 0 := hρnear.2.2
    have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) :=
      u6a_zeta_zero_order_nonneg_of_zero hzero
    have him_pos : 0 < |t - ρ.im| := hsep ρ hρnear.1 hzero
    have him_le_norm : |t - ρ.im| ≤ ‖s - ρ‖ := by
      have h := Complex.abs_im_le_norm (s - ρ)
      simpa [Complex.sub_im, hsim] using h
    have hdiv_le : ‖(1 : ℂ) / (s - ρ)‖ ≤ 1 / |t - ρ.im| := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le him_pos him_le_norm
    have horder_norm :
        ‖(riemannZeta.order ρ : ℂ)‖ = (riemannZeta.order ρ : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg horder_nonneg]
    calc
      ‖((1 : ℂ) / (s - ρ)) * (riemannZeta.order ρ : ℂ)‖
          ≤ ‖(1 : ℂ) / (s - ρ)‖ * ‖(riemannZeta.order ρ : ℂ)‖ :=
            norm_mul_le _ _
      _ ≤ (1 / |t - ρ.im|) * (riemannZeta.order ρ : ℝ) := by
            rw [horder_norm]
            exact mul_le_mul_of_nonneg_right hdiv_le horder_nonneg
  unfold u6aNearbyZeroPrincipalSum u6aReciprocalZeroSum
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ => (1 : ℂ) / (s - ρ)) hnear,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ => (1 : ℝ) / |t - ρ.im|) hrec]
  calc
    ‖∑ ρ ∈ hnear.toFinset,
        ((1 : ℂ) / (s - ρ)) * (riemannZeta.order ρ : ℂ)‖
        ≤ ∑ ρ ∈ hnear.toFinset,
          ‖((1 : ℂ) / (s - ρ)) * (riemannZeta.order ρ : ℂ)‖ := by
          exact norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hnear.toFinset,
          (1 / |t - ρ.im|) * (riemannZeta.order ρ : ℝ) := by
          exact Finset.sum_le_sum hterm_le
    _ ≤ ∑ ρ ∈ hrec.toFinset,
          (1 / |t - ρ.im|) * (riemannZeta.order ρ : ℝ) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
          intro ρ hρrec _hρnot
          have hρmem : ρ ∈ Zrec := hrec.mem_toFinset.mp hρrec
          have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) :=
            u6a_zeta_zero_order_nonneg_of_zero hρmem.2.2
          exact mul_nonneg (by positivity) horder_nonneg

/-- A horizontal zero gap supplies the separation hypothesis needed to bound
the nearby principal part by the reciprocal zero sum, on either horizontal side. -/
theorem norm_u6aNearbyZeroPrincipalSum_le_reciprocalZeroSum_of_zeroGap
    {σ₁ σ₂ T η t : ℝ} {s : ℂ}
    (hgap : horizontalSegmentZeroGap σ₁ σ₂ T η)
    (ht : t = T ∨ t = -T)
    (hsim : s.im = t) :
    ‖u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ ≤
      u6aReciprocalZeroSum σ₁ σ₂ t := by
  refine norm_u6aNearbyZeroPrincipalSum_le_reciprocalZeroSum_of_im_gap hsim ?_
  intro ρ hρre hρzero
  rcases hgap with ⟨hη, htop, hbot⟩
  rcases ht with htT | htT
  · have hdist := htop ρ hρre hρzero
    have hpos : 0 < |ρ.im - T| := hη.trans_le hdist
    have hrewrite : |t - ρ.im| = |ρ.im - T| := by
      rw [htT, abs_sub_comm]
    rwa [hrewrite]
  · have hdist := hbot ρ hρre hρzero
    have hpos : 0 < |ρ.im + T| := hη.trans_le hdist
    have hrewrite : |t - ρ.im| = |ρ.im + T| := by
      rw [htT]
      have hneg : -T - ρ.im = -(ρ.im + T) := by ring
      rw [hneg, abs_neg]
    rwa [hrewrite]

/-- The width-two reciprocal zero sum in the U6a strip is symmetric under
height reversal.  This is a finite reindexing over the closed windows via
conjugation, preserving zeta order. -/
theorem u6aReciprocalZeroSum_neg (T : ℝ) :
    u6aReciprocalZeroSum (-1) 2 (-T) = u6aReciprocalZeroSum (-1) 2 T := by
  classical
  let Zbot := riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
    (Set.Icc (-T - 2) (-T + 2))
  let Ztop := riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
    (Set.Icc (T - 2) (T + 2))
  let hbot : Zbot.Finite := u6aReciprocalZeroSet_finite (-1) 2 (-T)
  let htop : Ztop.Finite := u6aReciprocalZeroSet_finite (-1) 2 T
  unfold u6aReciprocalZeroSum
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ => (1 : ℝ) / |(-T) - ρ.im|) hbot,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ => (1 : ℝ) / |T - ρ.im|) htop]
  refine Finset.sum_bij (fun ρ _ => (starRingEnd ℂ) ρ) ?_ ?_ ?_ ?_
  · intro ρ hρ
    have hρbot : ρ ∈ Zbot := hbot.mem_toFinset.mp hρ
    refine htop.mem_toFinset.mpr ?_
    rcases hρbot with ⟨hre, him, hzero⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [Complex.conj_re] using hre
    · constructor
      · rw [Complex.conj_im]
        linarith [him.2]
      · rw [Complex.conj_im]
        linarith [him.1]
    · change riemannZeta ((starRingEnd ℂ) ρ) = 0
      rw [riemannZeta_conj, hzero, map_zero]
  · intro ρ hρ τ hτ hconj
    have h := congrArg (starRingEnd ℂ) hconj
    simpa [Complex.conj_conj] using h
  · intro ρ hρ
    refine ⟨(starRingEnd ℂ) ρ, ?_, ?_⟩
    · have hρtop : ρ ∈ Ztop := htop.mem_toFinset.mp hρ
      refine hbot.mem_toFinset.mpr ?_
      rcases hρtop with ⟨hre, him, hzero⟩
      refine ⟨?_, ?_, ?_⟩
      · simpa [Complex.conj_re] using hre
      · constructor
        · rw [Complex.conj_im]
          linarith [him.2]
        · rw [Complex.conj_im]
          linarith [him.1]
      · change riemannZeta ((starRingEnd ℂ) ρ) = 0
        rw [riemannZeta_conj, hzero, map_zero]
    · simp
  · intro ρ hρ
    have hden :
        |(-T) - ρ.im| = |T - ((starRingEnd ℂ) ρ).im| := by
      rw [Complex.conj_im]
      have hleft : (-T) - ρ.im = -(T + ρ.im) := by ring
      have hright : T - -ρ.im = T + ρ.im := by ring
      rw [hleft, abs_neg, hright]
    have horder :
        riemannZeta.order ((starRingEnd ℂ) ρ) = riemannZeta.order ρ :=
      u6a_riemannZeta_order_star ρ
    rw [hden, horder]

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

private lemma u6a_log_le_log_sq_of_three_le {T : ℝ} (hT : 3 ≤ T) :
    Real.log T ≤ Real.log T ^ 2 := by
  have hTpos : 0 < T := by linarith
  have hlog_ge_one : (1 : ℝ) ≤ Real.log T := by
    apply le_of_lt
    rw [Real.lt_log_iff_exp_lt hTpos]
    calc
      Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < T := by norm_num; linarith
  nlinarith

/-- Fixed-height composition: a partial-fraction approximation plus a bound
for the reciprocal zero sum gives the lane's pointwise `log²` horizontal
estimate at that height. -/
theorem logDeriv_bound_of_partialFraction_and_reciprocalBound
    {σ₁ σ₂ Cpf Tpf Crec T η t x : ℝ}
    (hPF : U6aPartialFractionApproximationHypothesis σ₁ σ₂ Cpf Tpf)
    (hT : 3 ≤ T) (hTpf : Tpf ≤ T)
    (hgap : horizontalSegmentZeroGap σ₁ σ₂ T η)
    (ht : t = T ∨ t = -T) (htabs : |t| = T)
    (hx : x ∈ Set.uIcc σ₁ σ₂)
    (hrec : u6aReciprocalZeroSum σ₁ σ₂ t ≤ Crec * Real.log T ^ 2) :
    ‖deriv riemannZeta ((x : ℂ) + t * I) / riemannZeta ((x : ℂ) + t * I)‖ ≤
      (Cpf + Crec) * Real.log T ^ 2 := by
  let s : ℂ := (x : ℂ) + t * I
  have hsim : s.im = t := by simp [s]
  have hsre : s.re ∈ Set.uIcc σ₁ σ₂ := by simpa [s] using hx
  have hT_abs_s : |s.im| = T := by simpa [hsim] using htabs
  have hpfT : Tpf ≤ |s.im| := by rw [hT_abs_s]; exact hTpf
  have h3s : 3 ≤ |s.im| := by rw [hT_abs_s]; exact hT
  have hA := hPF.2 s hsre hpfT h3s
  have hnear := norm_u6aNearbyZeroPrincipalSum_le_reciprocalZeroSum_of_zeroGap
    (σ₁ := σ₁) (σ₂ := σ₂) (T := T) (η := η) (t := t) (s := s)
    hgap ht hsim
  have hnear2 : ‖u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ ≤ Crec * Real.log T ^ 2 :=
    hnear.trans hrec
  have hlog_le_sq : Real.log T ≤ Real.log T ^ 2 := u6a_log_le_log_sq_of_three_le hT
  calc
    ‖deriv riemannZeta ((x : ℂ) + t * I) / riemannZeta ((x : ℂ) + t * I)‖
        = ‖(deriv riemannZeta s / riemannZeta s - u6aNearbyZeroPrincipalSum σ₁ σ₂ t s) +
            u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ := by
          simp [s]
    _ ≤ ‖deriv riemannZeta s / riemannZeta s -
          u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ +
        ‖u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ := norm_add_le _ _
    _ ≤ Cpf * Real.log T + Crec * Real.log T ^ 2 := by
          have hA' : ‖deriv riemannZeta s / riemannZeta s -
                u6aNearbyZeroPrincipalSum σ₁ σ₂ t s‖ ≤ Cpf * Real.log T := by
            simpa [hsim, htabs] using hA
          nlinarith
    _ ≤ Cpf * Real.log T ^ 2 + Crec * Real.log T ^ 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hlog_le_sq hPF.1.le) le_rfl
    _ = (Cpf + Crec) * Real.log T ^ 2 := by ring

/-- A fixed-height horizontal-segment wrapper: if both horizontal sides at
height `|t| = T` have the reciprocal zero sum bounded by `Crec log² T`, the
partial-fraction approximation gives the lane's `horizontalSegmentLogDerivBound`
at that height. -/
theorem horizontalSegmentLogDerivBound_of_partialFraction_and_reciprocalBound
    {σ₁ σ₂ Cpf Tpf Crec T η : ℝ}
    (hPF : U6aPartialFractionApproximationHypothesis σ₁ σ₂ Cpf Tpf)
    (hT : 3 ≤ T) (hTpf : Tpf ≤ T)
    (hgap : horizontalSegmentZeroGap σ₁ σ₂ T η)
    (hrec : ∀ t : ℝ, |t| = T →
      u6aReciprocalZeroSum σ₁ σ₂ t ≤ Crec * Real.log T ^ 2) :
    horizontalSegmentLogDerivBound σ₁ σ₂ T (Cpf + Crec) := by
  have hTpos : 0 < T := by linarith
  refine ⟨horizontalSegmentZeroFree_of_zeroGap hTpos hgap, ?_⟩
  intro x hx t htabs
  have htcase : t = T ∨ t = -T := by
    exact (abs_eq (by linarith : (0 : ℝ) ≤ T)).mp htabs
  exact logDeriv_bound_of_partialFraction_and_reciprocalBound
    (σ₁ := σ₁) (σ₂ := σ₂) (Cpf := Cpf) (Tpf := Tpf) (Crec := Crec)
    (T := T) (η := η) (t := t) (x := x) hPF hT hTpf hgap htcase htabs hx
    (hrec t htabs)

/-- U6a-strip specialization: by conjugation symmetry of the reciprocal zero
sum, it is enough to bound the selected positive height. -/
theorem horizontalSegmentLogDerivBound_of_partialFraction_and_top_reciprocalBound
    {Cpf Tpf Crec T η : ℝ}
    (hPF : U6aPartialFractionApproximationHypothesis (-1) 2 Cpf Tpf)
    (hT : 3 ≤ T) (hTpf : Tpf ≤ T)
    (hgap : horizontalSegmentZeroGap (-1) 2 T η)
    (hrecTop : u6aReciprocalZeroSum (-1) 2 T ≤ Crec * Real.log T ^ 2) :
    horizontalSegmentLogDerivBound (-1) 2 T (Cpf + Crec) := by
  refine horizontalSegmentLogDerivBound_of_partialFraction_and_reciprocalBound
    (σ₁ := (-1 : ℝ)) (σ₂ := 2) (Cpf := Cpf) (Tpf := Tpf) (Crec := Crec)
    (T := T) (η := η) hPF hT hTpf hgap ?_
  intro t ht
  have htcase : t = T ∨ t = -T := (abs_eq (by linarith : (0 : ℝ) ≤ T)).mp ht
  rcases htcase with rfl | rfl
  · exact hrecTop
  · simpa [u6aReciprocalZeroSum_neg] using hrecTop

/-- Consumer wrapper for the averaged selector: once the selected positive
height's averaged reciprocal-zero bound is compared to `C log² T`, the
horizontal-segment `log²` estimate follows on both sides. -/
theorem horizontalSegmentLogDerivBound_of_partialFraction_and_averagedSelection
    {Cpf Tpf Crec X δ M T : ℝ}
    (hPF : U6aPartialFractionApproximationHypothesis (-1) 2 Cpf Tpf)
    (hT : 3 ≤ T) (hTpf : Tpf ≤ T)
    (hsel : T ∈ u6aSafeHeightSet (-1) 2 X δ)
    (hrecSel : u6aReciprocalZeroSum (-1) 2 T ≤ u6aAveragedSelectionBound X δ M)
    (havg_le : u6aAveragedSelectionBound X δ M ≤ Crec * Real.log T ^ 2) :
    horizontalSegmentLogDerivBound (-1) 2 T (Cpf + Crec) :=
  horizontalSegmentLogDerivBound_of_partialFraction_and_top_reciprocalBound
    (Cpf := Cpf) (Tpf := Tpf) (Crec := Crec) (T := T) (η := δ)
    hPF hT hTpf hsel.2 (hrecSel.trans havg_le)

/-- The translated removable extension of `(w - 1)ζ(w)`, centered at `s`.
Jensen's disk-counting lemmas are centered at zero, so the PF-disk route applies
them to this translated entire function. -/
noncomputable def u6aShiftedZetaPoleRemoved (s z : ℂ) : ℂ :=
  Complex.zetaTimesSMinusOne_entire (s + z)

theorem differentiable_u6aShiftedZetaPoleRemoved (s : ℂ) :
    Differentiable ℂ (u6aShiftedZetaPoleRemoved s) := by
  intro z
  unfold u6aShiftedZetaPoleRemoved
  have hshift : DifferentiableAt ℂ (fun z : ℂ => s + z) z := by
    fun_prop
  exact Complex.zetaTimesSMinusOne_entire_differentiable.differentiableAt.comp z hshift

/-- Translate the global growth bound for `(w - 1)ζ(w)` to disks centered at
`s`.  The center dependence is explicit and will be specialized to high
horizontal lines in the PF-disk estimate. -/
theorem u6aShiftedZetaPoleRemoved_growth :
    ∃ C : ℝ, 0 < C ∧ ∀ s z : ℂ,
      Real.log (1 + ‖u6aShiftedZetaPoleRemoved s z‖) ≤
        C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + ‖z‖) ^ (2 : ℝ) := by
  obtain ⟨C, hCpos, hC⟩ := Complex.zeta_minus_pole_entire_growth
  refine ⟨C, hCpos, ?_⟩
  intro s z
  have hbase := hC (s + z)
  have hs_nonneg : 0 ≤ ‖s‖ := norm_nonneg s
  have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hleft_nonneg : 0 ≤ 1 + ‖s‖ := by positivity
  have hright_nonneg : 0 ≤ 1 + ‖z‖ := by positivity
  have hnorm : 1 + ‖s + z‖ ≤ (1 + ‖s‖) * (1 + ‖z‖) := by
    calc
      1 + ‖s + z‖ ≤ 1 + (‖s‖ + ‖z‖) := by
        gcongr
        exact norm_add_le s z
      _ ≤ (1 + ‖s‖) * (1 + ‖z‖) := by nlinarith [hs_nonneg, hz_nonneg]
  have hpow :
      (1 + ‖s + z‖) ^ (2 : ℝ) ≤
        ((1 + ‖s‖) * (1 + ‖z‖)) ^ (2 : ℝ) := by
    exact Real.rpow_le_rpow (by positivity) hnorm (by norm_num)
  have hsplit :
      ((1 + ‖s‖) * (1 + ‖z‖)) ^ (2 : ℝ) =
        (1 + ‖s‖) ^ (2 : ℝ) * (1 + ‖z‖) ^ (2 : ℝ) := by
    rw [Real.mul_rpow hleft_nonneg hright_nonneg]
  calc
    Real.log (1 + ‖u6aShiftedZetaPoleRemoved s z‖)
        ≤ C * (1 + ‖s + z‖) ^ (2 : ℝ) := by
          simpa [u6aShiftedZetaPoleRemoved] using hbase
    _ ≤ C * (((1 + ‖s‖) * (1 + ‖z‖)) ^ (2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpow hCpos.le
    _ = C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + ‖z‖) ^ (2 : ℝ) := by
          rw [hsplit, mul_assoc]

/-- Jensen/log-counting mass bound for zeros of the translated removable zeta
extension in a disk around `s`.  This is the centered disk-count source for the
PF-remainder route before the zeta-zero multiplicity bridge is applied. -/
theorem u6aShiftedZetaPoleRemoved_divisorMassClosedBall_le
    (s : ℂ) {R : ℝ} (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧
      Complex.Hadamard.divisorMassClosedBall₀ (u6aShiftedZetaPoleRemoved s) R ≤
        (C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + |2 * R|) ^ (2 : ℝ) +
            |Real.log ‖meromorphicTrailingCoeffAt (u6aShiftedZetaPoleRemoved s) 0‖|) /
          Real.log 2 := by
  obtain ⟨C, hCpos, hC⟩ := u6aShiftedZetaPoleRemoved_growth
  refine ⟨C, hCpos, ?_⟩
  have hgrowth_for_s :
      ∀ z : ℂ, Real.log (1 + ‖u6aShiftedZetaPoleRemoved s z‖) ≤
        (C * (1 + ‖s‖) ^ (2 : ℝ)) * (1 + ‖z‖) ^ (2 : ℝ) := by
    intro z
    simpa [mul_assoc] using hC s z
  simpa [mul_assoc] using
    Complex.Hadamard.divisorMassClosedBall₀_le_of_growth
      (f := u6aShiftedZetaPoleRemoved s) (ρ := (2 : ℝ))
      (C := C * (1 + ‖s‖) ^ (2 : ℝ))
      (differentiable_u6aShiftedZetaPoleRemoved s) hgrowth_for_s hR

/-- Away from the pole point, the translated removable extension is the zeta
factor multiplied by `s + z - 1`. -/
theorem u6aShiftedZetaPoleRemoved_eq_mul_riemannZeta {s z : ℂ}
    (h1 : s + z ≠ 1) :
    u6aShiftedZetaPoleRemoved s z = (s + z - 1) * riemannZeta (s + z) := by
  simpa [u6aShiftedZetaPoleRemoved] using
    Complex.zetaTimesSMinusOne_entire_eq_mul_riemannZeta h1

/-- On disks not meeting the pole point, zeros of the translated removable
extension are exactly zeta zeros.  Multiplicity packaging is the next PF-disk
bridge, but this is the zero-set identity needed before that step. -/
theorem u6aShiftedZetaPoleRemoved_zero_iff {s z : ℂ}
    (h1 : s + z ≠ 1) :
    u6aShiftedZetaPoleRemoved s z = 0 ↔ riemannZeta (s + z) = 0 := by
  rw [u6aShiftedZetaPoleRemoved_eq_mul_riemannZeta h1]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.2 h1)
  · intro h
    simp [h]

/-- Disk form of `u6aShiftedZetaPoleRemoved_zero_iff`: if the closed radius
`R` disk around the translated origin stays away from the pole point `1`, every
point in that disk has the same zero predicate for the removable extension and
for `ζ`. -/
theorem u6aShiftedZetaPoleRemoved_zero_iff_of_norm_le
    {s z : ℂ} {R : ℝ} (hz : ‖z‖ ≤ R) (hR : R < ‖s - 1‖) :
    u6aShiftedZetaPoleRemoved s z = 0 ↔ riemannZeta (s + z) = 0 := by
  apply u6aShiftedZetaPoleRemoved_zero_iff
  intro h
  have hs1 : s - 1 = -z := by
    calc
      s - 1 = s - (s + z) := by rw [h]
      _ = -z := by ring
  have hnorm : ‖s - 1‖ = ‖z‖ := by
    rw [hs1, norm_neg]
  linarith

/-- Local product identity for the translated removable zeta extension, away
from the pole point. -/
theorem u6aShiftedZetaPoleRemoved_eventuallyEq_mul {s z : ℂ}
    (h1 : s + z ≠ 1) :
    u6aShiftedZetaPoleRemoved s =ᶠ[nhds z]
      fun w => (s + w - 1) * riemannZeta (s + w) := by
  have hcont : ContinuousAt (fun w : ℂ => s + w) z := by fun_prop
  have hnear : {w : ℂ | w ≠ 1} ∈ nhds (s + z) :=
    isOpen_compl_singleton.mem_nhds (by simpa using h1)
  have hpre : (fun w : ℂ => s + w) ⁻¹' {w : ℂ | w ≠ 1} ∈ nhds z :=
    hcont hnear
  filter_upwards [hpre] with w hw
  exact u6aShiftedZetaPoleRemoved_eq_mul_riemannZeta (s := s) (z := w)
    (by simpa using hw)

/-- Divisor multiplicity transport for the translated removable zeta
extension.  Inside disks not meeting the pole point, Jensen's divisor mass for
`u6aShiftedZetaPoleRemoved s` counts zeta zeros with their usual order. -/
theorem u6aShiftedZetaPoleRemoved_divisor_eq_order {s z : ℂ}
    (h1 : s + z ≠ 1) :
    (MeromorphicOn.divisor (u6aShiftedZetaPoleRemoved s) Set.univ) z =
      riemannZeta.order (s + z) := by
  have hζan : AnalyticAt ℂ riemannZeta (s + z) :=
    riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr h1)
  have hlin : AnalyticAt ℂ (fun w : ℂ => s + w - 1) z := by fun_prop
  have hmero : MeromorphicOn (u6aShiftedZetaPoleRemoved s) Set.univ := fun x _ =>
    ((differentiable_u6aShiftedZetaPoleRemoved s).analyticAt x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ z)]
  have hcongr : meromorphicOrderAt (u6aShiftedZetaPoleRemoved s) z =
      meromorphicOrderAt (fun w : ℂ => (s + w - 1) * riemannZeta (s + w)) z :=
    meromorphicOrderAt_congr
      ((u6aShiftedZetaPoleRemoved_eventuallyEq_mul (s := s) (z := z) h1).filter_mono
        nhdsWithin_le_nhds)
  have hζcomp : MeromorphicAt (fun w : ℂ => riemannZeta (s + w)) z := by
    have hshift : AnalyticAt ℂ (fun w : ℂ => s + w) z := by fun_prop
    exact hζan.meromorphicAt.comp_analyticAt hshift
  have hmul :
      meromorphicOrderAt (fun w : ℂ => (s + w - 1) * riemannZeta (s + w)) z =
        meromorphicOrderAt (fun w : ℂ => s + w - 1) z +
          meromorphicOrderAt (fun w : ℂ => riemannZeta (s + w)) z :=
    meromorphicOrderAt_mul hlin.meromorphicAt hζcomp
  have hlin0 : meromorphicOrderAt (fun w : ℂ => s + w - 1) z = 0 := by
    rw [hlin.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (fun w : ℂ => s + w - 1) z = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by
        change s + z - 1 ≠ 0
        simpa [sub_eq_zero] using h1))
    simp [h0]
  have hshift : AnalyticAt ℂ (fun w : ℂ => s + w) z := by fun_prop
  have hderiv : deriv (fun w : ℂ => s + w) z ≠ 0 := by
    have hd : HasDerivAt (fun w : ℂ => s + w) 1 z := by
      simpa [one_mul] using (hasDerivAt_const z s).add (hasDerivAt_id z)
    rw [hd.deriv]
    norm_num
  have hcomp : meromorphicOrderAt (fun w : ℂ => riemannZeta (s + w)) z =
      meromorphicOrderAt riemannZeta (s + z) := by
    simpa [Function.comp_def] using
      (meromorphicOrderAt_comp_of_deriv_ne_zero (f := riemannZeta)
        (g := fun w : ℂ => s + w) hshift hderiv)
  rw [hcongr, hmul, hlin0, zero_add, hcomp, riemannZeta.order]
  rfl

/-- The shifted zeta zeros in a closed ball around the Jensen center form a
finite set after translating the center to the origin. -/
private lemma u6aShiftedZetaZeroBallSet_finite (s : ℂ) (R : ℝ) :
    {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0}.Finite := by
  let S : Set ℂ := Metric.closedBall s R ∩ riemannZeta.zeroes
  have hS_compact : IsCompact (Metric.closedBall s R) := isCompact_closedBall s R
  have hzeros : S.Finite :=
    riemannZeta.zeroes_on_Compact_finite' (S := Metric.closedBall s R) hS_compact
  refine (hzeros.image fun ρ : ℂ => ρ - s).subset ?_
  intro z hz
  rcases hz with ⟨hzR, hzeta⟩
  refine ⟨s + z, ?_, by ring⟩
  constructor
  · rw [Metric.mem_closedBall, dist_eq_norm]
    simpa [add_sub_cancel_left] using hzR
  · simpa [riemannZeta.zeroes] using hzeta

/-- Translated zeta zeros in a closed ball around `s`, indexed without
multiplicity.  Multiplicity is supplied by `riemannZeta.order` in the mass
lemma below. -/
noncomputable def u6aShiftedZetaZeroBallFinset (s : ℂ) (R : ℝ) : Finset ℂ :=
  (u6aShiftedZetaZeroBallSet_finite s R).toFinset

/-- Jensen-facing shifted zero-mass bridge: if the closed disk around `s` misses
the pole point and the center is not itself a zeta zero, then the
order-weighted zeta zeros in that shifted disk are bounded by Jensen's divisor
mass for `u6aShiftedZetaPoleRemoved s`. -/
theorem u6aShiftedZetaZeroBallMass_le_divisorMass {s : ℂ} {R : ℝ}
    (hR0 : 0 ≤ R) (hpole : R < ‖s - 1‖) (hcenter : riemannZeta s ≠ 0) :
    (∑ z ∈ u6aShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ)) ≤
      Complex.Hadamard.divisorMassClosedBall₀ (u6aShiftedZetaPoleRemoved s) R := by
  classical
  let D : Function.locallyFinsupp ℂ ℤ :=
    MeromorphicOn.divisor (u6aShiftedZetaPoleRemoved s) Set.univ
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport
      (Function.locallyFinsuppWithin.toClosedBall R D)
      (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  have hterm : ∀ z ∈ u6aShiftedZetaZeroBallFinset s R,
      (riemannZeta.order (s + z) : ℝ) = (D z : ℝ) := by
    intro z hz
    have hzmem : z ∈ {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0} :=
      (u6aShiftedZetaZeroBallSet_finite s R).mem_toFinset.mp hz
    have h1 : s + z ≠ 1 := by
      intro h
      have hs1 : s - 1 = -z := by
        calc
          s - 1 = s - (s + z) := by rw [h]
          _ = -z := by ring
      have hnorm : ‖s - 1‖ = ‖z‖ := by rw [hs1, norm_neg]
      linarith [hzmem.1]
    have hD : D z = riemannZeta.order (s + z) := by
      simpa [D] using u6aShiftedZetaPoleRemoved_divisor_eq_order (s := s) (z := z) h1
    exact_mod_cast hD.symm
  have hsubset : u6aShiftedZetaZeroBallFinset s R ⊆ S := by
    intro z hz
    have hzmem : z ∈ {z : ℂ | ‖z‖ ≤ R ∧ riemannZeta (s + z) = 0} :=
      (u6aShiftedZetaZeroBallSet_finite s R).mem_toFinset.mp hz
    have h1 : s + z ≠ 1 := by
      intro h
      have hs1 : s - 1 = -z := by
        calc
          s - 1 = s - (s + z) := by rw [h]
          _ = -z := by ring
      have hnorm : ‖s - 1‖ = ‖z‖ := by rw [hs1, norm_neg]
      linarith [hzmem.1]
    have hD_eq : D z = riemannZeta.order (s + z) := by
      simpa [D] using u6aShiftedZetaPoleRemoved_divisor_eq_order (s := s) (z := z) h1
    have hD_ne : D z ≠ 0 := by
      have horder_pos : 0 < riemannZeta.order (s + z) :=
        u6a_riemannZeta_order_pos_of_zero_ne_one h1 hzmem.2
      rw [hD_eq]
      exact ne_of_gt horder_pos
    have hsupp : z ∈ Function.locallyFinsuppWithin.support D :=
      Function.mem_support.mpr hD_ne
    have hnorm_abs : ‖z‖ ≤ |R| := by simpa [abs_of_nonneg hR0] using hzmem.1
    have hball : z ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support :=
      Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
        hsupp hnorm_abs
    have hSR : z ∈ SR :=
      (Set.Finite.mem_toFinset _).mpr hball
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hcenter (by simpa [hz0] using hzmem.2)
    exact Finset.mem_filter.mpr ⟨hSR, hz0⟩
  have hDnonneg : ∀ z : ℂ, 0 ≤ (D z : ℝ) := by
    intro z
    have hnn : (0 : ℤ) ≤ D z := by
      simpa [D] using Differentiable.divisor_nonneg
        (differentiable_u6aShiftedZetaPoleRemoved s) z
    exact_mod_cast hnn
  calc
    (∑ z ∈ u6aShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ))
        = ∑ z ∈ u6aShiftedZetaZeroBallFinset s R, (D z : ℝ) := by
          exact Finset.sum_congr rfl hterm
    _ ≤ ∑ z ∈ S, (D z : ℝ) := by
          exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
            (fun z _ _ => hDnonneg z)
    _ = Complex.Hadamard.divisorMassClosedBall₀ (u6aShiftedZetaPoleRemoved s) R := by
          rfl

/-- If the center is neither the pole nor a zeta zero, Jensen's trailing
coefficient for the translated removable extension is the center value
`(s - 1)ζ(s)`. -/
theorem u6aShiftedZetaPoleRemoved_trailingCoeffAt_zero_eq {s : ℂ}
    (hs1 : s ≠ 1) (hζ : riemannZeta s ≠ 0) :
    meromorphicTrailingCoeffAt (u6aShiftedZetaPoleRemoved s) 0 =
      (s - 1) * riemannZeta s := by
  have han : AnalyticAt ℂ (u6aShiftedZetaPoleRemoved s) 0 :=
    (differentiable_u6aShiftedZetaPoleRemoved s).analyticAt 0
  have hval :
      u6aShiftedZetaPoleRemoved s 0 = (s - 1) * riemannZeta s := by
    simpa using u6aShiftedZetaPoleRemoved_eq_mul_riemannZeta
      (s := s) (z := 0) (by simpa using hs1)
  have hnonzero : u6aShiftedZetaPoleRemoved s 0 ≠ 0 := by
    rw [hval]
    exact mul_ne_zero (sub_ne_zero.2 hs1) hζ
  rw [han.meromorphicTrailingCoeffAt_of_ne_zero hnonzero, hval]

/-- Jensen-growth bound for order-weighted zeta zeros in a shifted closed
ball, with the pole removed and the center assumed nonzero. -/
theorem u6aShiftedZetaZeroBallMass_le_jensen_growth {s : ℂ} {R : ℝ}
    (hR : 1 ≤ R) (hpole : R < ‖s - 1‖) (hcenter : riemannZeta s ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      (∑ z ∈ u6aShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ)) ≤
        (C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + |2 * R|) ^ (2 : ℝ) +
            |Real.log ‖(s - 1) * riemannZeta s‖|) / Real.log 2 := by
  have hR0 : 0 ≤ R := by linarith
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hpole
    simp at hpole
    linarith
  obtain ⟨C, hCpos, hmass⟩ := u6aShiftedZetaPoleRemoved_divisorMassClosedBall_le s hR
  refine ⟨C, hCpos, ?_⟩
  have hzero_mass :=
    u6aShiftedZetaZeroBallMass_le_divisorMass (s := s) (R := R) hR0 hpole hcenter
  have htail :
      meromorphicTrailingCoeffAt (u6aShiftedZetaPoleRemoved s) 0 =
        (s - 1) * riemannZeta s :=
    u6aShiftedZetaPoleRemoved_trailingCoeffAt_zero_eq hs1 hcenter
  calc
    (∑ z ∈ u6aShiftedZetaZeroBallFinset s R, (riemannZeta.order (s + z) : ℝ))
        ≤ Complex.Hadamard.divisorMassClosedBall₀ (u6aShiftedZetaPoleRemoved s) R :=
          hzero_mass
    _ ≤ (C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + |2 * R|) ^ (2 : ℝ) +
            |Real.log ‖meromorphicTrailingCoeffAt (u6aShiftedZetaPoleRemoved s) 0‖|) /
          Real.log 2 := hmass
    _ = (C * (1 + ‖s‖) ^ (2 : ℝ) * (1 + |2 * R|) ^ (2 : ℝ) +
            |Real.log ‖(s - 1) * riemannZeta s‖|) / Real.log 2 := by
          rw [htail]

private lemma u6aZetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma u6a_gamma_half_ne_zero_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    Gamma (s / 2) ≠ 0 := by
  refine Gamma_ne_zero ?_
  intro m hm
  have hre := congrArg Complex.re hm
  have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp at hre
  nlinarith

private lemma u6a_gamma_factor_ne_zero_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    zetaGammaFactor s ≠ 0 := by
  unfold zetaGammaFactor
  refine Gamma_ne_zero ?_
  intro m hm
  have hre := congrArg Complex.re hm
  have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp at hre
  nlinarith

private lemma u6a_gamma_factor_differentiableAt_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    DifferentiableAt ℂ zetaGammaFactor s := by
  unfold zetaGammaFactor
  refine (differentiableAt_Gamma _ ?_).comp s (by fun_prop)
  intro m hm
  have hre := congrArg Complex.re hm
  have hm_nonneg : (0 : ℝ) ≤ m := by exact_mod_cast Nat.zero_le m
  simp at hre
  nlinarith

private lemma u6a_gamma_factor_analyticAt_of_re_pos {s : ℂ} (hsre : 0 < s.re) :
    AnalyticAt ℂ zetaGammaFactor s := by
  refine Complex.analyticAt_iff_eventually_differentiableAt.mpr ?_
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const continuous_re
  filter_upwards [hopen.mem_nhds hsre] with w hw
  exact u6a_gamma_factor_differentiableAt_of_re_pos hw

private theorem u6a_completedZetaFactor_eq_riemannXi_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    completedZetaFactor s = riemannXi s := by
  have hs0 : s ≠ 0 := by
    intro hs
    rw [hs] at hsre0
    norm_num at hsre0
  have hs1 : s ≠ 1 := by
    intro hs
    rw [hs] at hsre1
    norm_num at hsre1
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, u6aZetaPiFactor_eq_cpow,
    riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    hGamma, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hs0, u6a_gamma_half_ne_zero_of_re_pos hsre0]

private lemma u6a_riemannXi_eventuallyEq_completedZetaFactor_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    riemannXi =ᶠ[nhds s] completedZetaFactor := by
  have hopen : IsOpen {w : ℂ | 0 < w.re ∧ w.re < 1} := by
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_re continuous_const)
  have hmem : s ∈ {w : ℂ | 0 < w.re ∧ w.re < 1} := ⟨hsre0, hsre1⟩
  filter_upwards [hopen.mem_nhds hmem] with w hw
  exact (u6a_completedZetaFactor_eq_riemannXi_of_criticalStrip hw.1 hw.2).symm

private lemma u6a_completedZetaFactor_order_eq_riemannZeta_order_of_criticalStrip
    {s : ℂ} (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    meromorphicOrderAt completedZetaFactor s = meromorphicOrderAt riemannZeta s := by
  let G : ℂ → ℂ := fun w => zetaPoleFactor w * zetaPiFactor w * zetaGammaFactor w
  have hG_an : AnalyticAt ℂ G s := by
    dsimp [G, zetaPoleFactor, zetaPiFactor]
    exact (((by fun_prop : AnalyticAt ℂ (fun w : ℂ => w - 1) s).mul
      (by
        rw [show (fun w : ℂ => Complex.exp (-(w / 2) * (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun w : ℂ => -(w / 2) * (Real.log Real.pi : ℂ)) by rfl]
        exact (Complex.differentiable_exp.analyticAt _).comp (by fun_prop))).mul
      (u6a_gamma_factor_analyticAt_of_re_pos hsre0))
  have hζ_an : AnalyticAt ℂ riemannZeta s := by
    have hs1 : s ≠ 1 := by
      intro hs
      rw [hs] at hsre1
      norm_num at hsre1
    exact riemannZeta_analyticOn_compl_one s (Set.mem_compl_singleton_iff.mpr hs1)
  have hG_ne : G s ≠ 0 := by
    dsimp [G, zetaPoleFactor, zetaPiFactor]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
    · intro h
      have hs : s = 1 := by simpa [sub_eq_zero] using h
      rw [hs] at hsre1
      norm_num at hsre1
    · exact Complex.exp_ne_zero _
    · exact u6a_gamma_factor_ne_zero_of_re_pos hsre0
  have hmul :
      meromorphicOrderAt (fun w : ℂ => G w * riemannZeta w) s =
        meromorphicOrderAt G s + meromorphicOrderAt riemannZeta s :=
    meromorphicOrderAt_mul hG_an.meromorphicAt hζ_an.meromorphicAt
  have hG0 : meromorphicOrderAt G s = 0 := by
    rw [hG_an.meromorphicOrderAt_eq]
    have horder : analyticOrderAt G s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hG_ne)
    simp [horder]
  calc
    meromorphicOrderAt completedZetaFactor s =
        meromorphicOrderAt (fun w : ℂ => G w * riemannZeta w) s := by
          rfl
    _ = meromorphicOrderAt G s + meromorphicOrderAt riemannZeta s := hmul
    _ = meromorphicOrderAt riemannZeta s := by rw [hG0, zero_add]

/-- In the non-trivial strip, the xi divisor counts zeta zeros with the same
order.  This is the multiplicity bridge needed to compare the xi-Hadamard
indexing with the Kadiri zeta-zero windows. -/
theorem u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip {s : ℂ}
    (hsre0 : 0 < s.re) (hsre1 : s.re < 1) :
    (MeromorphicOn.divisor riemannXi Set.univ) s = riemannZeta.order s := by
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ =>
    (Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ s)]
  have hcongr : meromorphicOrderAt riemannXi s =
      meromorphicOrderAt completedZetaFactor s :=
    meromorphicOrderAt_congr
      ((u6a_riemannXi_eventuallyEq_completedZetaFactor_of_criticalStrip
        (s := s) hsre0 hsre1).filter_mono nhdsWithin_le_nhds)
  rw [hcongr,
    u6a_completedZetaFactor_order_eq_riemannZeta_order_of_criticalStrip hsre0 hsre1,
    riemannZeta.order]
  rfl

/-- Non-trivial zeta zeros carry positive xi-divisor mass. -/
theorem u6aRiemannXi_divisor_pos_of_nontrivialZero (ρ : NontrivialZeros) :
    0 < (MeromorphicOn.divisor riemannXi Set.univ) (ρ : ℂ) := by
  have hre := ρ.property.1
  rw [u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip hre.1 hre.2]
  exact riemannZeta_order_pos_nontrivialZero ρ

/-- Non-trivial zeta zeros lie in the support of the xi divisor. -/
theorem u6aRiemannXi_divisor_ne_zero_of_nontrivialZero (ρ : NontrivialZeros) :
    (MeromorphicOn.divisor riemannXi Set.univ) (ρ : ℂ) ≠ 0 :=
  ne_of_gt (u6aRiemannXi_divisor_pos_of_nontrivialZero ρ)

/-- The xi divisor index has a concrete fiber over every non-trivial zeta zero. -/
theorem u6aRiemannXi_divisorZeroIndex₀_fiber_nonempty_of_nontrivialZero
    (ρ : NontrivialZeros) :
    Nonempty {p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ) //
      Complex.Hadamard.divisorZeroIndex₀_val p = (ρ : ℂ)} := by
  have htoNat : 0 <
      Int.toNat ((MeromorphicOn.divisor riemannXi Set.univ) (ρ : ℂ)) := by
    have hpos := u6aRiemannXi_divisor_pos_of_nontrivialZero ρ
    omega
  refine ⟨⟨⟨⟨(ρ : ℂ), ⟨0, htoNat⟩⟩, nontrivialZero_ne_zero ρ⟩, ?_⟩⟩
  rfl

/-- The xi divisor-index fiber over a non-trivial zeta zero has the expected
zeta order cardinality. -/
theorem u6aRiemannXi_divisorZeroIndex₀_fiber_card_eq_riemannZeta_order
    (ρ : NontrivialZeros) :
    (Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) (ρ : ℂ)).card =
      Int.toNat (riemannZeta.order (ρ : ℂ)) := by
  rw [Complex.Hadamard.divisorZeroIndex₀_fiberFinset_card_eq_toNat_divisor
    (f := riemannXi) (z₀ := (ρ : ℂ)) (nontrivialZero_ne_zero ρ)]
  have hre := ρ.property.1
  rw [u6aRiemannXi_divisor_eq_riemannZeta_order_of_criticalStrip hre.1 hre.2]

/-- Finite window-local reindexing over xi divisor fibers.  This is the local
bridge used in U6a: for any finite zeta-zero window already represented as
non-trivial zeros, summing over xi divisor-index fibers is the same as the
order-weighted zeta-zero sum. -/
theorem u6aRiemannXi_fiberWindow_sum_eq_zeroes_finset_sum
    (Z : Finset NontrivialZeros) (φ : ℂ → ℂ) :
    (∑ ρ ∈ Z,
        ∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) (ρ : ℂ),
          φ (Complex.Hadamard.divisorZeroIndex₀_val p)) =
      ∑ ρ ∈ Z, (riemannZeta.order (ρ : ℂ) : ℂ) * φ (ρ : ℂ) := by
  refine Finset.sum_congr rfl ?_
  intro ρ _hρ
  have hval : ∀ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) (ρ : ℂ),
      φ (Complex.Hadamard.divisorZeroIndex₀_val p) = φ (ρ : ℂ) := by
    intro p hp
    have hpval := (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset (f := riemannXi)
      (z₀ := (ρ : ℂ)) p).1 hp
    rw [hpval]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcard := u6aRiemannXi_divisorZeroIndex₀_fiber_card_eq_riemannZeta_order ρ
  have horder_nonneg : 0 ≤ riemannZeta.order (ρ : ℂ) := by
    exact le_of_lt (riemannZeta_order_pos_nontrivialZero ρ)
  have hcast :
      ((Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) (ρ : ℂ)).card : ℂ) =
        (riemannZeta.order (ρ : ℂ) : ℂ) := by
    rw [hcard]
    exact_mod_cast Int.toNat_of_nonneg horder_nonneg
  rw [hcast]

/-- Window-local finite reindexing in the `zeroes_sum` representation.  Once
the selected finite window is known to contain only non-trivial zeta zeros, the
sum over the corresponding xi divisor-index fibers is exactly the
order-weighted zeta-zero sum. -/
theorem u6aRiemannXi_fiberWindow_sum_eq_zeroes_sum_of_finite
    {I J : Set ℝ} (hfin : (riemannZeta.zeroes_rect I J).Finite)
    (hNT : ∀ ρ : ℂ, ρ ∈ riemannZeta.zeroes_rect I J → ρ ∈ NontrivialZeros)
    (φ : ℂ → ℂ) :
    (∑ ρ ∈ hfin.toFinset,
        ∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ,
          φ (Complex.Hadamard.divisorZeroIndex₀_val p)) =
      riemannZeta.zeroes_sum I J φ := by
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite φ hfin]
  refine Finset.sum_congr rfl ?_
  intro ρ hρ
  have hρmem : ρ ∈ riemannZeta.zeroes_rect I J := hfin.mem_toFinset.mp hρ
  let ρnt : NontrivialZeros := ⟨ρ, hNT ρ hρmem⟩
  have hval : ∀ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ,
      φ (Complex.Hadamard.divisorZeroIndex₀_val p) = φ ρ := by
    intro p hp
    have hpval := (Complex.Hadamard.mem_divisorZeroIndex₀_fiberFinset (f := riemannXi)
      (z₀ := ρ) p).1 hp
    rw [hpval]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcard := u6aRiemannXi_divisorZeroIndex₀_fiber_card_eq_riemannZeta_order ρnt
  have horder_nonneg : 0 ≤ riemannZeta.order ρ := by
    have hpos := riemannZeta_order_pos_nontrivialZero ρnt
    simpa [ρnt] using le_of_lt hpos
  have hcast :
      ((Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ).card : ℂ) =
        (riemannZeta.order ρ : ℂ) := by
    rw [hcard]
    exact_mod_cast Int.toNat_of_nonneg horder_nonneg
  rw [hcast]
  ring

/-- High-window specialization of the local finite reindexing theorem.  The
nontriviality hypothesis is discharged from `|t| ≥ 2`. -/
theorem u6aRiemannXi_fiberHighWindow_sum_eq_zeroes_sum_of_finite
    {t : ℝ}
    (hfin : (riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2)
      (Set.Icc (t - 1) (t + 1))).Finite)
    (ht : 2 ≤ |t|)
    (φ : ℂ → ℂ) :
    (∑ ρ ∈ hfin.toFinset,
        ∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ,
          φ (Complex.Hadamard.divisorZeroIndex₀_val p)) =
      riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1)) φ :=
  u6aRiemannXi_fiberWindow_sum_eq_zeroes_sum_of_finite hfin
    (u6a_zeroes_rect_high_window_subset_nontrivial ht) φ

/-- The finite xi-divisor fiber contribution over Kadiri's nearby zeta-zero
window, retaining only the principal `1 / (s - ρ)` term. -/
noncomputable def u6aXiFiberNearbyPrincipalSum (t : ℝ) (s : ℂ) : ℂ :=
  let hfin := u6aNearbyZeroSet_finite (-1) 2 t
  ∑ ρ ∈ hfin.toFinset,
    ∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ,
      (1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p)

/-- Window-local cancellation statement for the near principal part: after
finite reindexing through xi divisor fibers, the xi near principal contribution
is exactly Kadiri's order-weighted nearby zeta-zero sum. -/
theorem u6aXiFiberNearbyPrincipalSum_eq_nearbyZeroPrincipalSum
    {t : ℝ} (s : ℂ) (ht : 2 ≤ |t|) :
    u6aXiFiberNearbyPrincipalSum t s =
      u6aNearbyZeroPrincipalSum (-1) 2 t s := by
  let hfin := u6aNearbyZeroSet_finite (-1) 2 t
  unfold u6aXiFiberNearbyPrincipalSum u6aNearbyZeroPrincipalSum
  simpa [hfin] using
    (u6aRiemannXi_fiberHighWindow_sum_eq_zeroes_sum_of_finite
      (t := t) hfin ht (fun ρ : ℂ => (1 : ℂ) / (s - ρ)))

/-- The finite convergence-factor residue from the local nearby zeta-zero
window.  This is the `+ 1 / ρ` part of the genus-one Hadamard zero term after
the principal contribution has been locally cancelled. -/
noncomputable def u6aNearbyZeroConvergenceFactorSum (t : ℝ) : ℂ :=
  riemannZeta.zeroes_sum (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1))
    fun ρ => (1 : ℂ) / ρ

/-- The finite xi-divisor fiber contribution over Kadiri's nearby window,
including the genus-one `+1/ρ` convergence factor. -/
noncomputable def u6aXiFiberNearbyHadamardSum (t : ℝ) (s : ℂ) : ℂ :=
  let hfin := u6aNearbyZeroSet_finite (-1) 2 t
  ∑ ρ ∈ hfin.toFinset,
    ∑ p ∈ Complex.Hadamard.divisorZeroIndex₀_fiberFinset (f := riemannXi) ρ,
      ((1 : ℂ) / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p)

/-- Finite near-window decomposition for the xi Hadamard zero contribution:
the local principal part is exactly Kadiri's nearby zeta-zero sum, and the only
local residue is the finite convergence-factor sum. -/
theorem u6aXiFiberNearbyHadamardSum_eq_nearbyZeroPrincipalSum_add_convergence
    {t : ℝ} (s : ℂ) (ht : 2 ≤ |t|) :
    u6aXiFiberNearbyHadamardSum t s =
      u6aNearbyZeroPrincipalSum (-1) 2 t s + u6aNearbyZeroConvergenceFactorSum t := by
  let hfin := u6aNearbyZeroSet_finite (-1) 2 t
  unfold u6aXiFiberNearbyHadamardSum u6aNearbyZeroPrincipalSum
    u6aNearbyZeroConvergenceFactorSum
  rw [u6aRiemannXi_fiberHighWindow_sum_eq_zeroes_sum_of_finite
    (t := t) hfin ht
    (fun ρ : ℂ => (1 : ℂ) / (s - ρ) + 1 / ρ)]
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ : ℂ => (1 : ℂ) / (s - ρ) + 1 / ρ) hfin,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ : ℂ => (1 : ℂ) / (s - ρ)) hfin,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ : ℂ => (1 : ℂ) / ρ) hfin]
  simp only [add_mul, Finset.sum_add_distrib]

/-- The finite convergence-factor residue in a high nearby window is bounded
by the order-weighted nearby zero count. -/
theorem norm_u6aNearbyZeroConvergenceFactorSum_le_nearbyZeroCount
    {t : ℝ} (ht : 2 ≤ |t|) :
    ‖u6aNearbyZeroConvergenceFactorSum t‖ ≤ u6aNearbyZeroCount (-1) 2 t := by
  classical
  let Z := riemannZeta.zeroes_rect (Set.uIcc (-1 : ℝ) 2) (Set.Icc (t - 1) (t + 1))
  let hfin : Z.Finite := u6aNearbyZeroSet_finite (-1) 2 t
  have hterm_le : ∀ ρ ∈ hfin.toFinset,
      ‖((1 : ℂ) / ρ) * (riemannZeta.order ρ : ℂ)‖ ≤
        (1 : ℝ) * (riemannZeta.order ρ : ℝ) := by
    intro ρ hρ
    have hρmem : ρ ∈ Z := hfin.mem_toFinset.mp hρ
    have hzero : riemannZeta ρ = 0 := hρmem.2.2
    have horder_nonneg : 0 ≤ (riemannZeta.order ρ : ℝ) :=
      u6a_zeta_zero_order_nonneg_of_zero hzero
    have him_abs_ge_one : (1 : ℝ) ≤ |ρ.im| := by
      rcases (le_abs.mp ht) with htpos | htneg
      · have hlow : (1 : ℝ) ≤ ρ.im := by
          have him_low := hρmem.2.1.1
          linarith
        exact hlow.trans (le_abs_self ρ.im)
      · have hneg_im : (1 : ℝ) ≤ -ρ.im := by
          have him_high := hρmem.2.1.2
          linarith
        exact hneg_im.trans (neg_le_abs ρ.im)
    have hnorm_ge_one : (1 : ℝ) ≤ ‖ρ‖ :=
      him_abs_ge_one.trans (Complex.abs_im_le_norm ρ)
    have hdiv_le_one : ‖(1 : ℂ) / ρ‖ ≤ 1 := by
      rw [norm_div, norm_one]
      calc
        1 / ‖ρ‖ ≤ 1 / (1 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) hnorm_ge_one
        _ = 1 := by norm_num
    have horder_norm :
        ‖(riemannZeta.order ρ : ℂ)‖ = (riemannZeta.order ρ : ℝ) := by
      rw [Complex.norm_intCast, abs_of_nonneg horder_nonneg]
    calc
      ‖((1 : ℂ) / ρ) * (riemannZeta.order ρ : ℂ)‖
          ≤ ‖(1 : ℂ) / ρ‖ * ‖(riemannZeta.order ρ : ℂ)‖ := norm_mul_le _ _
      _ ≤ (1 : ℝ) * (riemannZeta.order ρ : ℝ) := by
            rw [horder_norm]
            exact mul_le_mul_of_nonneg_right hdiv_le_one horder_nonneg
  unfold u6aNearbyZeroConvergenceFactorSum u6aNearbyZeroCount
  rw [riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun ρ : ℂ => (1 : ℂ) / ρ) hfin,
    riemannZeta.zeroes_sum_eq_finset_of_finite
      (fun _ : ℂ => (1 : ℝ)) hfin]
  calc
    ‖∑ ρ ∈ hfin.toFinset, ((1 : ℂ) / ρ) * (riemannZeta.order ρ : ℂ)‖
        ≤ ∑ ρ ∈ hfin.toFinset,
          ‖((1 : ℂ) / ρ) * (riemannZeta.order ρ : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ ρ ∈ hfin.toFinset, (1 : ℝ) * (riemannZeta.order ρ : ℝ) :=
          Finset.sum_le_sum hterm_le

/-- After local finite cancellation, the near-window xi Hadamard residue is
bounded by the order-weighted nearby zero count. -/
theorem norm_u6aXiFiberNearbyHadamardSum_sub_nearbyZeroPrincipalSum_le_nearbyZeroCount
    {t : ℝ} (s : ℂ) (ht : 2 ≤ |t|) :
    ‖u6aXiFiberNearbyHadamardSum t s - u6aNearbyZeroPrincipalSum (-1) 2 t s‖ ≤
      u6aNearbyZeroCount (-1) 2 t := by
  have hdecomp :=
    u6aXiFiberNearbyHadamardSum_eq_nearbyZeroPrincipalSum_add_convergence
      (t := t) (s := s) ht
  rw [hdecomp]
  have hdiff :
      u6aNearbyZeroPrincipalSum (-1) 2 t s + u6aNearbyZeroConvergenceFactorSum t -
          u6aNearbyZeroPrincipalSum (-1) 2 t s =
        u6aNearbyZeroConvergenceFactorSum t := by
    abel
  rw [hdiff]
  exact norm_u6aNearbyZeroConvergenceFactorSum_le_nearbyZeroCount (t := t) ht

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

private lemma u6a_re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq_apply]
  ring

private lemma u6a_im_div_two (z : ℂ) : (z / 2).im = z.im / 2 := by
  rw [Complex.div_im]
  norm_num [Complex.normSq_apply]
  ring

/-- PF-rung digamma bound for the argument appearing in the Hadamard remainder.
For high horizontal lines in the U6a strip, the `s / 2 + 1` digamma term is
`O(log |Im s|)`. -/
theorem u6a_digamma_shift_le_log_abs_im :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, s.re ∈ Set.uIcc (-1 : ℝ) 2 → Tₘᵢₙ ≤ |s.im| →
        ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤ C * Real.log |s.im| := by
  obtain ⟨Cψ, hCψ, hψ⟩ :=
    Complex.exists_norm_digamma_le_log (a := (1 / 2 : ℝ)) (b := 2) (by norm_num)
  refine ⟨Cψ, 4, hCψ, by norm_num, ?_⟩
  intro s hsre hsT
  have hsT4 : (4 : ℝ) ≤ |s.im| := by simpa using hsT
  have hsTpos : 0 < |s.im| := by linarith
  have hlog_nonneg : 0 ≤ Real.log |s.im| :=
    Real.log_nonneg (by linarith)
  have harg_re : (s / 2 + 1).re = s.re / 2 + 1 := by
    rw [Complex.add_re, Complex.one_re, u6a_re_div_two]
  have hsIcc : s.re ∈ Set.Icc (-1 : ℝ) 2 := by
    simpa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using hsre
  have harg_re_low : (1 / 2 : ℝ) ≤ (s / 2 + 1).re := by
    rw [harg_re]
    have hs_low : (-1 : ℝ) ≤ s.re := hsIcc.1
    linarith
  have harg_re_high : (s / 2 + 1).re ≤ 2 := by
    rw [harg_re]
    have hs_high : s.re ≤ (2 : ℝ) := hsIcc.2
    linarith
  have harg_im_le : |(s / 2 + 1).im| + 2 ≤ |s.im| := by
    have him : |(s / 2 + 1).im| = |s.im| / 2 := by
      rw [Complex.add_im, Complex.one_im, add_zero, u6a_im_div_two, abs_div]
      norm_num
    rw [him]
    linarith
  have hlog_arg_le : Real.log (|(s / 2 + 1).im| + 2) ≤ Real.log |s.im| :=
    Real.log_le_log (by positivity) harg_im_le
  have hψ_arg :
      ‖digamma (s / 2 + 1)‖ ≤ Cψ * Real.log |s.im| := by
    exact (hψ (s / 2 + 1) harg_re_low harg_re_high).trans
      (mul_le_mul_of_nonneg_left hlog_arg_le hCψ.le)
  have hmul :
      ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤
        (1 / 2 : ℝ) * (Cψ * Real.log |s.im|) := by
    calc
      ‖(1 / 2 : ℂ) * digamma (s / 2 + 1)‖
          ≤ ‖(1 / 2 : ℂ)‖ * ‖digamma (s / 2 + 1)‖ := norm_mul_le _ _
      _ = (1 / 2 : ℝ) * ‖digamma (s / 2 + 1)‖ := by norm_num
      _ ≤ (1 / 2 : ℝ) * (Cψ * Real.log |s.im|) := by
        exact mul_le_mul_of_nonneg_left hψ_arg (by norm_num)
  have htarget_nonneg : 0 ≤ Cψ * Real.log |s.im| := by positivity
  exact hmul.trans (by nlinarith)

private lemma u6a_one_le_log_abs_im_of_four_le {s : ℂ} (hsT : (4 : ℝ) ≤ |s.im|) :
    (1 : ℝ) ≤ Real.log |s.im| := by
  have hsTpos : 0 < |s.im| := by linarith
  apply le_of_lt
  rw [Real.lt_log_iff_exp_lt hsTpos]
  calc
    Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    _ < |s.im| := by norm_num; linarith

/-- The zeta pole contribution in the Hadamard remainder is `O(log |Im s|)`
on high horizontal lines. -/
theorem u6a_pole_term_le_log_abs_im :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, Tₘᵢₙ ≤ |s.im| →
        ‖(1 : ℂ) / (s - 1)‖ ≤ C * Real.log |s.im| := by
  refine ⟨1, 4, by norm_num, by norm_num, ?_⟩
  intro s hsT
  have hsT4 : (4 : ℝ) ≤ |s.im| := by simpa using hsT
  have hsTpos : 0 < |s.im| := by linarith
  have hsTge1 : (1 : ℝ) ≤ |s.im| := by linarith
  have hlog_ge_one : (1 : ℝ) ≤ Real.log |s.im| :=
    u6a_one_le_log_abs_im_of_four_le hsT4
  have him_le_norm : |s.im| ≤ ‖s - 1‖ := by
    have h := Complex.abs_im_le_norm (s - 1)
    simpa [Complex.sub_im, Complex.one_im] using h
  have hnorm_bound : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / |s.im| := by
    rw [norm_div, norm_one]
    exact one_div_le_one_div_of_le hsTpos him_le_norm
  have hinv_le_one : 1 / |s.im| ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hsTge1
  calc
    ‖(1 : ℂ) / (s - 1)‖ ≤ 1 / |s.im| := hnorm_bound
    _ ≤ 1 := hinv_le_one
    _ ≤ (1 : ℝ) * Real.log |s.im| := by simpa using hlog_ge_one

/-- The constant `log π` contribution in the Hadamard remainder is
`O(log |Im s|)` on high horizontal lines. -/
theorem u6a_log_pi_term_le_log_abs_im :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, Tₘᵢₙ ≤ |s.im| →
        ‖(1 / 2 : ℂ) * Real.log Real.pi‖ ≤ C * Real.log |s.im| := by
  let C : ℝ := ‖(1 / 2 : ℂ) * Real.log Real.pi‖ + 1
  refine ⟨C, 4, by dsimp [C]; positivity, by norm_num, ?_⟩
  intro s hsT
  have hsT4 : (4 : ℝ) ≤ |s.im| := by simpa using hsT
  have hlog_ge_one : (1 : ℝ) ≤ Real.log |s.im| :=
    u6a_one_le_log_abs_im_of_four_le hsT4
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  calc
    ‖(1 / 2 : ℂ) * Real.log Real.pi‖ ≤ C := by dsimp [C]; linarith
    _ ≤ C * Real.log |s.im| := by nlinarith

/-- The derivative of the degree-one Hadamard polynomial is a constant, hence
is `O(log |Im s|)` on high horizontal lines. -/
theorem u6a_polynomial_derivative_term_le_log_abs_im {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, Tₘᵢₙ ≤ |s.im| →
        ‖Polynomial.eval s P.derivative‖ ≤ C * Real.log |s.im| := by
  let C : ℝ := ‖Polynomial.eval 0 P.derivative‖ + 1
  refine ⟨C, 4, by dsimp [C]; positivity, by norm_num, ?_⟩
  intro s hsT
  have hsT4 : (4 : ℝ) ≤ |s.im| := by simpa using hsT
  have hlog_ge_one : (1 : ℝ) ≤ Real.log |s.im| :=
    u6a_one_le_log_abs_im_of_four_le hsT4
  have hC_nonneg : 0 ≤ C := by dsimp [C]; positivity
  calc
    ‖Polynomial.eval s P.derivative‖ = ‖Polynomial.eval 0 P.derivative‖ := by
      rw [Polynomial.eval_derivative_eq_eval_derivative_zero_of_degree_le_one hP]
    _ ≤ C := by dsimp [C]; linarith
    _ ≤ C * Real.log |s.im| := by nlinarith

/-- The non-zero-sum terms in the Hadamard remainder are logarithmically
bounded on high horizontal lines in the U6a strip. -/
theorem u6a_hadamard_elementary_terms_le_log_abs_im {P : Polynomial ℂ}
    (hP : P.degree ≤ 1) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, s.re ∈ Set.uIcc (-1 : ℝ) 2 → Tₘᵢₙ ≤ |s.im| →
        ‖Polynomial.eval s P.derivative
          - 1 / (s - 1)
          + (1 / 2 : ℂ) * Real.log Real.pi
          - (1 / 2 : ℂ) * digamma (s / 2 + 1)‖ ≤
            C * Real.log |s.im| := by
  obtain ⟨CA, TA, hCA, hTA4, hA⟩ := u6a_polynomial_derivative_term_le_log_abs_im hP
  obtain ⟨CD, TD, hCD, hTD4, hD⟩ := u6a_pole_term_le_log_abs_im
  obtain ⟨CE, TE, hCE, hTE4, hE⟩ := u6a_log_pi_term_le_log_abs_im
  obtain ⟨CF, TF, hCF, hTF4, hF⟩ := u6a_digamma_shift_le_log_abs_im
  let C : ℝ := CA + CD + CE + CF
  let T : ℝ := max (max TA TD) (max TE TF)
  refine ⟨C, T, by dsimp [C]; positivity, ?_, ?_⟩
  · dsimp [T]
    exact le_max_of_le_left (le_max_of_le_left hTA4)
  intro s hsre hsT
  have hTA : TA ≤ |s.im| := by
    exact (le_max_left TA TD).trans (le_max_left (max TA TD) (max TE TF)) |>.trans hsT
  have hTD : TD ≤ |s.im| := by
    exact (le_max_right TA TD).trans (le_max_left (max TA TD) (max TE TF)) |>.trans hsT
  have hTE : TE ≤ |s.im| := by
    exact (le_max_left TE TF).trans (le_max_right (max TA TD) (max TE TF)) |>.trans hsT
  have hTF : TF ≤ |s.im| := by
    exact (le_max_right TE TF).trans (le_max_right (max TA TD) (max TE TF)) |>.trans hsT
  have hT4 : (4 : ℝ) ≤ |s.im| := by
    exact hTA4.trans hTA
  have hlog_nonneg : 0 ≤ Real.log |s.im| :=
    Real.log_nonneg (by linarith)
  have hAb := hA s hTA
  have hDb := hD s hTD
  have hEb := hE s hTE
  have hFb := hF s hsre hTF
  let A : ℂ := Polynomial.eval s P.derivative
  let D : ℂ := (1 : ℂ) / (s - 1)
  let E : ℂ := (1 / 2 : ℂ) * Real.log Real.pi
  let F : ℂ := (1 / 2 : ℂ) * digamma (s / 2 + 1)
  have htri : ‖A - D + E - F‖ ≤ ‖A‖ + ‖D‖ + ‖E‖ + ‖F‖ := by
    have h1 : ‖A - D + E - F‖ ≤ ‖A - D + E‖ + ‖F‖ := by
      simpa [sub_eq_add_neg, add_assoc, norm_neg] using norm_add_le (A - D + E) (-F)
    have h2 : ‖A - D + E‖ ≤ ‖A - D‖ + ‖E‖ := norm_add_le (A - D) E
    have h3 : ‖A - D‖ ≤ ‖A‖ + ‖D‖ := norm_sub_le A D
    calc
      ‖A - D + E - F‖ ≤ ‖A - D + E‖ + ‖F‖ := h1
      _ ≤ (‖A - D‖ + ‖E‖) + ‖F‖ := by
        nlinarith
      _ ≤ ((‖A‖ + ‖D‖) + ‖E‖) + ‖F‖ := by
        nlinarith
      _ = ‖A‖ + ‖D‖ + ‖E‖ + ‖F‖ := by ring
  have hAb' : ‖A‖ ≤ CA * Real.log |s.im| := by simpa [A] using hAb
  have hDb' : ‖D‖ ≤ CD * Real.log |s.im| := by simpa [D] using hDb
  have hEb' : ‖E‖ ≤ CE * Real.log |s.im| := by simpa [E] using hEb
  have hFb' : ‖F‖ ≤ CF * Real.log |s.im| := by simpa [F] using hFb
  calc
    ‖Polynomial.eval s P.derivative
          - 1 / (s - 1)
          + (1 / 2 : ℂ) * Real.log Real.pi
          - (1 / 2 : ℂ) * digamma (s / 2 + 1)‖
        = ‖A - D + E - F‖ := by rfl
    _ ≤ ‖A‖ + ‖D‖ + ‖E‖ + ‖F‖ := htri
    _ ≤ CA * Real.log |s.im| + CD * Real.log |s.im| +
        CE * Real.log |s.im| + CF * Real.log |s.im| := by
          nlinarith
    _ = C * Real.log |s.im| := by
          dsimp [C]
          ring

/-- The single remaining analytic zero-sum estimate for the PF remainder
route.  This is the term where the xi divisor indexing, the Kadiri nearby-zero
sum, and the weighted tail/local-count arguments must be reconciled. -/
def U6aZeroSumRemainderBoundHypothesis (σ₁ σ₂ C Tₘᵢₙ : ℝ) : Prop :=
  0 < C ∧ ∀ s : ℂ, s.re ∈ Set.uIcc σ₁ σ₂ → Tₘᵢₙ ≤ |s.im| → 3 ≤ |s.im| →
    ‖u6aXiHadamardZeroSum s - u6aNearbyZeroPrincipalSum σ₁ σ₂ s.im s‖ ≤
      C * Real.log |s.im|

/-- All non-zero-sum PF-rung estimates compose with the isolated zero-sum
estimate to give the Hadamard remainder bound on the U6a strip. -/
theorem U6aHadamardRemainderBoundHypothesis_of_zeroSum
    {P : Polynomial ℂ} (hP : P.degree ≤ 1) {Czero Tzero : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      U6aHadamardRemainderBoundHypothesis (-1) 2 C Tₘᵢₙ P := by
  obtain ⟨Celem, Telem, hCelem, hTelem4, helem⟩ :=
    u6a_hadamard_elementary_terms_le_log_abs_im hP
  let C : ℝ := Celem + Czero
  let T : ℝ := max Telem Tzero
  have hCpos : 0 < C := by
    dsimp [C]
    linarith [hCelem, hZero.1]
  refine ⟨C, T, hCpos, ?_, ?_⟩
  · dsimp [T]
    exact hTelem4.trans (le_max_left Telem Tzero)
  unfold U6aHadamardRemainderBoundHypothesis
  refine ⟨hCpos, ?_⟩
  intro s hsre hsT hT3
  have hTelem : Telem ≤ |s.im| := (le_max_left Telem Tzero).trans hsT
  have hTzero : Tzero ≤ |s.im| := (le_max_right Telem Tzero).trans hsT
  have hlog_nonneg : 0 ≤ Real.log |s.im| :=
    Real.log_nonneg (by linarith)
  have he := helem s hsre hTelem
  have hz := hZero.2 s hsre hTzero hT3
  let E : ℂ :=
    Polynomial.eval s P.derivative
      - 1 / (s - 1)
      + (1 / 2 : ℂ) * Real.log Real.pi
      - (1 / 2 : ℂ) * digamma (s / 2 + 1)
  let Z : ℂ := u6aXiHadamardZeroSum s - u6aNearbyZeroPrincipalSum (-1) 2 s.im s
  have heE : ‖E‖ ≤ Celem * Real.log |s.im| := by
    simpa [E] using he
  have hzZ : ‖Z‖ ≤ Czero * Real.log |s.im| := by
    simpa [Z] using hz
  have hrem_eq :
      u6aHadamardPartialFractionRemainder (-1) 2 s.im P s = E + Z := by
    unfold u6aHadamardPartialFractionRemainder
    dsimp [E, Z]
    ring
  calc
    ‖u6aHadamardPartialFractionRemainder (-1) 2 s.im P s‖
        = ‖E + Z‖ := by rw [hrem_eq]
    _ ≤ ‖E‖ + ‖Z‖ := norm_add_le E Z
    _ ≤ Celem * Real.log |s.im| + Czero * Real.log |s.im| := by
          nlinarith
    _ = C * Real.log |s.im| := by
          dsimp [C]
          ring

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

/-- Pointwise PF wrapper from the isolated zero-sum remainder estimate.  This
is the consumer shape needed on selected horizontal lines: the Hadamard
factorization and elementary non-zero-sum estimates are discharged once, while
the local legality conditions remain pointwise. -/
theorem exists_u6aPartialFractionPointwise_of_zeroSum
    {Czero Tzero : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ s : ℂ, s.re ∈ Set.uIcc (-1 : ℝ) 2 → Tₘᵢₙ ≤ |s.im| →
        (∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) →
        s ≠ 0 → s ≠ 1 →
        (∀ m : ℕ, s / 2 + 1 ≠ -m) →
        zetaGammaFactor s ≠ 0 →
        riemannZeta s ≠ 0 →
          ‖deriv riemannZeta s / riemannZeta s -
              u6aNearbyZeroPrincipalSum (-1) 2 s.im s‖ ≤ C * Real.log |s.im| := by
  obtain ⟨P, hPdeg, hfac⟩ := riemannXi_hadamard_factorization_no_monomial
  obtain ⟨C, Tₘᵢₙ, hC, hT4, hR⟩ :=
    U6aHadamardRemainderBoundHypothesis_of_zeroSum (P := P) hPdeg hZero
  refine ⟨C, Tₘᵢₙ, hC, hT4, ?_⟩
  intro s hsre hsT hz hs0 hs1 hΓdiff hΓ hζ
  have hT3 : 3 ≤ |s.im| := by linarith
  exact u6aPartialFractionApproximation_at_of_hadamardRemainderBound
    (P := P) (σ₁ := (-1 : ℝ)) (σ₂ := 2) (C := C) (Tₘᵢₙ := Tₘᵢₙ)
    (s := s) hfac hz hs0 hs1 hΓdiff hΓ hζ hR hsre hsT hT3

/-- Local Hadamard legality needed only on a selected horizontal line.  This
keeps the PF route pointwise, rather than requiring a global partial-fraction
hypothesis over the whole strip. -/
def U6aHadamardLegalityOnHorizontal (T : ℝ) : Prop :=
  ∀ x ∈ Set.uIcc (-1 : ℝ) 2, ∀ t : ℝ, |t| = T →
    let s : ℂ := (x : ℂ) + t * I
    (∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) ∧
    s ≠ 0 ∧ s ≠ 1 ∧
    (∀ m : ℕ, s / 2 + 1 ≠ -m) ∧
    zetaGammaFactor s ≠ 0 ∧
    riemannZeta s ≠ 0

private lemma u6a_gamma_half_avoid_neg_nat_of_shift {s : ℂ}
    (hs0 : s ≠ 0) (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  cases m with
  | zero =>
      apply hs0
      rw [show s = 2 * (s / 2) by ring, hm]
      ring
  | succ m =>
      have hbad : s / 2 + 1 = -(m : ℂ) := by
        rw [hm]
        norm_num
      exact hΓdiff m hbad

private lemma u6a_completedZetaFactor_eq_riemannXi_of_shift {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    completedZetaFactor s = riemannXi s := by
  have hΓhalf : Gamma (s / 2) ≠ 0 :=
    Gamma_ne_zero (u6a_gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff)
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, u6aZetaPiFactor_eq_cpow,
    riemannXi_eq_mul_completedRiemannZeta hs0 hs1,
    hGamma, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma u6a_riemannXi_ne_zero_of_zeta_ne_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0) (hζ : riemannZeta s ≠ 0) :
    riemannXi s ≠ 0 := by
  have heq := u6a_completedZetaFactor_eq_riemannXi_of_shift hs0 hs1 hΓdiff
  have hpole : zetaPoleFactor s ≠ 0 := by
    simp [zetaPoleFactor, sub_ne_zero, hs1]
  have hpi : zetaPiFactor s ≠ 0 := by
    simp [zetaPiFactor]
  have hcomp : completedZetaFactor s ≠ 0 := by
    unfold completedZetaFactor
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hpole hpi) hΓ) hζ
  exact fun hxi => hcomp (by rwa [heq])

private lemma u6a_riemannXi_avoids_divisorZeroIndex₀_of_ne_zero {s : ℂ}
    (hxi : riemannXi s ≠ 0) :
    ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p := by
  intro p hs
  have hmero : MeromorphicOn riemannXi Set.univ := fun x _ =>
    (Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi x).meromorphicAt
  have han : AnalyticAt ℂ riemannXi s :=
    Differentiable.analyticAt (f := riemannXi) differentiable_riemannXi s
  have hdiv_s : (MeromorphicOn.divisor riemannXi Set.univ) s = 0 := by
    rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ s)]
    rw [han.meromorphicOrderAt_eq]
    have horder : analyticOrderAt riemannXi s = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr hxi)
    simp [horder]
  have hdiv_val : (MeromorphicOn.divisor riemannXi Set.univ)
      (Complex.Hadamard.divisorZeroIndex₀_val p) = 0 := by
    rw [← hs]
    exact hdiv_s
  exact Complex.Hadamard.divisorZeroIndex₀_val_mem_divisor_support p hdiv_val

theorem U6aHadamardLegalityOnHorizontal_of_zeroFree {T : ℝ}
    (hT : 3 ≤ T) (hfree : horizontalSegmentZeroFree (-1) 2 T) :
    U6aHadamardLegalityOnHorizontal T := by
  intro x hx t htabs
  let s : ℂ := (x : ℂ) + t * I
  have hTnonneg : 0 ≤ T := by linarith
  have htcase : t = T ∨ t = -T := (abs_eq hTnonneg).mp htabs
  have hsre : s.re ∈ Set.uIcc (-1 : ℝ) 2 := by
    simpa [s] using hx
  have hsim : s.im = t := by simp [s]
  have hζ1 : riemannZeta s ≠ 0 ∧ s ≠ 1 := by
    rcases htcase with rfl | rfl
    · exact hfree.1 s hsre (by simp [s])
    · exact hfree.2 s hsre (by simp [s])
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    rw [ht0, abs_zero] at htabs
    linarith
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    have ht0 : t = 0 := by
      simpa [s] using him
    exact ht_ne_zero ht0
  have hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m := by
    intro m hm
    have him := congrArg Complex.im hm
    have ht0 : t = 0 := by
      have hhalf : t / 2 = 0 := by
        simpa [s] using him
      linarith
    exact ht_ne_zero ht0
  have hΓ : zetaGammaFactor s ≠ 0 := by
    unfold zetaGammaFactor
    exact Gamma_ne_zero hΓdiff
  have hxi : riemannXi s ≠ 0 :=
    u6a_riemannXi_ne_zero_of_zeta_ne_zero hs0 hζ1.2 hΓdiff hΓ hζ1.1
  exact ⟨u6a_riemannXi_avoids_divisorZeroIndex₀_of_ne_zero hxi,
    hs0, hζ1.2, hΓdiff, hΓ, hζ1.1⟩

/-- Fixed-height horizontal consumer for the zero-sum PF route.  A zero-sum
Hadamard remainder estimate supplies the PF approximation pointwise on the
selected line; a reciprocal-zero bound then gives the lane's horizontal
`log²` predicate. -/
theorem exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound
    {Czero Tzero Crec : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero)
    (hCrec : 0 < Crec) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ T η : ℝ, Tₘᵢₙ ≤ T → 3 ≤ T →
        horizontalSegmentZeroGap (-1) 2 T η →
        U6aHadamardLegalityOnHorizontal T →
        (∀ t : ℝ, |t| = T →
          u6aReciprocalZeroSum (-1) 2 t ≤ Crec * Real.log T ^ 2) →
          horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Cpf, Tpf, hCpf, hTpf4, hPF⟩ :=
    exists_u6aPartialFractionPointwise_of_zeroSum hZero
  refine ⟨Cpf + Crec, Tpf, by nlinarith, hTpf4, ?_⟩
  intro T η hTpf hT3 hgap hlegal hrec
  have hTpos : 0 < T := by linarith
  refine ⟨horizontalSegmentZeroFree_of_zeroGap hTpos hgap, ?_⟩
  intro x hx t htabs
  let s : ℂ := (x : ℂ) + t * I
  have hsim : s.im = t := by simp [s]
  have hsre : s.re ∈ Set.uIcc (-1 : ℝ) 2 := by simpa [s] using hx
  have hT_abs_s : |s.im| = T := by simpa [hsim] using htabs
  have hpfT : Tpf ≤ |s.im| := by rw [hT_abs_s]; exact hTpf
  rcases hlegal x hx t htabs with ⟨hz, hs0, hs1, hΓdiff, hΓ, hζ⟩
  have hA := hPF s hsre hpfT hz hs0 hs1 hΓdiff hΓ hζ
  have htcase : t = T ∨ t = -T :=
    (abs_eq (by linarith : (0 : ℝ) ≤ T)).mp htabs
  have hnear := norm_u6aNearbyZeroPrincipalSum_le_reciprocalZeroSum_of_zeroGap
    (σ₁ := (-1 : ℝ)) (σ₂ := 2) (T := T) (η := η) (t := t) (s := s)
    hgap htcase hsim
  have hnear2 :
      ‖u6aNearbyZeroPrincipalSum (-1) 2 t s‖ ≤ Crec * Real.log T ^ 2 :=
    hnear.trans (hrec t htabs)
  have hlog_le_sq : Real.log T ≤ Real.log T ^ 2 :=
    u6a_log_le_log_sq_of_three_le hT3
  calc
    ‖deriv riemannZeta ((x : ℂ) + t * I) / riemannZeta ((x : ℂ) + t * I)‖
        = ‖(deriv riemannZeta s / riemannZeta s -
              u6aNearbyZeroPrincipalSum (-1) 2 t s) +
            u6aNearbyZeroPrincipalSum (-1) 2 t s‖ := by
          simp [s]
    _ ≤ ‖deriv riemannZeta s / riemannZeta s -
            u6aNearbyZeroPrincipalSum (-1) 2 t s‖ +
          ‖u6aNearbyZeroPrincipalSum (-1) 2 t s‖ := norm_add_le _ _
    _ ≤ Cpf * Real.log T + Crec * Real.log T ^ 2 := by
          have hA' :
              ‖deriv riemannZeta s / riemannZeta s -
                  u6aNearbyZeroPrincipalSum (-1) 2 t s‖ ≤ Cpf * Real.log T := by
            simpa [hsim, htabs] using hA
          nlinarith
    _ ≤ Cpf * Real.log T ^ 2 + Crec * Real.log T ^ 2 := by
          exact add_le_add (mul_le_mul_of_nonneg_left hlog_le_sq hCpf.le) le_rfl
    _ = (Cpf + Crec) * Real.log T ^ 2 := by ring

/-- Fixed-height zero-sum PF consumer with all local Hadamard legality
discharged from the zero-gap condition. -/
theorem exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound_of_zeroGap
    {Czero Tzero Crec : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero)
    (hCrec : 0 < Crec) :
    ∃ C Tₘᵢₙ : ℝ, 0 < C ∧ 4 ≤ Tₘᵢₙ ∧
      ∀ T η : ℝ, Tₘᵢₙ ≤ T → 3 ≤ T →
        horizontalSegmentZeroGap (-1) 2 T η →
        (∀ t : ℝ, |t| = T →
          u6aReciprocalZeroSum (-1) 2 t ≤ Crec * Real.log T ^ 2) →
          horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨C, Tₘᵢₙ, hC, hT4, hmain⟩ :=
    exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound hZero hCrec
  refine ⟨C, Tₘᵢₙ, hC, hT4, ?_⟩
  intro T η hTmin hT3 hgap hrec
  have hTpos : 0 < T := by linarith
  have hlegal : U6aHadamardLegalityOnHorizontal T :=
    U6aHadamardLegalityOnHorizontal_of_zeroFree hT3
      (horizontalSegmentZeroFree_of_zeroGap hTpos hgap)
  exact hmain T η hTmin hT3 hgap hlegal hrec

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
    (intervalIntegrable_u6aReciprocalZeroSum_indicator hX hδ)
    (intervalIntegrable_u6aAveragedSelectionBound_indicator hX hδ) hAvg

/-- Averaged selector in the actual U6a strip, with the safe-set measure
hypothesis discharged by the crude-majorant geometric count source. -/
theorem exists_height_with_small_reciprocalZeroSum_of_crude_geometric_average :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X δ M : ℝ,
      0 < X → 0 < δ →
      2 * X + δ < (2 : ℝ) ^ (k + 1) →
      2 * δ * (C * 3 ^ k + D) ≤ X / 2 →
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X δ).indicator
            (u6aReciprocalZeroSum (-1) 2) t ∂volume) ≤
        ∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X δ).indicator
            (fun _ : ℝ => u6aAveragedSelectionBound X δ M) t ∂volume →
      ∃ T : ℝ, T ∈ u6aSafeHeightSet (-1) 2 X δ ∧
        u6aReciprocalZeroSum (-1) 2 T ≤ u6aAveragedSelectionBound X δ M := by
  obtain ⟨C, D, hC, hD, hEpos⟩ :=
    u6aSafeHeightSet_restrict_measure_ne_zero_of_crude_geometric
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X δ M hX hδ hT hsmall hAvg
  exact exists_height_with_small_reciprocalZeroSum_of_indicator_average hX
    (hEpos k X δ hX hδ hT hsmall)
    (intervalIntegrable_u6aReciprocalZeroSum_indicator hX hδ)
    (intervalIntegrable_u6aAveragedSelectionBound_indicator hX hδ) hAvg

/-- Averaged selector in the actual U6a strip with the explicit crude-majorant
`δ_X` choice. -/
theorem exists_height_with_small_reciprocalZeroSum_of_crude_delta_average :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X M : ℝ,
      0 < X →
      2 * X + u6aCrudeDelta C D X k < (2 : ℝ) ^ (k + 1) →
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k)).indicator
            (u6aReciprocalZeroSum (-1) 2) t ∂volume) ≤
        ∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k)).indicator
            (fun _ : ℝ => u6aAveragedSelectionBound X (u6aCrudeDelta C D X k) M)
              t ∂volume →
      ∃ T : ℝ, T ∈ u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k) ∧
        u6aReciprocalZeroSum (-1) 2 T ≤
          u6aAveragedSelectionBound X (u6aCrudeDelta C D X k) M := by
  obtain ⟨C, D, hC, hD, hsel⟩ :=
    exists_height_with_small_reciprocalZeroSum_of_crude_geometric_average
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X M hX hT hAvg
  exact hsel k X (u6aCrudeDelta C D X k) M hX
    (u6aCrudeDelta_pos k hX hC.le hD) hT
    (u6aCrudeDelta_small k hX hC.le hD) hAvg

/-- Averaged selector in the actual U6a strip with the safe-set measure and
fixed-window integral hypotheses discharged from the crude majorants. -/
theorem exists_height_with_small_reciprocalZeroSum_of_crude_delta :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ k : ℕ, ∀ X : ℝ,
      0 < X →
      2 * X + 2 < (2 : ℝ) ^ (k + 1) →
      ∃ T : ℝ, T ∈ u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k) ∧
        u6aReciprocalZeroSum (-1) 2 T ≤
          u6aAveragedSelectionBound X (u6aCrudeDelta C D X k) (C * 3 ^ k + D) := by
  obtain ⟨Cbad, Dbad, hCbad, hDbad, hbad⟩ :=
    u6aBadHeightFinset_card_le_crude_geometric
  obtain ⟨Cmass, Dmass, hCmass, hDmass, hmass⟩ :=
    u6aFixedWindowZeroMass_le_crude_geometric
  let C : ℝ := max Cbad Cmass
  let D : ℝ := Dbad + Dmass
  have hC : 0 < C := by
    exact lt_of_lt_of_le hCbad (by dsimp [C]; exact le_max_left Cbad Cmass)
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith
  refine ⟨C, D, hC, hD, ?_⟩
  intro k X hX hT
  let δ : ℝ := u6aCrudeDelta C D X k
  have hδ : 0 < δ := by
    dsimp [δ]
    exact u6aCrudeDelta_pos k hX hC.le hD
  have hδ_le_one : δ ≤ 1 := by
    dsimp [δ]
    unfold u6aCrudeDelta
    exact min_le_left _ _
  have hδ2 : δ ≤ 2 := hδ_le_one.trans (by norm_num)
  have hTδ : 2 * X + δ < (2 : ℝ) ^ (k + 1) := by
    have hle : 2 * X + δ ≤ 2 * X + 2 := by linarith
    exact lt_of_le_of_lt hle hT
  have hpow_nonneg : 0 ≤ (3 : ℝ) ^ k := by positivity
  have hbad_bound_constants :
      Cbad * 3 ^ k + Dbad ≤ C * 3 ^ k + D := by
    have hCbad_le : Cbad ≤ C := by
      dsimp [C]
      exact le_max_left Cbad Cmass
    have hmul : Cbad * 3 ^ k ≤ C * 3 ^ k :=
      mul_le_mul_of_nonneg_right hCbad_le hpow_nonneg
    have hDle : Dbad ≤ D := by
      dsimp [D]
      linarith [hDmass]
    linarith
  have hbad_card :
      ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ) ≤ C * 3 ^ k + D :=
    (hbad k X δ hTδ).trans hbad_bound_constants
  have hsmall_bad :
      2 * δ * ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ) ≤ X / 2 := by
    have hcoef : 0 ≤ 2 * δ := by positivity
    calc
      2 * δ * ((u6aBadHeightFinset (-1) 2 X δ).card : ℝ)
          ≤ 2 * δ * (C * 3 ^ k + D) := by
            exact mul_le_mul_of_nonneg_left hbad_card hcoef
      _ ≤ X / 2 := u6aCrudeDelta_small k hX hC.le hD
  have hmass_bound_constants :
      Cmass * 3 ^ k + Dmass ≤ C * 3 ^ k + D := by
    have hCmass_le : Cmass ≤ C := by
      dsimp [C]
      exact le_max_right Cbad Cmass
    have hmul : Cmass * 3 ^ k ≤ C * 3 ^ k :=
      mul_le_mul_of_nonneg_right hCmass_le hpow_nonneg
    have hDle : Dmass ≤ D := by
      dsimp [D]
      linarith [hDbad]
    linarith
  have hMass : u6aFixedWindowZeroMass (-1) 2 X ≤ C * 3 ^ k + D :=
    (hmass k X hT).trans hmass_bound_constants
  have hMeasure :
      ENNReal.ofReal (X / 2) ≤
        (volume.restrict (Set.Ioc X (2 * X)))
          (u6aSafeHeightSet (-1) 2 X δ) :=
    u6aSafeHeightSet_measure_ge_of_badHeightFinset hX hδ hsmall_bad
  have hAvg :
      (∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X δ).indicator
            (u6aReciprocalZeroSum (-1) 2) t ∂volume) ≤
        ∫ t in X..(2 * X),
          (u6aSafeHeightSet (-1) 2 X δ).indicator
            (fun _ : ℝ => u6aAveragedSelectionBound X δ (C * 3 ^ k + D)) t ∂volume :=
    integral_u6aReciprocalZeroSum_indicator_le_averagedSelectionBound_indicator_of_fixedWindowMass
      (σ₁ := (-1 : ℝ)) (σ₂ := 2) (X := X) (δ := δ) (M := C * 3 ^ k + D)
      hX hδ hδ2 hMass hMeasure
  simpa [δ] using
    exists_height_with_small_reciprocalZeroSum_of_badHeightFinset_average
      (σ₁ := (-1 : ℝ)) (σ₂ := 2) (X := X) (δ := δ) (M := C * 3 ^ k + D)
      hX hδ hsmall_bad hAvg

/-- Cofinal form of the unconditional averaged selector in the U6a strip.  For
every lower height threshold, one can choose a dyadic scale and a safe height in
that scale whose reciprocal zero sum is bounded by the averaged-selection
constant. -/
theorem exists_arbitrarily_large_height_with_small_reciprocalZeroSum_of_crude_delta :
    ∃ C D : ℝ, 0 < C ∧ 0 ≤ D ∧ ∀ T₀ : ℝ, ∃ k : ℕ, ∃ X T : ℝ,
      T₀ ≤ T ∧ 0 < X ∧
      2 * X + 2 < (2 : ℝ) ^ (k + 1) ∧
      T ∈ u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k) ∧
      u6aReciprocalZeroSum (-1) 2 T ≤
        u6aAveragedSelectionBound X (u6aCrudeDelta C D X k) (C * 3 ^ k + D) := by
  obtain ⟨C, D, hC, hD, hsel⟩ :=
    exists_height_with_small_reciprocalZeroSum_of_crude_delta
  refine ⟨C, D, hC, hD, ?_⟩
  intro T₀
  let X : ℝ := max T₀ 1
  have hX : 0 < X := by
    dsimp [X]
    exact lt_of_lt_of_le zero_lt_one (le_max_right T₀ 1)
  have hT₀X : T₀ ≤ X := by
    dsimp [X]
    exact le_max_left T₀ 1
  obtain ⟨k, hk⟩ := Real.exists_nat_le_two_pow (2 * (2 * X + 2))
  have hk_bound : 2 * (2 * X + 2) ≤ (2 : ℝ) ^ k := hk k le_rfl
  have hscale_lt : 2 * X + 2 < (2 : ℝ) ^ (k + 1) := by
    have hlt_double : 2 * X + 2 < 2 * (2 * X + 2) := by linarith
    have hpow_succ : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      nlinarith [show 0 ≤ (2 : ℝ) ^ k by positivity]
    exact hlt_double.trans_le (hk_bound.trans hpow_succ)
  obtain ⟨T, hTmem, hrec⟩ := hsel k X hX hscale_lt
  have hT₀T : T₀ ≤ T := by
    have hXT : X < T := hTmem.1.1
    exact hT₀X.trans hXT.le
  exact ⟨k, X, T, hT₀T, hX, hscale_lt, hTmem, hrec⟩

/-- The remaining comparison needed to turn the averaged selector's boxed
reciprocal-zero bound into the lane's `log² T` horizontal estimate.

This is intentionally separated from the selector: the current crude
polynomial count proves cofinal safe heights, but not this sharper
log-squared comparison. -/
def U6aAveragedSelectionLogSqComparisonHypothesis (C D Crec : ℝ) : Prop :=
  0 < Crec ∧ ∀ k : ℕ, ∀ X T : ℝ,
    0 < X →
    3 ≤ T →
    T ∈ u6aSafeHeightSet (-1) 2 X (u6aCrudeDelta C D X k) →
    2 * X + 2 < (2 : ℝ) ^ (k + 1) →
      u6aAveragedSelectionBound X (u6aCrudeDelta C D X k) (C * 3 ^ k + D) ≤
        Crec * Real.log T ^ 2

/-- Consumer-shape U6a composition: the proved cofinal averaged selector plus
a partial-fraction approximation and the one remaining averaged-bound
comparison give cofinally many horizontal segments with the desired
`log² T` bound in the Kadiri strip `[-1, 2]`. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_of_partialFraction_and_averagedComparison
    {Cpf Tpf : ℝ}
    (hPF : U6aPartialFractionApproximationHypothesis (-1) 2 Cpf Tpf)
    (hAvgCmp : ∀ C D : ℝ, 0 < C → 0 ≤ D →
      ∃ Crec : ℝ, U6aAveragedSelectionLogSqComparisonHypothesis C D Crec) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Csel, Dsel, hCsel, hDsel, hsel⟩ :=
    exists_arbitrarily_large_height_with_small_reciprocalZeroSum_of_crude_delta
  obtain ⟨Crec, hCmp⟩ := hAvgCmp Csel Dsel hCsel hDsel
  refine ⟨Cpf + Crec, by nlinarith [hPF.1, hCmp.1], ?_⟩
  intro T₀
  let Tbase : ℝ := max (max T₀ Tpf) 3
  obtain ⟨k, X, T, hTbase, hX, hscale, hTmem, hrec⟩ := hsel Tbase
  have hT₀ : T₀ ≤ T := by
    exact (le_max_left T₀ Tpf).trans (le_max_left (max T₀ Tpf) 3) |>.trans hTbase
  have hTpf : Tpf ≤ T := by
    exact (le_max_right T₀ Tpf).trans (le_max_left (max T₀ Tpf) 3) |>.trans hTbase
  have hT3 : 3 ≤ T := by
    exact (le_max_right (max T₀ Tpf) 3).trans hTbase
  have havg_le :
      u6aAveragedSelectionBound X (u6aCrudeDelta Csel Dsel X k)
          (Csel * 3 ^ k + Dsel) ≤ Crec * Real.log T ^ 2 :=
    hCmp.2 k X T hX hT3 hTmem hscale
  exact ⟨T, hT₀, hT3,
    horizontalSegmentLogDerivBound_of_partialFraction_and_averagedSelection
      (Cpf := Cpf) (Tpf := Tpf) (Crec := Crec) (X := X)
      (δ := u6aCrudeDelta Csel Dsel X k) (M := Csel * 3 ^ k + Dsel)
      (T := T) hPF hT3 hTpf hTmem hrec havg_le⟩

/-- Cofinal U6a composition for the zero-sum PF route.  This avoids the
global partial-fraction hypothesis: the zero-sum Hadamard remainder estimate
is consumed only on the selected horizontal lines. -/
theorem exists_arbitrarily_large_horizontalSegmentLogDerivBound_of_zeroSum_and_averagedComparison
    {Czero Tzero : ℝ}
    (hZero : U6aZeroSumRemainderBoundHypothesis (-1) 2 Czero Tzero)
    (hAvgCmp : ∀ C D : ℝ, 0 < C → 0 ≤ D →
      ∃ Crec : ℝ, U6aAveragedSelectionLogSqComparisonHypothesis C D Crec) :
    ∃ C : ℝ, 0 < C ∧ ∀ T₀ : ℝ, ∃ T : ℝ, T₀ ≤ T ∧ 3 ≤ T ∧
      horizontalSegmentLogDerivBound (-1) 2 T C := by
  obtain ⟨Csel, Dsel, hCsel, hDsel, hsel⟩ :=
    exists_arbitrarily_large_height_with_small_reciprocalZeroSum_of_crude_delta
  obtain ⟨Crec, hCmp⟩ := hAvgCmp Csel Dsel hCsel hDsel
  obtain ⟨Cout, Tpf, hCout, _hTpf4, hmain⟩ :=
    exists_horizontalSegmentLogDerivBound_of_zeroSum_and_reciprocalBound_of_zeroGap
      hZero hCmp.1
  refine ⟨Cout, hCout, ?_⟩
  intro T₀
  let Tbase : ℝ := max (max T₀ Tpf) 3
  obtain ⟨k, X, T, hTbase, hX, hscale, hTmem, hrecTop⟩ := hsel Tbase
  have hT₀ : T₀ ≤ T := by
    exact (le_max_left T₀ Tpf).trans (le_max_left (max T₀ Tpf) 3) |>.trans hTbase
  have hTpf : Tpf ≤ T := by
    exact (le_max_right T₀ Tpf).trans (le_max_left (max T₀ Tpf) 3) |>.trans hTbase
  have hT3 : 3 ≤ T := by
    exact (le_max_right (max T₀ Tpf) 3).trans hTbase
  have havg_le :
      u6aAveragedSelectionBound X (u6aCrudeDelta Csel Dsel X k)
          (Csel * 3 ^ k + Dsel) ≤ Crec * Real.log T ^ 2 :=
    hCmp.2 k X T hX hT3 hTmem hscale
  have hrecAll : ∀ t : ℝ, |t| = T →
      u6aReciprocalZeroSum (-1) 2 t ≤ Crec * Real.log T ^ 2 := by
    intro t ht
    have htcase : t = T ∨ t = -T :=
      (abs_eq (by linarith : (0 : ℝ) ≤ T)).mp ht
    rcases htcase with rfl | rfl
    · exact hrecTop.trans havg_le
    · simpa [u6aReciprocalZeroSum_neg] using hrecTop.trans havg_le
  exact ⟨T, hT₀, hT3,
    hmain T (u6aCrudeDelta Csel Dsel X k) hTpf hT3 hTmem.2 hrecAll⟩

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
