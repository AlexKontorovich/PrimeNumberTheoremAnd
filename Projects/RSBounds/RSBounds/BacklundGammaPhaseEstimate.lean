import RSBounds.BacklundGammaPhasePrimitive
import RSBounds.BacklundTrapezoid

open Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

theorem arctan_unit_error_bounds {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ) :
    0 ≤ trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ∧
    trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1 a (a + 1) ≤
      ((-τ / ((a + 1) ^ 2 + τ ^ 2)) - (-τ / (a ^ 2 + τ ^ 2))) / 8 := by
  apply BacklundTrapezoid.error_bounds
    (f' := fun x : ℝ ↦ -τ / (x ^ 2 + τ ^ 2))
    (f'' := fun x : ℝ ↦ 2 * τ * x / (x ^ 2 + τ ^ 2) ^ 2)
  · intro x hx
    exact hasDerivAt_arctan_quotient (ha.trans_le hx.1)
  · intro x hx
    exact hasDerivAt_arctan_quotient_deriv (ha.trans_le hx.1)
  · apply Continuous.intervalIntegrable
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro x
    positivity
  · intro x hx
    have hx0 : 0 < x := ha.trans_le hx.1
    positivity

noncomputable def arctanTrapSum (τ : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
    (1 / 4 + (k : ℝ)) (1 / 4 + (k : ℝ) + 1)

theorem arctanTrapSum_bounds {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    0 ≤ arctanTrapSum τ N ∧
      arctanTrapSum τ N ≤
        ((-τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2)) -
          (-τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2))) / 8 := by
  induction N with
  | zero => simp [arctanTrapSum]
  | succ N ih =>
    have hu := arctan_unit_error_bounds (a := 1 / 4 + (N : ℝ)) (by positivity) hτ
    have he : arctanTrapSum τ (N + 1) = arctanTrapSum τ N +
        trapezoidal_error (fun x : ℝ ↦ Real.arctan (τ / x)) 1
          (1 / 4 + (N : ℝ)) (1 / 4 + (N : ℝ) + 1) := by
      simp [arctanTrapSum, Finset.sum_range_succ]
    rw [he]
    push_cast
    constructor
    · linarith [ih.1, hu.1]
    · have hp : 1 / 4 + ((N : ℝ) + 1) = 1 / 4 + (N : ℝ) + 1 := by ring
      rw [hp]
      linarith [ih.2, hu.2]

theorem arctanTrapSum_le {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    arctanTrapSum τ N ≤ 1 / (8 * τ) := by
  have hu := (arctanTrapSum_bounds hτ N).2
  have hn : -τ / ((1 / 4 + (N : ℝ)) ^ 2 + τ ^ 2) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have he : τ / ((1 / 4 : ℝ) ^ 2 + τ ^ 2) ≤ 1 / τ := by
    rw [div_le_div_iff₀ (by positivity) hτ]
    nlinarith
  have he' : 1 / (8 * τ) = (1 / τ) / 8 := by ring
  rw [he']
  simp only [neg_div] at hu hn
  linarith

theorem arctanTrapSum_eq (τ : ℝ) (N : ℕ) :
    arctanTrapSum τ N =
      (∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ)))) +
        (Real.arctan (τ / (1 / 4 + (N : ℝ))) - Real.arctan (τ / (1 / 4))) / 2 -
        (arctanPrimitive τ (1 / 4 + (N : ℝ)) - arctanPrimitive τ (1 / 4)) := by
  unfold arctanTrapSum
  rw [BacklundTrapezoid.sum_error_eq N]
  · rw [integral_arctan_quotient (by norm_num : (0 : ℝ) < 1 / 4)]
  · intro k _
    apply ContinuousOn.intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by linarith : 1 / 4 + (k : ℝ) ≤ 1 / 4 + (k : ℝ) + 1)] at hx
    have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx.1
    exact (hasDerivAt_arctan_quotient (τ := τ) hx0).continuousAt.continuousWithinAt

theorem tendsto_arctanTrapSum {τ : ℝ} (hτ : 0 < τ) :
    Tendsto (arctanTrapSum τ) atTop
      (𝓝 (arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
        phaseAt (1 / 4) τ)) := by
  have hG := tendsto_arctan_gauss_phase hτ.le
  have hP := tendsto_arctanPrimitive_sub_log (by norm_num : (0 : ℝ) < 1 / 4) hτ
  have hq : Tendsto (fun N : ℕ ↦ τ / (1 / 4 + (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop)
  have hA : Tendsto (fun N : ℕ ↦ Real.arctan (τ / (1 / 4 + (N : ℝ)))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hq
  have hC : Tendsto (fun _ : ℕ ↦ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)
      atTop (𝓝 (arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2)) :=
    tendsto_const_nhds
  convert ((hC.sub hG).sub hP).add (hA.div_const 2) using 1
  · funext N
    rw [arctanTrapSum_eq]
    ring
  · ring

theorem phaseAt_remainder_bound {τ : ℝ} (hτ : 0 < τ) :
    |phaseAt (1 / 4) τ - τ * Real.log τ + τ + Real.pi / 8| ≤ 1 / (8 * τ) := by
  have hlim := tendsto_arctanTrapSum hτ
  have hE0 : 0 ≤ arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
      phaseAt (1 / 4) τ := by
    apply ge_of_tendsto hlim
    exact Filter.Eventually.of_forall (fun N ↦ (arctanTrapSum_bounds hτ N).1)
  have hE1 : arctanPrimitive τ (1 / 4) - Real.arctan (τ / (1 / 4)) / 2 - τ -
      phaseAt (1 / 4) τ ≤ 1 / (8 * τ) :=
    le_of_tendsto' hlim (arctanTrapSum_le hτ)
  have hC := phase_correction_bounds hτ
  have hu : 3 / (32 * τ) ≤ 1 / (8 * τ) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [abs_le]
  constructor <;> linarith [hC.1, hC.2]

/-- A branch-consistent explicit Stirling phase bound, stronger than the
`25/(48T)` allowance used by Backlund. The proof uses IEANTN's actual
digamma series, recurrence, and a finite trapezoidal estimate. -/
theorem gamma_phase_remainder_bound {T : ℝ} (hT : 0 < T) :
    |phaseIntegral T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8| ≤
      1 / (4 * T) := by
  have hh := phaseAt_remainder_bound (τ := T / 2) (by positivity)
  have he : phaseAt (1 / 4) (T / 2) = phaseIntegral T := by
    simp [phaseAt, phaseIntegral]
  rw [he] at hh
  convert hh using 1 <;> ring

/-- The numerical Gamma phase allowance in Backlund's zero-count estimate. -/
theorem backlund_gamma_phase_remainder_bound {T : ℝ} (hT : 0 < T) :
    |phaseIntegral T - T / 2 * Real.log (T / 2) + T / 2 + Real.pi / 8| ≤
      25 / (48 * T) := by
  refine (gamma_phase_remainder_bound hT).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

end TernaryGoldbach.RSBounds.BacklundGammaPhase
