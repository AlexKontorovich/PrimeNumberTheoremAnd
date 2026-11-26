import RSBounds.BacklundTrapezoid
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Positive trapezoidal bounds on an infinite tail

The unit-interval Peano-kernel estimate is reused from `BacklundTrapezoid`.
Its derivative-variation bound telescopes before passage to the limit.
-/

open Set Filter MeasureTheory intervalIntegral
open scoped Interval Topology

namespace TernaryGoldbach.RSBounds.InfiniteTrapezoid

theorem finite_bounds {f g h : ℝ → ℝ} (N M : ℕ) (hNM : N ≤ M)
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ)))
    (hnn : ∀ x : ℝ, (N : ℝ) ≤ x → 0 ≤ h x) :
    0 ≤ (∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
        - (∫ x in (N : ℝ)..M, f x) ∧
      (∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2
        - (∫ x in (N : ℝ)..M, f x) ≤ (g M - g N) / 8 := by
  have hfc : ContinuousOn f (Ici (N : ℝ)) :=
    fun x hx => (hf x hx).continuousAt.continuousWithinAt
  have hint {u v : ℝ} (hu : (N : ℝ) ≤ u) (huv : u ≤ v) :
      IntervalIntegrable f volume u v ∧ IntervalIntegrable h volume u v := by
    have hsub : uIcc u v ⊆ Ici (N : ℝ) := by
      rw [uIcc_of_le huv]
      exact fun x hx => hu.trans hx.1
    exact ⟨(hfc.mono hsub).intervalIntegrable, (hc.mono hsub).intervalIntegrable⟩
  induction M, hNM using Nat.le_induction with
  | base => simp
  | succ M hNM ih =>
      have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
      have hM1 : (M : ℝ) ≤ M + 1 := by linarith
      have hi1 := hint le_rfl hNM'
      have hi2 := hint hNM' hM1
      have hloc := BacklundTrapezoid.error_bounds
        (a := (M : ℝ))
        (fun x hx => hf x (hNM'.trans hx.1))
        (fun x hx => hg x (hNM'.trans hx.1)) hi2.2
        (fun x hx => hnn x (hNM'.trans hx.1))
      rw [trapezoidal_error, trapezoidal_integral_one] at hloc
      have hadd := integral_add_adjacent_intervals hi1.1 hi2.1
      rw [Finset.sum_Ico_succ_top hNM]
      push_cast
      rw [← hadd]
      constructor <;> nlinarith [hloc.1, hloc.2, ih.1, ih.2]

/-- The full sum lies between its trapezoidal tail center and that center
minus one eighth of the first derivative at the cutoff. -/
theorem infinite_bounds {f g h : ℝ → ℝ} (N : ℕ) {S : ℝ}
    (hf : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt f (g x) x)
    (hg : ∀ x : ℝ, (N : ℝ) ≤ x → HasDerivAt g (h x) x)
    (hc : ContinuousOn h (Ici (N : ℝ)))
    (hnn : ∀ x : ℝ, (N : ℝ) ≤ x → 0 ≤ h x)
    (hsum : Tendsto (fun M : ℕ => ∑ k ∈ Finset.range M, f k) atTop (𝓝 S))
    (hf0 : Tendsto (fun M : ℕ => f M) atTop (𝓝 0))
    (hg0 : Tendsto (fun M : ℕ => g M) atTop (𝓝 0))
    (hfi : IntegrableOn f (Ioi (N : ℝ))) :
    (∑ k ∈ Finset.range N, f k) + f N / 2 + (∫ x in Ioi (N : ℝ), f x) ≤ S ∧
      S ≤ (∑ k ∈ Finset.range N, f k) + f N / 2 +
        (∫ x in Ioi (N : ℝ), f x) - g N / 8 := by
  have hsum' : Tendsto (fun M : ℕ => ∑ k ∈ Finset.Ico N M, f k) atTop
      (𝓝 (S - ∑ k ∈ Finset.range N, f k)) := by
    apply (hsum.sub_const _).congr'
    filter_upwards [eventually_ge_atTop N] with M hM
    exact (Finset.sum_Ico_eq_sub _ hM).symm
  have hIF := intervalIntegral_tendsto_integral_Ioi (N : ℝ) hfi
    tendsto_natCast_atTop_atTop
  have hL := (hsum'.add ((hf0.sub_const (f N)).div_const 2)).sub hIF
  have hR := (hg0.sub_const (g N)).div_const 8
  have hlo := le_of_tendsto_of_tendsto tendsto_const_nhds hL
    (show ∀ᶠ M : ℕ in atTop,
      0 ≤ (∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2 -
        (∫ x in (N : ℝ)..M, f x) from by
      filter_upwards [eventually_ge_atTop N] with M hM
      exact (finite_bounds N M hM hf hg hc hnn).1)
  have hhi := le_of_tendsto_of_tendsto hL hR
    (show ∀ᶠ M : ℕ in atTop,
      (∑ k ∈ Finset.Ico N M, f k) + (f M - f N) / 2 -
        (∫ x in (N : ℝ)..M, f x) ≤ (g M - g N) / 8 from by
      filter_upwards [eventually_ge_atTop N] with M hM
      exact (finite_bounds N M hM hf hg hc hnn).2)
  constructor <;> linarith

end TernaryGoldbach.RSBounds.InfiniteTrapezoid
