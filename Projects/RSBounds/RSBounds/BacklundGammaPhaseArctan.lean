/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in ../licenses/.
The reciprocal integral below is adapted from ArctanLogIntegrals.lean,
gersh/ternary-goldbach-lean@27df23af6a712895f22204d0d81102baa74f0ebe.
-/
import RSBounds.BacklundGammaPhaseShift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

open Complex Real Filter MeasureTheory intervalIntegral
open scoped Topology Interval

namespace TernaryGoldbach.RSBounds.BacklundGammaPhase

/-- `∫_0^τ c/(c²+t²) dt = arctan(τ/c)` for `c > 0` (any `τ`). -/
theorem integral_const_div_sq_add_sq {c : ℝ} (hc : 0 < c) (τ : ℝ) :
    ∫ t in (0:ℝ)..τ, c / (c ^ 2 + t ^ 2) = Real.arctan (τ / c) := by
  have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) τ,
      HasDerivAt (fun u : ℝ => Real.arctan (u / c)) (c / (c ^ 2 + t ^ 2)) t := by
    intro t _
    have h1 : HasDerivAt (fun u : ℝ => u / c) (1 / c) t := by
      simpa using (hasDerivAt_id t).div_const c
    have h2 := h1.arctan
    convert h2 using 1
    have hden : (0:ℝ) < 1 + (t / c) ^ 2 := by positivity
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => c / (c ^ 2 + t ^ 2)) (Set.uIcc 0 τ) := by
    apply ContinuousOn.div continuousOn_const (by fun_prop)
    intro t _
    positivity
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    hcont.intervalIntegrable
  simpa using this


theorem phaseAt_add_one {a : ℝ} (ha : 0 < a) (τ : ℝ) :
    phaseAt (a + 1) τ = phaseAt a τ + Real.arctan (τ / a) := by
  have he : ∀ t : ℝ, (Complex.digamma (((a + 1 : ℝ) : ℂ) + t * I)).re =
      (Complex.digamma ((a : ℂ) + t * I)).re + a / (a ^ 2 + t ^ 2) := by
    intro t
    have hn := GammaSolution.ne_neg_natCast_of_mem
      (s := (a : ℂ) + t * I)
      (GammaSolution.mem_rightHalfPlane_iff.mpr (by simpa using ha))
    have hrec := Complex.digamma_apply_add_one ((a : ℂ) + t * I) hn
    have harg : (a : ℂ) + t * I + 1 = ((a + 1 : ℝ) : ℂ) + t * I := by
      push_cast
      ring
    rw [harg] at hrec
    rw [hrec, Complex.add_re, Complex.inv_re, Complex.normSq_apply]
    simp [pow_two]
  have hi : IntervalIntegrable (fun t : ℝ ↦ (Complex.digamma ((a : ℂ) + t * I)).re) volume 0 τ :=
    (Complex.continuous_re.comp (continuous_digamma_unscaled ha)).intervalIntegrable 0 τ
  have hj : IntervalIntegrable (fun t : ℝ ↦ a / (a ^ 2 + t ^ 2)) volume 0 τ := by
    apply Continuous.intervalIntegrable
    apply Continuous.div continuous_const (by fun_prop)
    intro t
    positivity
  unfold phaseAt
  simp_rw [he]
  rw [intervalIntegral.integral_add hi hj, integral_const_div_sq_add_sq ha τ]

theorem phaseAt_add_nat {a : ℝ} (ha : 0 < a) (τ : ℝ) (N : ℕ) :
    phaseAt (a + N) τ = phaseAt a τ +
      ∑ k ∈ Finset.range N, Real.arctan (τ / (a + k)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hpos : 0 < a + (N : ℝ) := by positivity
    rw [Nat.cast_add_one, ← add_assoc, phaseAt_add_one hpos, ih, Finset.sum_range_succ]
    ring

/-- The Gauss phase limit is for the continuous branch fixed by the
digamma integral; no `Complex.log (Complex.Gamma z)` is involved. -/
theorem tendsto_arctan_gauss_phase {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun N : ℕ ↦ τ * Real.log N -
        ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))))
      atTop (𝓝 (phaseAt (1 / 4) τ)) := by
  have hlim : Tendsto (fun N : ℕ ↦ phaseAt (1 / 4) τ -
      (phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N))
      atTop (𝓝 (phaseAt (1 / 4) τ - 0)) :=
    tendsto_const_nhds.sub (tendsto_phaseAt_quarter_shift hτ)
  have he : ∀ N : ℕ, phaseAt (1 / 4) τ -
      (phaseAt ((N : ℝ) + 1 / 4) τ - τ * Real.log N) =
      τ * Real.log N - ∑ k ∈ Finset.range N, Real.arctan (τ / (1 / 4 + (k : ℝ))) := by
    intro N
    rw [add_comm (N : ℝ) (1 / 4), phaseAt_add_nat (by norm_num : (0 : ℝ) < 1 / 4)]
    ring
  simp only [sub_zero, he] at hlim
  exact hlim

/-- `arctan x ≤ x` for `x ≥ 0`. -/
theorem arctan_le_self' {x : ℝ} (hx : 0 ≤ x) : Real.arctan x ≤ x := by
  have hmono : MonotoneOn (fun u : ℝ => u - Real.arctan u) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact (continuous_id.sub Real.continuous_arctan).continuousOn
    · exact (differentiable_id.sub Real.differentiable_arctan).differentiableOn
    · intro u _
      have hd : HasDerivAt (fun u : ℝ => u - Real.arctan u)
          (1 - 1 / (1 + u ^ 2)) u := (hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)
      rw [hd.deriv]
      have : (0:ℝ) < 1 + u ^ 2 := by positivity
      rw [sub_nonneg, div_le_one this]
      nlinarith
  have := hmono (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
  simpa [Real.arctan_zero] using this


end TernaryGoldbach.RSBounds.BacklundGammaPhase

