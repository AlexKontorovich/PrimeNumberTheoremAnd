/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Elementary complex-analysis API

Small algebraic and metric lemmas for complex half-planes and basic rational expressions.
-/

@[expose] public section

namespace Complex

/-- If `z ≠ 1`, then `z / (z - 1) = 1 + (z - 1)⁻¹`. -/
theorem div_sub_one_eq_one_add_one_div (z : ℂ) (hz : z ≠ 1) : z / (z - 1) = 1 + (z - 1)⁻¹ := by
  have h : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  calc
    z / (z - 1) = ((z - 1) + 1) / (z - 1) := by ring_nf
    _ = (z - 1) / (z - 1) + 1 / (z - 1) := by rw [add_div]
    _ = 1 + (z - 1)⁻¹ := by simp [div_eq_mul_inv, h]

/-- A continuous complex-valued function is bounded on a closed ball. -/
lemma exists_norm_bound_on_closedBall {f : ℂ → ℂ} {R : ℝ}
    (hcont : ContinuousOn f (Metric.closedBall (0 : ℂ) R)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖f z‖ ≤ M := by
  have hcomp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  exact (hM z (Metric.mem_closedBall.mpr (by simpa using hz))).trans (le_max_left _ _)

/-- If `a < re z`, nested open balls around `z` stay in the half-plane `re · ≥ a`. -/
theorem exists_pos_radius_forall_mem_ball_re_ge {z₀ : ℂ} {a : ℝ} (ha : a < z₀.re) :
    ∃ δ > 0, ∀ (x y : ℂ), dist x z₀ < δ → dist y x < δ → a ≤ y.re := by
  set δ : ℝ := (z₀.re - a) / 2 with hδdef
  have hpos : 0 < z₀.re - a := sub_pos.mpr ha
  have hδpos : 0 < δ := by simpa [hδdef] using half_pos hpos
  refine ⟨δ, hδpos, ?_⟩
  intro x y hx hy
  have htri : dist y z₀ ≤ dist y x + dist x z₀ := dist_triangle y x z₀
  have hsumlt : dist y x + dist x z₀ < δ + δ := add_lt_add hy hx
  have hnorm_lt : ‖y - z₀‖ < δ + δ := by simpa [dist_eq_norm] using lt_of_le_of_lt htri hsumlt
  have hdeltaSum : δ + δ = z₀.re - a := by simp [hδdef, add_halves]
  have hnorm_lt_re : ‖y - z₀‖ < z₀.re - a := by simpa [hdeltaSum] using hnorm_lt
  have h_eps_lt : a < z₀.re - ‖y - z₀‖ := by
    have hsum' : a + ‖y - z₀‖ < z₀.re := by
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using
        (add_lt_add_left hnorm_lt_re a)
    simpa [lt_sub_iff_add_lt] using hsum'
  have hre_lower : -‖y - z₀‖ ≤ (y - z₀).re := (abs_le.mp (abs_re_le_norm (y - z₀))).1
  have hyge : z₀.re - ‖y - z₀‖ ≤ y.re := by
    have h' : z₀.re + (-‖y - z₀‖) ≤ z₀.re + (y - z₀).re := add_le_add_right hre_lower z₀.re
    have h'' : z₀.re + (y - z₀).re = y.re := by
      simp [sub_eq_add_neg]
    simpa [sub_eq_add_neg, h''] using h'
  exact le_of_lt (lt_of_lt_of_le h_eps_lt hyge)

end Complex
