/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import Mathlib.Analysis.Complex.AbsMax

/-!
# Maximum-modulus bounds on disks

This file records a disk bound from a boundary bound on the sphere, in the form needed by
growth estimates for holomorphic functions.
-/

@[expose] public section

namespace Complex

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- If `f` is holomorphic on the disk `‖·‖ < r` and bounded by `C` on the circle `‖·‖ = r`, then
`‖f z‖ ≤ C` for every `z` in the disk. -/
theorem norm_le_of_mem_ball_of_forall_sphere_norm_le {f : ℂ → F} {r C : ℝ} {z : ℂ}
    (hd : Differentiable ℂ f) (hrpos : 0 < r)
    (hz : z ∈ Metric.ball (0 : ℂ) r) (hsphere : ∀ u : ℂ, ‖u‖ = r → ‖f u‖ ≤ C) :
    ‖f z‖ ≤ C := by
  let U : Set ℂ := Metric.ball (0 : ℂ) r
  have hfront : ∀ u ∈ frontier U, ‖f u‖ ≤ C := by
    intro u hu
    have hur : ‖u‖ = r := by
      have hfront' : frontier (Metric.ball (0 : ℂ) r) = Metric.sphere (0 : ℂ) r := by
        simpa using (frontier_ball (x := (0 : ℂ)) (r := r) (ne_of_gt hrpos))
      have : u ∈ Metric.sphere (0 : ℂ) r := by simpa [U, hfront'] using hu
      simpa [Metric.mem_sphere, dist_zero_right] using this
    exact hsphere u hur
  exact norm_le_of_forall_mem_frontier_norm_le (f := f) (U := U) Metric.isBounded_ball
    hd.diffContOnCl hfront (subset_closure hz)

end Complex
