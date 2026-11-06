/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNGamma.Oscillation
import RSBounds.IEANTNGamma.Periodic

/-!
# `ψ = G` on the positive real axis

The payoff of stages 1 and 2a–2f: the three hypotheses of
`eq_zero_of_periodic_of_nat_of_oscillation` are now all available for `E := ψ - G`, so `E` is
identically zero to the right of the origin.

| hypothesis | supplied by |
|---|---|
| `E(x+1) = E x` for `x > 0` | `Complex.digamma_apply_add_one` and `gaussSum_add_one` (2b, 2d) |
| `E(n+1) = 0` | `digamma_eq_gaussSum_nat_add_one` (2e) |
| `‖E a - E b‖ ≤ 5/n` | `norm_error_sub_le` (2f) |

**This is the Gauss representation on the reals**, which is the fact Mathlib's `Digamma.lean`
lists as a `TODO`, and the thing the node's docstring correctly identified as the obstruction.
What remains for the node is transport: the identity theorem carries it to `ℂ` (2g), and the
estimate then follows on a strip (Stage 3).
-/

namespace GammaSolution

open Complex

/-- The error `E = ψ - G`, as a function on the reals. -/
noncomputable def gaussError (x : ℝ) : ℂ :=
  Complex.digamma (x : ℂ) - gaussSum (x : ℂ)

/-- A positive real avoids every pole of `ψ` and of `G`. -/
theorem ofReal_ne_neg_nat {x : ℝ} (hx : 0 < x) (m : ℕ) : (x : ℂ) ≠ -(m : ℂ) :=
  ofReal_ne_neg_natCast hx m

/-- **2d, the shift**: `E(x+1) = E(x)` for `x > 0`, because `ψ` and `G` satisfy the same
recurrence.

Note this is a *shift to the right of the origin*, not periodicity on all of `ℝ`: both
recurrences carry the hypothesis `s ∉ {0, -1, -2, …}`, and at a pole both sides are junk. -/
theorem gaussError_add_one {x : ℝ} (hx : 0 < x) : gaussError (x + 1) = gaussError x := by
  have hne := ofReal_ne_neg_nat hx
  have hcast : ((x + 1 : ℝ) : ℂ) = (x : ℂ) + 1 := by push_cast; ring
  have hx0 : (x : ℂ) ≠ 0 := by simpa using hne 0
  simp only [gaussError, hcast]
  rw [Complex.digamma_apply_add_one _ hne, gaussSum_add_one hne]
  ring

/-- **2e, the vanishing at the naturals**, restated for `E`. -/
theorem gaussError_nat_add_one (n : ℕ) : gaussError ((n : ℝ) + 1) = 0 := by
  have hcast : (((n : ℝ) + 1 : ℝ) : ℂ) = (n : ℂ) + 1 := by push_cast; ring
  simp only [gaussError, hcast]
  rw [digamma_eq_gaussSum_nat_add_one n, sub_self]

/-- **2f, the oscillation**, restated for `E`. -/
theorem norm_gaussError_sub_le {n : ℕ} (hn : 1 ≤ n) {a b : ℝ}
    (ha : (n : ℝ) ≤ a) (hb : (n : ℝ) ≤ b) (hab : |a - b| ≤ 1) :
    ‖gaussError a - gaussError b‖ ≤ 5 / n :=
  norm_error_sub_le hn ha hb hab

/-- **The Gauss representation on the positive reals**:
`ψ(x) = -γ + ∑ₖ (1/(k+1) - 1/(k+x))` for every real `x > 0`. -/
theorem digamma_eq_gaussSum_of_pos {x : ℝ} (hx : 0 < x) :
    Complex.digamma (x : ℂ) = gaussSum (x : ℂ) := by
  have h : gaussError x = 0 :=
    eq_zero_of_periodic_of_nat_of_oscillation
      (fun y hy ↦ gaussError_add_one hy)
      gaussError_nat_add_one
      (fun n hn a b ha hb hab ↦ norm_gaussError_sub_le hn ha hb hab)
      hx
  rwa [gaussError, sub_eq_zero] at h

end GammaSolution
