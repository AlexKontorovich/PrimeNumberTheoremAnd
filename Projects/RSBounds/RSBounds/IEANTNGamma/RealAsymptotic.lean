/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Stage 1: `|ψ(x) − log x| ≤ 1/x` for real `x > 0`

The digamma asymptotic on the reals, from log-convexity alone — no series and no integral
representation. `log Γ` is convex, so its derivative is monotone; the slope of `log Γ` across
`[x, x+1]` is exactly `log x`, because `Γ(x+1) = x Γ(x)`; and the mean value theorem puts that
slope between the derivative at `x` and at `x+1`, which differ by `1/x`.

**This is the piece the node's own docstring said would need a Gauss or Binet representation, and
it does not.** `Real.convexOn_log_Gamma` is enough. The Gauss series is still wanted downstream —
it is what identifies `ψ` with the series on all of `ℂ` — but the *asymptotic itself*, on the
reals, with an explicit constant `1`, comes out of convexity in a hundred lines.

Mathlib has no `Real.digamma`, so the derivative is spelled `deriv (fun t ↦ log (Γ t))`
throughout; `Complex.digamma` restricted to the reals agrees with it, and connecting the two is
Stage 3's business, not this file's.
-/

namespace GammaSolution

open Real Set

/-- `log ∘ Γ` is differentiable on the positive reals. -/
theorem differentiableAt_log_Gamma {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℝ (fun t ↦ Real.log (Real.Gamma t)) x := by
  have hΓ : DifferentiableAt ℝ Real.Gamma x :=
    Real.differentiableAt_Gamma (fun m ↦ by
      intro hcon
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      rw [hcon] at hx
      linarith)
  exact (Real.differentiableAt_log (Real.Gamma_pos_of_pos hx).ne').comp x hΓ

/-- The slope of `log Γ` across `[x, x+1]` is `log x`. -/
theorem log_Gamma_add_one_sub {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x) = Real.log x := by
  rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
  ring

/-- **The recurrence**, `ψ(x+1) = ψ(x) + 1/x`, by differentiating
`log Γ(t+1) = log t + log Γ(t)` — an identity that holds on a whole neighbourhood of `x`, which
is what lets the derivatives be compared. -/
theorem deriv_log_Gamma_add_one {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)
      = deriv (fun t ↦ Real.log (Real.Gamma t)) x + 1 / x := by
  have hpos : {t : ℝ | 0 < t} ∈ nhds x :=
    (isOpen_lt continuous_const continuous_id).mem_nhds hx
  have hEq : (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      =ᶠ[nhds x] (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1))) := by
    filter_upwards [hpos] with t ht
    rw [Real.Gamma_add_one (ne_of_gt ht), Real.log_mul (ne_of_gt ht)
      (Real.Gamma_pos_of_pos ht).ne']
  -- The left side, differentiated through the shift.
  have hL : HasDerivAt (fun t : ℝ ↦ Real.log (Real.Gamma (t + 1)))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := by
    have hshift : HasDerivAt (fun t : ℝ ↦ t + 1) 1 x := (hasDerivAt_id x).add_const 1
    have hout := (differentiableAt_log_Gamma (by linarith : (0:ℝ) < x + 1)).hasDerivAt
    simpa [Function.comp_def] using hout.comp x hshift
  -- The right side, differentiated termwise.
  have hR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (x⁻¹ + deriv (fun t ↦ Real.log (Real.Gamma t)) x) x :=
    (Real.hasDerivAt_log hx.ne').add (differentiableAt_log_Gamma hx).hasDerivAt
  have hLR : HasDerivAt (fun t : ℝ ↦ Real.log t + Real.log (Real.Gamma t))
      (deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1)) x := hL.congr_of_eventuallyEq hEq
  have := hLR.unique hR
  rw [this, one_div]
  ring

/-- `ψ` is monotone on the positive reals, because `log Γ` is convex there. -/
theorem monotoneOn_deriv_log_Gamma :
    MonotoneOn (deriv (fun t ↦ Real.log (Real.Gamma t))) (Ioi 0) :=
  Real.convexOn_log_Gamma.monotoneOn_deriv (fun _ hx ↦ differentiableAt_log_Gamma hx)

/-- **The squeeze**: `ψ(x) ≤ log x ≤ ψ(x+1)`. -/
theorem deriv_log_Gamma_le_log_le {x : ℝ} (hx : 0 < x) :
    deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x ∧
      Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
  have hsub : Icc x (x + 1) ⊆ Ioi 0 := fun t ht ↦ lt_of_lt_of_le hx ht.1
  have hcont : ContinuousOn (fun t ↦ Real.log (Real.Gamma t)) (Icc x (x + 1)) := fun t ht ↦
    (differentiableAt_log_Gamma (hsub ht)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hcs⟩ :=
    exists_deriv_eq_slope (fun t ↦ Real.log (Real.Gamma t)) (by linarith) hcont
      (fun t ht ↦ (differentiableAt_log_Gamma (lt_trans hx ht.1)).differentiableWithinAt)
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x)
      = Real.log x := by
    rw [add_sub_cancel_left, div_one, log_Gamma_add_one_sub hx]
  rw [hslope] at hcs
  have hcpos : (0 : ℝ) < c := lt_trans hx hc.1
  have h1 : deriv (fun t ↦ Real.log (Real.Gamma t)) x ≤ Real.log x := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hcpos) hc.1.le
  have h2 : Real.log x ≤ deriv (fun t ↦ Real.log (Real.Gamma t)) (x + 1) := by
    rw [← hcs]
    exact monotoneOn_deriv_log_Gamma (Set.mem_Ioi.mpr hcpos)
      (Set.mem_Ioi.mpr (by linarith)) hc.2.le
  exact ⟨h1, h2⟩

/-- **`|ψ(x) − log x| ≤ 1/x` for real `x > 0`**, with the constant explicit and equal to `1`. -/
theorem abs_deriv_log_Gamma_sub_log_le {x : ℝ} (hx : 0 < x) :
    |deriv (fun t ↦ Real.log (Real.Gamma t)) x - Real.log x| ≤ 1 / x := by
  obtain ⟨hle, hge⟩ := deriv_log_Gamma_le_log_le hx
  rw [deriv_log_Gamma_add_one hx] at hge
  rw [abs_le]
  constructor <;> linarith

end GammaSolution
