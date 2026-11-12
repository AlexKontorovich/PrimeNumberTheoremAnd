/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNGamma.RealIdentity
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.Convex

/-!
# Stages 2c and 2g: `G` is analytic, and `ψ = G` on the right half-plane

`RealIdentity.lean` has `ψ = G` on the positive real axis. This file carries it to the complex
plane by the identity theorem, which needs both sides analytic on a connected open set containing
those reals.

## The domain is the right half-plane, not the slit plane, and that is a choice

The natural maximal domain is `ℂ \ {0, -1, -2, …}`, and the identity is true there. What is proved
here is the restriction to `{s | 0 < Re s}`, for two reasons:

* **It is everything the node needs.** The conclusion quantifies over `1 ≤ Re w`, which is well
  inside. Nothing downstream asks for more.
* **It makes the uniform bound one line instead of a case split.** The hypothesis of
  `differentiableOn_tsum_of_summable_norm` is a bound *uniform on the set*, and on a half-plane
  `‖k + s‖ ≥ Re (k + s) = k + Re s`, which is exactly what is wanted. On a neighbourhood inside the
  slit plane the same bound needs the poles handled separately: one shows `‖s + k‖ > r` for every
  `k` from `closedBall s₀ r ⊆ U` and `-k ∉ U`, then splits the comparison series at `k ≈ 2‖s₀‖`
  because the two bounds cross there. That is perfectly doable and is the shape a Mathlib version
  should take; it is not done here because it would be work the node cannot use.

So `digamma_eq_gaussSum` below is weaker than the truth, deliberately, and the gap is recorded
rather than hidden. **Anyone extending this to the slit plane changes only this file** — the
statements before it are already about the general case, and Stage 3 only ever evaluates at
`Re w ≥ 1`.

## Why analyticity was not needed earlier

Nothing in stages 1 and 2a–2f uses it: that whole argument runs along the real axis, where `G` is a
convergent series of real terms and the vanishing lemma is a statement about functions on `ℝ`.
Analyticity is needed only to *transport* the identity, which is this file's only job.
-/

namespace GammaSolution

open Complex

/-! ### The half-plane -/

/-- The open right half-plane, `{s | 0 < Re s}`. -/
def rightHalfPlane : Set ℂ := {s : ℂ | 0 < s.re}

theorem isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re

theorem isPreconnected_rightHalfPlane : IsPreconnected rightHalfPlane :=
  (convex_halfSpace_re_gt 0).isPreconnected

theorem mem_rightHalfPlane_iff {s : ℂ} : s ∈ rightHalfPlane ↔ 0 < s.re := Iff.rfl

/-- A point of the right half-plane is not a pole of `Γ` or of `G`. -/
theorem ne_neg_natCast_of_mem {s : ℂ} (hs : s ∈ rightHalfPlane) (m : ℕ) : s ≠ -(m : ℂ) := by
  intro h
  have hre : s.re = -(m : ℝ) := by rw [h]; simp
  have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have := mem_rightHalfPlane_iff.mp hs
  linarith

/-! ### The uniform bound, and 2c -/

/-- **The bound that makes the series locally uniformly convergent.**

On `Re s ≥ δ` with `‖s‖ ≤ M` and `0 < δ ≤ 1`, every term is at most `(M+1)/(δ (k+1)²)`.

The half-plane is doing the work: `‖k + s‖ ≥ Re (k + s) = k + Re s ≥ k + δ`, and then
`(k+1)(k+δ) ≥ δ (k+1)²` because `δ ≤ 1`. No case split on `k`. -/
theorem norm_gaussTerm_le_of_re {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {s : ℂ}
    (hre : δ ≤ s.re) (hM : ‖s‖ ≤ M) (k : ℕ) :
    ‖gaussTerm s k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hspos : (0 : ℝ) < s.re := lt_of_lt_of_le hδ0 hre
  have hne : ∀ m : ℕ, s ≠ -(m : ℂ) := ne_neg_natCast_of_mem (mem_rightHalfPlane_iff.mpr hspos)
  have hMnn : (0 : ℝ) ≤ M := le_trans (norm_nonneg s) hM
  -- The two factors of the denominator.
  have hk1 : ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 := by
    have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hc, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  have hks : (k : ℝ) + δ ≤ ‖(k : ℂ) + s‖ := by
    refine le_trans ?_ (Complex.re_le_norm _)
    simp only [Complex.add_re, Complex.natCast_re]
    linarith
  have hkspos : (0 : ℝ) < ‖(k : ℂ) + s‖ := lt_of_lt_of_le (by linarith) hks
  -- The numerator.
  have hnum : ‖s - 1‖ ≤ M + 1 := by
    refine le_trans (norm_sub_le s 1) ?_
    simpa using hM
  rw [gaussTerm_eq hne k, norm_div, norm_mul, hk1]
  have hden : (0 : ℝ) < ((k : ℝ) + 1) * ‖(k : ℂ) + s‖ := by positivity
  have hden2 : (0 : ℝ) < δ * ((k : ℝ) + 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden hden2]
  -- `‖s-1‖ δ (k+1)² ≤ (M+1) (k+1) ‖k+s‖`, since `‖k+s‖ ≥ k+δ ≥ δ(k+1)`.
  have hstep : δ * ((k : ℝ) + 1) ≤ ‖(k : ℂ) + s‖ := by nlinarith
  have hM1 : (0 : ℝ) ≤ (M + 1) * ((k : ℝ) + 1) := by positivity
  calc ‖s - 1‖ * (δ * ((k : ℝ) + 1) ^ 2)
      = (‖s - 1‖ * ((k : ℝ) + 1)) * (δ * ((k : ℝ) + 1)) := by ring
    _ ≤ ((M + 1) * ((k : ℝ) + 1)) * ‖(k : ℂ) + s‖ :=
        mul_le_mul (mul_le_mul_of_nonneg_right hnum (by linarith)) hstep (by positivity) hM1
    _ = (M + 1) * (((k : ℝ) + 1) * ‖(k : ℂ) + s‖) := by ring

/-- The comparison series is summable. -/
theorem summable_gaussTerm_bound {δ M : ℝ} (hδ0 : 0 < δ) :
    Summable (fun k : ℕ ↦ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)) := by
  have hbase : Summable (fun k : ℕ ↦ 1 / ((k : ℝ) + 1) ^ 2) := by
    have h := (_root_.summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hEq : ∀ k : ℕ, (M + 1) / (δ * ((k : ℝ) + 1) ^ 2)
      = ((M + 1) / δ) * (1 / ((k : ℝ) + 1) ^ 2) := by
    intro k
    field_simp
  simpa only [hEq] using hbase.mul_left ((M + 1) / δ)

/-- Each term is entire off its single pole, so in particular differentiable on the half-plane. -/
theorem differentiableOn_gaussTerm (k : ℕ) {V : Set ℂ} (hV : V ⊆ rightHalfPlane) :
    DifferentiableOn ℂ (fun s ↦ gaussTerm s k) V := by
  intro s hs
  have hne : ((k : ℂ) + s) ≠ 0 := by
    intro h
    have hre : (k : ℝ) + s.re = 0 := by
      have := congrArg Complex.re h
      simpa using this
    have h1 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have h2 := mem_rightHalfPlane_iff.mp (hV hs)
    linarith
  refine DifferentiableAt.differentiableWithinAt ?_
  simp only [gaussTerm]
  exact (differentiableAt_const _).sub (((differentiableAt_const _).add differentiableAt_id).inv hne)

/-- **Stage 2c**: `G` is differentiable at every point of the right half-plane.

Differentiability is local, so the uniform bound only has to hold on *some* neighbourhood: a ball
around `s₀` intersected with a half-plane `Re s > δ` and a ball about the origin, which bounds
`‖s‖` and keeps `Re s` away from `0` at once. -/
theorem differentiableAt_gaussSum {s₀ : ℂ} (hs₀ : s₀ ∈ rightHalfPlane) :
    DifferentiableAt ℂ gaussSum s₀ := by
  have hre₀ : 0 < s₀.re := mem_rightHalfPlane_iff.mp hs₀
  set δ : ℝ := min (s₀.re / 2) 1 with hδ
  set M : ℝ := ‖s₀‖ + 1 with hM
  have hδ0 : 0 < δ := lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδre : δ < s₀.re := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set V : Set ℂ := {s : ℂ | δ < s.re} ∩ Metric.ball 0 M with hV
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ V := by
    refine ⟨hδre, ?_⟩
    simp [Metric.mem_ball, dist_zero_right, hM]
  have hVsub : V ⊆ rightHalfPlane := fun s hs ↦
    mem_rightHalfPlane_iff.mpr (lt_trans hδ0 hs.1)
  -- The uniform bound on `V`.
  have hbound : ∀ (k : ℕ) (w : ℂ), w ∈ V → ‖gaussTerm w k‖ ≤ (M + 1) / (δ * ((k : ℝ) + 1) ^ 2) := by
    intro k w hw
    refine norm_gaussTerm_le_of_re hδ0 hδ1 (le_of_lt hw.1) ?_ k
    have := hw.2
    simp only [Metric.mem_ball, dist_zero_right] at this
    exact this.le
  have hsum : DifferentiableOn ℂ (fun w : ℂ ↦ ∑' k : ℕ, gaussTerm w k) V :=
    Complex.differentiableOn_tsum_of_summable_norm (summable_gaussTerm_bound (M := M) hδ0)
      (fun k ↦ differentiableOn_gaussTerm k hVsub) hVopen hbound
  have hat : DifferentiableAt ℂ (fun w : ℂ ↦ ∑' k : ℕ, gaussTerm w k) s₀ :=
    hsum.differentiableAt (hVopen.mem_nhds hs₀V)
  have hres : DifferentiableAt ℂ
      (fun w : ℂ ↦ -(Real.eulerMascheroniConstant : ℂ) + ∑' k : ℕ, gaussTerm w k) s₀ :=
    (differentiableAt_const _).add hat
  exact hres

theorem differentiableOn_gaussSum : DifferentiableOn ℂ gaussSum rightHalfPlane :=
  fun _ hs ↦ (differentiableAt_gaussSum hs).differentiableWithinAt

theorem analyticOnNhd_gaussSum : AnalyticOnNhd ℂ gaussSum rightHalfPlane :=
  differentiableOn_gaussSum.analyticOnNhd isOpen_rightHalfPlane

/-! ### `ψ` is analytic there too -/

theorem differentiableOn_Gamma_rightHalfPlane :
    DifferentiableOn ℂ Complex.Gamma rightHalfPlane := fun s hs ↦
  (Complex.differentiableAt_Gamma s (ne_neg_natCast_of_mem hs)).differentiableWithinAt

theorem differentiableOn_digamma : DifferentiableOn ℂ Complex.digamma rightHalfPlane := by
  have hΓ := differentiableOn_Gamma_rightHalfPlane
  have hd : DifferentiableOn ℂ (deriv Complex.Gamma) rightHalfPlane :=
    hΓ.deriv isOpen_rightHalfPlane
  have hne : ∀ s ∈ rightHalfPlane, Complex.Gamma s ≠ 0 := fun s hs ↦
    Complex.Gamma_ne_zero (ne_neg_natCast_of_mem hs)
  have := hd.div hΓ hne
  simpa only [Complex.digamma_def, logDeriv] using this

theorem analyticOnNhd_digamma : AnalyticOnNhd ℂ Complex.digamma rightHalfPlane :=
  differentiableOn_digamma.analyticOnNhd isOpen_rightHalfPlane

/-! ### 2g: the identity theorem -/

/-- The positive reals accumulate at `1`, which is what the identity theorem consumes. -/
theorem frequently_digamma_eq_gaussSum :
    ∃ᶠ z in nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ, Complex.digamma z = gaussSum z := by
  set u : ℕ → ℂ := fun n ↦ (((1 : ℝ) + 1 / ((n : ℝ) + 1) : ℝ) : ℂ) with hu
  have hpos : ∀ n : ℕ, (0 : ℝ) < 1 + 1 / ((n : ℝ) + 1) := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    positivity
  have htend : Filter.Tendsto u Filter.atTop (nhds (1 : ℂ)) := by
    have h0 : Filter.Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (0 : ℝ)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hc : Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (nhds (1 : ℝ)) :=
      tendsto_const_nhds
    have hr : Filter.Tendsto (fun n : ℕ ↦ (1 : ℝ) + 1 / ((n : ℝ) + 1)) Filter.atTop
        (nhds (1 : ℝ)) := by simpa using hc.add h0
    simpa [hu, Function.comp_def] using (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hr
  have hne : ∀ n : ℕ, u n ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    intro n
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have h2 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    simp only [hu, Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have : (1 : ℝ) + 1 / ((n : ℝ) + 1) = 1 := by exact_mod_cast h
    linarith
  have hwithin : Filter.Tendsto u Filter.atTop (nhdsWithin (1 : ℂ) {(1 : ℂ)}ᶜ) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within u htend
      (Filter.Eventually.of_forall hne)
  refine hwithin.frequently (Filter.Frequently.of_forall fun n ↦ ?_)
  simpa [hu] using digamma_eq_gaussSum_of_pos (hpos n)

/-- **Stage 2g, and the Gauss representation on the right half-plane**:
`ψ(s) = -γ + ∑ₖ (1/(k+1) - 1/(k+s))` whenever `Re s > 0`. -/
theorem digamma_eq_gaussSum {s : ℂ} (hs : 0 < s.re) : Complex.digamma s = gaussSum s := by
  have h1 : (1 : ℂ) ∈ rightHalfPlane := by simp [mem_rightHalfPlane_iff]
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq analyticOnNhd_digamma
    analyticOnNhd_gaussSum isPreconnected_rightHalfPlane h1 frequently_digamma_eq_gaussSum
    (mem_rightHalfPlane_iff.mpr hs)

end GammaSolution
