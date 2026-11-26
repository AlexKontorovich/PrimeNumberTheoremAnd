/-
Copyright (c) 2026 IEANTN contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Tao
-/
import RSBounds.IEANTNGamma.GaussSeries

/-!
# Stages 2b and 2e: the recurrence for the Gauss series, and its value at the integers

Two of the three hypotheses of the vanishing lemma, for `E := ψ - G` where

  `G s := -γ + ∑ₖ (1/(k+1) - 1/(k+s))`.

* **2b**, `gaussSum_add_one`: `G(s+1) = G(s) + 1/s`. With `Complex.digamma_apply_add_one` this is
  what makes `E` 1-periodic. The proof is a telescoping series: subtracting the two Gauss series
  termwise cancels the `1/(k+1)` and leaves `1/(k+s) - 1/(k+1+s)`, whose partial sums are
  `1/s - 1/(n+s)`.
* **2e**, `digamma_eq_gaussSum_nat_add_one`: `ψ(n+1) = G(n+1)`, both sides being `-γ + Hₙ`.

## What the Mathlib bump changed here

The node's `formalization.yaml` records that `Analysis/SpecialFunctions/Gamma/Digamma.lean` "is 64
lines and contains the definition, `digamma_zero`, `digamma_one`, `digamma_one_half`,
`digamma_apply_add_one` and `meromorphic_digamma`, and no bound of any kind." **That was true when
it was written and is no longer true.** On this repository's pin the file is 153 lines and also
carries `digamma_apply_add_nat`, `digamma_nat_add_one`, Euler's reflection formula
`digamma_one_sub`, and the duplication formula `digamma_two_mul`.

The half of that observation which still holds is the operative one: there is still no bound of
any kind, so the node's conclusion is still open and the Gauss representation is still a `TODO` in
that file. But `digamma_nat_add_one` is exactly step 2e's `ψ` side, so that step is now two
`rw`s rather than an induction, and the `limitations` entry saying the reflection formula awaits a
future bump has been overtaken by the bump that already happened.
-/

namespace GammaSolution

open Complex

/-- The Gauss series, `G s = -γ + ∑ₖ (1/(k+1) - 1/(k+s))`.

Not yet known to equal `ψ`; that is what the rest of the solution is for. -/
noncomputable def gaussSum (s : ℂ) : ℂ :=
  -(Real.eulerMascheroniConstant : ℂ) + ∑' k, gaussTerm s k

/-- **A telescoping series**: if `f n → 0` and the differences are summable, they sum to `f 0`.

Stated for its own sake rather than inlined, because the argument is entirely about partial sums
and has nothing to do with `Γ` — and stated over an arbitrary complete normed group because it is
used twice at different types: over `ℂ` for the recurrence below, and over `ℝ` in
`Oscillation.lean`, where the same telescoping sums `1/((k+t)(k+t+1))` to `1/t`. -/
theorem hasSum_sub_succ {F : Type*} [NormedAddCommGroup F] [CompleteSpace F] {f : ℕ → F}
    (hsum : Summable fun k ↦ f k - f (k + 1))
    (hlim : Filter.Tendsto f Filter.atTop (nhds 0)) :
    HasSum (fun k ↦ f k - f (k + 1)) (f 0) := by
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, (f i - f (i + 1)) = f 0 - f n :=
    fun n ↦ Finset.sum_range_sub' f n
  have h1 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h1
  have h2 : Filter.Tendsto (fun n : ℕ ↦ f 0 - f n) Filter.atTop (nhds (f 0)) := by
    simpa using tendsto_const_nhds.sub hlim
  rw [← tendsto_nhds_unique h1 h2]
  exact hsum.hasSum

/-- `1/(k+s) → 0`, because `‖k + s‖ ≥ k - ‖s‖ → ∞`. -/
theorem tendsto_inv_natCast_add (s : ℂ) :
    Filter.Tendsto (fun k : ℕ ↦ ((k : ℂ) + s)⁻¹) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp only [norm_inv]
  refine Filter.Tendsto.inv_tendsto_atTop ?_
  refine Filter.tendsto_atTop_mono (fun k ↦ ?_)
    (Filter.tendsto_atTop_add_const_right _ (-‖s‖) tendsto_natCast_atTop_atTop)
  have h := norm_sub_norm_le ((k : ℂ)) (-s)
  simp only [norm_neg, sub_neg_eq_add] at h
  simpa using h

/-- **Stage 2b, the recurrence**: `G(s+1) = G(s) + 1/s`.

Termwise, `gaussTerm (s+1) k - gaussTerm s k = 1/(k+s) - 1/(k+1+s)`: the `1/(k+1)` that carries
the divergence cancels, and what is left telescopes. -/
theorem gaussSum_add_one {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) :
    gaussSum (s + 1) = gaussSum s + s⁻¹ := by
  have hs' : ∀ n : ℕ, s + 1 ≠ -n := fun n h ↦
    hs (n + 1) (by push_cast at h ⊢; linear_combination h)
  set f : ℕ → ℂ := fun k ↦ ((k : ℂ) + s)⁻¹ with hf
  have hdiff : ∀ k : ℕ, gaussTerm (s + 1) k - gaussTerm s k = f k - f (k + 1) := by
    intro k
    simp only [gaussTerm, hf]
    push_cast
    ring
  have hsub : Summable (fun k ↦ f k - f (k + 1)) := by
    have h := (summable_gaussTerm hs').sub (summable_gaussTerm hs)
    simpa only [hdiff] using h
  have htel := hasSum_sub_succ hsub (tendsto_inv_natCast_add s)
  have hHS : HasSum (fun k ↦ gaussTerm (s + 1) k - gaussTerm s k)
      ((∑' k, gaussTerm (s + 1) k) - ∑' k, gaussTerm s k) :=
    (summable_gaussTerm hs').hasSum.sub (summable_gaussTerm hs).hasSum
  have hHS' : HasSum (fun k ↦ gaussTerm (s + 1) k - gaussTerm s k) (f 0) := by
    simpa only [hdiff] using htel
  have hkey := hHS.unique hHS'
  have hf0 : f 0 = s⁻¹ := by simp [hf]
  rw [hf0] at hkey
  simp only [gaussSum]
  linear_combination hkey

@[simp]
theorem gaussTerm_one (k : ℕ) : gaussTerm 1 k = 0 := by simp [gaussTerm]

theorem gaussSum_one : gaussSum 1 = -(Real.eulerMascheroniConstant : ℂ) := by
  simp [gaussSum]

/-- **`G` at a positive integer**: `G(n+1) = -γ + Hₙ`, by induction from the recurrence. -/
theorem gaussSum_nat_add_one (n : ℕ) :
    gaussSum ((n : ℂ) + 1)
      = -(Real.eulerMascheroniConstant : ℂ) + ((harmonic n : ℚ) : ℂ) := by
  induction n with
  | zero => simpa using gaussSum_one
  | succ n ih =>
    have hne : ∀ m : ℕ, ((n : ℂ) + 1) ≠ -(m : ℂ) := by
      intro m h
      have hre : (n : ℝ) + 1 = -(m : ℝ) := by exact_mod_cast congrArg Complex.re h
      have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    have hstep : gaussSum (((n : ℂ) + 1) + 1) = gaussSum ((n : ℂ) + 1) + ((n : ℂ) + 1)⁻¹ :=
      gaussSum_add_one hne
    have hcast : (((n : ℕ) + 1 : ℕ) : ℂ) + 1 = ((n : ℂ) + 1) + 1 := by push_cast; ring
    rw [hcast, hstep, ih, harmonic_succ]
    push_cast
    ring

/-- **Stage 2e**: `ψ` and `G` agree at the positive integers — the second hypothesis of
`eq_zero_of_periodic_of_nat_of_oscillation`.

Both sides are `-γ + Hₙ`: the left by `Complex.digamma_nat_add_one`, the right by
`gaussSum_nat_add_one`. -/
theorem digamma_eq_gaussSum_nat_add_one (n : ℕ) :
    Complex.digamma ((n : ℂ) + 1) = gaussSum ((n : ℂ) + 1) := by
  rw [Complex.digamma_nat_add_one n, gaussSum_nat_add_one n]
  ring

end GammaSolution
