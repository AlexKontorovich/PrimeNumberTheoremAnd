import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trusted numerical boundaries introduced by FKS2 Corollary 24

This file collects, in one place and with **minimal imports**, the trusted numerical
`sorry`s that the formalisation of FKS2 Corollary 24 (`corollary_24_all`) **introduces**:
twenty-two bounds on compact windows `x ∈ [eᵃ, eᵇ]`, two per Table-7 row — a small-`x`
*floor* and a large-`x` *sliver*/*band* at the threshold.  Each is a finite-range
numerical datum taken from the published computations of

> M. Cully-Hugill, D. R. Johnston, T. S. Trudgian, A. Yang (FKS2),
> *Explicit bounds for `π(x)` and related functions* (arXiv:2206.12557).

## Scope

These twenty-two are the trust that Corollary 24 adds *on top of* the existing
development.  `corollary_24_all` additionally relies on trusted numerical `sorry`s that
already live elsewhere in the repository and are **not** reproduced here:

* the Büthe bounds `Buthe.theorem_2e` / `theorem_2f` (used via `Epi_le_xpow_half`),
  backing the proved Büthe `x^{-1/2}` floor segments;
* `Table4Ext.allCells_trusted` — the ancillary Table-4 cell data, backing the numerical
  mid-range envelope.

So `#print axioms corollary_24_all` reports `sorryAx` on account of those as well as of
the facts gathered here.

## What the facts are

The eleven *floor* windows are small-`x` (`x ≲ 10⁴`): there `π(x)` is an exact prime
count and `Li(x) = ∫_2^x dt / log t` a certified quadrature, so the bound is a direct
finite check with no analytic input — the "checks directly for particularly small `x`"
step of FKS2 §5.2–§5.3.  The eleven *sliver*/*band* windows sit at the Table-7 threshold
and are of a different, **tabular** character: they lie at astronomically large `x` (from
`e^43 ≈ 5·10¹⁸` up to `e^3757.6`), far beyond any direct prime count, and rest on FKS2's
interpolation of the numerical results of Theorem 6 (the "more refined collection of
values than Table 4").  None is a zero-free region or an unproved asymptotic to be
discharged inside this development; each is a finite, paper-verified numerical datum.

## Auditing

To keep imports minimal this file does not import the main development; the FKS2
abbreviation `E_π` that appears below is written out here from Mathlib primitives only:

* `Epi x` is `E_π(x) = |π(x) − Li(x)| / (x / log x)` with
  `π(x) = Nat.primeCounting ⌊x⌋₊` and `Li(x) = ∫_2^x dt / log t`.

The Table-7 bound curves (`c · (log x)^a · x^{-1/2}`, `x^{-1/k}`) are already elementary
and appear verbatim.  `Epi` is *definitionally equal* to the root-namespace `Eπ` of the
main development (`Defs.lean`); the equality is guarded by a `rfl` `example` in
`FKS2Cor24.lean`, and the row files discharge their goals by `exact` against the lemmas
below.
-/

open MeasureTheory

namespace FKS2.Cor24Trusted

/-- `E_π(x) = |π(x) − Li(x)| / (x / log x)`, written out with Mathlib primitives only
(`π(x) = Nat.primeCounting ⌊x⌋₊`, `Li(x) = ∫_2^x dt / log t`).  Definitionally equal to
the main development's root-namespace `Eπ` (`Defs.lean`). -/
noncomputable def Epi (x : ℝ) : ℝ :=
  |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| / (x / Real.log x)

/-! ### Row 1 — curve `2·log x·x^{-1/2}` -/

/-- **Row 1 floor** `[e^1, e^4]` (`x ∈ [2.72, 54.6]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ 2·log x·x^{-1/2}`.  Purely computational. -/
theorem floor_trusted_row1 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (4:ℝ)),
    Epi x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  sorry

/-- **Row 1 band** `[e^43, e^57]` (`x` from `≈5·10¹⁸`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's Theorem-6 interpolation, no direct prime count.
`E_π(x) ≤ 2·log x·x^{-1/2}`. -/
theorem band_row1 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (57:ℝ)),
    Epi x ≤ 2 * Real.log x * x ^ (-(1:ℝ) / 2) := by
  sorry

/-! ### Row 2 — curve `(log x)^{3/2}·x^{-1/2}` -/

/-- **Row 2 floor** `[e^1, e^8]` (`x ∈ [2.72, 2981]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ (log x)^{3/2}·x^{-1/2}`.  Purely computational. -/
theorem floor_trusted_row2 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (8:ℝ)),
    Epi x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  sorry

/-- **Row 2 band** `[e^43, e^65.65]` (`x` from `≈5·10¹⁸`): trusted **tabular** boundary
at the Table-7 threshold — FKS2's Theorem-6 interpolation, no direct prime count.
`E_π(x) ≤ (log x)^{3/2}·x^{-1/2}`. -/
theorem band_row2 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (65.65:ℝ)),
    Epi x ≤ (Real.log x) ^ (3/2 : ℝ) * x ^ (-(1:ℝ) / 2) := by
  sorry

/-! ### Row 3 — curve `(1/(8π))·(log x)^2·x^{-1/2}` -/

/-- **Row 3 floor** `[e^8, e^9]` (`x ∈ [2981, 8103]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ (1/(8π))·(log x)^2·x^{-1/2}`.  Purely computational. -/
theorem floor_trusted_row3 : ∀ x ∈ Set.Icc (Real.exp (8:ℝ)) (Real.exp (9:ℝ)),
    Epi x ≤ (1 / (8 * Real.pi)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-- **Row 3 band** `[e^43, e^60.8]` (`x` from `≈5·10¹⁸`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's Theorem-6 interpolation, no direct prime count.
`E_π(x) ≤ (1/(8π))·(log x)^2·x^{-1/2}`. -/
theorem band_row3 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (60.8:ℝ)),
    Epi x ≤ (1 / (8 * Real.pi)) * (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-! ### Row 4 — curve `(log x)^2·x^{-1/2}` -/

/-- **Row 4 floor** `[e^1, e^3]` (`x ∈ [2.72, 20.1]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ (log x)^2·x^{-1/2}`.  Purely computational. -/
theorem floor_trusted_row4 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3:ℝ)),
    Epi x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-- **Row 4 band** `[e^43, e^70.6]` (`x` from `≈5·10¹⁸`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's Theorem-6 interpolation, no direct prime count.
`E_π(x) ≤ (log x)^2·x^{-1/2}`. -/
theorem band_row4 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (70.6:ℝ)),
    Epi x ≤ (Real.log x) ^ 2 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-! ### Row 5 — curve `(log x)^3·x^{-1/2}` -/

/-- **Row 5 floor** `[e^1, e^3]` (`x ∈ [2.72, 20.1]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ (log x)^3·x^{-1/2}`.  Purely computational. -/
theorem floor_trusted_row5 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3:ℝ)),
    Epi x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-- **Row 5 band** `[e^43, e^80]` (`x` from `≈5·10¹⁸`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's Theorem-6 interpolation, no direct prime count.
`E_π(x) ≤ (log x)^3·x^{-1/2}`. -/
theorem band_row5 : ∀ x ∈ Set.Icc (Real.exp (43:ℝ)) (Real.exp (80:ℝ)),
    Epi x ≤ (Real.log x) ^ 3 * x ^ (-(1:ℝ) / 2) := by
  sorry

/-! ### Row 6 — curve `x^{-1/3}` -/

/-- **Row 6 floor** `[e^1, e^8]` (`x ∈ [2.72, 2981]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/3}`.  Purely computational. -/
theorem floor_trusted_row6 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (8:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/3) := by
  sorry

/-- **Row 6 sliver** `[e^80, e^80.55]` (`x ≈ 5·10³⁴`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond any direct
prime count.  `E_π(x) ≤ x^{-1/3}`. -/
theorem sliver_row6 : ∀ x ∈ Set.Icc (Real.exp (80:ℝ)) (Real.exp (80.55:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/3) := by
  sorry

/-! ### Row 7 — curve `x^{-1/4}` -/

/-- **Row 7 floor** `[e^1, e^6]` (`x ∈ [2.72, 403]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/4}`.  Purely computational. -/
theorem floor_trusted_row7 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (6:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/4) := by
  sorry

/-- **Row 7 sliver** `[e^107, e^107.6]` (`x ≈ 3·10⁴⁶`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond any direct
prime count.  `E_π(x) ≤ x^{-1/4}`. -/
theorem sliver_row7 : ∀ x ∈ Set.Icc (Real.exp (107:ℝ)) (Real.exp (107.6:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/4) := by
  sorry

/-! ### Row 8 — curve `x^{-1/5}` -/

/-- **Row 8 floor** `[e^1, e^5]` (`x ∈ [2.72, 148]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/5}`.  Purely computational. -/
theorem floor_trusted_row8 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (5:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/5) := by
  sorry

/-- **Row 8 sliver** `[e^134, e^134.8]` (`x ≈ 1.6·10⁵⁸`): trusted **tabular** boundary at
the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond any direct
prime count.  `E_π(x) ≤ x^{-1/5}`. -/
theorem sliver_row8 : ∀ x ∈ Set.Icc (Real.exp (134:ℝ)) (Real.exp (134.8:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/5) := by
  sorry

/-! ### Row 9 — curve `x^{-1/10}` -/

/-- **Row 9 floor** `[e^1, e^4]` (`x ∈ [2.72, 54.6]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/10}`.  Purely computational. -/
theorem floor_trusted_row9 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (4:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/10) := by
  sorry

/-- **Row 9 sliver** `[e^270, e^270.8]` (`x` astronomically large): trusted **tabular**
boundary at the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond
any direct prime count.  `E_π(x) ≤ x^{-1/10}`. -/
theorem sliver_row9 : ∀ x ∈ Set.Icc (Real.exp (270:ℝ)) (Real.exp (270.8:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/10) := by
  sorry

/-! ### Row 10 — curve `x^{-1/50}` -/

/-- **Row 10 floor** `[e^1, e^4]` (`x ∈ [2.72, 54.6]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/50}`.  Purely computational. -/
theorem floor_trusted_row10 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (4:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/50) := by
  sorry

/-- **Row 10 sliver** `[e^1358, e^1358.6]` (`x` astronomically large): trusted **tabular**
boundary at the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond
any direct prime count.  `E_π(x) ≤ x^{-1/50}`. -/
theorem sliver_row10 : ∀ x ∈ Set.Icc (Real.exp (1358:ℝ)) (Real.exp (1358.6:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/50) := by
  sorry

/-! ### Row 11 — curve `x^{-1/100}` -/

/-- **Row 11 floor** `[e^1, e^3.5]` (`x ∈ [2.72, 33.1]`): direct `π`/`Li` check for small
`x` (FKS2 §5.2–§5.3); `E_π(x) ≤ x^{-1/100}`.  Purely computational. -/
theorem floor_trusted_row11 : ∀ x ∈ Set.Icc (Real.exp (1:ℝ)) (Real.exp (3.5:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/100) := by
  sorry

/-- **Row 11 sliver** `[e^3756, e^3757.6]` (`x` astronomically large): trusted **tabular**
boundary at the Table-7 threshold — FKS2's refined Theorem-6 interpolation, far beyond
any direct prime count.  `E_π(x) ≤ x^{-1/100}`. -/
theorem sliver_row11 : ∀ x ∈ Set.Icc (Real.exp (3756:ℝ)) (Real.exp (3757.6:ℝ)),
    Epi x ≤ x ^ (-(1:ℝ)/100) := by
  sorry

end FKS2.Cor24Trusted
