module

public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Trusted numerical boundaries introduced by FKS2 Corollary 23

This file collects, in one place and with **minimal imports**, the trusted numerical
`sorry`s that the formalisation of FKS2 Corollary 23 (`corollary_23_all`) **introduces**:
ten bounds on compact windows `x ∈ [eᵃ, eᵇ]`, one per Table-6 row plus a gap band for
row 8.  Each is a finite-range numerical datum taken from the published computations of

> M. Cully-Hugill, D. R. Johnston, T. S. Trudgian, A. Yang (FKS2),
> *Explicit bounds for `π(x)` and related functions* (arXiv:2206.12557).

## Scope

These ten are the trust that Corollary 23 adds *on top of* the existing development.
`corollary_23_all` additionally relies on trusted numerical `sorry`s that already live
on `main` in their own files and are **not** reproduced here:

* `Table4Ext.allCells_trusted` — the ancillary Table-4 cell data, backing the
  `[e^10, e^20000]` mid-range;
* the Büthe bounds `Buthe.theorem_2e` / `theorem_2f` — backing the `[e^5, e^10]`
  floor segments.

So `#print axioms corollary_23_all` reports `sorryAx` on account of those as well as of
the facts gathered here.

## What the facts are

For the small-`x` floor windows (rows 2–9, `x ≲ 400`) the bound is a direct finite
check: `π(x)` is an exact prime count and `Li(x) = ∫_2^x dt / log t` a certified
quadrature, so the inequality is bounded arithmetic with no analytic input.  Two
windows are of a different, still purely *tabular* character (each flagged in its own
docstring): the near-threshold row-1 window `[e^22.955, e^23.5]` (`x ≈ 10¹⁰`) rests on
FKS2's large-scale computed values of `π`, and the row-8 gap band `[e^5500, e^9500]`
rests on FKS2's *refined* Table-4 tabulation (a finer subdivision than the coarse
in-repo grid).  None is a zero-free region or an unproved asymptotic to be discharged
inside this development; each is a finite, paper-verified numerical datum.

## Auditing

To keep imports minimal this file does not import the main development; the two FKS2
abbreviations that appear below are written out here from Mathlib primitives only:

* `Epi x` is `E_π(x) = |π(x) − Li(x)| / (x / log x)` with
  `π(x) = Nat.primeCounting ⌊x⌋₊` and `Li(x) = ∫_2^x dt / log t`;
* `classicalCurve A B C R x` is the FKS2 admissible bound
  `A · (log x / R)^B · exp(−C · (log x / R)^{1/2})`.

Both are *definitionally equal* to the root-namespace `Eπ` and `admissible_bound` of the
main development (`Defs.lean`); the equality is guarded by `rfl` `example`s in
`FKS2Cor23.lean`, and the row files discharge their goals by `exact` against the lemmas
below.
-/

@[expose] public section

open MeasureTheory

namespace FKS2.TrustedNumerics

/-- `E_π(x) = |π(x) − Li(x)| / (x / log x)`, written out with Mathlib primitives only
(`π(x) = Nat.primeCounting ⌊x⌋₊`, `Li(x) = ∫_2^x dt / log t`).  Definitionally equal to
the main development's root-namespace `Eπ` (`Defs.lean`). -/
noncomputable def Epi (x : ℝ) : ℝ :=
  |(Nat.primeCounting ⌊x⌋₊ : ℝ) - ∫ t in (2 : ℝ)..x, 1 / Real.log t| / (x / Real.log x)

/-- The FKS2 *admissible bound* `A · (log x / R)^B · exp(−C · (log x / R)^{1/2})`,
written out here so this file needs no FKS2 import.  Definitionally equal to the main
development's root-namespace `admissible_bound` (`Defs.lean`). -/
noncomputable def classicalCurve (A B C R x : ℝ) : ℝ :=
  A * (Real.log x / R) ^ B * Real.exp (-C * (Real.log x / R) ^ ((1 : ℝ) / (2 : ℝ)))

/-- **Row 1 floor**, window `[e^22.955, e^23.5]` (`x ∈ [9.3·10⁹, 1.6·10¹⁰]`).
Trusted **tabular** boundary resting on FKS2's large-scale computed value of `π(x)`
(`x ≈ 10¹⁰`, not recomputable in Lean today) against a certified `Li(x)`:
`E_π(x) ≤ 0.000120 · (log x / R)^{1/4} · exp(−(log x / R)^{1/2})`, `R = 5.5666305`.
A finite, paper-verified numerical datum. -/
theorem row1_floor : ∀ x ∈ Set.Icc (Real.exp 22.955) (Real.exp 23.5),
    Epi x ≤ classicalCurve 0.000120 0.25 1 5.5666305 x := by
  sorry

/-- **Row 2 floor**, window `[e^1, e^6]` (`x ∈ [2.72, 403]`).  Trusted numerical
boundary (FKS2 "checks directly for particularly small `x`"): the exact `π`/`Li`
interpolation gives `E_π(x) ≤ 0.826 · (log x / R)^{1/4} · exp(−(log x / R)^{1/2})`,
`R = 5.5666305`.  Purely computational. -/
theorem row2_floor : ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 6),
    Epi x ≤ classicalCurve 0.826 0.25 1 5.5666305 x := by
  sorry

/-- **Row 3 floor**, window `[e^2, e^6]` (`x ∈ [7.39, 403]`).  Trusted numerical
boundary: the exact `π`/`Li` interpolation gives
`E_π(x) ≤ 1.41 · (log x / R)^{1/2} · exp(−1.5 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row3_floor : ∀ x ∈ Set.Icc (Real.exp 2) (Real.exp 6),
    Epi x ≤ classicalCurve 1.41 0.5 1.5 5.5666305 x := by
  sorry

/-- **Row 4 floor**, window `[e^3, e^5]` (`x ∈ [20.09, 148.41]`).  Trusted numerical
boundary from FKS2 §5.2–§5.3: on this range `π(x)` is exact and `Li(x)` is a certified
quadrature of `∫_2^x dt / log t`, so
`E_π(x) ≤ 1.76 · (log x / R) · exp(−1.5 · (log x / R)^{1/2})`, `R = 5.5666305`, is a
finite arithmetic verification.  Purely computational. -/
theorem row4_floor : ∀ x ∈ Set.Icc (Real.exp 3) (Real.exp 5),
    Epi x ≤ classicalCurve 1.76 1 1.5 5.5666305 x := by
  sorry

/-- **Row 5 floor**, window `[e^3, e^5]` (`x ∈ [20.09, 148.41]`).  Trusted numerical
boundary (FKS2 §5.2–§5.3 direct `π`/`Li` interpolation):
`E_π(x) ≤ 2.22 · (log x / R)^{3/2} · exp(−1.5 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row5_floor : ∀ x ∈ Set.Icc (Real.exp 3) (Real.exp 5),
    Epi x ≤ classicalCurve 2.22 1.5 1.5 5.5666305 x := by
  sorry

/-- **Row 6 floor**, window `[e^1, e^5]` (`x ∈ [2.72, 148.41]`).  Trusted numerical
boundary (FKS2 §5.2–§5.3):
`E_π(x) ≤ 12.4 · (log x / R)^{3/2} · exp(−1.9 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row6_floor : ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 5),
    Epi x ≤ classicalCurve 12.4 1.5 1.9 5.5666305 x := by
  sorry

/-- **Row 7 floor**, window `[e^1, e^5]` (`x ∈ [2.72, 148.41]`).  Trusted numerical
boundary (FKS2 §5.2–§5.3):
`E_π(x) ≤ 38.8 · (log x / R)^{3/2} · exp(−1.95 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row7_floor : ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 5),
    Epi x ≤ classicalCurve 38.8 1.5 1.95 5.5666305 x := by
  sorry

/-- **Row 8 floor**, window `[e^1, e^5]` (`x ∈ [2.72, 148.41]`).  Trusted numerical
boundary (FKS2 §5.2–§5.3):
`E_π(x) ≤ 121.107 · (log x / R)^{3/2} · exp(−2 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row8_floor : ∀ x ∈ Set.Icc (Real.exp 1) (Real.exp 5),
    Epi x ≤ classicalCurve 121.107 1.5 2 5.5666305 x := by
  sorry

/-- **Row 8 gap band**, window `[e^5500, e^9500]`.  Trusted **tabular** boundary: at
`x ≈ e^9500` there is no direct prime count, so this rests on FKS2's *refined* Table-4
collection (a finer subdivision than the coarse in-repo `allCells`), which certifies
`E_π(x) ≤ 121.107 · (log x / R)^{3/2} · exp(−2 · (log x / R)^{1/2})`, `R = 5.5666305`,
on this band.  A finite, paper-verified tabulated datum. -/
theorem row8_band : ∀ x ∈ Set.Icc (Real.exp 5500) (Real.exp 9500),
    Epi x ≤ classicalCurve 121.107 1.5 2 5.5666305 x := by
  sorry

/-- **Row 9 floor**, window `[e^3, e^5]` (`x ∈ [20.09, 148.41]`).  Trusted numerical
boundary (FKS2 §5.2–§5.3):
`E_π(x) ≤ 6.60 · (log x / R)^{2} · exp(−2 · (log x / R)^{1/2})`, `R = 5.5666305`.
Purely computational. -/
theorem row9_floor : ∀ x ∈ Set.Icc (Real.exp 3) (Real.exp 5),
    Epi x ≤ classicalCurve 6.60 2 2 5.5666305 x := by
  sorry

end FKS2.TrustedNumerics
