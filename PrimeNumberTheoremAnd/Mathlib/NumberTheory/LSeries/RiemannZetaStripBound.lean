/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity

/-!
# Strip bounds for the Riemann zeta function

Summary of strip bounds on `riemannZeta` used in `ZetaFiniteOrder` (finite order of
`completedRiemannZeta₀`). Proofs are in `RiemannZetaConvexity` and
`RiemannZetaAbelContinuation`.

## Main results

* `norm_riemannZeta_le`, `norm_zetaAbelContinuationFormula_le` :
  strip bounds on `zetaAbelContinuationDomain`
* `zetaAbelContinuationDomain`, `riemannZeta_eq_zetaAbelContinuationFormula` : Abel continuation API
* `norm_riemannZeta_shift_le` : linear bound for `ζ (s + 3/2 + it)` with `‖s‖ ≤ 1`
* `norm_riemannZeta_ratio_le_on_verticalLine`, `norm_riemannZeta_ratio_le_on_vertical_line` :
  vertical-line lower bounds via Euler products (see also `RiemannZeta`)
-/
