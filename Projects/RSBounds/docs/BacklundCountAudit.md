# Zero-count proof audit

This is a source audit, not a compilation or axiom audit of the external project.
The inspected revision of `gersh/ternary-goldbach-lean` is
`27df23af6a712895f22204d0d81102baa74f0ebe` (also its `main` when checked).
It uses Lean 4.32.1; this package uses Lean 4.35.0.

The sharp Rosser estimate is still a `sorry` in
[`RosserSchoenfeldZeta.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/forks/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RosserSchoenfeldZeta.lean):

`riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 1.588`.

The exact statement is available in the literature: Rosser (1941), Theorem 19,
pp. 223–224, [DOI 10.2307/2371291](https://doi.org/10.2307/2371291).
The issue is formalizing the proof, rather than locating a suitable estimate.

## Existing weaker result

[`BacklundRvMLooseUnconditional.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundRvMLooseUnconditional.lean)
supplies a closed proof expression for
`riemann_vonMangoldt_7_30_55_holds`, with parameters `(7, 0, 30.55)`.
Its proof combines the argument-variation identity, a coarse Jensen estimate,
and an explicit Stirling remainder bound.

**The wrapper's comment about a native certificate is stale.** The actual
[`BacklundF3Numeric.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundF3Numeric.lean)
uses the ordinary arithmetic proofs in
[`BacklundF3OrdinaryCertificate.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundF3OrdinaryCertificate.lean).
For the zeta argument, only the even full-window upper and lower traces are
used: 277 stopped cells in total. The capstone imports six traces, including
four not needed for this particular theorem. No replacement of `native_decide`
was identified in this F3 component. A fresh transitive axiom audit would
still be required before making a kernel-verification claim for the entire
coarse-count theorem.

The static import closure is substantial: the read-only crawl was stopped
after reaching 360 non-Mathlib modules, with further imports pending. This
overestimates the minimum theorem dependency closure, because imported files
also contain unrelated results. No port or compilation of that closure was
attempted here. Whether its coarse constants suffice for the requested
`b = 23` row, possibly with the larger 1976 low-zero head, remains unproved.

The external project's `riemannZeta.N T` counts zeros in `0 < Im rho < T`.
The finite counting function in `WeightedZeroSums.lean` uses `gamma <= T`.
An application needs a proved endpoint-convention bridge; these definitions
are not interchangeable by definitional equality.

## What this package establishes

`BacklundPhase.lean` proves that for every nonzero complex `z` there are
strictly increasing exponents `n(j)` such that

`(z / norm z) ^ n(j) -> 1`

and

`log(abs(Re(z ^ n(j)))) / n(j) -> log(norm z)`.

This supplies the center-phase step for Rosser's use of powers of zeta.
Fresh compilation and all five theorem axiom audits passed; see
`verification/backlund-phase-run.json` and the corresponding logs. It does
not establish the zero-count estimate. The sharp argument still needs the
Backlund reflection/argument-variation estimates and explicit boundary-integral
bounds. Mathlib already supplies the exact circle-average Jensen identity
and a divisor-count inequality in `Analysis/Complex/JensenFormula.lean`;
those general complex-analysis tools need not be reproved.
