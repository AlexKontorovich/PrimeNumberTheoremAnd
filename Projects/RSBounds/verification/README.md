# Fresh verification

These logs concern the reconstructed sources in this package. They are fresh
checks, not reconstructions of lost logs from an earlier workspace.

Successful builds and axiom audits are recorded for Totient,
SmallTotientProduct, Mertens, WeightedZeroSums, BacklundPhase,
TotientAnalyticReduction, PolynomialSmoothing, PolynomialPsi, QuarticMellin,
PolynomialZeroKernel, PolynomialResidue, PolynomialPrimeSum,
PolynomialPsiMellin, PolynomialExplicitFormula, PolynomialQuarticFormula,
PolynomialZetaFormula, PolynomialAveragedFormula, PolynomialLeftRemainder,
PolynomialZeroCancellation, PolynomialLowerKernel, and RS75Polynomial. The audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

The native Comparator passed with exit code 0. It compared the two restricted
totient statements with a separate Mathlib-only challenge, checked the permitted
axioms, and replayed the exported solution with Lean's default kernel. The
transcript ends with `Your solution is okay!`. Exact inputs and the command are
recorded in `totient-run.json`.

The default sandbox launch failed with `bwrap: Failed to mount tmpfs`.
That attempt is preserved in `totient-sandbox-attempt.*`. The subsequent run
uses `--inadvisably-no-sandbox` on the reviewed sources. This disables process
sandboxing; it does not disable statement comparison, axiom checks, or Lean
kernel replay. It is not a sandboxed IEANTN receipt.

The polynomial modules prove the integrated explicit formula, with an explicit
left vertical remainder, and supporting smoothing identities. They do not yet
prove the numerical b = 23 bound. The actual-zeta formula has no RH or numerical
zero-count premise; its quantitative application is unfinished.

After these additions, the aggregate `lake build` passed with exit code 0;
see `aggregate-build-rs75-polynomial.{log,json}`. `Targets.lean` also passes
syntax checking. Definitions of target propositions assert no proof of them.

Further fresh checks complete the actual averaged left-line integral bound,
including kernel scaling, integrability, finite-difference interchange, and
the scalar majorant. See `polynomial-remainder-final-run.json`,
`kernel-scaling-left-run.json`, and `polynomial-remainder-majorant-run.json`.
Both actual averaged remainders are less than 0.1 for `x >= exp 23` at
`delta = 0.0000211`, with no RH or zero-count premise.

`totient-global-run.json` checks the finite prime-product certificate through
557 and the all-n implication from two explicit RS62 analytic inputs above
563. Those inputs are not proved by this implication.

`ieantn-gamma-run.json` verifies the imported IEANTN Gauss-series proof and
its summability. The eight upstream proof bodies are unchanged; provenance
and licensing are retained. No challenge or unproved conclusion is imported.

The combined build including these additions passes; exact commands and
hashes are in `aggregate-complete-remainder-run.json`. That run also audits
the centered Mertens tail identity and conditional variation bound in
`MertensTailReduction.lean`, reusing the existing unconditional identity.
