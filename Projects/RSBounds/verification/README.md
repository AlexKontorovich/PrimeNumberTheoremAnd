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

`backlund-jensen-run.json` records the fresh build and eight standard-axiom
audits for angular Jensen and its limit along powers. This is a component
of Rosser's zero-count proof, not the sharp zero-count theorem itself.

`backlund-reflection-run.json` records the build and twelve standard-axiom
audits for the exact reflected logarithmic derivative and the constructive
first/last crossing lemmas. These small ports import Mathlib only; they do
not import the external project's full zero-count development.

`backlund-gamma-reflection-run.json` records seventeen standard-axiom audits
and the build for the reused IEANTN digamma bound and the new quantitative
reflection integral. Its actual zeta integral is proved integrable and at
most `4*delta^2/T`, hence less than `8/T`, under explicit local nonvanishing.

`backlund-center-run.json` checks the exact Euler-product ratio lower bound.
The separate `backlund-center-rational.json` is an exact Python integer/
rational integral-test computation, not a Lean certificate. It shows why
`3.426`, rather than the printed `3.425`, is a safe upward rounding for this
ratio. No decimal center bound has been silently inserted into a Lean proof.

The combined root build after these components is recorded in
`aggregate-backlund-run.json`, with exact toolchain, manifest, and source
hashes. None of these component audits asserts the sharp zero-count theorem.
