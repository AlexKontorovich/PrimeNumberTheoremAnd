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

The later `backlund-center-numerics-run.json` records the completed Lean
certificate for `3.425 < zeta(5/4)/zeta(5/2) < 3.426` and the resulting
center lower bound `1/3.426`. Its 1250 finite root checks use the ordinary
kernel, and its tails use the proved integral test. This supersedes the
earlier absence of a Lean numerical enclosure; the tighter Python interval
remains a separate diagnostic.

`backlund-paired-run.json` records the constructive reflected pairing and
power-limit argument. All three modules compile and all ten audits use
only the standard three axioms. The bound retains the unmatched right-hand
zeros, obtaining reflection loss `E/(2*pi)`.

`BacklundTrapezoidAudit.lean` and `backlund-trapezoid-axioms.log` record the
six standard-axiom checks for the unit Peano-kernel identity, derivative
variation bound, and finite error-sum identity.

`backlund-gamma-phase-run.json` records the five-module gamma phase proof,
seven standard-axiom audits, and source hashes. The main unconditional
bound is `abs(S_Gamma(T)) <= 1/(4*T)` for `T > 0`; the historical
`25/(48*T)` allowance is a checked corollary. The continuous branch and
its relation to the rectangle integral are proved explicitly.

`backlund-anchor-run.json` records nine standard-axiom audits for the Euler
logarithm bound, positivity of the real part of zeta on `Re(s)=5/4`, and
the vertical argument integral identity. The certified upper bound
`zeta(5/4)<23/5` fixes the branch without an argument or winding assumption.

`backlund-count-identity-run.json` records the actual rectangle count,
symmetry reduction, equivalence with zeta multiplicities, and exact
Riemann–von Mangoldt identity. All eighteen audits use the standard three
axioms. The only height conditions are positivity and exclusion of zero
ordinates; no numerical count or RH premise is used.

`backlund-zeta-phase-run.json` records eleven standard-axiom audits for the
actual horizontal zeta argument bound. It discharges the abstract phase,
crossing, reflection, and disk analyticity hypotheses; its remaining
quantitative input is a common circle majorant for zeta at the two translates.

The combined root build after these components is recorded in
`aggregate-backlund-run.json`, with exact toolchain, manifest, and source
hashes. Those earlier component audits alone did not assert the sharp zero-count theorem.

## Completed analytic zero-count theorem

`backlund-high-count-run.json` now records the fresh proof of
`Rosser1941.zero_count_bounds_high`: for every real `T >= 100`, the actual
positive-ordinate zeta zero count, with multiplicities and the inclusive
upper endpoint, satisfies Rosser's bound with constants `.137`, `.443`,
and `1.588`. Its only hypothesis is the height range. In particular it has
no RH, finite-zero-table, zero-count, circle-majorant, or numerical-integral
assumption. All five audited declarations use only the standard three axioms.

`RosserCountDefinition.lean` defines that public count directly as a finite-support
sum of `analyticOrderAt riemannZeta`, independently of the rectangle machinery,
and proves equality with its closed-endpoint count. `BacklundCountEndpoint.lean`
handles heights equal to zero ordinates. The scalar comparison is recorded in
`backlund-scalar-run.json`; the actual circle majorant and its integral are
recorded in `backlund-circle-majorant-run.json` and
`backlund-angular-assembly-run.json`.

The boundary estimates are now actual proved zeta bounds. Their receipts are
`backlund-zeta-boundary-run.json`, `backlund-bottom-run.json`,
`backlund-strip-run.json`, and `backlund-left-zeta-boundary-run.json`.
The gamma modulus proof uses the separately recorded IEANTN Gauss series,
Stirling remainder, and horizontal integration; see
`backlund-gamma-modulus-run.json` and `backlund-functional-strip-run.json`.

`aggregate-backlund-high-run.json` records the successful root-module build
including this analytic theorem. That checkpoint has now been extended to the
full range, as recorded below. The separate b=23 psi estimate remains unfinished.

## Completed finite table and full Rosser theorem

`rh100-replay-run.json` records all 99 freshly checked modules and 28
standard-three-axiom audits of the pinned public zero certificate.
`backlund-rh100-bridge-run.json` records five further audits connecting its
count to our actual inclusive zeta multiplicity count. Per-module source,
toolchain, dependency and object hashes allow compatible completed checks to
be reused. No numerical certificate was rerun for the subsequent wrappers.

`backlund-low-count-run.json` checks the strict bound `abs(N(T)-F(T)) < 1`
for every `0 <= T <= 100`, including zero ordinates and `T=0`.
`zeta-zero-table-run.json` checks the reusable `first29` table: all entries
are actual simple zeros, they are strictly ordered and lie in their rational
brackets, and they exhaust all positive-ordinate zeros through 100. It also
checks exact real-threshold counts and computable rational bracket-count
bounds. All twelve finite-bound audits and seven table audits use only the
three standard axioms. `zero-table-data.json` separately verifies that the
public JSON reproduces the exact rational endpoints in the Lean source.

The first joint import exposed duplicate names in two independent Gamma
ports. `backlund-namespace-adaptation.json` records a namespace-only change;
reversing it reproduces the original source hashes. The eleven affected
analytic modules and aggregate were rebuilt, with 21 standard-axiom checks;
see `backlund-namespace-integration-run.json`. The RH100 certificates were
unchanged and did not require another replay.

`zero-count-run.json` now records the freshly compiled full theorem
`Rosser1941.zero_count_bounds`, for every `T >= 2`, and its guarded five-entry
public axiom audit. The independent Mathlib-only challenge fixes both the
count definition and the two count theorem statements; no definition holes
are permitted. The Comparator export/run result is recorded separately in
that same receipt and must finish successfully before a Comparator pass is
claimed. Its process sandbox is disabled because this workspace cannot mount
the required bwrap filesystem. The statement, axiom and kernel checks are
still required. Exact fresh export hashes are recorded; a previously prepared
challenge export is reused only after its source, toolchain, manifest,
configuration, object and export hashes all match.

The height-280 strict error bound and a certified first-1000 table are not
proved by these results.
