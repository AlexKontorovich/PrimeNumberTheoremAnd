# Fresh verification

These logs concern the reconstructed sources in this package. They are fresh
checks, not reconstructions of lost logs from an earlier workspace.

Successful builds and axiom audits are recorded for Totient,
SmallTotientProduct, Mertens, WeightedZeroSums, BacklundPhase,
TotientAnalyticReduction, PolynomialSmoothing, and PolynomialPsi. The audited
theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

The native Comparator checks the two restricted totient statements against a
separate Mathlib-only challenge. Its current command and actual exit code are
recorded in `totient-run.json`; no final success is implied until that record
contains `exit_code: 0` and the transcript ends successfully.

The default sandbox launch failed with `bwrap: Failed to mount tmpfs`.
That attempt is preserved in `totient-sandbox-attempt.*`. The subsequent run
uses `--inadvisably-no-sandbox` on the reviewed sources. This disables process
sandboxing; it does not disable statement comparison, axiom checks, or Lean
kernel replay. It is not a sandboxed IEANTN receipt.

The polynomial smoothing proofs are supporting results. They do not yet prove
the integrated explicit formula or the numerical b = 23 zero-sum bound.
