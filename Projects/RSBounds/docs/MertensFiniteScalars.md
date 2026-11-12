# Checked finite weighted-Mertens reductions

`RSBounds/MertensFiniteScalars.lean` has passed a fresh exact-source build and
four transitive axiom audits. Every audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

The four public results are:

| Declaration | Result |
|---|---|
| `mertensE_lt_neg_thirteen_tenths` | The actual RS62 constant `E` is less than `-1.3`. |
| `primeWeightedSum_mono` | The actual sum of `log p / p` is nondecreasing. |
| `lower_main_mono` | `log x - 1/(2 log x)` is nondecreasing for `x > 1`. |
| `mertens_lower_of_block` | An exact anchor at the left endpoint and main-term check at the right endpoint prove the original strict RS62 lower bound throughout a real interval. |

The constant bound uses the already checked Euler-constant interval and exact
rational logarithm certificates for the first ten prime terms through 29 of
the defining convergent prime sum. No zero, finite-RH, or prime-number
estimate is assumed. These reductions are the foundation of the separate
finite walk; they do not by themselves assert its full range or the global
Mertens inequality.

Source SHA-256:
`afd3aee79cfa766babf60c4b3a8d8e254cd58d94adf5d5991169aebbc4c93494`.

Receipt: `verification/mertens-finite-scalars-run.json`.
Audit: `verification/MertensFiniteScalarsAudit.lean`.
Reproduce from the recovery project after sourcing `../lean-env.sh` with
`python3 verification/run_mertens_finite_scalars_check.py`.
The interrupted pre-refresh run and the failed rational-normalization pass
are retained separately; the successful receipt binds the exact corrected
source, input, log, and output object hashes.
