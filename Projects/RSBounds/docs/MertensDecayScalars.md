# Scalar budget for the moving zero cutoff

Status: **fresh source check and all seven transitive axiom audits passed**
on 2026-11-06, using only `propext`, `Classical.choice`, and `Quot.sound`.
The successful pass took 51.41 seconds. Source SHA256:
`acf3eb5ff93389fe93385d44e3095ab160924308bc25d0c7ba7d986ee0d9ff44`.

`MertensDecayScalars.lean` imports only Mathlib. It defines the explicit
reciprocal-square tail expression `squareExpr(T)` and the scalar envelope

\[
B(X)=0.0463e^{-5X^2}+0.0463e^{-X}
+2\,\mathrm{squareExpr}(17e^X)+6000e^{-15X^2}
+\frac{\log(2\pi)}{e^{10X^2}}.
\]

For `X ≥ 15`, its final theorem `scalarEnvelope_lt` states

\[
B(X)<\frac1{(10X^2)^2}.
\]

The intermediate theorem `scalarEnvelope_le` bounds the whole expression
by `(X/25)e^(−X)`. The function `X^5 e^(−X)` is bounded by its value at 15
using the elementary inequality `log(X/15)≤X/15−1`. The explicit bound
`exp15 ≥ 3200000` then proves the strict final margin.

The intended substitution is `log x = 10X²` and `T = 17expX`.
`cutoff_height` verifies `T ≥ 1894439` throughout the range. These scalar
facts have **no prime, zeta, finite-RH, or PNT hypothesis**. Connecting the
envelope to the actual signed Mertens tail is a separate analytic theorem
in `MertensPotentialDecay`/`MertensLargeBudget`.

Exact-source check: `verification/run_mertens_decay_scalars_check.py`.
Receipt: `verification/mertens-decay-scalars-run.json`.
Audited exports: `exp_fifteen_lower`, `log_seventeen_bounds`, `cutoff_height`,
`twice_squareExpr_le`, `scalarEnvelope_le`, `fifth_power_exp_le`, and
`scalarEnvelope_lt`.
