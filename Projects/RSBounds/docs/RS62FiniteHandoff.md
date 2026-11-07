# Finite RS62 prime-product handoff

The pinned upstream source
`TernaryGoldbach/Prelim/SmallMertensProd.lean` was freshly compiled, including
all one-hundred kernel-checked walk blocks. Its public theorem is exactly

\[
\prod_{p\le q}\frac p{p-1}
<e^\gamma\log\theta(q)+\frac{2.50637}{\log\theta(q)}
\qquad(q\text{ prime},\ 5\le q\le100000).
\]

This is an unconditional finite computation. The source imports only the
elementary `RamareWalk` certificate infrastructure, and its transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`. In
particular, no RH, Büthe estimate, or Ramaré Möbius-sum estimate is an input.

The fresh source SHA256 is
`ac74a9aacb156f36bcf71a08db2319733a126fd68a8eec8bbdd11ace6fe4760f`.
The successful source-and-four-axiom-audit receipt is
`verification/small-mertens-prod-run.json`; the check took 1214.7 seconds.

`RSBounds/RS62FiniteHandoff.lean` exposes the same theorem using the local
`Totient.primeProduct` and `Totient.primeTheta` definitions. Its checked
global handoff permits an analytic threshold `X≤100001`: the exact same
prime-product inequality is required as an explicit hypothesis for primes
`p≥X`. The existing exchange argument then yields the totient bound for
every integer `n≥3`, without an upper restriction on `n`.

This does **not** move the required analytic threshold to 100001. Any smaller
threshold, including the earlier 563 handoff, remains admissible. Nor does
the finite certificate itself prove the analytic tail or the unrestricted
totient theorem. The separate bridge check passed on 2026-11-06, with
all three transitive axiom audits restricted to the standard three axioms.
The receipt is `verification/rs62-finite-handoff-run.json`; the bridge
source SHA256 is
`371cdd896153f58cb2cbf3a8256bee19b76b72f36d8f3bf9d5a4947bc09bf2d5`.

The similarly named upstream `SmallMertensLower.lean` proves a lower bound
for `ΣΛ(n)/n` through 10000 with the constant `log(3/√2)`. It is useful
certificate infrastructure but is not the requested RS62 prime-weighted
lower bound with `E−1/(2log x)`.

The completed finite weighted-prime route uses the coarse scalar bound
`E<−1.3` and checks the increasing real main term at the right endpoint of
each block. `MertensFiniteScalars.lean` has now passed its independent fresh-source
check and all four standard-axiom audits; see
`verification/mertens-finite-scalars-run.json`. No finite weighted range
is claimed from a floating-point diagnostic. The exact integer
101-block weighted-prime certificate and readable witness data are
described separately in `MertensFinite100000.md`. The numerical replay
has passed, proving the original exact-constant weighted-prime lower
bound for every real `1 < x ≤ 100000`; all five transitive axiom audits
use only the standard three axioms. See
`verification/mertens-finite-100000-run.json`. Its global handoff still
requires the analytic inequality on `x ≥ 100000` explicitly.

References: Rosser–Schoenfeld (1962), Theorem 15,
<https://doi.org/10.1215/ijm/1255631807>; upstream pinned revision
`calr3/ternary-goldbach@ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.
