# Moderate psi estimate from the quartic formula

Status: checked. Fresh-source compilation and all 22 transitive axiom
audits passed on 2026-11-06 at 20:45:39 UTC. The source was unchanged
during the check; only `propext`, `Classical.choice`, and `Quot.sound`
occur in the audited declarations.

The checked public export is
`TernaryGoldbach.RSBounds.ModeratePsi.psi_error_le`:

\[
\mathrm{FiniteRH}(1894439),\quad x\ge100000
\quad\Longrightarrow\quad
|\psi(x)-x|\le0.0023x+6\sqrt x.
\]

It holds on a half-line, although its immediate use is the finite interval
from 100000 to exp23 in the Mertens/totient handoff. A constant relative
error estimate alone is not the decaying tail needed for absolute
integrability at infinity.

All new declarations are in `RSBounds/ModeratePsi.lean`. The supporting
quartic, zero-count, first29 table, and integral modules remain unchanged.
The three logical namespaces in this file are:

* `PolynomialRemainderFlexibleStep`: apply the existing left-contour
  majorant to any positive step delta≤.01 with 1/delta≤65536; the normalized
  remainder is at most 25000/(pi*sqrt(x)). The existing majorant, its
  integral≤50000, and the exact integral identity are reused.
* `ModeratePsiScalars`: seven exact rational `LogCert` checks imply the
  elementary reciprocal/fifth-tail allowances. Only kernel-checked integer
  and rational arithmetic is used in those certificates.
* `ModeratePsi`: actual upper/lower quartic coefficients, finite sums with
  analytic multiplicity, finite-RH specialization, and passage through the
  existing explicit formula and psi sandwich.

The step is delta=.001 and the positive ordinate split is Y=2000.
Set C=17000000000000, an upper bound for R4(delta)/delta^4. The sufficient
scalar bounds are

\[
 I(100,2000)\le2.1,\qquad (G(100)-29)/100\le.03,\qquad
 C\,[J(2000)+2R(2000)/2000^5]\le.27.
\]

The proved first29 head≤.592316 then gives a full finite-RH contribution
at most 5.995521264 sqrt(x), which is relaxed to 6 sqrt(x). No cancellation
band refinement is needed. The inclusive cutoff A=1894439 belongs to the
finite-RH part; the high tail is the interval (A,T].

The high contribution uses the existing reciprocal-cube tail<3e-13 and
`t^(-5) <= A^(-2)*t^(-3)`. Consequently its coefficient is below2e-12,
and reflection gives the factor x+1. No new zero-free-region hypothesis is
used. The left remainder plus log(2pi) is at most .000295x on x≥100000;
the high tail costs at most .000005x, and unsmoothing costs .002x.

The verification command, after sourcing `../lean-env.sh`, is
`python verification/run_moderate_psi_check.py`. It directly compiles the
exact source and its22 axiom queries in one process, recording source,
dependency, input, and object hashes. Only `propext`, `Classical.choice`,
and `Quot.sound` are accepted. The final receipt is
`verification/moderate-psi-run.json`; the log is
`verification/moderate-psi-build-audit.log`.

The successful source SHA-256 is
`832dc16238e12d935edf16b9290c788789678f766b2d1c23d3f948f9dd6214b6`;
the object SHA-256 is
`90b8741c6be1222ed02ab9e99b8d82cd11786f2d0bceb5fb77898f3a456c9a29`.
The single-process check took 323.91 seconds. The two earlier failed
attempts are preserved under the `moderate-psi-attempt1` and
`moderate-psi-attempt2` verification prefixes; their failures were local
elaboration issues, and neither is a successful receipt.
