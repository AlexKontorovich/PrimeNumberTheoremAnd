# Quantitative left remainder and its endpoint limit

The modules `MertensIntervalLeftBound.lean` and `MertensEndpointLeft.lean`
continue the finite-interval explicit formula in `MertensSignedInterval.lean`.
They concern the actual left vertical integral, not a numerical surrogate.
No RH premise or assumed integral evaluation is used.

For positive endpoints `a,b`, write

\[
L(a,b)=\frac1{2\pi}\int_{\mathbb R}
 \frac{\zeta'}{\zeta}(-\tfrac12+it)
 \frac{b^{-3/2+it}-a^{-3/2+it}}
 {(-\tfrac12+it)(-\tfrac32+it)}\,dt.
\]

`MertensIntervalLeftBound.norm_leftRemainder_le` bounds its norm by

\[
6000\,(a^{-3/2}+b^{-3/2}).
\]

The proof uses the existing unconditional bound
`PolynomialLeftRemainder.norm_logDeriv_zeta_left_log` and the following
explicit estimates:

* the numerator is at most `a^(-3/2)+b^(-3/2)` on the left line;
* each denominator factor has norm at least `(1+|t|)/4`;
* the logarithmic derivative has norm at most `500 sqrt(1+|t|)`;
* the full-line integral of `(1+|t|)^(-3/2)` is exactly `4`.

Thus the unnormalized integral is bounded by `32000` times the endpoint
sum, and division by `2*pi` gives the stated coarse constant. The exact
power integral is proved from a real antiderivative and the symmetry
identity `MeasureTheory.integral_comp_abs`.

The endpoint module defines

\[
F(c)=\frac1{2\pi}\int_{\mathbb R}
 \frac{\zeta'}{\zeta}(-\tfrac12+it)
 \frac{c^{-3/2+it}}{(-\tfrac12+it)(-\tfrac32+it)}\,dt.
\]

Its checked public chain is:

| Declaration | Statement |
|---|---|
| `integrable_endpointIntegrand` | The endpoint integral converges for `c>0`. |
| `norm_F_le` | `norm (F c) <= 6000*c^(-3/2)` for `c>0`. |
| `leftRemainder_eq_sub_F` | `L(a,b) = F(b)-F(a)` for positive endpoints. |
| `leftRemainder_add` | `L(a,b)+L(b,c)=L(a,c)`. |
| `tendsto_F_atTop` | `F(c)` tends to zero as `c` tends to infinity. |
| `tendsto_leftRemainder_atTop` | `L(a,b)` tends to `-F(a)` for fixed `a>0`. |

The minus sign in the final limit follows from the endpoint order in the
interval kernel. These results remove the left remainder as a separate
obstruction to taking the infinite-interval limit. They do not establish
the zero-sum limit at the moving endpoint, Euler-constant normalization,
or either final RS62 inequality.

The reproducible verification commands are
`python verification/run_mertens_interval_left_bound_check.py` and
`python verification/run_mertens_endpoint_left_check.py`, after sourcing
`../lean-env.sh`. Their JSON receipts are the authority for verification
status. Each compiles the exact source with the public axiom checks
appended in the same process and records source, dependency, input, and
object hashes. Only `propext`, `Classical.choice`, and `Quot.sound` are
accepted by the audit guard.

Both modules passed their fresh-source checks on 2026-11-06. The finite
bound has eight audited declarations; the endpoint module has ten. The
endpoint source SHA-256 is
`b5213c334c91e93ab32b2705a5b6cdcdd4881e4cff9e7fed5d1a823b65a757a7`.
Its successful receipt is `verification/mertens-endpoint-left-run.json`;
the final endpoint replay took 290 seconds, including 281 seconds loading
imports. Earlier incomplete or failed attempts remain archived separately.
