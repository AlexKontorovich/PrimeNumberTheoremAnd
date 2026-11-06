# Exact Backlund count identity

The development in `RSBounds/BacklundCountIdentity.lean` proves, for every
`T > 0` at which zeta has no zero with imaginary part `T`,

\[
N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78
+\frac{A(T)}\pi+\frac{R_\Gamma(T)}\pi.
\]

Here `N(T)` counts **all** zeros with `0 < Im(rho) < T`, with their actual
analytic multiplicities. The count is a natural number defined by a finite
sum. Its identification with zeta zeros and zeta analytic orders is proved
in `BacklundCountMultiplicity.lean`; no simple-zero assumption is used.

The actual argument integral has anchor `5/4`:

\[
A(T)=\int_0^T\Re\frac{\zeta'}\zeta(5/4+it)\,dt
-\int_{1/2}^{5/4}\Im\frac{\zeta'}\zeta(\sigma+iT)\,d\sigma.
\]

The gamma remainder uses a continuous phase, rather than the principal
logarithm of Gamma:

\[
R_\Gamma(T)=\int_0^{T/2}\Re\operatorname{digamma}(1/4+it)\,dt
-\frac T2\log\frac T2+\frac T2+\frac\pi8.
\]

Public namespace: `TernaryGoldbach.RSBounds.BacklundCountIdentity`.

| Export | Content |
| --- | --- |
| `mem_positiveZeros_iff_zeta` | The finite support is exactly the zeta zeros with `0 < Im < T`. |
| `N_eq_sum_zetaMultiplicity` | The weights are actual analytic orders of zeta. |
| `rectangle_count_identity` | The upper-rectangle integral of xi'/xi equals `2*pi*i*N(T)`. |
| `pi_mul_N_eq_xiArcVar` | Xi symmetry identifies its arc variation with `pi*N(T)`. |
| `xiArcVar_eq_pi_add_theta_add_zetaArgVar` | Exact evaluation of pole, pi, Gamma, and zeta factors. |
| `count_identity` | `N = 1 + theta/pi + A/pi`. |
| `count_identity_mainTerm` | The displayed Riemann--von Mangoldt identity. |

The proof uses the upper rectangle `[-1/4,5/4] x [0,T]`. Thus the rectangle
already contains just the positive-ordinate zeros; no conjugate-multiplicity
halving is needed. Nonvanishing of xi on the real axis is proved directly
from calr's Euler--Maclaurin integral. The residue theorem and xi function
come from calr's existing checked development. Boundary folding and the
pole-factor antiderivatives adapt the method in Gershon Bialer's count
proof; the gamma rectangle uses the separately checked IEANTN digamma
analyticity. Exact source revisions and adaptations are recorded in
`verification/backlund-count-identity-provenance.json`.

No RH certificate, zero-count bound, asymptotic PNT, or unproved analytic
input is assumed. A good height means only that zeta has no zero on that
horizontal line. The inclusive upper endpoint and the numerical Rosser
inequality are separate developments.

Fresh direct Lean 4.35 compilation of all eight dependency modules and
18 transitive axiom audits passed on 2026-11-06, finishing at 11:41:43 UTC.
Every audit contains exactly `propext`, `Classical.choice`, and `Quot.sound`.
The exact source hashes, commands, and exit codes are in
`verification/backlund-count-identity-run.json`. The reproducible sequential
runner is `verification/run_backlund_count_identity_check.py`.

## Inclusive endpoint extension

`RSBounds/BacklundCountEndpoint.lean` now defines `N_le(T)` with the
convention `0 < Im(rho) <= T`, retaining actual zeta analytic multiplicities.
The theorem `exists_right_interval_good_count` proves that, for every
positive T, there is a nonempty interval immediately above T on which every
height is good and the open count equals `N_le(T)`. This follows from the
finite zero set below `T+1`; it requires no RH certificate.

`closed_count_abs_le_of_good_height_bound` transfers a bound
`|N(S)-M(S)| <= B(S)` at good heights `S>T` to the inclusive count at T,
provided M and B are continuous at T. The `_abs_lt_` variant preserves a
strict target bound by using a positive margin. One-sided variants are
also supplied.

Six fresh transitive axiom audits passed, each with exactly the standard
three axioms. Evidence: `verification/backlund-count-endpoint-run.json`
and `verification/backlund-count-endpoint-axioms.log`; finished at 2026-11-06T11:50:41.340294+00:00.
