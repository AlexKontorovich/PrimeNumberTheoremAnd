# The proved reciprocal-cube tail

For every real `T >= A`, where `A = 1894439`, the new module proves

\[
\sum_{A<\gamma\le T}\frac{m_\rho}{\gamma^3}<3\cdot10^{-13}.
\]

The sum is over actual nontrivial zeros of Mathlib's Riemann zeta function
with positive ordinate. Multiplicity is the actual analytic order. The
lower endpoint is excluded and the upper endpoint included, even when an
endpoint is a zero. **There is no RH assumption.**

The source compiled successfully, and all eight public transitive axiom
audits report only `propext`, `Classical.choice`, and `Quot.sound`.
This is a component toward the global theta estimate, not that estimate
itself.

## API

Import [`RSBounds.RosserCubicTail`](../RSBounds/RosserCubicTail.lean).
The declarations live in `TernaryGoldbach.RSBounds.RosserCubicTail`.

```lean
theorem cubic_sum_A_lt {T : ℝ} (hT : 1894439 ≤ T) :
    WeightedZetaZeros.weightedSum 1894439 T (fun t => 1 / t ^ 3) < 3e-13
```

The underlying `WeightedZetaZeros.weightedSum` is the same actual finite
zero sum used in the completed quartic psi proof. The general theorem
`cubic_sum_le` holds for `7 <= a <= b`; `cubic_sum_le_head` retains the exact
lower endpoint count correction. The integral identities are also exported.

## Proof and constants

Write `R(t) = 0.137 log t + 0.443 log log t + 1.588` and
`c(a) = 0.137 + 0.443/log a`. The proved Rosser count estimate and the
existing decreasing-weight partial summation theorem give

\[
\sum_{a<\gamma\le b}\frac{m_\rho}{\gamma^3}
\le
\frac{\frac12\log(a/(2\pi))+\frac14}{2\pi a^2}
+\frac{c(a)}{3a^3}+\frac{2R(a)}{a^3}.
\]

The elementary tail primitive is

\[
J_3(c,t)=
\frac{\frac12\log(t/(2\pi))+\frac14}{2\pi t^2}
+\frac{c}{3t^3}.
\]

Its negative has derivative
`(log(t/(2*pi))/(2*pi) + c/t)/t^3`. The proof integrates on the finite
interval `[a,b]` and discards the nonnegative `J_3(c(a),b)`; no improper
zero-sum convergence claim is needed.

The final scalar certificate uses the proved inequalities

\[
\log(A/(2\pi))\le13,\quad
1\le\log A\le15,\quad
\log\log A\le3,\quad \pi>3.14.
\]

They imply `c(A) <= 0.58` and `R(A) <= 6`. Exact rational arithmetic then
checks

\[
\frac{27/4}{6.28A^2}+\frac{0.58}{3A^3}+\frac{12}{A^3}
<3\cdot10^{-13}.
\]

The logarithm bounds follow from Mathlib's exponential bounds. No external
floating-point computation is part of the proof.

## Reuse and verification

The proof reuses
[`WeightedZetaZeros.weightedSum_le_decreasing_head`](../RSBounds/WeightedZetaZeros.lean),
the already proved actual Rosser count, and the density bounds in
[`RosserTailIntegrals`](../RSBounds/RosserTailIntegrals.lean).
The method is the decreasing-weight partial summation used in
[Rosser–Schoenfeld (1975), Section 3](https://doi.org/10.1090/S0025-5718-1975-0457373-7),
with the actual count supplied by
[Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).

The fresh exact-source build and eight in-process audits took 9.41 seconds:
[receipt](../verification/rosser-cubic-tail-run.json),
[build log](../verification/rosser-cubic-tail-build.log),
[axiom output](../verification/rosser-cubic-tail-axioms.log), and
[reproducible runner](../verification/run_rosser_cubic_tail_check.py).
The receipt records source, exact compiler-input, and output-object hashes.

The planned theta application chooses a variable quartic step
`delta = 1/(50 log x)` for `log x >= 400`, combines this cube tail with the
proved RS75 zero-free region, and uses the completed b=23 estimate below
that transition. The proposed target is `0.1*x/log x` for all `x >= exp 23`.
The variable-step zero-sum and remainder assembly remains to be proved.
