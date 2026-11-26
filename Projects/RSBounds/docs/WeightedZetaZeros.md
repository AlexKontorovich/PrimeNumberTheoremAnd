# Weighted sums over the actual zeta zeros

`RSBounds/WeightedZetaZeros.lean` connects the already proved finite
partial-summation lemmas to Mathlib's actual zeta zeros, retaining analytic
multiplicity and the inclusive upper endpoint. It imports the unconditional
Rosser count theorem; it does not ask applications to supply a counting
estimate or an RH hypothesis.

Write `m(rho)` for the analytic zero order and

\[
 S(a,b;\phi)=\sum_{a<\Im\rho\le b}m(\rho)\phi(\Im\rho).
\]

The Lean definition `weightedSum` uses the proved finite set
`closedPositiveZeros b`, not a numerical list of purported zeros. The
finite set `zeroCopies b` repeats each zero exactly `m(rho)` times. The
lemma `ordinateCount_zeroCopies` proves that its counting function equals
`Rosser1941.positiveZeroCount t` whenever `0 < t <= b`.

For `0 < a <= b`, a weight with derivative `phi'` throughout `[a,b]`, and
an interval-integrable derivative, `weightedSum_eq` gives

\[
 S(a,b;\phi)=N(b)\phi(b)-N(a)\phi(a)-\int_a^b N(t)\phi'(t)\,dt.
\]

Both counts are inclusive, so the summation interval is exactly `(a,b]`.
`intervalIntegrable_count_mul` separately proves integrability of the actual
count times an interval-integrable function on each positive finite interval.

For `2 <= a <= b` and `phi' <= 0` in the interior, set

\[
 F(t)=\frac{t}{2\pi}\log\frac{t}{2\pi}-\frac{t}{2\pi}+\frac78,
 \qquad R(t)=0.137\log t+0.443\log\log t+1.588.
\]

The theorem `weightedSum_le_decreasing` states

\[
\begin{aligned}
S(a,b;\phi)\le {}&\int_a^b
\left(\frac{\log(t/(2\pi))}{2\pi}
+\frac{0.137+0.443/\log t}{t}\right)\phi(t)\,dt\\
&+(N(b)-F(b)-R(b))\phi(b)\\
&-(N(a)-F(a)-R(a))\phi(a).
\end{aligned}
\]

The proof instantiates the existing decreasing-ordinate-sum theorem using
the proved Rosser bound. It proves the required main-term and envelope
derivatives and their integrability internally. In particular, no assumed
counting bound remains in the exported statement.

If additionally `0 <= phi b`, `weightedSum_le_decreasing_head` discards the
nonpositive upper correction and retains

\[
S(a,b;\phi)\le\int_a^b(F'(t)+R'(t))\phi(t)\,dt
 +(F(a)+R(a)-N(a))\phi(a).
\]

Thus a certified finite count, such as `N(100)=29`, can enter as the exact
lower endpoint rather than being replaced by a second error envelope.

These are finite-sum theorems. They do not yet assert an infinite-tail limit,
evaluate the specific quartic smoothing integral, or complete the `b=23`
psi estimate. The new module is separate from the frozen two-theorem
Comparator challenge.

The module freshly compiled and all eight transitive axiom audits passed
on 2026-11-06 at 14:17:52 UTC. Every audited export uses only `propext`,
`Classical.choice`, and `Quot.sound`. The reproducible checker is
`verification/run_weighted_zeta_zeros_check.py`; source hashes, successful
exit codes, and timings are recorded in
`verification/weighted-zeta-zeros-run.json` and the corresponding logs.
This verification covers the new module separately from the zero-count
Comparator's two target theorems.
