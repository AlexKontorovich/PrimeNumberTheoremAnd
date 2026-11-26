# A decaying actual signed-tail envelope

`RSBounds/MertensPotentialDecay.lean` passed its exact-source build and all
six transitive axiom audits, with only the standard three axioms.

For `1 ≤ x ≤ u`, `T ≥ 1894439`, and the explicit premise
`Goals.FiniteRH 1894439`, the actual zero potential satisfies

\[
\|P(u)\|\le0.0463x^{-1/2}
 +0.0463x^{-1/(10\log(T/17))}+2\,\mathrm{squareAllowance}(T).
\]

The corresponding bound on the actual signed psi integral adds
`6000*x^(-3/2) + log(2*pi)/x`. The same bound controls `|J(u)|`, where `J`
is the function in the checked second-Mertens formula. The cutoff `T` is
chosen from the lower endpoint `x`, so the estimate is uniform for every
`u ≥ x`.

Finite RH is used only in the head through 1894439. The entire middle
window uses the proved unconditional RS75 zero-free region, weakened to
constant 10. The final tail uses the proved unconditional actual zero
count and reciprocal-square partial summation. Increasing `T` introduces
no stronger RH assumption.

The separate scalar specialization takes
`T = 17*exp(sqrt(log x/10))`. It is not an extra hypothesis in the intended
closed numerical bound; that specialization has its own checks.

Receipt: `verification/mertens-potential-decay-run.json`.
Source SHA256: `c4cac720b55a75c5d24483971f3f0eaba7d16ee24fd3cb94b39f794e8faad0c8`.
The two earlier failed source checks are preserved separately.
