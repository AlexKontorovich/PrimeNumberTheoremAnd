# Quantitative signed Mertens tail through finite RH

`RSBounds/MertensPotentialBound.lean` passed its exact-source build and all
fifteen transitive axiom audits. Only `propext`, `Classical.choice`, and
`Quot.sound` occur. Finite RH is an explicit hypothesis, not an axiom.

For every real `x ≥ 1`, assuming `Goals.FiniteRH 1894439`, the actual
signed integral from `MertensSignedLimit` satisfies

\[
 \|I(x)\|<j(x):=0.0463x^{-1/2}+2.4\cdot10^{-6}
       +6000x^{-3/2}+\log(2\pi)/x.
\]

The same `j(x)` bounds `|J(u)|` uniformly for every `u ≥ x`, with `J`
the actual function in the checked second-Mertens identity.

The finite-RH premise is used only for ordinates at most 1894439. The high
tail follows from the checked unconditional Rosser count and partial
summation, with the conjugation factor exactly two. All zeros carry their
actual analytic multiplicities. A finite-subset exhaustion and summability
pass the estimate to the actual infinite zero potential.

The module also binds the checked scalar budgets to the exact weighted
prime sum: the moderate psi estimate closes `100000 ≤ x ≤ exp 23`; the
b23 estimate closes the subsequent range through `log x = 2400`. The psi
estimates are explicit interface inputs in these two adapters.

The fixed high-tail constant does not decay. This theorem therefore does
not by itself settle the unbounded Mertens or totient range. The separate
variable-cutoff estimate is being checked for that purpose.

Receipt: `verification/mertens-potential-bound-run.json`.
Source SHA256: `6e48ff3157ad7959f6307a9d7fc50c2518125845e7e4e8f63e890a3f08150c90`.
The first two failed passes are archived separately; the final pass took
265.52 seconds and emitted the object before the audit guards succeeded.
