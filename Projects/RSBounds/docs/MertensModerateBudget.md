# Scalar Mertens handoffs

`RSBounds/MertensModerateBudget.lean` passed its exact-source build and all
three axiom audits, with only the standard three axioms. It imports Mathlib
only; there is no prime, zero, RH, or PNT assumption.

Writing

\[
j(x)=0.0463x^{-1/2}+2.4\cdot10^{-6}
      +6000x^{-3/2}+\log(2\pi)/x,
\]

the two strict numerical inequalities are:

* `x ≥ 100000`, `log x ≤ 23` implies
  `(.0023 + 6/sqrt x) + j(x) < 1/(2 log x)`.
* `x ≥ 10^9`, `log x ≤ 2400` implies
  `.00020211 + j(x) < 1/(2 log x)`.

These are scalar budgets. Their binding to the actual signed integral is
the separate `MertensPotentialBound` proof and is not asserted by this module.

Receipt: `verification/mertens-moderate-budget-run.json`.
Source SHA256: `12e4fd73b89e8a35de6a43ad7438bda17391ad9666e5423158193008d6e2f039`.
