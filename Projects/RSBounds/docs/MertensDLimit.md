# Euler-normalized signed Mertens identity

`RSBounds/MertensDLimit.lean` passed its exact-source build and twelve
transitive axiom audits. The audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. Three audited finite identities are
imported from `MertensDFinite`; nine declarations are local.

The main identity is unconditional, for every real `x ≥ 1`:

\[
E_{1,\Lambda}(x)=\frac{\psi(x)-x}{x}-\gamma-\Re I(x),
\qquad I(x)=\lim_{b\to\infty}\int_x^b\frac{\psi(t)-t}{t^2}\,dt.
\]

The actual improper limit was established in `MertensSignedLimit`. The
Euler constant is identified using the checked Abel transform and the
Laurent expansion of the actual zeta function. No pointwise prime number
theorem, finite RH assertion, or normalization constant is assumed.

`J_eq_signedLimit` identifies the signed function used in
`MertensSecondSigned` with `Re I(x)`. The prime-power comparison then gives
the exact RS62 constant in `primeWeightedSum_lower_signed`.
`mertens_lower_of_errors` reduces the quantitative weighted lower bound to
an endpoint psi bound and a signed-tail budget; it does not assert those
numerical premises.

Receipt: `verification/mertens-d-limit-run.json`.
Source SHA256: `5ecf362a262c56637b1e5d50fe09afdcd201bd20059861c19a6581d3520764dd`.
The first failed pass, containing a missing import and redundant final
tactic, is retained as attempt1 evidence.

The global quantitative Mertens and totient targets remain separate pending
work. Any closure using the finite-height critical-line check must retain
that check as an explicit hypothesis.
