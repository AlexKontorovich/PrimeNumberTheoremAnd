# A closed bound for the actual signed integral

`RSBounds/MertensLargeBudget.lean` passed its exact-source build and all six
transitive axiom audits, using only the standard three axioms.

Assuming only `Goals.FiniteRH 1894439`, for every real `x ≥ exp 2400` and
every `u ≥ x`, the actual improper signed integral satisfies

\[
 \left|\int_u^\infty\frac{\psi(t)-t}{t^2}\,dt\right|
 <\frac1{(\log x)^2}.
\]

Here the integral notation denotes the already proved limit of the finite
interval integrals. The theorem also bounds the actual function `J(u)` in
the second-Mertens identity by the same expression.

The cutoff is the actual expression
`17 * exp(sqrt(log x / 10))`. Its square root, logarithm and exponential
identities are proved in `actual_envelope_eq`. The generic zero-potential
bound and every numerical scalar allowance are then discharged by checked
dependencies. No free zero-sum, normalization, or PNT premise remains in
`norm_signedLimit_lt` or `abs_J_lt`.

Finite RH is used only through height 1894439. The higher cutoff is a
division of the zero sum: the proved unconditional zero-free region
controls its middle window and the proved zero count controls its tail.

The final adapter `mertens_lower_of_weak_psi` combines this bound with an
explicit `0.1*x/log x` psi premise; the separate global Mertens assembly
supplies that premise from the checked `WeakPsiTail` theorem.

Receipt: `verification/mertens-large-budget-run.json`.
Source SHA256: `6ac8957e3935b6d96d3728c412b5430d624f04ac6bbb3a32022691658d0efe0a`.
The first failed pass is preserved; its sole remaining error was a final
division-normalization tactic in the weighted-Mertens adapter.
