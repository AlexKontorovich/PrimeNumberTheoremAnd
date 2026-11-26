# Normalizing the signed Mertens formulas

Write

\[
E_{1,\Lambda}(x)=\sum_{n\le x}\frac{\Lambda(n)}n-\log x,
\qquad D(x)=E_{1,\Lambda}(x)-\frac{\psi(x)}x.
\]

The finite Abel identity already proved in this project gives
`D(x) = integral(1..x, (psi(t)-t)/t^2)` for `x >= 1`.
Consequently, convergence of the signed integral supplies convergence of D
directly. A pointwise prime number theorem is unnecessary for identifying its
constant.

## Checked ingredients

- `MertensAbelIdentity.error_abel_identity` proves, for every real `s > 1`,
  `(s-1) * integral(1..infinity, E1Lambda(x)*x^(-s))`
  `= -Re(zeta'(s)/zeta(s)) - 1/(s-1)`.
  It reuses Mathlib's summatory-coefficient integral theorem and the existing
  unconditional boundedness of `E1Lambda` in the calr port of PNTMertens.
- `MertensPsiAbel.D_abel_identity` proves that the corresponding average of D
  is `-(Re(zeta'/zeta(s)) + 1/(s-1) + 1)/s`.
  Chebyshev's elementary `psi(x)=O(x)` bound suffices. All ten exports in this
  module passed their standard-axiom audits.
- `MertensAbelianNormalization.normalized_logDeriv_tendsto` obtains the
  limit `-EulerGamma` from Mathlib's existing Laurent expansion in
  `Mathlib.NumberTheory.Harmonic.ZetaAsymp`.
- `MellinAbelianLimit.average_tendsto` proves that a bounded, measurable real
  function tending to C at infinity has its Mellin-Abelian average tending to
  C as `s -> 1+`. Together with its helpers and the pole-limit theorem, five
  exports passed the transitive audit.
- `MertensLimitNormalization.limit_eq_neg_euler` identifies the limit of
  `E1Lambda` as `-EulerGamma` **if convergence is supplied**. It does not assert
  that convergence and is not a proof of the quantitative RS62 inequality.
- `MertensCenteredNormalization.centered_limit_eq` identifies the limit of
  D as `-EulerGamma-1` **if convergence is supplied**. Both exports in this
  module have passed their standard-axiom audits.
- `MertensDLimit.D_eq_integral` and `D_sub_eq_integral`, in the separate
  `MertensDFinite` module, prove the exact finite signed-integral identities.
  All three exports in that module have passed their standard-axiom audits.

These ingredients are unconditional and use only `propext`, `Classical.choice`
and `Quot.sound`. Their receipts are `verification/mertens-abel-identity-run.json`,
`mertens-psi-abel-run.json`, `mellin-abelian-limit-run.json`, and
`mertens-limit-normalization-run.json`, `mertens-centered-normalization-run.json`,
and `mertens-d-finite-run.json`.

## Remaining assembly

Combining the checked centered normalization with the
actual zero-potential and left-remainder limit will identify the improper
signed integral at 1 as `-EulerGamma-1`, giving

\[
E_{1,\Lambda}(x)=\frac{\psi(x)-x}{x}-\gamma-J(x),
\quad J(x)=\lim_{b\to\infty}\int_x^b\frac{\psi(t)-t}{t^2}\,dt.
\]

The limit notation matters: convergence of this improper signed integral alone
does not assert absolute Lebesgue integrability. The zero-sum construction
keeps that distinction explicit.

Numerical bounds on the two displayed errors, the finite weighted-prime
certificate, and the product/totient handoff are further obligations. Any
quantitative result using the b=23 estimate retains its finite-RH hypothesis
until a separate certificate discharges it.
