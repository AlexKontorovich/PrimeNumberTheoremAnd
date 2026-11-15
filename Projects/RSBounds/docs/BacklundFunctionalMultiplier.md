# Checked Gamma baseline and functional-equation multiplier

`BacklundGammaBaseline.lean` proves the exact identity, for `t > 0`,

\[
|\Gamma(1+it)|^2=\frac{\pi t}{\sinh(\pi t)}
=\frac{2\pi t e^{-\pi t}}{1-e^{-2\pi t}}.
\]

It follows directly from Mathlib's proved Gamma reflection, recurrence,
and conjugation formulae. No effective Stirling estimate is assumed.

`BacklundFunctionalMultiplier.lean` then proves the exact endpoint

\[
|\zeta(it)|\le\sqrt{\frac{t}{2\pi}}\,|\zeta(1+it)|.
\]

The squared functional-equation multiplier here is
`t/(2*pi) * sinh(pi*t/2)/cosh(pi*t/2)`, which is at most `t/(2*pi)`.

`BacklundFunctionalStrip.lean` proves, for `-1/2 <= sigma <= 1/2` and
`t >= 50`,

\[
|\zeta(\sigma+it)|\le
\left(\frac{t}{2\pi}\right)^{1/2-\sigma}
\exp\!\left(\frac{5}{2t^2}\right)
|\zeta(1-\sigma+it)|.
\]

The constant in the exponential has two proved contributions:
`9/(4*t^2)` from the symmetric horizontal Gamma modulus comparison in
`BacklundGammaModulusHorizontal.lean`, and `1/(4*t^2)` from the hyperbolic
factor. The latter is bounded using
`exp(-pi*t) <= 1/(8*t^2)` and
`sqrt((1+q)/(1-q)) <= exp(2*q)` for `0 <= q <= 1/2`.

The five baseline audits and three strip audits report only `propext`,
`Classical.choice`, and `Quot.sound`. Fresh source hashes and commands are
recorded in `verification/backlund-gamma-baseline-run.json` and
`verification/backlund-functional-strip-run.json`.

These inequalities supply functional-equation inputs to the separate
boundary estimates; they do not themselves assert Rosser's complete
zero-count bound.
