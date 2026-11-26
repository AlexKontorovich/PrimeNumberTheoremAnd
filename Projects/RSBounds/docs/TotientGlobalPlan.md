# Global totient bound: analytic inputs and the finite handoff

The requested theorem is for every integer `n >= 3`:

\[
\frac{n}{\varphi(n)}<e^{\gamma_E}\log\log n+
 \frac{2.50637}{\log\log n}.
\]

The existing result for at most twenty distinct prime factors is a finite
certificate, not a substitute for this theorem. The finite verification should
be chosen to meet an analytic bound on the prime-product function.

## A concrete handoff using the published RS62 inputs

Let `G = exp(gamma_E)`, `F(x) = product_{p <= x} p/(p-1)`, and let theta be
Chebyshev's function. The checked scalar reduction in
`RSBounds/TotientAnalyticReduction.lean` uses

\[
\theta(x)\ge x\left(1-\frac1{2\log x}\right),\qquad
F(x)<G\left(\log x+\frac1{2\log x}\right).
\]

Together with `log x >= 6` and `1 <= G <= 1.7811`, it gives

\[
F(x)<G\log\theta(x)+\frac{2.50637}{\log\theta(x)}.
\]

The published theta input RS62 (3.14) starts at `x = 563`; the product
input (3.29) starts at `x = 286`. Thus the direct published-input handoff is
**prime cutoff 563**, and the finite prime-product certificates must cover
primes through **557**. The condition `log x >= 6` in the scalar lemma does
not by itself lower the threshold of (3.14). Proving extra theta values
between 409 and 557 could lower this handoff, but is not necessary.

The existing exchange lemma compares any n with the primorial determined by
its number of distinct prime factors. Consequently, this finite-prime check
and the analytic prime-product estimate cover all n; no arbitrary maximum n
is needed.

RS62's own Section 9 makes a somewhat sharper handoff. It checks primorial
comparisons through the prime 313, covering `log n < 294`, and uses Lemma 15
analytically for `log n >= 255`. The intermediate range uses Theorem 19;
the larger range uses (3.14). Its coefficient 2.5 has an exceptional integer
223092870; the uniform coefficient 2.50637 is Theorem 16, equation (3.42).

## What a psi-error input must supply

Write `Q(t) = psi(t)-t` and `e(t) = Q(t)/t`. The relevant signed tail in the
logarithmic Mertens-product argument is

\[
\int_x^\infty e(t)\frac{1+\log t}{t\log^2t}\,dt.
\]

A fixed bound `abs(Q(t)) <= epsilon*t` does not bound this integral by
absolute integration: the resulting majorant includes
`epsilon * integral_x^infinity dt/(t*log t)`, which diverges. The inspected
Rankin/Euler-product comparison similarly retains an error of order epsilon
when only this fixed relative bound is substituted. This is a limitation of
these direct reductions, not an impossibility claim about other arguments
using additional facts about zeta.

Thus the moderate-error psi row can support a finite or intermediate range,
but the full proof must also control this signed tail, or use a sufficiently
decaying error envelope. RS62 Section 8, Lemmas 7 and 8, obtains the signed
integrals from the explicit formula and zero sums; its product estimate is
not obtained by inserting a constant epsilon into an absolutely convergent
tail integral.

## A useful sufficient criterion from a decaying envelope

The following is a mathematical reduction, **not yet a Lean theorem in this
project**. Suppose for all `t >= x > 1` that `abs(Q(t)) <= t*eta(t)`, with the
weighted integrals below absolutely convergent. Finite Abel summation,
followed by the existing Mertens limit and the global Chebyshev bound to
dispose of the upper endpoint, gives

\[
|E_{2\Lambda}(x)|\le M(x):=
 \frac{\eta(x)}{\log x}+
 \int_x^\infty\eta(t)\frac{1+\log t}{t\log^2t}\,dt.
\]

If `T(x)` bounds the prime-power truncation error in the log Euler product,
then

\[
F(x)\le G\log x\,\exp(M(x)+T(x)).
\]

If also `psi(x)-theta(x) <= B(x)`, set

\[
s_0=\log x+\log\left(1-\eta(x)-\frac{B(x)}x\right).
\]

Provided the logarithm is defined, `s_0 >= sqrt(2.50637/G)`, and

\[
G\log x\,\exp(M(x)+T(x))
 <G s_0+\frac{2.50637}{s_0},
\]

the desired prime-product bound follows by monotonicity of `G*s+c/s`.
This criterion determines a genuine analytic handoff from the estimates
actually proved, rather than choosing a maximum n first.

For example, `eta(t)=a/log(t)^2` gives exactly

\[
M(x)=\frac{a}{2\log^2x}+\frac{4a}{3\log^3x}.
\]

With the usual vanishing prime-power corrections, the leading scalar
condition has room whenever `a < 2*2.50637/G`. A numerical threshold still
requires a complete, certified envelope and the correction bounds; this
document does not assert one.

## Reuse before new proofs

- The local IEANTN solution `RosserSchoenfeld1962.v1` proves the unconditional
  bound `psi(x) < 1.03883*x` (RS62 (3.35)); it does not contain the product
  estimate (3.29) or the totient theorem. Its coarse upper bound is useful
  for prime-power corrections.
- `TernaryGoldbach/Prelim/PNTMertens.lean` already ports the IEANTN/PNT+
  Mertens identity with the constant identified as Euler's constant. That
  identity should be reused, not re-proved.
- `RSBounds/MertensTailReduction.lean` makes its missing quantitative input
  explicit. Centering the integral at `E1(x)` gives
  `E2(x) = -integral_x^infinity (E1(t)-E1(x))/(t*log(t)^2) dt`.
  Consequently a uniform tail-variation bound `abs(E1(t)-E1(x)) <= D`
  gives `abs(E2(x)) <= D/log(x)`, with no factor two. This conditional
  reduction does not supply the analytic variation estimate itself.
  Both lemmas and the reused identity compile; the audit in
  `verification/MertensTailReductionAudit.lean` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.
- The existing `Prelim/MertensProduct.lean` contains useful elementary
  product-tail lemmas, but its numerical global theorem currently uses RH
  and Buthe inputs. Those numerical dependencies must not be imported as
  if they had been discharged.

Primary source: [Rosser and Schoenfeld (1962), Sections 8 and 9, pp. 83–89](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
