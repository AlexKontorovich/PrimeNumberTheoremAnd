# Explicit weighted bounds for the actual zeta zeros

The new modules build on `WeightedZetaZeros`, whose finite sum

\[
S_\phi(a,b)=\sum_{a<\Im\rho\le b}
  \operatorname{ord}_\rho\zeta\,\phi(\Im\rho)
\]

uses actual zeros and analytic multiplicities. Write `S1` and `S5` for
weights `1/t` and `1/t^5`, and put `G=F+R`, with Rosser's original
`R(t)=0.137 log(t)+0.443 log(log(t))+1.588`.

For `7 <= a <= b`, `RosserWeightedBounds` proves

\[
S_1(a,b)\le I(a,b)+\frac{N(b)-G(b)}b+\frac{G(a)-N(a)}a,
\]

where

\[
I(a,b)=\frac{\log^2(b/(2\pi))-\log^2(a/(2\pi))}{4\pi}
 +\left(0.137+\frac{0.443}{\log a}\right)
  \left(\frac1a-\frac1b\right).
\]

The nonpositive upper correction can be discarded. The same module proves

\[
S_5(a,b)\le J(a)+\frac{G(a)-N(a)}{a^5}
 \le J(a)+\frac{2R(a)}{a^5},
\]

where `J` is the checked elementary tail expression in
`RosserTailIntegrals.J`. A fifth-power version retaining the signed upper
endpoint is also exported. These are finite-sum bounds uniform in `b`,
not an unproved passage to an infinite sum.

For `2 <= l <= u`, the reciprocal band lower bounds are

\[
S_1(l,u)\ge\frac{N(u)-N(l)}u
 \ge\frac{F(u)-R(u)-F(l)-R(l)}u.
\]

The principal declarations are `reciprocal_sum_le_endpoints`,
`reciprocal_sum_le_head`, `fifth_sum_le_endpoints`, `fifth_sum_le_head`,
`fifth_sum_le`, `reciprocal_sum_ge_count`, and `reciprocal_sum_ge_rosser`.
`weightedSum_const_eq` and `weightedSum_mono` supply finite count and
pointwise comparison helpers.

`RosserWeightedSplit` combines the endpoint corrections before rounding.
For `7 <= D <= Y <= T`, `k,C >= 0`, and `k/Y <= C/Y^5`, it proves

\[
\begin{aligned}
kS_1(D,Y)+CS_5(Y,T)\le{}&
k\left(I(D,Y)+\frac{G(D)-N(D)}D\right)+CJ(Y)\\
&+2R(Y)\left(\frac C{Y^5}-\frac kY\right).
\end{aligned}
\]

The same module supplies exact adjacent-window decomposition and monotone
finite telescoping for arbitrary weights. It also sums the explicit
reciprocal-band lower bound over any finite monotone partition, with an
optional nonnegative coefficient per band. Setting the number of bands to
eight matches the scalar budget's `bandMass` expression.

All these analytic estimates use the proved Rosser count theorem and have
no RH or count-envelope premise. They do not yet assert domination of the
particular quartic explicit-formula zero sum or the final psi estimate.

`RosserWeightedBounds` freshly compiled and all thirteen export audits
passed on 2026-11-06 at 14:35:24 UTC, using only `propext`,
`Classical.choice`, and `Quot.sound`. Evidence is in
`verification/rosser-weighted-bounds-run.json` and the corresponding logs.
`RosserWeightedSplit` also freshly compiled and all six export audits
passed, with only the standard three axioms, at 14:39:38 UTC. Its separate
record is `verification/rosser-weighted-split-run.json`. Both modules were
checked independently of the frozen zero-count Comparator challenge.
