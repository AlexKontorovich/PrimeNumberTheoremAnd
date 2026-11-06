# Unrestricted totient bound: source audit

The goal is the inequality for every integer `n >= 3`, not a bound whose
usefulness depends on an arbitrarily chosen upper limit for n.

## What RS62 actually uses

In Rosser–Schoenfeld (1962), the uniform coefficient `2.50637` is Theorem 16,
equation (3.42). Theorem 15 has coefficient `2.5`, with the single exception
`n = 223092870` (the primorial ending at 23).

The proof in §9, pp. 88–89, checks primorial intervals through the prime 313.
This covers `log n < 294`. Its Lemma 15 supplies an overlapping analytic
argument for `log n >= 255`: up to 1340 it uses the limited-range theta
estimate in Theorem 19; thereafter it uses (3.14). Both parts use the Euler
product estimate (3.29). Thus the finite work is on a short list of prime
cutoffs, not on all integers below a large power of ten.

The published input ranges are:

- (3.29): `product_{p<=x} p/(p-1) < exp(gamma)*(log x + 1/(2 log x))`, for
  `x >= 286`.
- (3.14): `theta(x) > x*(1 - 1/(2 log x))`, for `x >= 563`.

The paper derives (3.29) in §8 using integrated explicit-formula estimates
in Lemmas 6–13. It does not derive that estimate merely by substituting one
constant relative error bound into an absolutely convergent tail integral.

Primary source: [RS62](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf),
especially pp. 70, 72, 83–89.

## A simpler handoff for the current Lean reduction

The checked `rs62_primeProduct_bound_of_inputs` in
[`TotientAnalyticReduction.lean`](../RSBounds/TotientAnalyticReduction.lean)
requires `log x >= 6`, the two analytic inputs above, and
`1 <= exp(gamma) <= 1.7811` (the upper bound is already checked in the finite
certificate module). Since `563 > exp 6`, the direct handoff using the
published input ranges is the prime 563. A finite certificate through 557
now covers every smaller prime cutoff. This conditional handoff is checked in
[`TotientGlobalReduction.lean`](../RSBounds/TotientGlobalReduction.lean): its
final theorem covers every integer `n >= 3`. The two analytic inputs remain
unproved in this project and are explicit theorem arguments.

One could reduce the finite cutoff to 401 only after separately proving the
theta lower estimate at the intervening primes 409 through 557. The scalar
lemma's threshold alone does not establish that additional finite work.

The new certificate extends the existing checked walk from 71 to 557,
reusing its generic checker and preserving the earlier proof sources.
`scripts/gen_totient_handoff.py` reproduces the five added certificates.
The checker verifies the target product inequality directly and includes
the delicate prime-23 case through the original certificate. No estimate
for all integers up to the corresponding primorial is checked individually.
All four exported results passed a fresh transitive axiom audit; the record
is `verification/totient-global-run.json`.

## Why one constant relative psi bound needs further analysis

This is a limitation of the direct partial-summation argument, not a claim
of a logical independence result for the actual zeta function.

If `|psi(t)-t| <= epsilon*t` with a fixed positive epsilon, estimating the
standard Mertens tail in absolute value would encounter

\[
\epsilon\int_x^\infty\frac{1+\log t}{t\log^2t}\,dt,
\]

which diverges. Also, a constant relative theta lower bound gives only a
constant additive difference between `log theta(x)` and `log x`; this does
not directly supply the shrinking `1/log x` allowance in the target
product bound. A decaying error envelope, or a separately proved cancellation
estimate for the integrated error, is needed for this route.

The local upstream `Prelim/PNTMertens.lean` already identifies the Mertens
constant as Euler's gamma without RH or Büthe hypotheses. Its exact
error identity is useful, but does not by itself give the missing numerical
tail bound. In contrast, upstream `Prelim/MertensProduct.lean` declares
`Fact RHUpTo` and `Fact ButhePsi`, and its analytic proof uses a decaying
large-x theta bound and an integrated plateau error. That proof cannot be
imported as the requested unconditional analytic input.
