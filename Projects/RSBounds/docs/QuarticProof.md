# The four-integration proof: checked formula and remaining estimates

The target remains the RS75 row at `b = 23`, with `m = 4`,
`delta = 0.0000211`, and RH assumed only through height `1894439`.
The numerical row itself is not proved by this project yet.

## Checked formula

Write

\[
P(s)=s(s+1)(s+2)(s+3)(s+4),\qquad
\Psi_4(x)=\frac1{24}\sum_{n\le x}\Lambda(n)(x-n)^4.
\]

`PolynomialZeta.explicit_formula_Psi4_at_heights` proves the zero-sum limit
corresponding to

\[
\Psi_4(x)=\frac{x^5}{120}
 -\lim_{k\to\infty}\sum_{|\Im\rho|<T_k}
       m_\rho\frac{x^{\rho+4}}{P(\rho)}
 -\frac{x^4\log(2\pi)}{24}-E_4(x),
\]

where the finite sums are precisely the zeros, with multiplicity, of the
entire function `(s-1)*zeta(s)` in the rectangle, and

\[
E_4(x)=\frac{x^4}{2\pi}\int_{-\infty}^{\infty}
 \frac{\zeta'}{\zeta}(-\tfrac12+it)
 \frac{x^{-1/2+it}}{P(-\tfrac12+it)}\,dt.
\]

The theorem is stated as convergence of complex finite sums. It does not
assume an unevaluated infinite zero sum is convergent. A single sequence
`T_k in [k+1,k+2]` can be used for every positive x, so taking a fourth finite
difference does not require comparing independently chosen subsequences.

The rectangle has fixed vertical sides at real parts -1/2 and 3/2. The
kernel decays as the inverse fifth power of height. Existing good-height
bounds control the logarithmic derivative on the horizontal sides.
No quantitative zero-free boundary is used in this contour step.

The checked finite-difference identities give upper and lower smoothings
of psi with main terms `x+2h` and `x-2h`. The checked individual-zero
estimates are the fourfold-integral bound and the bound from the rational
kernel's denominator. The upper and lower averaged formulas are now proved in
`PolynomialAveragedFormula.lean`, with main terms `x+2h` and `x-2h`,
the exact constant `-log(2*pi)`, and their explicit left remainders.
The kernel scaling and actual averaged remainder estimate are now checked:
with `h = 0.0000211*x`, both smoothing directions satisfy

\[
|\Delta_h^4 E_4(x)/h^4|,\quad
|\Delta_h^4 E_4(x-4h)/h^4|
\le \frac{25000}{\pi\sqrt{x}}<0.1\qquad(x\ge e^{23}).
\]

This is unconditional and is an absolute error bound. The exact integral
interchange is in `PolynomialRemainderIntegral.lean`; the end-to-end bound
is in `PolynomialRemainderBound.lean`. It uses a proved integrable majorant,
not an assumed evaluation of the integral.
The numerical estimate of the sum over actual zeros remains separate and
unfinished. In particular, the full psi table row is not proved.

## Remaining numerical work

- Prove an adequate zero-count envelope for actual zeta zeros, including
  multiplicities and endpoint conventions. `WeightedZeroSums.lean` proves
  how to use such an envelope; it does not prove the envelope itself.
- Certify the finite low-zero data used in the numerical bound, or replace
  those data by another proved estimate.
- Combine these estimates with finite RH and certify all numerical
  inequalities uniformly for `x >= exp 23`.

RS75's historical estimate of the off-line high-zero tail uses its
zero-free inequality in equations (3.9)-(3.10); the proof explicitly invokes
Theorem 1 at that point. That is a separate quantitative step from the
ordinary rectangular contour. Replacing it requires a justified tail
estimate, rather than simply dropping that factor while claiming the same
printed coefficient.

At the user's request, RS75 Theorem 1 is an explicit separate target,
`Goals.ZeroFreeRegion1975`: under the finite RH verification through 1894439,
there are no zeta zeros in

\[
\sigma\ge 1-\frac1{9.645908801\log(|t|/17)},\qquad |t|\ge21.
\]

This target is not yet a proved theorem. Existing Stechkin machinery can be
reused, but the weaker existing `R = 11` region above height `10^9` does not
supply these constants or this height range.

## Verification and sources

The three explicit-formula modules have fresh compilation and axiom-audit
logs in `verification/polynomial-{explicit,quartic,zeta}-formula-*`.
The audited results depend only on `propext`, `Classical.choice`, and
`Quot.sound`. The mathematical statements above refer to those checked
declarations, not to a numerical diagnostic.

- [Rosser-Schoenfeld (1975), Section 3, especially Lemma 8](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
- [Rosser (1941), the integrated explicit formula and zero-count estimate](https://doi.org/10.2307/2371291).
- [Checked formula source](../RSBounds/PolynomialZetaFormula.lean).
- [Checked finite-difference and psi comparisons](../RSBounds/PolynomialPsi.lean).
- [Checked individual-zero bounds](../RSBounds/PolynomialZeroKernel.lean).
