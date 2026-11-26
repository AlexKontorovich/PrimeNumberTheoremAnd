# A checked bound for the continuous Gamma phase

The completed theorem `BacklundGammaPhase.gamma_phase_remainder_bound`
proves, for every real `T > 0`,

\[
\left|\Phi(T)-\frac T2\log\frac T2+\frac T2+\frac\pi8\right|
\le \frac1{4T},\qquad
\Phi(T)=\int_0^{T/2}\Re\frac{\Gamma'}{\Gamma}(1/4+it)\,dt.
\]

The theorem `backlund_gamma_phase_remainder_bound` immediately supplies
the weaker allowance `25/(48*T)`. Neither theorem assumes RH, a
zero-free region, an unproved Stirling remainder, or an effective
zero-count estimate. The branch is fixed by the displayed integral;
the principal logarithm of `Gamma` is not used.

## What is reused

The proof uses the existing IEANTN Gauss series for the digamma function,
its real estimate `abs(digamma(x)-log(x)) <= 1/x`, and Mathlib's digamma
recurrence. The imported IEANTN files retain their original attribution.
The rectangle argument and reciprocal integral are adapted from
[Gershon Bialer's sources at revision 27df23af](https://github.com/gersh/ternary-goldbach-lean/tree/27df23af6a712895f22204d0d81102baa74f0ebe),
specifically `BacklundXiArcVariation.lean` and `ArctanLogIntegrals.lean`.
The new quantitative argument uses the checked finite Peano-kernel lemma
in `BacklundTrapezoid.lean`.

## Quantitative proof

Put `tau=T/2` and `f(x)=atan(tau/x)`. The digamma recurrence and the
uniform shifted-phase bound prove the actual limit

\[
\Phi(T)=\lim_{N\to\infty}
\left(\tau\log N-\sum_{k<N}f(k+1/4)\right).
\]

The shifted-phase error is at most
`tau*(2*tau+5/4)/N`; its proof comes from the Gauss series and the real
digamma estimate. Thus this limit is proved for the continuous branch,
rather than inferred from equality of exponentials.

On a unit interval the positive Peano kernel is at most `1/8`.
Since

\[
f'(x)=-\frac\tau{x^2+\tau^2},\qquad
f''(x)=\frac{2\tau x}{(x^2+\tau^2)^2}\ge0,
\]

the finite trapezoidal error `E_N` is nonnegative and telescopes to a
bound at most `1/(8*tau)`. Its limit `E` therefore satisfies the same
bounds. The explicit primitive is

\[
F(x)=x\arctan(\tau/x)+\frac\tau2\log(x^2+\tau^2).
\]

The elementary correction between the endpoint expression and the
Stirling main term is

\[
C=\frac\tau2\log\left(1+\frac1{16\tau^2}\right)
 +\frac14\arctan\frac1{4\tau},
\qquad 0\le C\le\frac3{32\tau}.
\]

The required phase remainder is `C-E`. Since both nonnegative quantities
are at most `1/(8*tau)`, its absolute value is at most `1/(8*tau)=1/(4*T)`.

## Connection to the counting path

The checked theorem `digamma_rectangle` proves for any real `a >= 1/2`
and any real `T` that

\[
\int_0^T\Re\psi_\Gamma((a+it)/2)\,dt
-\int_{1/2}^a\Im\psi_\Gamma((\sigma+iT)/2)\,d\sigma
=2\Phi(T).
\]

Here `psi_Gamma` is the digamma function, not Chebyshev's function. This
identity makes the Gamma branch in the zero-count path agree with the
branch in the explicit remainder bound.

All five `BacklundGammaPhase*.lean` modules compile. The seven theorem
audits in `verification/BacklundGammaPhaseAudit.lean`, including both
final bounds, report only `propext`, `Classical.choice`, and `Quot.sound`.
The complete zero-count estimate additionally needs the separate
counting-path and zeta-argument estimates.
