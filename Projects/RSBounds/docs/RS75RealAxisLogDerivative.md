# The near-pole real-axis input for RS75

This note records a sufficient replacement for the near-pole logarithmic-derivative input in the RS75 zero-free-region argument. It is separate from the already completed b = 23 psi theorem.

## Statement and current verification

The target in [`RS75RealAxisLogDerivative.lean`](../RSBounds/RS75RealAxisLogDerivative.lean) is

\[
-\Re\frac{\zeta'(\sigma)}{\zeta(\sigma)}
<\frac1{\sigma-1}-\gamma+0.2(\sigma-1)
\qquad(1<\sigma<1.03),
\]

where \(\gamma\) is Mathlib's Euler–Mascheroni constant. No RH premise is used.
The final theorem has compiled, and all eight declarations in its transitive axiom audit use only `propext`, `Classical.choice`, and `Quot.sound`. The Gamma, xi increment, and numerical components have also passed their recorded builds and axiom audits.

## The checked increment estimates

Put

\[
g(\sigma)=\frac1\sigma+\frac12\Re\psi_\Gamma(\sigma/2),
\]

where \(\psi_\Gamma\) denotes the digamma function. The Gauss series imported from IEANTN gives

\[
\frac12\Re\bigl(\psi_\Gamma(\sigma/2)-\psi_\Gamma(1/2)\bigr)
=\sum_{n\ge0}\frac{\sigma-1}{(2n+1)(2n+\sigma)}.
\]

For \(\sigma\ge1\), the term \(n=0\) is \((\sigma-1)/\sigma\). It cancels \(1/\sigma-1\) exactly. Each remaining term is bounded above by \((\sigma-1)/(2n+1)^2\), giving

\[
g(\sigma)-g(1)
\le0.23391(\sigma-1).
\]

This is [`gammaAxis_increment_le`](../RSBounds/RS75RealAxisGamma.lean).
The odd-square constant is proved by 24 exact rational terms and a telescoping upper bound \(1/98\) for the remaining tail; see [`RS75RealAxisNumerics.lean`](../RSBounds/RS75RealAxisNumerics.lean).

Independently, [`xi_logDeriv_increment_lower`](../RSBounds/RS75XiIncrement.lean) proves

\[
\Re\frac{\xi'(\sigma)}{\xi(\sigma)}-
\Re\frac{\xi'(1)}{\xi(1)}
\ge0.03414(\sigma-1)
\qquad(1\le\sigma\le1.03).
\]

Its finite contribution comes from the certified first 29 positive zeros and their conjugates. The actual xi partial-fraction approximation and positivity of the omitted increments are proved; the inequality is not an assumed zero-sum estimate.

## Endpoint normalization and assembly

The existing completed function `zetaF` is identified with Mathlib's `riemannZeta₁`, the analytic extension of \((s-1)\zeta(s)\) at one. Mathlib supplies

\[
\texttt{riemannZeta₁}(1)=1,\qquad
\texttt{riemannZeta₁}'(1)=\gamma.
\]

The xi product factorization extends across one because `Gammaℝ 1 = 1`. Its logarithmic derivative gives

\[
\Re\frac{\xi'(\sigma)}{\xi(\sigma)}
=g(\sigma)-\tfrac12\log\pi+
\Re\frac{\texttt{zetaF}'(\sigma)}{\texttt{zetaF}(\sigma)}.
\]

Consequently the two increment estimates yield

\[
-\Re\frac{\zeta'(\sigma)}{\zeta(\sigma)}
\le\frac1{\sigma-1}-\gamma+0.19977(\sigma-1),
\]

which is strictly below the displayed target for \(\sigma>1\). The source formalizes this assembly in `neg_re_logDeriv_zeta_lt`.

## Verification records

- [Final theorem build and eight axiom audits](../verification/rs75-real-axis-log-derivative-run.json).

- [Gamma build and three axiom audits](../verification/rs75-real-axis-gamma-run.json).
- [Xi increment build and eight axiom audits](../verification/rs75-xi-increment-run.json).
- [Exact rational constants and nine axiom audits](../verification/rs75-real-axis-numerics-run.json).

The checked audits permit only `propext`, `Classical.choice`, and `Quot.sound`. This input alone does not establish the complete RS75 zero-free region.
