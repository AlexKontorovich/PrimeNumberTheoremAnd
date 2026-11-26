# Checked logarithmic-moment tails

`InfiniteTrapezoid.lean` and `RS75MomentCalculus.lean` have passed fresh Lean
compilation and a combined transitive axiom audit of 13 public declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The exact sources,
compiler command, combined compiler input hash, timings, and audit result are
recorded in
[`rs75-moment-calculus-run.json`](../verification/rs75-moment-calculus-run.json).

## Generic theorem and hypotheses

[`InfiniteTrapezoid.infinite_bounds`](../RSBounds/InfiniteTrapezoid.lean)
proves the following. Let \(N\) be a natural number, let \(f'=g\) and
\(g'=h\) on \([N,\infty)\), and suppose \(h\) is continuous and nonnegative
there. Suppose also that

\[
\sum_{k<M}f(k)\longrightarrow S,\qquad f(M),g(M)\longrightarrow0
\quad(M\in\mathbb N,\ M\to\infty),
\]

and that \(f\) is integrable on \((N,\infty)\). Then

\[
C\le S\le C-\frac{g(N)}8,\qquad
C=\sum_{k<N}f(k)+\frac{f(N)}2+\int_N^\infty f(t)\,dt.
\]

The proof sums the already checked positive Peano-kernel inequality in
[`BacklundTrapezoid.error_bounds`](../RSBounds/BacklundTrapezoid.lean),
telescopes the derivative increments, and passes to the limit. No estimate
on an uncomputed infinite tail is an assumption.

## Concrete calculus at the cutoff 64

Put \(f_j(t)=(\log t)^j t^{-s}\), with \(j\in\{0,1,2\}\), and assume
\(1.6\le s\le1.7\). The checked module
[`RS75MomentCalculus`](../RSBounds/RS75MomentCalculus.lean) proves the actual
first and second derivatives, \(f_j''(t)\ge0\) for \(t\ge64\), and the
vanishing of \(f_j\) and \(f_j'\) at infinity. It also proves integrability
and evaluates the improper integral. With \(a=s-1\) and \(\ell=\log64\),

\[
I_0=\frac{64^{1-s}}a,\qquad
I_1=64^{1-s}\left(\frac\ell a+\frac1{a^2}\right),
\]
\[
I_2=64^{1-s}\left(\frac{\ell^2}a+
                       \frac{2\ell}{a^2}+\frac2{a^3}\right).
\]

Consequently `moment_bounds` proves, assuming summability of the actual
moment series,

\[
T_j\le\sum_{n\ge1}(\log n)^j n^{-s}
\le T_j+\frac{(s\ell^j-j\ell^{j-1})64^{-s}}{512},
\]
\[
T_j=\sum_{1\le n<64}(\log n)^j n^{-s}
       +\frac{\ell^j64^{-s}}2+I_j.
\]

For \(j=0\), the term carrying the factor \(j\) is zero. Lean's series is
indexed by all natural numbers; its zero-index term is proved to vanish.
The `GoldenSeries` bridge is responsible for discharging the summability
hypothesis, and `GoldenTails` binds these exact expressions to the finite
scalar certificate. Their validation is recorded separately.

The final binding
[`RS75GoldenTails.center_le_moment_le_upper`](../RSBounds/RS75GoldenTails.lean)
now discharges summability using the actual L-series theorem and proves both
bounds with only \(1.6\le s\le1.7\) and \(j\le2\) as hypotheses. Its finite
center and upper allowance are definitionally the quantities used by the
scalar certificates. All five public binding declarations passed the
standard-three-axiom audit; see
[`rs75-golden-tails-run.json`](../verification/rs75-golden-tails-run.json).

These tail estimates have no RH or zero-free-region hypothesis. They are
auxiliary inputs for the separate RS75 golden-ratio calculation and do not
change the assumptions of the completed \(b=23\) psi theorem.
