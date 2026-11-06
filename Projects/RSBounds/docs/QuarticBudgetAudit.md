# Audit of the proposed RS75 quartic budget

This is a mathematical and source audit of
[`rs75-budget-diagnostic.py`](../verification/rs75-budget-diagnostic.py),
not a proof of the table row. Its 60-digit `mpmath` output is **not interval
arithmetic or a Lean certificate**. The corrected fixed-parameter diagnostic
is below the target, but the zero-count input, finite head data, and numerical
assembly still require proofs. The averaged contour remainder is now bounded
in Lean; it has not yet been assembled with the actual zero sum.

The individual upper/lower kernel bounds and the cancellation estimate
described below now have checked Lean proofs. The
[build and axiom-audit record](../verification/polynomial-cancellation-lower-run.json)
reports successful checks; all 20 audited declarations use only `propext`,
`Classical.choice`, and `Quot.sound`.

## Parameters and exact hypotheses

Take
\[
A=1894439,\quad \delta=0.0000211,\quad x\ge e^{23},\quad
D=158.84998,\quad N(D)=57,\quad S=0.8113925.
\]
Here \(N(t)\) must count nontrivial zeta zeros with
\(0<\Im\rho\le t\), **with multiplicity**, and the head input is
\(\sum_{0<\Im\rho\le D}m_\rho/|\rho|\le S\).
These are independent finite-data obligations, not consequences of finite RH.
Assume finite RH for \(|\Im\rho|\le A\), and the two-sided envelope
\[
|N(t)-F(t)|\le R(t)\quad(t\ge2),\qquad
F(t)=\frac{t}{2\pi}\left(\log\frac{t}{2\pi}-1\right)+\frac78,
\quad R(t)=0.137\log t+0.443\log\log t+1.588.
\]
The needed endpoint and positivity checks are
\(0<\delta\le0.000022\), \(4\delta<1\), and \(2\le D<L<U<T<A\), where
\[
a=1+2\delta,\quad R_4=((1+\delta)^5+1)^4,\quad
T=\frac{(R_4/a)^{1/4}}\delta,\quad
L=\frac4{3\delta},\quad U=\frac{2(1-4\delta)}\delta.
\]
The zero multiset must have conjugation and critical-line reflection
symmetries preserving multiplicities. Its identification with the zeros in
the checked contour formula, and passage to the limiting sums, are also
required. The finite-RH proposition is specified in
[`Targets.lean`](../RSBounds/Targets.lean).

## Both smoothing directions and the corrected band

For \(\rho=1/2+i\gamma\), integrating one variable gives numerator
\((y+\delta)^{\rho+1}-y^{\rho+1}\), divided by
\(\delta\rho(\rho+1)\). The remaining three variables put
\(y\in[1,1+3\delta]\) for the upper average, and
\(y\in[1-4\delta,1-\delta]\) for the lower average.

With \(v=\gamma\delta\) and
\(\theta=(\gamma/2)\log((y+\delta)/y)\), the common band gives
\[
\frac{v}{2(1+4\delta)}\le\theta\le
\frac{v}{2(1-4\delta)}\le1.
\]
Mathlib's `Real.sin_bound` yields
\(\sin\theta\le\theta-47\theta^3/300\) on this interval.
The resulting normalized fourfold kernel is at most \(0.931/\gamma\)
for **both** averages. This is proved in
[`PolynomialZeroCancellation.lean`](../RSBounds/PolynomialZeroCancellation.lean),
including the two `*_rs75` corollaries. The proof includes the amplitude
increment and all three remaining integrations.

The initially proposed endpoint \(2/\delta\) was unsuitable for the lower
phase argument: at \(y=1-4\delta\), it gives
\(\theta=\delta^{-1}\log((1-3\delta)/(1-4\delta))>1\).
The corrected endpoint is exactly \(2/\delta-8\).
The baseline lower bounds are now proved separately in
[`PolynomialLowerKernel.lean`](../RSBounds/PolynomialLowerKernel.lean):
the low bound is at most \(1/|\rho|\le a/|\rho|\), and the high numerator
bound is \(16\le R_4\).

## Partial summation, pairing, and endpoints

Writing \(G=F+R\), the script's quantities have the transparent forms
\[
B=S+\int_D^T\frac{G'(t)}t\,dt
       +T^4\int_T^\infty\frac{G'(t)}{t^5}\,dt
       +\frac{G(D)-N(D)}D,
\qquad
H=\int_A^\infty\frac{G'(t)}{t^5}\,dt+\frac{2R(A)}{A^5}.
\]
These follow conditionally from the stated envelope by partial summation.
For \(H\), the endpoint term uses \(G(A)-N(A)\le2R(A)\);
no exact value of \(N(A)\) is assumed. The script's exponential-integral
terms match these formulas; in particular its
\(0.443E_1(5\log A)\) has no missing factor of \(1/5\).

Use the disjoint conventions \(0<\gamma\le D\), \(D<\gamma\le T\),
and \(T<\gamma\), and use \(L<\gamma\le U\) for the saving.
The crossover weight is continuous because
\(a/T=R_4/(\delta^4T^5)\). Thus no assumption that any cutoff avoids a
zero ordinate is needed. The band count satisfies
\(N(U)-N(L)\ge F(U)-R(U)-F(L)-R(L)\).
An externally supplied theorem using \(\gamma<t\) instead needs a proved
endpoint-convention bridge; see [the zero-count audit](BacklundCountAudit.md).

For high zeros, reflection \(\beta\leftrightarrow1-\beta\) and
\[
x^{\beta-1}+x^{-\beta}\le1+x^{-1}\quad(0\le\beta\le1,\ x\ge1)
\]
give a factor \(1/2\) when averaging positive ordinates. Conjugation's
factor 2 cancels it. Consequently the high term
\((1+x^{-1})R_4\delta^{-4}H\) has the correct factor, conditional on the
multiplicity-preserving symmetries. Extending the positive critical-line
weight from \(\gamma\le A\) to all ordinates is only a conservative
numerical majorant; it does **not** assume RH above \(A\). The separately
added high term then overcounts conservatively. The saving band lies below
\(A\), where finite RH justifies the cancellation estimate.

## Diagnostic values and remaining work

For the fixed parameters, the current output is:

| Quantity | Approximate diagnostic value |
|---|---:|
| Baseline total | 0.000202686810726714 |
| Lower bound for the band count | 47411.2278130122 |
| Saving from the corrected band | 0.000000699726615324 |
| Improved total | 0.000201987084111390 |
| Target minus improved total | 0.000000122915888610 |

The total uses \(2aB/\sqrt{x}\), the high term above, and
\(2\delta+\log(2\pi)/x\), minus the band saving
\[
\frac{2(a-0.931)}{U\sqrt{x}}
 [F(U)-R(U)-F(L)-R(L)].
\]
The displayed diagnostic values omit the left-line remainder. That remainder
has now been bounded in Lean by `25000/(pi sqrt(x)) < 0.1` for both smoothing
directions at the fixed historical delta and `x >= exp 23`; in the relative
error budget its contribution is at most `0.1/x`. See
[`PolynomialRemainderBound.lean`](../RSBounds/PolynomialRemainderBound.lean).
The diagnostic is still not a certified numerical assembly. Alternatively,
an exact classical remainder
\(-\log(2\pi)-\tfrac12\log(1-t^{-2})\) would give the claimed bound after
proving its averaged absolute value is at most \(\log(2\pi)\) over the
relevant interval; that alternative exact evaluation was not used. A derivation from a
midpoint version of psi must also handle its jump-point convention.

The remaining obligations are therefore the sharp count envelope; head
certificates; the contour-zero/count/multiplicity bridges;
and rigorous numerical assembly for every \(x\ge e^{23}\). Evaluating at
\(e^{23}\) additionally needs monotonicity of the combined bound (in
particular positivity of the coefficient of \(x^{-1/2}\) after subtraction).
The optimizer in the script is unnecessary for the fixed-parameter target.

Some bridges already have substantial source support. In the pinned calr
revision `ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`,
[`Xi.lean`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/Xi.lean)
proves `xiF_half_ne_zero`, `xiF_eq_zero_iff`, and `xiF_one_sub`.
Thus finite RH through positive height excludes real nontrivial zeros:
a real zero would have to be at \(1/2\). This needs a short connecting
lemma, not a new general real-axis zero-free theorem.
[`XiPartial.lean`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/XiPartial.lean)
proves `xiF_conj`; Mathlib also has `riemannZeta_conj` and
`analyticOrderAt_comp_of_deriv_ne_zero`. Exact multiplicity-preserving
reindexing lemmas were not identified in this limited search; function
symmetries alone are not yet that interface.

Sources: [Rosser–Schoenfeld (1975), Section 3 and Lemma 8](https://doi.org/10.1090/S0025-5718-1975-0457373-7);
[Rosser (1941), Theorem 19, pp. 223–224](https://doi.org/10.2307/2371291).
The cancellation refinement and the conservative tail budget above are
the present argument, not a claim that the printed RS75 proof omits its
zero-free-region input.
