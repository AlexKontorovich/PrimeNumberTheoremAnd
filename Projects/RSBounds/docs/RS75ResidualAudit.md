# A scalar route using weaker real-axis bounds

This note checks the numerical assembly for the separate RS75 zero-free-region
proof. **It is not a Lean proof of that theorem.** The complete scalar assembly is now checked in
[`RS75ZeroFreeScalars`](../RSBounds/RS75ZeroFreeScalars.lean), with
[16 standard-axiom audits](../verification/rs75-zero-free-scalars-final-run.json).
The independent exact-rational Python
[diagnostic](../verification/rs75-residual-diagnostic.py) and its
[output](../verification/rs75-residual-diagnostic.json) check the arithmetic
below. The zeta estimates and their final analytic assembly remain separate obligations.
Nothing here changes the completed [b = 23 psi proof](PsiTable1975.md).

The primary source is Rosser–Schoenfeld (1975), §1, especially Lemma 2,
(1.24)–(1.26), and the proof of Theorem 1 on pp. 249–251:
[DOI](https://doi.org/10.1090/S0025-5718-1975-0457373-7),
[public scan](https://scispace.com/pdf/sharper-bounds-for-the-chebyshev-functions-theta-x-and-psi-x-1jqd60f50e.pdf).
The scan was inspected for this audit. The method here retains the exact
polynomial already proved in [RS75Polynomial.lean](../RSBounds/RS75Polynomial.lean),
but strengthens one elementary approximation to the variable Stechkin parameter.
That permits weaker real-axis inputs and a weaker frequency remainder than the
paper uses.

## Inputs sufficient for this assembly

Put \(x=\sigma-1\),
\(r=(1+\sqrt5)/2\),
\(\sigma_0=(1+\sqrt{5+12x+8x^2})/2\), and
\(\kappa=(1+2x)/\sqrt{5+12x+8x^2}\).
The required real-axis bounds can be weakened to

\[
-\frac{\zeta'}{\zeta}(1+x)
 <\frac1x-\gamma+0.2x,
\qquad
\frac{\zeta'}{\zeta}(\sigma_0)<-1.1398+3.3606x.
\]

The second follows from the three sufficient inputs

\[
\frac{\zeta'}{\zeta}(r)<-1.1398,\qquad
\left(\frac{\zeta'}{\zeta}\right)'(r)<2.5,\qquad
\sigma_0-r<1.34424x,
\]

together with monotonic decrease of the positive Dirichlet series for
\((\zeta'/\zeta)'\) on the real interval to the right of \(r\).
The product \(2.5\cdot1.34424=3.3606\) is exact.
The golden-ratio value and derivative estimates have separate proof obligations;
this scalar module and its diagnostic do not certify evaluations of zeta.

For each nonzero frequency it is enough to prove the proposed bound with
remainder \(15/t^2\), followed by the usual Stechkin nonnegativity and
one distinguished-zero subtraction. Define

\[
(a_0,a_1,a_2,a_3,a_4)=
(11.1859355312082048,19.073344004352,11.67618784,4.7568,1),
\]
\[
A_0=\sum_{k=1}^4a_k=36.506331844352,\quad
D=52.38865,\quad H=\sum_{k=1}^4a_k/k^2<22.584.
\]

The needed consequence for an off-line zero \(\beta+it\), with
\(t\ge1894439\), is

\[
\frac{a_1}{\sigma-\beta}-\frac{a_0}{x}
\le \frac{1-\kappa}{2}A_0\log t
+a_0\{\kappa(-1.1398+3.3606x)-\gamma+0.2x\}
-\frac{1-\kappa}{2}D+\frac{15H}{t^2}.
\tag{*}
\]

Here the actual sum \(\sum_{k=1}^4a_k\log(2\pi/k)\) exceeds \(D\).
Its coefficient is negative, since \(\kappa<1\).
The exact-rational diagnostic verifies this lower bound using Mathlib's
existing `Real.pi_gt_d20` / `Real.pi_lt_d20` enclosures and explicit logarithm
series. It also checks the rational bound for \(H\).
The Euler constant lower bound
\(\gamma\ge0.5772156646\) is already available in
[`SmallTotientProduct.gamma_bounds`](../RSBounds/SmallTotientProduct.lean).

The statement (*) is an analytic assembly obligation, **not** an assumption
that may remain in the final zero-free theorem.

## Sharper elementary kappa bound

Set

\[
q(x)=1+\frac45x-\frac{26}{25}x^2+\frac65x^3.
\]

For \(0\le x\le0.03\),

\[
\frac{q(x)}{\sqrt5}\le\kappa(x).
\tag{1}
\]

Indeed, \(q(x)>0\), and the exact polynomial identity is

\[
5(1+2x)^2-(5+12x+8x^2)q(x)^2
=\frac{4x^3}{625}
\left(125-1925x-4598x^2-197x^3+420x^4-1800x^5\right).
\]

Dropping the positive fourth-degree term and bounding each remaining negative
power at \(0.03\) leaves
\(3155321863/50000000=63.10643726>63\).
Both sides to be square-rooted are nonnegative, proving (1).
This algebraic proof is now checked in
[`RS75Parameters.cubic_kappa_lower`](../RSBounds/RS75Parameters.lean).
The same module proves the exact Stechkin parameter identities, reflected-partner
inequality, broad frequency ranges, and golden-ratio slope comparison. Its
[verification record](../verification/rs75-parameters-run.json) contains a fresh
build and 21 transitive audits using only Lean's standard three axioms.

Using the paper's coarser quadratic kappa bound with both relaxed real-axis
constants does not leave enough margin in the rounded residual. Inequality (1)
is the specific repair; simply changing the two real-axis constants in the
old rounded polynomial would be insufficient.

## Residual polynomial and rational margin

Let

\[
k=1/\sqrt5,\quad h=(1-k)A_0/2,\quad
v=\frac{2\sqrt{a_0}(\sqrt{a_1}-\sqrt{a_0})}{(1-k)A_0},\quad
x=\frac{v}{\log(t/17)}.
\]

The interval diagnostic verifies

\[
0<x<0.029172\quad(t\ge1894439),\qquad
v\in(0.339013351752804501264407,
       0.339013351752804501264408).
\]

Subtract \(h\log(t/17)\) from the right side of (*).
Use \(\log t=v/x+\log17\), replace \(\gamma\) by its proved lower bound
\(g=0.5772156646\), and put \(b=1.1398,c=3.3606,\ell=\log17\).
The coefficient of \(\kappa\), multiplied by \(x>0\), is

\[
x\{a_0(-b+cx)+D/2-A_0(v/x+\ell)/2\}.
\]

It is less than \(-5.36\): drop its two negative terms involving \(bx\)
and \(\ell x\), use \(x\le0.03\), and use the lower enclosure for \(v\).
Consequently replacing \(\kappa\) by the lower bound (1) gives an upper bound.
The resulting residual, apart from \(15H/t^2\), is the polynomial

\[
\begin{aligned}
P(x)={}&-a_0g-D/2+h\ell+0.2a_0x\\
&+k\left[
 q(x)\{a_0(-b+cx)+D/2\}
 -\frac{A_0}{2}\left(\frac45-\frac{26}{25}x+\frac65x^2\right)
 (v+x\ell)\right].
\end{aligned}
\]

Exact interval arithmetic encloses its five coefficients as follows.
Displayed decimals are outward rounded.

| Degree | Lower bound | Upper bound used below |
|---:|---:|---:|
| 0 | -0.264914857914280 | -0.26491 |
| 1 | 8.234603398819318 | 8.23461 |
| 2 | 27.927962171877485 | 27.92797 |
| 3 | -38.021981038175407 | 0 |
| 4 | 20.173691671866086 | 20.17370 |

Furthermore,

\[
\frac{15H}{t^2}<\frac{15\cdot22.584}{1894439^2}<10^{-10}.
\]

All nonconstant coefficients of the chosen upper polynomial are nonnegative.
Therefore, for \(X=0.029172\) and every \(0\le x\le X\),

\[
\begin{aligned}
P(x)+15H/t^2
&<-0.26491+8.23461X+27.92797X^2+20.17370X^4+10^{-10}\\
&=\frac{-35487834170741864106663}{39062500000000000000000000}\\
&<-0.0009.
\end{aligned}
\]

This margin uses only rational arithmetic after the coefficient enclosures.
The unrounded endpoint residual is about \(-0.00185746\); dropping the negative
cubic term accounts for most of the deliberately discarded margin.

## Final constant and finite range

The above strict inequality reduces (*) to

\[
\frac{a_1}{\sigma-\beta}<\left(\frac{a_0}{v}+h\right)\log(t/17).
\]

The exact definitions of \(v,h\) then give

\[
\beta<1-\frac1{R_1\log(t/17)},\qquad
R_1=\frac{(1-1/\sqrt5)A_0}
          {2(\sqrt{a_1}-\sqrt{a_0})^2}.
\]

The radical comparison is genuinely tight, unlike the residual bound:

\[
9.645908800268114995272594<R_1<
9.645908800268114995272595<9.645908801.
\]

The final Lean certificate should retain exact radical definitions until this
comparison; rounding \(v\) or \(R_1\) prematurely can lose the required margin.
The diagnostic uses rational square brackets with 32 decimal places, checked
by integer squaring. Much less precision is enough, but no numerical axiom is
needed.

The separate handoff for \(21\le|t|\le1894439\), and the case \(\beta=1/2\),
use the now-proved elementary check that the target boundary exceeds \(1/2\)
in `RS75FiniteHandoff.boundary_gt_half`.
For example \(\log(21/17)>0.21\) and \(9.645908801\cdot0.21>2\) suffice.
Finite RH supplies the critical-line location in the bounded range; conjugation
handles negative ordinates.

## Tractable Lean certificate tasks

1. **Completed:** the polynomial identity and positive lower bound proving (1),
   together with the elementary parameter and golden-ratio transfer lemmas,
   are checked in `RS75Parameters`.
2. **Completed:** certify the short list of square-root/logarithm enclosures for \(v,R_1,\ell\),
   the cutoff \(x<0.029172\), and \(D\). Existing `LogCert`, gamma and pi bounds
   supply the needed numerical framework.
3. **Completed:** derive the five coefficient bounds and finish with the displayed single
   rational inequality. This requires no grid search or transcendental
   monotonicity calculation for the residual.
4. **Completed:** the golden-ratio value and derivative bounds, near-pole
   inequality, frequency estimate, and Stechkin/difference assembly (*) are
   now proved and assembled in `RS75ZeroFree1975`. These analytic proofs are
   separate from the scalar diagnostic.

The polynomial residual, final radical/logarithm certificate, and actual-kappa/
Euler-constant substitution are now checked in `RS75ZeroFreeScalars`. Its final
`chosen_residual_lt` theorem has only the height condition `1894439 ≤ t`. The
parameter module has 21 standard-axiom audits; the scalar assembly has 16.
The Python diagnostic remains an independent exact-rational calculation rather
than a proof oracle.
