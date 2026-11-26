# Checked golden-ratio constants for RS75

**Status:** the actual golden-ratio estimates and their shifted real-axis
consequence are proved in
[`RS75GoldenRatio.lean`](../RSBounds/RS75GoldenRatio.lean), with no RH,
numerical-enclosure, summability, or infinite-tail hypothesis. Fresh Lean
compilation and all nine transitive axiom audits passed using only
`propext`, `Classical.choice`, and `Quot.sound`. The
[final receipt](../verification/rs75-golden-ratio-run.json) records exact
source and dependency-object hashes, and the
[audit output](../verification/rs75-golden-ratio-axioms.log) gives the checked
exports. This is a proved auxiliary estimate for the separate RS75
zero-free-region argument, not itself the complete zero-free-region theorem.

For the separate RS75 zero-free-region argument, the following sufficient bounds are now proved, with
\(r=(1+\sqrt5)/2\),

\[
\frac{\zeta'}{\zeta}(r)<-1.1398,
\qquad
\left(\frac{\zeta'}{\zeta}\right)'(r)<2.5.
\]

These deliberately weaker constants can replace the sharper golden-ratio
constants in RS75 §1, equations (1.24)–(1.25), when combined with the improved
rational lower bound on \(\kappa\) in the separate residual audit. They are
not premises of the completed b=23 psi theorem.

## Avoiding numerical powers at an irrational exponent

Use the exact rational endpoints

\[
s_- = 55/34 < r < 233/144=s_+.
\]

The formal comparisons reuse
[`RS75Parameters.sqrt_five_bounds`](../RSBounds/RS75Parameters.lean), namely
\(2.23606<\sqrt5<2.23608\). On \(s>1\), put \(L(s)=\zeta'(s)/\zeta(s)\). The absolutely
convergent von Mangoldt series gives

\[
L(s)=-\sum_{n\ge1}\frac{\Lambda(n)}{n^s},\qquad
L'(s)=\sum_{n\ge1}\frac{\Lambda(n)\log n}{n^s}.
\]

Thus \(L\) is increasing and \(L'\) is decreasing. It suffices to certify

\[
L(s_+)<-1.1398,\qquad L'(s_-)<2.5.
\]

Every finite power now has rational exponent. The existing checked
[`CenterNumerics.root_lower` and `root_upper`](../RSBounds/BacklundCenterNumericsBase.lean)
prove enclosures for \(n^{-p/k}\) from the integer inequalities

\[
b^k n^p\le D^k\le(b+1)^k n^p.
\]

Here \((p,k)=(233,144)\) or \((55,34)\), and \(D=10^{12}\).
No floating-point exponentiation or interval exponential is required.

## Three moments and their tails

Let

\[
M_j(s)=\sum_{n\ge1}(\log n)^j n^{-s},\quad j=0,1,2.
\]

Then \(M_0=\zeta\), \(M_1=-\zeta'\), \(M_2=\zeta''\), and

\[
L=-M_1/M_0,\qquad L'=M_2/M_0-(M_1/M_0)^2.
\]

For \(f_j(t)=(\log t)^j t^{-s}\), set \(N=64\), \(a=s-1\), \(\ell=\log N\),
and

\[
T_j=\sum_{1\le n<N}f_j(n)+\tfrac12f_j(N)+I_j,
\]
\[
I_0=Nf_0(N)/a,
\quad I_1=Nf_0(N)(\ell/a+1/a^2),
\]
\[
I_2=Nf_0(N)(\ell^2/a+2\ell/a^2+2/a^3).
\]

These \(I_j\) are the exact integrals over \([N,\infty)\). The positive
Peano-kernel bound already checked in
[`BacklundTrapezoid.error_bounds`](../RSBounds/BacklundTrapezoid.lean)
yields, by the checked finite summation and passage to the limit in
[`InfiniteTrapezoid`](../RSBounds/InfiniteTrapezoid.lean) and
[`RS75GoldenTails`](../RSBounds/RS75GoldenTails.lean),

\[
T_j\le M_j(s)\le T_j-f_j'(N)/8.
\]

The infinite-tail specialization is proved. Its sign
conditions are elementary: for both rational exponents, \(1.6<s<1.7\), and
for \(t\ge64\) one has \(\log t>4\). Explicitly,

\[
f_j''(t)=t^{-s-2}
\bigl[s(s+1)(\log t)^j-j(2s+1)(\log t)^{j-1}
+j(j-1)(\log t)^{j-2}\bigr],
\]

with vanishing terms omitted when \(j=0\) or \(1\). These are positive in
this range. Also \(f_j,f_j'\to0\), the sums and integrals converge, and
\(\int_N^\infty f_j''=-f_j'(N)\). Hence the unit-interval error bounds telescope
with the stated sign and constant.

## Exact scalar preparation

The runnable script
[`rs75-golden-moments-diagnostic.py`](../verification/rs75-golden-moments-diagnostic.py)
uses only integers and `Fraction` for its bounds. It checks all 128 root
brackets by the exact inequalities above and reproduces the already checked
12-term [`LogCert`](../RSBounds/BacklundLowScalarBase.lean) arithmetic for
\(\log n\), \(2\le n\le64\). Floating-point values in the output are
presentation-only; assertions use the exact fractions.

The result is recorded in
[`rs75-golden-moments-diagnostic.json`](../verification/rs75-golden-moments-diagnostic.json).
The diagnostic intervals, rounded outwards here, are:

| Point | \(M_0\) | \(M_1\) | \(M_2\) |
|---|---|---|---|
| \(233/144\) | \([2.23827679,2.23828058]\) | \([2.55132143,2.55133482]\) | \([8.46067056,8.46071650]\) |
| \(55/34\) | \([2.23931971,2.23932350]\) | \([2.55478102,2.55479443]\) | \([8.47748999,8.47753599]\) |

The final application needs only the much coarser bounds

\[
M_0(s_+)\le2.23829,\qquad M_1(s_+)\ge2.55131,
\]
\[
2.2393\le M_0(s_-)\le2.2394,\quad
M_1(s_-)\ge2.5547,\quad M_2(s_-)\le8.4776.
\]

The final rational comparisons have useful slack:

\[
\frac{2.55131}{2.23829}-1.1398>0.0000478,
\]
\[
\frac{8.4776}{2.2393}
 -\left(\frac{2.5547}{2.2394}\right)^2
 <2.484409<2.5.
\]

## Reused interfaces and checked assembly

The necessary Mathlib series identities are already available:

- [`ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/LSeries/Dirichlet.lean) identifies the actual logarithmic derivative on \(\Re s>1\).
- [`LSeries_hasDerivAt`, `LSeries_iteratedDeriv`, and `LSeriesSummable_logMul_of_lt_re`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/LSeries/Deriv.lean) supply the differentiated series and convergence.
- `LSeries.abscissaOfAbsConv_one = 1`, in the preceding Dirichlet source, applies to the three ordinary zeta moments.
- [`isLittleO_log_rpow_rpow_atTop`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean) supplies the elementary endpoint limits for log-power terms.

The finite scalar certificate has now been replayed in Lean in
[`RS75GoldenNumerics`](../RSBounds/RS75GoldenNumerics.lean), using the checked
[`GoldenScalar.Expr.sound`](../RSBounds/RS75GoldenScalarBase.lean). Each
certificate expression is proved equal to its named actual finite center or
upper-error expression. The integer powers use kernel reduction through
`decide +kernel`.

The checked assembly binds those centers to the infinite moments, binds the
moments to actual zeta derivatives, and transfers the rational-point estimates
by the nonnegative von Mangoldt series:

- [`RS75GoldenSeries`](../RSBounds/RS75GoldenSeries.lean) supplies actual moment summability, derivatives, quotient identities, and monotonicity; [ten audited exports](../verification/rs75-golden-series-run.json).
- [`RS75MomentCalculus`](../RSBounds/RS75MomentCalculus.lean) proves the required derivatives, convexity, limits, and improper integrals; [thirteen audited exports](../verification/rs75-moment-calculus-run.json). A [separate guide](RS75MomentTails.md) gives the generic tail theorem.
- [`RS75GoldenTails`](../RSBounds/RS75GoldenTails.lean) binds the finite expressions to the actual moments, discharging summability; [five audited exports](../verification/rs75-golden-tails-run.json).
- [`RS75GoldenRatio`](../RSBounds/RS75GoldenRatio.lean) assembles the final actual zeta estimates; [nine audited exports](../verification/rs75-golden-ratio-run.json).

The scalar checker and its six finite estimates have a separate
[seven-export audit](../verification/rs75-golden-numerics-run.json). All these
audits use only the three standard axioms stated above.

The checked mean-value-theorem application gives, for \(u\ge r\),

\[
L(u)<-1.1398+2.5(u-r).
\]

Together with \(\sigma_0-r<1.34424(\sigma-1)\), this gives the requested
usable real-axis bound
\(L(\sigma_0)<-1.1398+3.3606(\sigma-1)\) for \(1<\sigma<1.03\), where
\(\sigma_0=(1+\sqrt{8\sigma^2-4\sigma+1})/2\). The exported theorem is
`RS75GoldenRatio.shifted_real_axis_bound`; its only premises are these two
inequalities on \(\sigma\).

Primary source: J. B. Rosser and L. Schoenfeld,
["Sharper bounds for the Chebyshev functions θ(x) and ψ(x)" (1975), §1](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
