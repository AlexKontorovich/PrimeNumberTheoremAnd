# Full-range RS62 Mertens and totient estimates

**Both full-range theorems have passed their fresh source checks and
transitive axiom audits.** The weighted Mertens theorem and the all-integer
totient theorem use only `propext`, `Classical.choice`, and `Quot.sound`,
apart from their displayed finite-RH parameter. The independent Comparator
workflow is active; no completed native verdict is claimed yet.

The statements retain the sole explicit premise `Goals.FiniteRH 1894439`:
every actual zeta zero in the open critical strip with absolute ordinate at
most 1894439 lies on the critical line. This is a hypothesis, not a declared
axiom or a certificate supplied by this project.

## Exact targets

For every real `x > 1`, the checked weighted-prime theorem is

\[
 \sum_{p\le x}\frac{\log p}{p}
 >\log x+E-\frac1{2\log x},\qquad
 E=-\gamma-\sum_p\frac{\log p}{p(p-1)}.
\]

The public export is
`RS62MertensFromFiniteRH.mertens_lower_of_finiteRH`, with result type
`Goals.MertensLower`.

Its completed receipt is
`verification/rs62-mertens-from-finite-rh-run.json`. The source SHA256 is
`7cab9f56a2e264be53c30ed14e443f2e9c6dc5d7a8021da070c8c23233f2fc9f`.
The complete theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`, apart from its displayed finite-RH parameter.

For every integer `n ≥ 3`, the checked totient theorem is

\[
 \frac n{\varphi(n)}
 <e^\gamma\log\log n+\frac{2.50637}{\log\log n}.
\]

The public export is
`RS62TotientFromFiniteRH.totient_bound_of_finiteRH`, with result type
`Goals.TotientBound`. There is no upper restriction on `n`.

Its completed receipt is
`verification/rs62-totient-from-finite-rh-run.json`. All seven audited
exports passed. Source SHA256:
`cdfb8f02676c1a8d0bfbf14386db0119b1417ca9d54792db5aac8191fdca9c8d`.

The target propositions in `Targets.lean` are unconditional statements.
The displayed finite-RH parameter remains visible in these two derivations;
this work does not assert either target with that parameter omitted.

## Checked common analytic ingredients

`MertensSignedLimit` constructs the actual limit of the finite signed
integrals of `(psi(t)-t)/t^2`. `MertensDLimit` identifies its normalization
using the checked Abel transform and Mathlib's Laurent expansion. For
`x ≥ 1` it gives

\[
 E_{1,\Lambda}(x)=\frac{\psi(x)-x}{x}-\gamma-I(x),\qquad
 I(x)=\lim_{b\to\infty}\int_x^b\frac{\psi(t)-t}{t^2}\,dt.
\]

The function `J` in `MertensSecondSigned` is proved to equal this actual
signed tail. Its checked second-Mertens identity bounds the error by

\[
 |E_{2,\Lambda}(x)|\le\frac e{\log x}
       +2j\left(\frac1{\log x}+\frac1{\log^2x}\right)
\]

whenever `|psi(x)-x| ≤ e*x` and `|J(u)| ≤ j` for every `u ≥ x`.
No pointwise prime number theorem is a premise of these identities or their
Euler normalization.

The quantitative signed-tail bounds use actual zeta zeros and their analytic
multiplicities. The fixed-cutoff bound is

\[
 j(x)=0.0463x^{-1/2}+2.4\cdot10^{-6}
       +6000x^{-3/2}+\log(2\pi)/x.
\]

For `x ≥ exp 2400`, the variable cutoff
`17*exp(sqrt(log x/10))` proves the stronger uniform bound
`|J(u)| < 1/log(x)^2` for `u ≥ x`. Finite RH is used only through 1894439;
the larger cutoff uses the proved unconditional RS75 zero-free region and
Rosser zero count.

## Range handoffs

| Range | Actual psi input | Signed-tail allowance |
| --- | --- | --- |
| `100000 ≤ x`, `log x ≤ 23` | `0.0023*x + 6*sqrt x` | `j(x)` |
| `exp 23 ≤ x`, `log x ≤ 2400` | `0.00020211*x` | `j(x)` |
| `exp 2400 ≤ x` | `0.1*x/log x` | `1/log(x)^2` |

The weighted Mertens range `1 < x ≤ 100000` has a separate unconditional
kernel certificate. The prime-product certificate covers every prime
cutoff through 100000. These finite statements are transferred to real
arguments and arbitrary integers by checked monotonicity and primorial
reductions.

For the product, `MertensProductCorrection` proves unconditionally, for
every integer `n ≥ 100000`,

\[
0\le\log\prod_{p\le n}\frac p{p-1}
 -\sum_{d\le n}\frac{\Lambda(d)}{d\log d}
 \le\frac{5.6}{\sqrt n\log n}.
\]

`PsiThetaElementary` reuses Mathlib's elementary prime-power decomposition
to obtain `psi(x)-theta(x) ≤ 6.5*sqrt x` above 100000. The checked numerical
budgets feed the existing RS62 prime-product-to-totient reduction.

## Independent comparison

`comparator/RS62GlobalChallenge.lean` imports Mathlib only and independently
specifies finite RH, the exact constant `E`, and both full-range targets.
`comparator-rs62-global.json` permits only `propext`, `Classical.choice`, and
`Quot.sound`, with no definition holes. The solution imports the actual
proof modules, never the challenge.

The prepared runner is `verification/run_rs62_global_comparator.py`.
**The workflow is running locally; its native verdict is pending.** It
validated the two successful final audit receipts and their exact source/object hashes before building fresh wrapper
objects, exporting the targets and invoking the native Comparator. This is
a standalone Lean 4.35 check, not an official IEANTN verification receipt.
