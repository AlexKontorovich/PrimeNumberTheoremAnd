# Remaining analytic inputs for the RS62 Mertens and totient bounds

> Historical dependency audit. The route described here has now been
> completed under the explicit premise `FiniteRH 1894439`; see
> [the full-range statements and verification status](RS62Global.md).
> The finite-RH premise itself has not been discharged, so the unconditional
> target propositions are not asserted without it. The older outstanding
> inputs below describe the earlier stage of this development.

This is a mathematical dependency audit, not a new Lean proof. The checked
moderate-error theorem
[`RosserSchoenfeld1975.psi_error_b23`](../RSBounds/RosserSchoenfeld1975.lean)
now gives

\[
 |\psi(x)-x|<0.00020211x\qquad(x\ge e^{23}),
\]

assuming `Goals.FiniteRH 1894439`. Its fresh compilation and standard-axiom
audit are recorded in
[`rosser-schoenfeld-1975-run.json`](../verification/rosser-schoenfeld-1975-run.json).
The two unrestricted RS62 targets in
[`Targets.lean`](../RSBounds/Targets.lean) remain unproved. Their current
specifications are unconditional, so a derivation using this row would also
retain its finite-RH premise until that premise is discharged.

## What the original proof supplies

Primary source: J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas
for some functions of prime numbers*, Illinois J. Math. 6 (1962), 64–94
([PDF](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)). Page references
below are printed page numbers.

Section 8, pp. 83–87, controls signed error integrals. Its Lemma 6 bounds
the zero sum `K(1,x)` using, among other terms, the zero-free-region factor
\(x^{-1/(R\log K)}\). Lemmas 7 and 8 on p. 84 give

\[
 |J_1(x)|<K(1,x)+\frac{1.84}{x}+\frac{0.31}{x^3},
\]
\[
 |J_2(x)|<\frac{\log x+2}{\log^2x}
 \left(K(1,x)+\frac{1.84}{x}+\frac{0.31}{x^3}\right),
\]

where

\[
 J_1(x)=\int_x^\infty\frac{t-\psi(t)}{t^2}\,dt,
 \qquad
 J_2(x)=\int_x^\infty
 \frac{(t-\psi(t))(1+\log t)}{t^2\log^2t}\,dt.
\]

Theorem 6's weighted-prime estimate uses Lemma 7. The product estimate
(3.29) uses Lemma 8 through Lemma 13. Section 9, pp. 88–89, combines the
product estimate with theta estimates and a finite primorial verification.
These are extra analytic inputs, not consequences obtained by integrating
one fixed relative-error bound absolutely.

## Checked interfaces and their limits

| Checked interface | What it supplies | What remains |
| --- | --- | --- |
| [`primeWeightedSum_sub_log_eq_anchor`](../RSBounds/Mertens.lean) and its von Mangoldt counterpart | Exact finite-anchor Abel identities | Quantitative control of the endpoint and signed-integral combination |
| [`mertensError_eq_neg_centered_tail`](../RSBounds/MertensTailReduction.lean) | The second Mertens error with Euler's constant, as a convergent centered tail | A numerical, one-sided tail estimate |
| [`mertensError_abs_le_of_tail_variation`](../RSBounds/MertensTailReduction.lean) | Tail variation at most \(D\) implies \(|E_{2\Lambda}(x)|\le D/\log x\) | A suitable shrinking \(D=D(x)\), or a sharper direct integral bound |
| [`totient_ratio_lt_of_prime_product_at_rank`](../RSBounds/Totient.lean) | Transfer from prime products to arbitrary integers | The prime-product estimate at every remaining prime cutoff |
| [`totient_ratio_lt_of_rs62_inputs`](../RSBounds/TotientGlobalReduction.lean) | An all-integer implication, with finite prime checks through 557 already proved | RS62-style theta and product bounds from 563 onward |

The last row is a sufficient route, not a minimal dependency list. In
particular, it need not be used if one proves the direct product comparison
below. No arbitrary upper bound on the integer \(n\) is needed.

## A smaller, coupled totient target

Write

\[
 P(x)=\prod_{p\le x}\frac p{p-1},\quad L=\log x,\quad
 s=\log\theta(x),\quad G=e^{\gamma_E},\quad c=2.50637,
\]

and define the prime-power truncation difference

\[
 \tau(x)=\log P(x)-\sum_{n\le x}\frac{\Lambda(n)}{n\log n}.
\]

For \(x>1\) and \(s>0\), the exact second-Mertens identity shows that
the desired prime-product inequality is equivalent to

\[
 \boxed{\quad
 E_{2\Lambda}(x)+\tau(x)-\log(s/L)
 <\log\!\left(1+\frac{c}{Gs^2}\right).
 \quad}
\]

This is a one-sided averaged estimate coupled to \(\theta(x)\). The existing
checked identity is

\[
 E_{2\Lambda}(x)=
 -\int_x^\infty
 \frac{E_{1\Lambda}(t)-E_{1\Lambda}(x)}{t\log^2t}\,dt.
\]

Its integrability is already proved. Thus the boxed target can be stated
without first proving a separate pointwise theta estimate, and without
assuming absolute integrability of a psi-error tail. This new scalar
equivalence and its quantitative application have not yet been encoded in
Lean here.

When the signed psi-tail identity is established, one can also write
\(E_{2\Lambda}(x)=e(x)/L+J_2(x)\), where
\(e(x)=(\psi(x)-x)/x\). Comparing directly with \(\log(s/L)\) retains
first-order endpoint cancellation. Replacing both terms by unrelated
absolute bounds would lose that cancellation.

## The separate weighted-Mertens target

The requested lower bound is

\[
 \sum_{p\le x}\frac{\log p}{p}
 >\log x+E-\frac1{2\log x},\qquad
 E=-\gamma_E-\sum_p\frac{\log p}{p(p-1)}.
\]

After proving the normalized signed-tail identity, its error is

\[
 \sum_{p\le x}\frac{\log p}{p}-\log x-E
 =e(x)+J_1(x)+H(x),
 \qquad
 H(x)=\sum_{\substack{p^k>x\\ k\ge2}}\frac{\log p}{p^k}\ge0.
\]

Consequently, the single one-sided estimate

\[
 e(x)+J_1(x)>-\frac1{2\log x}
\]

is sufficient above an analytic handoff; bounding the nonnegative tail
\(H\) is unnecessary for this direction. The normalization
\(E_{1\Lambda}(x)\to-\gamma_E\) is a separate bridge, not a consequence
already provided by the second-Mertens identity. No numerical
weighted-Mertens anchor certificate was found in the current recovery
modules; the existing anchor statements are exact identities.

Mathlib provides the needed Laurent constant in
[`Harmonic/ZetaAsymp.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean):
`log_deriv_riemannZeta_add_inv_sub_sub_isLittleO` says
\(\zeta'/\zeta(s)+1/(s-1)-\gamma_E\to0\) as \(s\to1\).
The regularized function `riemannZeta₁` satisfies
`riemannZeta₁_one` and `deriv_riemannZeta₁_one`, namely values \(1\) and
\(\gamma_E\). These supply normalization, not a numerical error rate.

## What the fixed row does and does not supply

Substituting only \(|\psi(t)-t|\le\varepsilon t\) into the finite Abel
identity gives, for \(t\ge x\),

\[
 |E_{1\Lambda}(t)-E_{1\Lambda}(x)|
 \le 2\varepsilon+\varepsilon\log(t/x).
\]

This does not yield the shrinking tail bound above. Absolute integration
of the corresponding psi-error majorant also contains
\(\varepsilon\int_x^\infty dt/(t\log t)\), which diverges. These observations
identify missing estimates in the available reductions; they are not an
impossibility or independence claim about other arguments for the actual
prime functions.

A convenient stronger common input would be an explicit envelope

\[
 |\psi(t)-t|\le\frac{t}{4\log^2t}\qquad(t\ge X).
\]

After the tail identities and their constants are justified, elementary
integration gives

\[
 |e(x)+J_1(x)|\le\frac1{4\log x}+\frac1{4\log^2x},\qquad
 |E_{2\Lambda}(x)|\le\frac1{8\log^2x}+\frac1{3\log^3x}.
\]

This supplies room for both targets, subject to explicit prime-power
corrections and a finite verification reaching the chosen analytic
threshold. It is sufficient, not minimal. A sharper signed-integral estimate
may be easier than proving this pointwise envelope. The finite verification
must meet the actual analytic threshold; the certificate through 557 does
not automatically cover a later handoff.

## Uncompiled source is not an available theorem

[`Theta.lean`](../RSBounds/Theta.lean) contains a draft \(R=20\) zero-free
region. [`ThetaLarge.lean`](../RSBounds/ThetaLarge.lean) contains a draft
\(0.2x/\log^3x\) estimate above \(\exp(10^6)\). Neither module has a built
olean or a completed dedicated verification receipt in the audited state,
and the checked root aggregate does not import them. An older aggregate
receipt lists their source hashes; that listing does not show they were
compiled. They are possible reusable source, not established inputs to this
audit.
