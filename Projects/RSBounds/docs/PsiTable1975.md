# The proved b = 23 psi estimate

The project now proves

\[
\boxed{\quad |\psi(x)-x|<0.00020211\,x\qquad(x\ge e^{23})\quad}
\]

assuming that every nontrivial zero of the actual Riemann zeta function with
\(|\Im\rho|\le1894439\) lies on the critical line. This is the sole
mathematical premise. The finite zero table, zero-count estimates, kernel
bounds, integral bounds, and numerical inequalities used below are proved
in the imported Lean development.

The main theorem has compiled, and its transitive axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. **The independent native
Comparator has also passed:** exact statement and definition matching, the
allowed-axiom check, and full replay with Lean's default kernel. The final
log explicitly reports that the kernel accepts the solution.

## Exact statement and API

Import [`RSBounds.RosserSchoenfeld1975`](../RSBounds/RosserSchoenfeld1975.lean).
The public declaration is:

```lean
TernaryGoldbach.RSBounds.RosserSchoenfeld1975.psi_error_b23
  (hRH : Goals.FiniteRH 1894439) (x : ℝ)
  (hx : Real.exp 23 ≤ x) :
  |Chebyshev.psi x - x| < 0.00020211 * x
```

Here `Chebyshev.psi` is Mathlib's actual Chebyshev function, and
[`Goals.FiniteRH`](../RSBounds/Targets.lean) unfolds to

```lean
∀ ρ : ℂ, riemannZeta ρ = 0 → 0 < ρ.re → ρ.re < 1 →
  |ρ.im| ≤ A → ρ.re = 1 / 2
```

The height condition is inclusive. The threshold is exactly `exp 23`, and
the error inequality is strict. `PsiTable1975.proved` also discharges the
previously declared proposition `Goals.PsiTable1975`.

There is no premise of full RH, a stronger finite-RH height, a quantitative
zero-free region, a PNT estimate, Büthe's theorem, or a Ramaré estimate.
The finite-RH statement through 1894439 itself remains an explicit input;
the replayed certificate through height 100 does not establish it.

## Four integrations at the stated threshold

The proof follows the fourfold polynomial smoothing method of
[Rosser–Schoenfeld (1975), Lemmas 7–9 and Theorem 4](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
Its fixed parameters are

\[
m=4,\qquad \delta=0.0000211=\frac{211}{10^7},\qquad h=\delta x.
\]

The fourth primitive is expressed using the truncated polynomial
\((t_+)^4/24\). Taking its fourth forward difference with step \(h\),
then dividing by \(h^4\), gives upper and lower smoothings of \(\psi\).
Their starts are \(x\) and \(x-4h\); their main terms are \(x+2h\)
and \(x-2h\). The sandwich is proved in
[`PolynomialPsi`](../RSBounds/PolynomialPsi.lean).

[`PolynomialAveragedFormula`](../RSBounds/PolynomialAveragedFormula.lean)
proves the averaged explicit formulas with the actual complex coefficient
`PolynomialAveraged.zeroCoefficient`, the actual contour zeros, and their
analytic multiplicities. Both left-line remainder norms are less than
\(0.1\) for every \(x\ge e^{23}\), by
[`PolynomialRemainderBound`](../RSBounds/PolynomialRemainderBound.lean).
These are proved integrals and bounds, not additional hypotheses in the
final theorem.

The numerical organization is a refinement of the paper's quartic method:
it uses a certified 29-zero head and eight disjoint cancellation subbands.
It does not reproduce the paper's 57-zero head computation. The smoothing
degree, \(\delta\), threshold, finite-RH height, and final 1975 constant
are retained.

## Actual zeros and their weighted sums

Let \(N(t)\) count zeros with \(0<\gamma\le t\), including analytic
multiplicity. The unconditional theorem
[`Rosser1941.zero_count_bounds`](../RSBounds/Rosser1941.lean) proves

\[
|N(t)-F(t)|<R(t)\quad(t\ge2),
\]
\[
F(t)=\frac{t}{2\pi}\left(\log\frac{t}{2\pi}-1\right)+\frac78,
\qquad R(t)=0.137\log t+0.443\log\log t+1.588.
\]

The count refers to actual Mathlib zeta zeros. It is not an abstract
function with an assumed envelope. Its lower range uses the replayed
finite certificates; its analytic proof covers heights at least 100.

The replayed first 29 zeros give \(N(100)=29\), simplicity and completeness
through height 100. The exact rational bracket calculation and the actual
finite-set identification prove

\[
\sum_{0<\gamma\le100}\frac{m_\rho}{|\rho|}<0.592316.
\]

See [`ZetaZeroTableHead`](../RSBounds/ZetaZeroTableHead.lean) and
[`ZetaZeroHeadBound`](../RSBounds/ZetaZeroHeadBound.lean). No larger finite
head is required by this proof.

[`WeightedZetaZeros`](../RSBounds/WeightedZetaZeros.lean) proves partial
summation for these actual finite zero sets. The consequences in
[`RosserWeightedBounds`](../RSBounds/RosserWeightedBounds.lean) and
[`RosserWeightedSplit`](../RSBounds/RosserWeightedSplit.lean) bound reciprocal
and fifth-power weights, keeping the relevant count corrections at split
endpoints. Their integral evaluations are proved in
[`RosserTailIntegrals`](../RSBounds/RosserTailIntegrals.lean).

## Low zeros and eight cancellation subbands

Write

\[
A=1894439,\quad a=1+2\delta,\quad
C=\frac{((1+\delta)^5+1)^4}{\delta^4},\quad Y=\frac2\delta,
\]
\[
L=\frac4{3\delta},\qquad U=\frac{2(1-4\delta)}\delta=Y-8.
\]

Finite RH is used to set \(\Re\rho=1/2\) for \(0<\gamma\le A\).
The ordinary low kernel bound has coefficient \(a/|\rho|\); the
high-decay bound has coefficient \(C/\gamma^5\). The reciprocal estimate
is used through \(Y\), and the fifth-power estimate beyond \(Y\).
Since their values differ at \(Y\), the proof retains and bounds the
endpoint correction

\[
2R(Y)\left(\frac{C}{Y^5}-\frac aY\right).
\]

On the entire closed band \([L,U]\), the checked cancellation lemma
improves the dimensionless kernel bound to \(0.931/\gamma\), for both
smoothings. Divide this band into eight equal subbands with
\(t_j=L+j(U-L)/8\). The windows \((t_j,t_{j+1}]\) are disjoint, so
inclusive zero counts give their multiplicities exactly. The saved
reciprocal mass is bounded below by

\[
M=\sum_{j=0}^{7}
\frac{F(t_{j+1})-R(t_{j+1})-F(t_j)-R(t_j)}{t_{j+1}}.
\]

The division by the upper endpoint has the correct direction for this
lower bound. An endpoint may itself be a zero; no avoidance condition is
needed. The resulting actual positive low-zero estimate is
[`QuarticLowZeroBounds.positive_low_sum_le`](../RSBounds/QuarticLowZeroBounds.lean).
The underlying pointwise estimates are in
[`PolynomialZeroMajorants`](../RSBounds/PolynomialZeroMajorants.lean) and
[`PolynomialZeroCancellation`](../RSBounds/PolynomialZeroCancellation.lean).

## High zeros, multiplicities, and the limiting formula

Above \(A\), only the ordinary critical-strip restriction is used.
Conjugation and reflection \(\rho\mapsto1-\overline\rho\) preserve the
actual finite sets and their multiplicities. The elementary inequality

\[
x^\beta+x^{1-\beta}\le x+1\qquad(0\le\beta\le1,\ x\ge1)
\]

turns the high-zero norm sum into at most \((x+1)K\), where
\(K=\texttt{highWeight}\) is the proved fifth-power tail budget.
Thus its relative contribution is \(K(1+1/x)\). The precise bridges and
pairing are in [`PolynomialZeroCountBridge`](../RSBounds/PolynomialZeroCountBridge.lean)
and [`PolynomialZeroPairing`](../RSBounds/PolynomialZeroPairing.lean).
There is no quantitative zero-free boundary in this step.

For both quartic smoothings, the final finite-sum estimate is

\[
\left\|\sum_{\rho\in\mathrm{zerosRectD}(T)}m_\rho K_x(\rho)\right\|
\le \sqrt{x}\,Q+(x+1)K,
\]

at every sufficiently large good height, where
\(Q=\texttt{sqrtCoefficient}\) is twice the positive low-zero budget
after cancellation. The final module splits exactly at
\(|\gamma|\le A\) versus \(|\gamma|>A\).

The averaged formulas already supply convergence along a common proved
`GoodHeights` sequence. The uniform finite-sum bounds pass to those limits
by continuity of the norm. No new infinite-zero-series convergence
assumption is introduced. The reduction in
[`PolynomialPsiFromZeroSums`](../RSBounds/PolynomialPsiFromZeroSums.lean)
then gives

\[
\frac{|\psi(x)-x|}{x}
\le2\delta+K+\frac{Q}{\sqrt x}
       +\frac{K+\log(2\pi)+0.1}{x}.
\]

## The scalar inequality for every x

[`QuarticFirst29BudgetNumerics`](../RSBounds/QuarticFirst29BudgetNumerics.lean)
certifies the literal expressions defining \(K\), \(Q\), the endpoint
correction and all eight subband contributions. In particular it proves
\(Q>0\). Rational arithmetic and logarithm enclosures are checked by
Lean's ordinary kernel; the exploratory Python diagnostic is not used as
a proof oracle.

[`QuarticFirst29BudgetApplication.relativeBudget_lt`](../RSBounds/QuarticFirst29BudgetApplication.lean)
proves, for every \(x\ge e^{23}\), that the displayed total is strictly
less than \(0.00020211\). It establishes
\(98715<\sqrt{e^{23}}\), bounds the denominators using
\(\sqrt x\ge98715\) and \(x\ge98715^2\), and uses positivity of the
combined coefficient \(Q\). This completes the stated psi estimate at
its original threshold.

## Verification records and remaining goals

The final source compilation and public transitive axiom audit are recorded
in [`rosser-schoenfeld-1975-run.json`](../verification/rosser-schoenfeld-1975-run.json),
with the [axiom output](../verification/rosser-schoenfeld-1975-axioms.log).
The independently run psi Comparator is tracked in
[`psi-run.json`](../verification/psi-run.json). The first session left no
final verdict; the replay of the same hash-validated exports is tracked in
[`psi-resume-run.json`](../verification/psi-resume-run.json). **That replay
passed with exit code 0**, after 3143.89 seconds. It validated 226 recorded
source/configuration hashes, 221 object hashes, and both export hashes before
starting. The [final log](../verification/psi-comparator-resume.log) records
acceptance by Lean's default kernel. Process sandboxing was disabled because
bwrap could not mount the required filesystem; statement, definition, axiom,
and kernel checks remained enabled. No sandboxed attestation is claimed.

Selected component records are:

| Component | Checked record |
|---|---|
| Actual global Rosser count | [zero-count-run.json](../verification/zero-count-run.json) |
| Replayed height-100 certificates | [rh100-replay-run.json](../verification/rh100-replay-run.json) |
| Actual positive head | [zeta-zero-head-bound-run.json](../verification/zeta-zero-head-bound-run.json) |
| Partial summation and finite integrals | [weighted-zeta-zeros-run.json](../verification/weighted-zeta-zeros-run.json), [rosser-tail-integrals-run.json](../verification/rosser-tail-integrals-run.json) |
| Weighted bounds and split | [rosser-weighted-bounds-run.json](../verification/rosser-weighted-bounds-run.json), [rosser-weighted-split-run.json](../verification/rosser-weighted-split-run.json) |
| Actual finite pairing | [polynomial-zero-pairing-run.json](../verification/polynomial-zero-pairing-run.json) |
| Positive low-zero assembly | [quartic-low-zero-run.json](../verification/quartic-low-zero-run.json) |
| Scalar certificate and all-x application | [quartic-first29-scalar-run.json](../verification/quartic-first29-scalar-run.json), [quartic-first29-application-run.json](../verification/quartic-first29-application-run.json) |
| Passage from zero sums to psi | [polynomial-psi-from-zero-sums-run.json](../verification/polynomial-psi-from-zero-sums-run.json) |

This completes the **1975 constant 0.00020211** under the stated finite-RH
premise. Since this page was written, the RS62 Mertens estimate and the
RS62 totient inequality for all \(n\ge3\) have been proved under the same
premise ([RS62Global.md](RS62Global.md)), and so has the separate RS75
quantitative zero-free region, unconditionally for \(|t|\ge1894439\)
([RS75ZeroFreeAudit.md](RS75ZeroFreeAudit.md)). The tighter
**1976 constant 0.00020171** and the requested global \(x/\log x\) bound
for \(\theta\) remain unproved in this development. Existing partial or
finite-range results do not discharge those global goals.
