# Quartic b = 23 budget from the certified first 29 zeros

This is a **dependency audit and scalar budget**, not a proof of the psi
table row. The original diagnostic uses 60-digit `mpmath`; its output is not
a certificate. The finite head, elementary integral bounds, actual count
bridges, and the displayed eight-band scalar expression have subsequently
been proved in Lean. The mathematical domination of the actual zero sums
and final psi assembly are still separate obligations. The proposed route uses the existing 29-zero certificates and the
proved Rosser count envelope; it does not require a larger finite zero table
or the quantitative RS75 zero-free region.

The reproducible calculation is
[`rs75-first29-budget-diagnostic.py`](../verification/rs75-first29-budget-diagnostic.py).
Its output, including source hashes and exact subband endpoints, is
[`rs75-first29-budget-diagnostic.json`](../verification/rs75-first29-budget-diagnostic.json).
Run from the project root:

```sh
python verification/rs75-first29-budget-diagnostic.py \
  --output verification/rs75-first29-budget-diagnostic.json
```

The script reads the existing rational brackets. It does not change Lean
source, certificate data, or any earlier diagnostic. It also checks the
original exponential-integral formulas against independently evaluated
integrals; this is a consistency check, not numerical certification.

## Fixed inputs and the smaller head

Keep
\[
m=4,\qquad \delta=211/10^7=0.0000211,\qquad
x\ge e^{23},\qquad A=1894439.
\]
Finite RH is assumed only through \(A\). The actual count, including analytic
multiplicity and with the inclusive convention \(0<\gamma\le t\), satisfies
the now-proved envelope
\[
|N(t)-F(t)|<R(t)\quad(t\ge2),
\]
where
\[
F(t)=\frac{t}{2\pi}\left(\log\frac{t}{2\pi}-1\right)+\frac78,
\qquad R(t)=0.137\log t+0.443\log\log t+1.588.
\]
See [`Rosser1941.zero_count_bounds`](../RSBounds/Rosser1941.lean).

The replayed height-100 certificate proves \(N(100)=29\), simplicity, and
completeness. [`BacklundLowZeros.lean`](../RSBounds/BacklundLowZeros.lean)
provides 29 ordered, disjoint rational brackets. Their lower endpoints are

```text
14.13, 21.02, 25.01, 30.42, 32.93, 37.58, 40.91, 43.32,
48, 49.77, 52.97, 56.44, 59.34, 60.83, 65.11, 67.075,
69.54, 72.06, 75.70, 77.14, 79.33, 82.91, 84.73, 87.42,
88.80, 92.49, 94.65, 95.865, 98.83.
```

If these endpoints are \(l_j\), the exact rational sum is

```text
sum_j 1/l_j =
2540034054079986794944092506500151149170004028605797153595744837641091146499
/
4288310989711760238929705028214427343006127006004212403549420316940174788432.
```

It is approximately \(0.592315729939799850995\), strictly below
\(S=0.592316\). Since \(|1/2+i\gamma_j|\ge\gamma_j>l_j\), this supplies
the intended head bound
\[
\sum_{0<\gamma\le100}\frac{m_\rho}{|\rho|}<0.592316.
\]
No square-root evaluation is needed to certify this finite head. The actual
first-29 reciprocal-norm sum and the rational bracket-sum bound are now
proved in [`ZetaZeroTableHead.lean`](../RSBounds/ZetaZeroTableHead.lean),
with four fresh audits using only `propext`, `Classical.choice`, and
`Quot.sound`; see
[`zeta-zero-table-head-run.json`](../verification/zeta-zero-table-head-run.json).
The identification of this indexed head with the contour's counted zero
sum remains part of the separate assembly.

For comparison with the earlier, unproved 57-zero head at
\(D_0=158.84998\), \(N(D_0)=57\), \(S_0=0.8113925\), switching to
\(D=100\), \(N(D)=29\), \(S=0.592316\) increases the existing weighted
quantity \(B\) by approximately
\[
0.0111174403219543.
\]
The corresponding additional relative error at \(e^{23}\) is
\(2.25250927265188\times10^{-7}\). The 57-zero data are used only for this
comparison; they are not premises of the proposed 29-zero budget.

## Recovering the cost with disjoint subbands

Put
\[
a=1+2\delta,\qquad R_4=((1+\delta)^5+1)^4,\qquad
L=\frac4{3\delta},\qquad U=\frac{2(1-4\delta)}\delta.
\]
The checked upper and lower cancellation lemmas in
[`PolynomialZeroCancellation.lean`](../RSBounds/PolynomialZeroCancellation.lean)
give a normalized kernel bound \(0.931/\gamma\) throughout the **closed**
band \([L,U]\), when \(\Re\rho=1/2\). Here
\(L\approx63191.15324\), \(U\approx94778.72986<A\), and the crossover
\(T=(R_4/a)^{1/4}/\delta\) is approximately \(94790.73004>U\).
Thus finite RH applies throughout this band, and the baseline coefficient
there is \(a/\gamma\).

For \(n=8\) or \(16\), use the exact rational endpoints
\[
t_j=L+\frac{j}{n}(U-L)\quad(0\le j\le n).
\]
The sets \((t_j,t_{j+1}]\) are disjoint and cover \((L,U]\). The inclusive
count gives their exact multiplicity counts as
\(N(t_{j+1})-N(t_j)\), with no assumption that an endpoint avoids a zero.
For each zero in a subband,
\(1/\gamma\ge1/t_{j+1}\). Since \(a-0.931>0\), the saved positive
reciprocal mass is bounded below by
\[
M_n=\sum_{j=0}^{n-1}
\frac{F(t_{j+1})-R(t_{j+1})-F(t_j)-R(t_j)}{t_{j+1}}.
\]
Accordingly the relative error saving is
\[
\frac{2(a-0.931)M_n}{\sqrt x}.
\]
This uses exactly the existing kernel lemma on smaller subintervals, with
no new zero-location assertion and no double counting. Every displayed
count lower bound is positive in the diagnostic; the smallest for eight
subbands is approximately \(5802.39019\). The eight-band formula and its
weighting and endpoint directions were independently checked by a second
agent against the actual Lean cancellation statements.

Using the earlier exact-crossover/exponential-integral budget, including
the proved absolute remainder allowance \(0.1\), the diagnostic totals are:

| Disjoint subbands | Relative error at \(e^{23}\) | Target minus total |
|---:|---:|---:|
| 1 | 0.000202212345300535 | \(-1.0234530\times10^{-7}\) |
| 8 | 0.000202084624281668 | \(2.5375718\times10^{-8}\) |
| 16 | 0.000202075227756665 | \(3.4772243\times10^{-8}\) |

The target is \(0.00020211\). A single band is insufficient; eight or
sixteen disjoint subbands leave a positive diagnostic margin.

## A simpler scalar certificate with only logarithms

Set \(Y=2/\delta=20000000/211\), \(C=R_4/\delta^4\), and \(G=F+R\).
Then \(U=Y-8<Y<T<A\). Use the low weight \(a/t\) up to and including
\(Y\), and the high weight \(C/t^5\) strictly above \(Y\). These weights
do not agree at \(Y\); the resulting endpoint term must be retained.

The two partial-summation endpoint contributions combine to
\[
(N(Y)-G(Y))\left(\frac aY-\frac C{Y^5}\right).
\]
Because \(Y<T\), the second factor is negative. The lower count envelope
gives \(N(Y)-G(Y)\ge-2R(Y)\), so the correct upper correction is
\[
2R(Y)\left(\frac C{Y^5}-\frac aY\right)>0.
\]
The script checks the rational inequalities \(U<Y<T<A\) without evaluating
a fourth root, by comparing fourth powers.

The remaining logarithmic integrals admit elementary upper bounds:
\[
\int_D^Y\frac{dt}{t^2\log t}
 \le\frac{1/D-1/Y}{\log D},\qquad
\int_z^\infty\frac{dt}{t^6\log t}
 \le\frac1{5z^5\log z}\quad(z=Y,A).
\]
All denominators are positive. Define
\[
I=\frac{\log^2(Y/(2\pi))-\log^2(D/(2\pi))}{4\pi}
 +0.137(1/D-1/Y)+\frac{0.443(1/D-1/Y)}{\log D},
\]
\[
J(z)=\frac{\log(z/(2\pi))/4+1/16}{2\pi z^4}
      +\frac{0.137}{5z^5}+\frac{0.443}{5z^5\log z},
\]
\[
W=a\left(S+I+\frac{G(D)-29}{D}\right)+CJ(Y)
       +2R(Y)\left(\frac C{Y^5}-\frac aY\right),
\qquad K=C\left(J(A)+\frac{2R(A)}{A^5}\right).
\]
The proposed total, after inserting \(n\) cancellation subbands, is
\[
E_n(x)=2\delta+K+\frac{Q_n}{\sqrt x}
                  +\frac{K+\log(2\pi)+0.1}{x},
\qquad Q_n=2W-2(a-0.931)M_n.
\]
For both eight and sixteen subbands, \(Q_n>0\) in the diagnostic
(approximately \(15.46662507\) and \(15.46569749\), respectively). Once
these signs and scalar bounds are proved, this expression decreases for
\(x\ge e^{23}\). The constant \(0.1/x\) is the existing averaged
left-remainder allowance, not an omitted term.

The elementary-log replacement costs approximately
\(3.0547618\times10^{-9}\) relative to the earlier diagnostic. A further
convenient simplification is to prove \(\sqrt x\ge98715\) and
\(x\ge98715^2\) for \(x\ge e^{23}\). Apply these only **after combining**
the saving into the positive coefficient \(Q_n\). The resulting totals are:

| Subbands | Rational \(Y\), elementary logarithms | Also use \(\sqrt x\ge98715\) | Remaining margin |
|---:|---:|---:|---:|
| 8 | 0.000202087679043466 | 0.000202088902778541 | \(2.1097221\times10^{-8}\) |
| 16 | 0.000202078282518463 | 0.000202079506180146 | \(3.0493820\times10^{-8}\) |

Sixteen subbands give additional room for certified logarithmic rounding,
without changing the smoothing degree, delta, threshold, or RH height.

## What this establishes, and what remains

This audit supplies a feasible replacement for the missing 57-zero head.
**That larger head is not necessary if the proposed assembly is certified.**
It does not assert the final psi inequality. The remaining proof obligations
include the head/count/contour multiplicity bridges, conjugation and
reflection reindexing, the weighted-tail limit arguments, the displayed
elementary integral bounds, and certified scalar arithmetic and monotonicity.
Some of these may be proved independently after this audit was written;
their actual Lean declarations and audit records determine their status.

The high-zero estimate still uses the ordinary critical-strip restriction
and multiplicity-preserving symmetries, yielding the factor \(1+1/x\).
It uses no quantitative RS75 zero-free boundary. The separate RS75
zero-free-region target and the global \(x/\log x\) target are unaffected
by this fixed-relative-error calculation.

## Checked components added after the diagnostic

- [Actual zero-sum partial summation](../RSBounds/WeightedZetaZeros.lean), with
  eight standard-axiom audits in `verification/weighted-zeta-zeros-run.json`.
- [Finite reciprocal head](../RSBounds/ZetaZeroTableHead.lean) and its
  [actual-zero reindexing](../RSBounds/ZetaZeroHeadBound.lean), with four and
  six standard-axiom audits respectively.
- [Elementary finite integral bounds](../RSBounds/RosserTailIntegrals.lean),
  with thirteen standard-axiom audits in `verification/rosser-tail-integrals-run.json`.
- [Contour/count/multiplicity bridges](../RSBounds/PolynomialZeroCountBridge.lean),
  with sixteen standard-axiom audits, including both multiplicity symmetries.
- [Literal scalar certificate](../RSBounds/QuarticFirst29BudgetNumerics.lean):
  `scalarBudget_lt` proves the displayed eight-band rational-denominator
  expression is strictly below `0.00020211`; `sqrtCoefficient_pos` proves
  the required coefficient is positive. Its nine standard-axiom audits are
  recorded in `verification/quartic-first29-scalar-run.json`.

The scalar expression is identified with the displayed `W`, `K`, `M_8`, and
`Q_8` formulas in Lean. This certifies arithmetic and logarithm enclosures;
it is not itself a theorem bounding `psi`.
