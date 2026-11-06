# Explicit Rosser–Schoenfeld estimates: partial formalization

This standalone Lean 4.35 project now proves the requested **RS75 b = 23 psi
entry**:

$$
\mathrm{FiniteRH}(1894439)\;\Longrightarrow\;
|\psi(x)-x|<0.00020211\,x\qquad(x\ge e^{23}).
$$

The public theorem is
[`RosserSchoenfeld1975.psi_error_b23`](RSBounds/RosserSchoenfeld1975.lean).
Finite RH means that every zero in the open critical strip with absolute
ordinate at most 1894439 lies on the critical line. This is the sole
mathematical premise apart from the displayed range of x. The proof uses
four integrations, the historical delta 0.0000211, the certified first 29
zeros, and eight cancellation subintervals. See the
[statement and proof guide](docs/PsiTable1975.md).

The complete theorem has freshly compiled and its transitive axiom audit
uses only `propext`, `Classical.choice`, and `Quot.sound`. Its independent
Comparator has passed statement and definition matching, the allowed-axiom
check, and full replay with Lean's default kernel. The successful replay took
3143.89 seconds; see [the completed receipt](verification/psi-resume-run.json)
and [final log](verification/psi-comparator-resume.log). The original fresh
build/export record is `verification/psi-run.json`. Process sandboxing was
disabled for the workspace's recorded bwrap limitation; this is not a
sandboxed attestation.

The project also proves **Rosser (1941), Theorem 19,
unconditionally for every real `T >= 2`, including zero ordinates**:

$$
|N(T)-F(T)| < 0.137\log T + 0.443\log\log T + 1.588.
$$

Here `N(T)` counts actual zeros of Mathlib's Riemann zeta function with
`0 < Im(rho) <= T`, with analytic multiplicity, and
`F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`.
The public theorem is
[`Rosser1941.zero_count_bounds`](RSBounds/Rosser1941.lean).
There is no RH or numerical-count premise.

The stronger finite-range estimate **`abs(N(T)-F(T)) < 1` for
`0 <= T <= 100`** is separately proved, with `F(0)=7/8`.
A reusable [certified table](docs/CertifiedZeroTable.md) provides all 29 zeros
through 100, their rational brackets, simplicity, completeness, and inexpensive
bounds on counts at rational thresholds. The [exact table data](data/zeta-zeros-to-100.json)
is also readable without Lean. See [the public theorem guide](docs/ZeroCountTheorems.md)
for precise statements, imports, citations, and verification records.

Both count theorems passed Comparator's statement and definition matching,
allowed-axiom checks, and full replay with Lean's default kernel. Only
`propext`, `Classical.choice`, and `Quot.sound` are permitted. The native
Comparator command took 2747.55 seconds; see the
[completed receipt](verification/zero-count-run.json).
Process sandboxing was disabled because `bwrap` could not mount its required
filesystem in this workspace; this is not a sandboxed attestation.

**The requested global theta estimate and the full RS62 Mertens/totient
bounds remain unfinished.** The separate RS75 quantitative zero-free region,
the stronger 1976 b = 23 coefficient 0.00020171, the strict count error through
height 280, and a certified first-1000 zero table also remain unproved here.

The completed b = 23 proof assembles the actual finite complex zero sums,
including analytic multiplicities, with the averaged explicit formula.
The high-zero estimate uses conjugation and critical-line reflection; the
quantitative zero-free-region target is a separate problem.

| Result | Freshly checked status |
| --- | --- |
| RS62 totient coefficient 2.50637 for at most twenty distinct prime factors | Proved |
| Its corollary for 3 ≤ q ≤ 10^27 | Proved |
| Finite prime-product certificate through 557, followed by an unrestricted all-n totient reduction | Proved; the two analytic RS62 inputs above 563 remain explicit, unproved hypotheses |
| Exact finite-anchor Abel identities for weighted prime and von Mangoldt sums | Proved |
| Centered Mertens tail identity and variation-to-tail bound | Proved from the existing PNT/Mertens identity; the required quantitative variation bound remains an input |
| Weighted zero-sum partial summation and envelope transfers | Proved for the actual zeta zeros with analytic multiplicity, using the unconditional Rosser estimate |
| Reciprocal-zero head through 100 | Proved: the complete first-29 head has sum of reciprocal norms less than 0.592316 |
| Elementary reciprocal and fifth-power integrals | Proved with explicit logarithmic upper bounds for 7 ≤ a ≤ b |
| Contour/count/multiplicity conversions | Proved, including strict/inclusive endpoints and conjugation/reflection multiplicity symmetries |
| Eight-band budget and its actual zero-sum domination | Proved; assembled with the explicit formula to give the b = 23 psi bound |
| Backlund's phase-aligned subsequence for powers of a nonzero complex number | Proved |
| Angular Jensen inequality, constructive reflected pairing, and the limit along phase-aligned powers | Proved, including the reflection loss E/(2 pi) and the actual horizontal zeta argument bound |
| Exact zeta/digamma reflection identity and constructive first/last crossings | Proved by selective reuse; no zero-count premise |
| Actual horizontal reflection-error integral | Proved: at most 4 delta^2/T, hence less than 8/T, for T >= 1 and 0 <= delta <= 3/4, at nonvanishing horizontal segments |
| Euler-product center lower bound | Proved in Lean: 3.425 < zeta(5/4)/zeta(5/2) < 3.426, hence norm(zeta(5/4+it)) >= 1/3.426 for every real t |
| Continuous gamma phase remainder | Proved for every T > 0: abs(S_gamma(T)) <= 1/(4T), hence also <= 25/(48T) |
| Trapezoidal error via the positive Peano kernel | Proved, including the finite error-sum identity |
| Continuous zeta branch on the anchor line Re(s) = 5/4 | Proved via the Euler logarithm; the vertical argument integral equals the principal argument and has absolute value at most pi/2 |
| Exact Riemann–von Mangoldt count identity | Proved for positive heights off zero ordinates, with the actual positive-ordinate zeta multiplicities and the continuous gamma phase |
| Backlund (54) | Proved: norm(zeta(sigma+it)) ≤ log(t) − 0.048 for sigma ≥ 1, t ≥ 50 |
| Backlund (56) | Proved: norm(zeta(sigma+it)) ≤ t²/(t²−4) · (t/(2 pi))^((1−sigma)/2) · log(t), for 0 ≤ sigma ≤ 1, t ≥ 50 |
| Backlund (77) | Proved: norm(zeta(sigma+it)) < (t/(2 pi))^(1/2−sigma) · log(t), for −1/2 ≤ sigma ≤ 0, t ≥ 50 |
| Upper half-strip maximum principle and finite bottom-edge certificate | Proved; used with the actual normalized zeta function to establish (56) |
| Quantitative digamma and horizontal Gamma-modulus bounds | Proved by adapting Zeta23's quantitative estimate to IEANTN's checked Gauss series |
| Actual common circle majorant at radius 1.32 and its angular integral | Proved, including nonnegativity, integrability, both translated zeta bounds, and numerical coefficients |
| Rosser's .137/.443/1.588 zero-count estimate | Proved unconditionally for every T ≥ 2, including zero ordinates |
| Uniform zero-count error < 1 through height 100 | Proved for 0 ≤ T ≤ 100, including T=0 and zero ordinates |
| Complete first-29 zero table | Proved; rational brackets, exact multiplicities, completeness, and computable bracket-count bounds |
| Quartic kernel bounds, fourth-difference identities, and the upper/lower psi sandwich | Proved |
| Mellin transform of the truncated quartic, with its exact five-factor denominator | Proved for Re(s) > 0 |
| Fourfold integral identity and low/high bounds for an individual zero's quartic contribution | Proved |
| Finite rectangular residue identity, including the quartic kernel's pole at zero | Proved |
| Prime-sum Mellin inversion using only hypotheses on the right vertical line | Proved |
| Fourfold integrated explicit formula for the actual finite sum Psi4, using one common sequence of rectangle heights | Proved, with the left vertical remainder explicit |
| Upper and lower averaged explicit formulas, including the exact main terms and constant at zero | Proved, with the left remainders explicit |
| Logarithmic bound for zeta'/zeta on Re(s) = -1/2 | Proved |
| Both actual averaged left-line remainders, with delta = 0.0000211 | Proved: at most 25000/(pi sqrt(x)), and less than 0.1 for x >= exp 23; no RH premise |
| Lower kernel bounds and a sharper cancellation bound for both smoothing signs on a finite ordinate band | Proved; used in the completed b = 23 row |
| RS75 Theorem 1: zero-free region with R = 9.645908801 and log(abs(t)/17) | Separate target; not proved |
| RS75 real-axis xi/Gamma increments and variable Stechkin parameters | Proved and audited as separate components; the full zero-free theorem remains unfinished |
| RS75's exact degree-four cosine polynomial and its nonnegativity | Proved |
| Gauss series for digamma and its summability on Re(s) > 0 | Reused from IEANTN GammaAsymptotics.v2; freshly compiled and audited on this toolchain |
| Scalar reduction from stated RS62 analytic inputs to the totient product bound | Proved as an implication; those inputs remain unproved |
| Moderate-error psi row b = 23 | Proved for every x ≥ exp 23, assuming only finite RH through 1894439 |
| Full RS62 Mertens/totient bounds and requested global theta estimate | Unfinished |

The unconditional zero-count and finite totient results assume neither RH,
Buethe nor Ramare's sum estimate.
The finite arithmetic through the twentieth prime, 71, is checked by the
ordinary Lean kernel. The checked theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

The unrestricted totient inequality is the goal. The earlier `10^27`
corollary is not an adequate final range. `TotientGlobalReduction.lean`
now checks the prime-product inequality through prime cutoff 557 and proves
the all-n implication from the RS62 product and theta estimates at every
integer cutoff at least 563. Those two analytic estimates still need proofs.

## The b = 23 proof

The chosen method is RS75's **four integrations**, equivalently a degree-four
truncated-power smoothing. The threshold remains `exp 23`.

`Psi4(y) = (1/24) sum_n Lambda(n) max(y-n,0)^4`.

Normalized fourth differences at x and x−4h give upper and lower smoothings
of psi(x), with main terms x+2h and x−2h. The zero contribution has denominator
`rho*(rho+1)*(rho+2)*(rho+3)*(rho+4)`. The parameters remain `m = 4`,
`delta = 0.0000211`, with finite RH through 1894439. The polynomial smoothing
and its finite psi comparisons are checked, as are the bounds for an individual
zero's contribution, for both smoothing signs. The contour is an ordinary fixed rectangle with vertical
sides at Re(s) = -1/2 and Re(s) = 3/2; no quantitative zero-free boundary is
used for it. The integrated formula is now checked, with the residue at zero
evaluated. The actual averaged left remainder is bounded unconditionally by
`25000/(pi sqrt(x)) < 0.1` for `x >= exp 23` at the historical delta.
The quantitative zero-sum estimate and its final assembly are now proved.
See the [completed proof guide](docs/PsiTable1975.md); the older
[quartic formula note](docs/QuarticProof.md) records the earlier construction.

RS75's zero-free region is now a separate target in `RSBounds/Targets.lean`:
assuming the finite RH verification through 1894439, zeta has no zeros where
`abs(t) >= 21` and `sigma >= 1 - 1/(9.645908801 * log(abs(t)/17))`.
This is Theorem 1 of RS75, whose proof uses the finite verification. It remains
a separate requested target. The alternative fixed-parameter b=23 budget in
`docs/QuarticBudgetAudit.md` uses only the critical strip above the finite RH
height, and therefore does not require this quantitative zero-free region.
It does not itself provide a globally decaying `c/log(x)` relative error.
The zero-free theorem itself remains unproved here. Its exact trigonometric
polynomial is checked in `RS75Polynomial.lean`; the remaining analytic inputs
are tracked separately in [the zero-free-region audit](docs/RS75ZeroFreeAudit.md).

The needed zero-count estimate is Rosser (1941), Theorem 19, p. 223:

`abs(N(T)-F(T)) < .137 log(T) + .443 log(log(T)) + 1.588`, for T ≥ 2,

where `F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`.
**The analytic range `T >= 100` is now proved with these exact constants.**
The public count is an unconditional sum of Mathlib's analytic zero orders,
with the inclusive upper endpoint. The endpoint extension is also proved;
the result is not restricted to heights avoiding zeros.

The checked proof includes the angular Jensen/powers step, constructive
reflected crossings, the actual reflection-error integral, the continuous
anchor argument, the exact count/argument-principle identity, and the
branch-correct gamma phase remainder. Backlund's three zeta estimates
(54), (56), and (77) are proved at their original height threshold 50.
The proof of (56) includes its half-strip maximum principle and finite
bottom-edge computation. An actual nonnegative circle majorant is integrated
over all four sectors; the right-arc quadrature and the final constants are
certified in Lean. The rounded envelope is strictly below Rosser's target
for every `T >= 100`.

No finite RH result is used in that analytic theorem. The finite handoff is
also complete: an independently replayed certificate gives all 29 zeros through
100, and the checked rational endpoint inequalities prove the stronger error
`< 1` throughout `[0,100]`. Combining the ranges proves the full theorem. See [the circle-majorant audit](docs/BacklundCircleMajorantAudit.md),
[the Gamma-modulus audit](docs/BacklundGammaModulusAudit.md),
[the primary-source audit](docs/BacklundCountAudit.md) and
[the current IEANTN/PNT+ reuse audit](docs/ZeroCountReuseAudit.md).

The printed center denominator `3.425` needs care: an independent exact
rational computation puts `zeta(5/4)/zeta(5/2)` between `3.425382` and
`3.425390`. Lean now proves the sufficient enclosure `(3.425, 3.426)` and
the center lower bound with denominator `3.426`; the 625-term sums and their
integral-test tails use no numerical axiom. This does not assert
a failure of the final counting theorem. See [the center audit](docs/BacklundCenterAudit.md).
The unconditional certificate for all 29 zeros through height 100 is reused
from `teal-sea/zeta-lab`. All 99 modules have been replayed on this toolchain,
and all 28 pinned axiom audits passed. Its complete table and the resulting
finite-range error theorem are public exports. It is not imported by the
separate analytic `T >= 100` theorem. See [the finite-height audit](docs/LowHeightCertificateAudit.md).
The older RS75 row uses a finite head of 57 zeros; the improved 1976 row uses
a larger head. Those larger numerical zero certificates remain to be formalized. The new
[first-29 route](docs/QuarticFirst29Budget.md) supplies a checked smaller head
and scalar budget and completes the b=23 assembly using that smaller head.

## Reuse from IEANTN

The Gauss-series representation is imported from the actual proved solution
`GammaAsymptotics.v2`, not from a challenge or node statement. Eight original
proof modules compile unchanged apart from import paths; attribution, license,
upstream hashes, and fresh audits are retained. See
[the port record](docs/IEANTNGammaPort.md) and
[the targeted reuse audit](docs/IEANTNReuseAudit.md).

The quantitative vertical digamma estimate is adapted from Zeta23's
`GammaFacts/StirlingVert.lean` in `teal-sea/zeta-lab`, pinned at
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, with IEANTN supplying the
proved series input. The half-strip maximum principle adapts Mathlib's
Phragmén–Lindelöf argument. These are checked proof ports, distinct from the completed finite-height
replay. The local Gamma ports have isolated namespaces so both developments
can be imported together; the affected dependency chain was rebuilt and audited. Original notices, pinned source links, and
licenses are recorded in [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Reproduction

Run from this directory, using its own toolchain:

```sh
lake exe cache get
lake build
lake comparator
lake comparator --config comparator-zero-count.json
python verification/run_psi_check.py
```

`RSBounds.lean` imports completed modules only. `RSBounds/Targets.lean` defines
propositions, not proofs or axioms. Other source files may be under development.

Three independent Comparator configurations are provided: `comparator.json`
for the restricted totient statements, `comparator-zero-count.json` for
the full Rosser count theorem and the strict finite-range error bound, and
`comparator-psi.json` for the b = 23 psi theorem under finite RH. Use the
Python driver shown above for the psi check; it compiles the independent
challenge and solution directly and passes their fresh exports to Comparator.
All three configurations have passed their independent statement/definition,
allowed-axiom, and default-kernel checks.
None asserts the unfinished global theta, full RS62, or zero-free-region
goals. All completed public theorems have fresh Lean builds and transitive
axiom audits, using only `propext`, `Classical.choice`, and `Quot.sound`.
Fresh build logs, axiom audits,
and exact source hashes are in `verification/`. Comparator outcomes and any
sandbox limitation are recorded there.

The dependency `calr3/ternary-goldbach` is pinned at
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`; all revisions are in
`lake-manifest.json`. See `THIRD_PARTY_NOTICES.md` for attribution.

## Sources

- [Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).
- [Backlund, Acta Mathematica 41, pp. 345–375](https://doi.org/10.1007/BF02422950).
- [Rosser–Schoenfeld (1975), Lemmas 7–9 and Theorem 4](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
- [Schoenfeld (1976)](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
- [Rosser–Schoenfeld (1962)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
