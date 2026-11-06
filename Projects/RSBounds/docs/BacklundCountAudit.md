# Zero-count proof audit

This is a source audit, not a compilation or axiom audit of the external project.
The inspected revision of `gersh/ternary-goldbach-lean` is
`27df23af6a712895f22204d0d81102baa74f0ebe` (also its `main` when checked).
It uses Lean 4.32.1; this package uses Lean 4.35.0.

The sharp Rosser estimate is still a `sorry` in
[`RosserSchoenfeldZeta.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/forks/PrimeNumberTheoremAnd/PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RosserSchoenfeldZeta.lean):

`riemannZeta.Riemann_vonMangoldt_bound 0.137 0.443 1.588`.

The exact statement is available in the literature: Rosser (1941), Theorem 19,
pp. 223–224, [DOI 10.2307/2371291](https://doi.org/10.2307/2371291).
The issue is formalizing the proof, rather than locating a suitable estimate.

## Primary-source statement and provenance

The actual printed pages, not just later citations, were inspected on
2026-11-06. Put

\[
 F(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+\frac78,
 \qquad
 R(T)=0.137\log T+0.443\log\log T+1.588.
\]

Rosser, p. 223, defines `N(T)` by **`0 < gamma <= T`**, counting the
nontrivial zeros with their multiplicities. Theorem 19 states the strict
inequality

\[
 |N(T)-F(T)|<R(T)\qquad(T\ge2).
\]

The scan has `0.443`; the Internet Archive OCR misreads this as `0.448`.
This theorem is unconditional. Finite RH is not an assumption in its
statement or its high-height analytic proof.

The precise attribution is **Rosser's sharpening of Backlund's method**.
Backlund, *Über die Nullstellen der Riemannschen Zetafunktion*, Acta
Mathematica 41, pp. 345–375, [DOI 10.1007/BF02422950](https://doi.org/10.1007/BF02422950),
has the different constants

\[
 |N(T)-F(T)|<0.137\log T+0.445\log\log T+4.350
\]

in (39), p. 355. His initial counting argument excludes heights equal to a
zero ordinate (p. 349). The analytic estimate is established for
`T > 50 + 1.32 = 51.32`; the final paragraph, p. 375, extends (39) to
`T >= 2` using the known zeros below height 200. The footnote records the
completeness of 79 zeros in that range. Backlund's final global range should
not be confused with the initial discussion of an older bound for `T > 200`.
The scan's imprint says 1918; bibliographies variously date this volume
1916–1918, so the volume, pages, and DOI are the unambiguous locators.

### Rosser's analytic proof, pp. 223–224

To avoid confusing the power exponent with the counting function, write
`m` for the positive integer exponent. Rosser uses

\[
 G_m(z)=\frac{\zeta(z+5/4+iT)^m+\zeta(z+5/4-iT)^m}{2},
 \quad r=1.32,\quad q=\log(4r/3),
\]

and the gamma remainder

\[
 S_\Gamma(T)=\Im\log\Gamma(1/4+iT/2)
       -\frac T2\log\frac T2+\frac T2+\frac\pi8.
\]

His intermediate inequality at the bottom of p. 223 is

\[
\begin{aligned}
 |N(T)-F(T)|<&\frac{1}{2\pi q m}
       \int_0^\pi\log|G_m(re^{i\varphi})|\,d\varphi
       +\frac12+\frac4{\pi T}+\frac{k}{m}\\
       &-\frac{\log|G_m(0)|}{2qm}
       +\frac{|S_\Gamma(T)|}{\pi},
\end{aligned}
\]

where `k` is independent of `m`. The proof explicitly cites Backlund
pp. 354–361 for the argument/reflection/Jensen step and pp. 361–369 for
the boundary bounds. At the center it takes a subsequence of powers with

\[
 G_m(0)/|\zeta(5/4+iT)^m|\longrightarrow1,
 \qquad |\zeta(5/4+iT)|\ge1/3.425.
\]

The checked phase theorem below supplies the subsequence step; it does not
supply the preceding count-versus-integral inequality. The displayed center
inequality with denominator `3.425` is a transcription of Rosser's printed
claim, not a verified input to this project; see the numerical audit below.

**Center-constant audit flag.** The ordinary Euler-product lower bound is

\[
 |\zeta(5/4+iT)|\ge\frac{\zeta(5/2)}{\zeta(5/4)}.
\]

Independent high-precision floating-point evaluations, including an
80-decimal-digit `mpmath` calculation during this audit, give

\[
 \frac{\zeta(5/4)}{\zeta(5/2)}
 \approx 3.4253861160482534176383572338483047761390.
\]

Consequently `3.425` is rounded in the wrong direction **for this
Euler-product derivation**. We will target the conservative denominator
`3.426`, with a proved numerical enclosure, rather than import the printed
number. This is a warning about an intermediate numerical justification,
not a proved counterexample to Rosser's final zero-count theorem.
The floating-point calculation is neither a Lean proof nor a certified
interval computation.

Rosser cites reference 5, p. 26, for the printed center bound. Reference 5
is *The n-th Prime is Greater than n log n*, Proceedings of the London
Mathematical Society (2) 45, pp. 21–44,
[DOI 10.1112/plms/s2-45.1.21](https://doi.org/10.1112/plms/s2-45.1.21).
The 1941 bibliography and the publisher date it 1939; it is also commonly
cited as 1938. The publisher metadata was accessible, but the full paper
and p. 26 were not retrieved in this audit. We therefore do not claim to
have checked the cited derivation there.

In the provisional numerical exploration of a direct boundary majorant,
changing `3.425` to `3.426` adds
`log(3.426/3.425)/(2*log(1.76))`, approximately `0.000258200121`,
to the constant term. The explored constant increases from approximately
`1.580688317` to `1.580946517`, both below the tentative round upper bound
`1.581`. Thus that rounding change does not consume the margin in the
explored `T >= 150` comparison using `1.581`. **Neither this comparison
nor the proposed lower analytic cutoff is proved yet.**

Concrete analytic components visible in Backlund's proof are:

* The gamma-controlled reflection estimate (44), p. 357,
  `abs(Delta_1 arg zeta + Delta_2 arg zeta) < 8/T`, for `T > 1`,
  on symmetric horizontal segments from `1/2` to `1/2 +/- delta`, with
  `0 <= delta <= 3/4`, at a height without zeta zeros on the path.
* The reflected argument-level crossings and paired zero distances,
  pp. 359–360. These give the factor of two in Jensen; a generic
  unpaired disk zero count does not recover the sharp leading constant.
* The zeta bound (54), p. 362,
  `abs(zeta(sigma + i*t)) < log(t) - 0.048` for `sigma >= 1`, `t >= 50`.
* The strip estimate (56), p. 363,
  `abs(zeta(sigma + i*t)) < t^2/(t^2-4) * (t/(2*pi))^((1-sigma)/2) * log(t)`
  for `0 <= sigma <= 1`, `t >= 50`. Its proof includes an explicit
  gamma estimate and a Phragmen–Lindelof argument.
* The functional-equation bound (77), p. 369,
  `abs(zeta(sigma + i*t)) < (t/(2*pi))^(1/2-sigma) * log(t)`
  for `-1/2 <= sigma <= 0`, `t >= 50`.
* The gamma remainder estimate, p. 374,
  `abs(S_Gamma(T))/pi < 25/(48*pi*T)`.
* The angular majorant integration and finite numerical bounds,
  pp. 371–374. On the right semicircle the non-elementary integral is
  `(1/(2*pi)) * integral_0^(pi/2) log(zeta(5/4+r*cos(phi))) dphi`;
  Backlund bounds it by `0.1367` using convexity and a trapezoidal rule.

These are source-level proof obligations. This list does not assert that
none has reusable formal components; see the separate external-code audit.
Rosser's powers must be handled explicitly in the boundary estimate:
an upper bound for the average of two values does not automatically give
the same upper bound for their high powers.

### The finite range is a separate input

Rosser defines `A_0` by `F(A_0) = 1041`, obtaining approximately
`1467.47747`. This `A_0` is unrelated to the finite-RH height `1894439`
used for the requested psi table entry. For `T >= A_0`, he uses the
analytic argument above. For `2 <= T <= A_0`, he invokes:

* Theorem 17: `abs(N(T)-F(T)) < 1` for `0 <= T <= 280`, from
  Hutchinson's computations (reference 7, pp. 49–60).
* Theorem 18: `abs(N(T)-F(T)) < 2` for `0 < T <= A_0`, together
  with `N(A_0) = 1041` and finite RH through `A_0`. The count information
  comes from Titchmarsh's computations (references 8 and 9), completed
  by Rosser's extra verification of `N(A_0) < 1043`.

A premise saying only that zeros up to a height lie on the critical line
does not provide these counting-error bounds. A certified complete list
of sufficiently narrow ordinate intervals could provide them. If only
a high-height tail count is needed, the global low-height extension
need not be included in that theorem; any different analytic cutoff
must itself be proved rather than read into Rosser's statement.

### Source files and reproducibility

Canonical public locators:

* [Rosser issue scan](https://archive.org/details/sim_american-journal-of-mathematics_1941-01_63_1),
  [PDF mirror](https://ia600607.us.archive.org/4/items/sim_american-journal-of-mathematics_1941-01_63_1/sim_american-journal-of-mathematics_1941-01_63_1.pdf),
  [OCR](https://archive.org/stream/sim_american-journal-of-mathematics_1941-01_63_1/sim_american-journal-of-mathematics_1941-01_63_1_djvu.txt).
  Printed p. 223 is image leaf 228 and PDF page 229.
* [Backlund PDF](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/5290-11511_2006_Article_BF02422950.pdf).
  Printed p. 345 is PDF page 1.

The downloaded source scans remain outside this package, in the workspace
`sources/` cache. They are not redistributed in the repository.

| Cache file | SHA-256 |
| --- | --- |
| `sources/rosser1941_issue.pdf` | `5295b310a6a1050fe1abee4b252c899e90c7174f446408bc95d1eab49a1f2518` |
| `sources/rosser1941_issue.txt` | `58f066a793aefd5a1bcd91bea40592118c9595d7aa4b97ae85bfec7643cb9f7e` |
| `sources/rosser1941_p223.jpg` | `ba7c0f36b244fa18e193998a4b7885fcbb914138434c141f34dddb4fe417ad4f` |
| `sources/rosser1941_image.jpg` (p. 224) | `0d78ced35d4401b3c25ffb6dc66203ea7d9d4d3061b07b23e68bd72b3256131c` |
| `sources/backlund1918.pdf` | `0a8b93537e8e15f866b2770c31f8735c96f6c9bd7555de81f8d2dac95744c43f` |

Both primary papers were accessible; no user upload is currently needed.

## Existing weaker result

[`BacklundRvMLooseUnconditional.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundRvMLooseUnconditional.lean)
supplies a closed proof expression for
`riemann_vonMangoldt_7_30_55_holds`, with parameters `(7, 0, 30.55)`.
Its proof combines the argument-variation identity, a coarse Jensen estimate,
and an explicit Stirling remainder bound.

**The wrapper's comment about a native certificate is stale.** The actual
[`BacklundF3Numeric.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundF3Numeric.lean)
uses the ordinary arithmetic proofs in
[`BacklundF3OrdinaryCertificate.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundF3OrdinaryCertificate.lean).
For the zeta argument, only the even full-window upper and lower traces are
used: 277 stopped cells in total. The capstone imports six traces, including
four not needed for this particular theorem. No replacement of `native_decide`
was identified in this F3 component. A fresh transitive axiom audit would
still be required before making a kernel-verification claim for the entire
coarse-count theorem.

The static import closure is substantial: the read-only crawl was stopped
after reaching 360 non-Mathlib modules, with further imports pending. This
overestimates the minimum theorem dependency closure, because imported files
also contain unrelated results. No port or compilation of that closure was
attempted here. Whether its coarse constants suffice for the requested
`b = 23` row, possibly with the larger 1976 low-zero head, remains unproved.

The external project's `riemannZeta.N T` counts zeros in `0 < Im rho < T`.
The finite counting function in `WeightedZeroSums.lean` uses `gamma <= T`.
An application needs a proved endpoint-convention bridge; these definitions
are not interchangeable by definitional equality.

## What this package establishes

`BacklundPhase.lean` proves that for every nonzero complex `z` there are
strictly increasing exponents `n(j)` such that

`(z / norm z) ^ n(j) -> 1`

and

`log(abs(Re(z ^ n(j)))) / n(j) -> log(norm z)`.

This supplies the center-phase step for Rosser's use of powers of zeta.
Fresh compilation and all five theorem axiom audits passed; see
`verification/backlund-phase-run.json` and the corresponding logs. This
phase component alone does not establish the zero-count estimate; it is
now connected to the reflected crossing, argument-count assembly, and
explicit boundary-integral bounds described below. Mathlib supplies the
exact circle-average Jensen identity and a divisor-count inequality in
`Analysis/Complex/JensenFormula.lean`; the formal proof reuses those tools.

### Further completed components

`BacklundJensen.lean` now retains the angular majorant in Jensen's inequality
and passes to the phase-aligned powers, with eight standard-axiom audits.
`BacklundFirstCrossing.lean` and `BacklundReflection.lean` selectively reuse
the constructive crossings and exact reflected logarithmic derivative;
twelve fresh audits pass. See `BacklundReflectionReuse.md` for provenance.

`IEANTNDigammaDifference.lean` reuses the proved IEANTN difference estimate
from `Solutions/CH2.v1/Section81Titch.lean`. With recurrence and a telescoping
bound for the remaining small heights, `BacklundGammaReflection.lean` proves

\[
 \left|\int_{1/2}^{1/2+\delta}
 \left(\Im\frac{\zeta'}{\zeta}(\sigma+iT)
 -\Im\frac{\zeta'}{\zeta}(1-\sigma+iT)\right)\,d\sigma\right|
 \le \frac{4\delta^2}{T}<\frac8T.
\]

The hypotheses are `T >= 1`, `0 <= delta <= 3/4`, and nonvanishing at both
evaluated points throughout the closed interval. Integrability is separately
proved. There is no RH or numerical counting premise. Seventeen fresh audits
use only `propext`, `Classical.choice`, and `Quot.sound`.

`BacklundCenter.lean` proves the exact Euler-product ratio lower bound,
including the specialization at `5/4`. Its two axiom audits pass; the
independent numerical enclosure is explained in `BacklundCenterAudit.md`.

### Further checked components

`BacklundPairedJensen.lean`, `BacklundPairedCrossing.lean`, and
`BacklundPairedPower.lean` now construct the reflected crossings and prove
the limiting argument bound. Retaining the unmatched right-hand zeros
gives reflection loss `E/(2*pi)`. The radius condition is only `R > 3/4`,
so the theorem applies to Rosser's `R = 1.32`; it does not assume that every
reflected partner lies in the disk. Ten exported theorem audits use only
the standard three axioms.

`BacklundCenterNumerics.lean` now proves
`3.425 < zeta(5/4)/zeta(5/2) < 3.426` and the center lower bound `1/3.426`
in Lean. The finite root certificates and integral-test tails are checked
without an external numerical axiom.

`BacklundGammaPhaseEstimate.lean` proves the stronger unconditional bound
`abs(S_Gamma(T)) <= 1/(4*T)` for every `T > 0`, and hence the requested
`25/(48*T)` bound. The phase is the continuous digamma integral, with a
proved rectangle identity connecting it to the argument principle.
The proof uses the actual IEANTN Gauss series and the positive
trapezoidal Peano kernel, not a stipulated Stirling remainder. Seven fresh
audits use only the standard three axioms. See
[`BacklundGammaPhase.md`](BacklundGammaPhase.md).

`BacklundCountIdentity.lean` now proves the exact Riemann–von Mangoldt
identity for every positive height not equal to a zero ordinate. Its count
is explicitly identified with the sum of actual zeta multiplicities at
`0 < Im rho < T`. The rectangle argument and symmetry reduction have no
counting premise. Eighteen fresh audits use only the standard three axioms.

`BacklundAnchor.lean` fixes the vertical logarithm branch through the Euler
logarithm bound, and `BacklundZetaPhase.lean` specializes the constructive
Jensen theorem to the actual horizontal zeta argument. Their nine and eleven
audits, respectively, use only the standard three axioms.

The sharp zeta boundary majorants, numerical angular integral, and endpoint
extension are now connected to these components. The resulting unconditional
estimate with Rosser's original constants is checked for every `T >= 100`,
including zero ordinates; see the final status section below. The full
`T >= 2` range still awaits the finite-height handoff. A public finite-height
source certificate through 100 is documented in
[`LowHeightCertificateAudit.md`](LowHeightCertificateAudit.md); its local
replay is in progress and its 59 scalar certificates are already checked.

### Checked sharp right-edge estimate and Euler--Maclaurin remainder

`BacklundEulerMaclaurin.lean` proves the complex second-order quadrature
identity, its sharp `1/12` integral remainder, and finite and regularized
infinite forms. `BacklundZetaRegularization.lean` supplies the regularized
Dirichlet-sum limit throughout `Re s > 0`, reusing the existing first-order
Euler--Maclaurin theorem from `Prelim.PNTMertens` and the already proved
sawtooth continuation in `Explicit.ZetaGrowth`.

Consequently `BacklundZetaBoundary.zeta_second_order_remainder_explicit_of_pos`
proves, for `Re s > 0`, `s != 1`, and an integer `N >= 1`,

\[
\left|\zeta(s)-\sum_{1\le n<N}n^{-s}-\frac{N^{-s}}2
-\frac{N^{1-s}}{s-1}-\frac{sN^{-s-1}}{12}\right|
\le \frac{|s(s+1)|}{12(\Re s+1)}N^{-\Re s-1}.
\]

The same file now proves Backlund's right-edge estimate (54):

\[
 |\zeta(\sigma+it)|\le\log t-0.048
 \qquad(\sigma\ge1,\ t\ge50).
\]

This theorem is unconditional. The proof uses `N=floor(t/3)+1`, the existing
Ramaré harmonic-number bound, the previously checked Euler-constant
enclosure, and elementary rational estimates. Its limiting argument at
`sigma=1` uses continuity of zeta. All three modules were freshly compiled;
all six exported theorem audits use only `propext`, `Classical.choice`, and
`Quot.sound`. See `verification/backlund-zeta-boundary-run.json` and
`verification/backlund-zeta-boundary-axioms.log`.


### Checked finite bottom edge at height 50

`BacklundBottomCertificates.lean`, `BacklundBottomData.lean`, and
`BacklundBottomFiniteSum.lean` prove the unconditional bound

\[
 |\zeta(\sigma+50i)|\le 3.75
 \qquad(1/2\le\sigma\le1).
\]

The exported theorem is
`BacklundBottomCertificates.norm_zeta_height_fifty_le` (within the
`TernaryGoldbach.RSBounds` namespace). The proof applies the checked
second-order Euler--Maclaurin formula above with `N=20`. Rational
logarithm, quarter-turn, and Taylor certificates enclose the real and
imaginary parts of the entire finite sum uniformly in `sigma` and show
that its norm is at most `2.03`. The remaining analytic terms are bounded
by `0.08946`, `0.047`, and `1.555` respectively. Thus this is a concrete
finite calculation, not a premise asserting a bottom-edge bound.

The historical proof in Backlund uses `N=10` with a fourth-order
Euler--Maclaurin correction. Using `N=20` lets this formalization reuse
its proved second-order remainder without changing height 50.
`scripts/gen_backlund_bottom_data.py` merely selects rational witnesses;
Lean checks all rows and aggregate inequalities by kernel reduction.
The generated floating-point report is explicitly not proof evidence.
Fresh compile hashes and five exported axiom audits are recorded in
`verification/backlund-bottom-run.json` and
`verification/backlund-bottom-axioms.log`.


### Checked unconditional analytic zero count, `T >= 100`

`BacklundHighCount.lean` now proves
`Rosser1941.zero_count_bounds_high`: for every real `T >= 100`,

\[
\left|N(T)-\left(\frac{T}{2\pi}\log\frac{T}{2\pi}
-\frac{T}{2\pi}+\frac78\right)\right|
<0.137\log T+0.443\log\log T+1.588.
\]

Here `Rosser1941.positiveZeroCount` is defined directly from Mathlib's
`riemannZeta` and `analyticOrderAt`, counting multiplicities with
`0 < Im rho <= T`. Its equality with the finite count used by the
argument-principle proof is itself proved. The endpoint theorem extends
the analytic estimate to heights equal to zero ordinates.

There are no RH, numerical zero-certificate, zero-count estimate, or
unproved analytic-bound premises. The three sharp zeta boundary estimates,
angular integration, and rational scalar rounding are proved components.
`verification/backlund-high-count-run.json` records fresh compilation and
five successful axiom audits, all using only `propext`, `Classical.choice`,
and `Quot.sound`. `verification/aggregate-backlund-high-run.json` records
the successful root-module build on 2026-11-06.

The full `T >= 2` statement remains pending until the separate finite
zero-certificate replay, count-convention bridge, and low-height assembly
are checked. Its 59 scalar endpoint certificates are already compiled and
audited. This status does not assert completion of the downstream quartic
smoothing integral estimate, the `b=23` psi table entry, or the quantitative
RS75 zero-free region merely from the count theorem.
