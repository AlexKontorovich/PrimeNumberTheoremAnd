# RS75 zero-free region: dependency audit

The separate target is `Goals.ZeroFreeRegion1975` in
[`Targets.lean`](../RSBounds/Targets.lean): assuming `FiniteRH 1894439`,

\[
 |t|\ge21,\qquad
 \sigma\ge1-\frac{1}{9.645908801\log(|t|/17)}
 \quad\Longrightarrow\quad\zeta(\sigma+it)\ne0.
\]

This is **a specification, not yet a proved theorem**. It preserves RS75
Theorem 1's constants and closed boundary. The paper uses a finite RH check
through \(A=1894438.51224\ldots\); the specified integer height covers it.
Primary reference: Rosser–Schoenfeld (1975), §1, Lemmas 1–2 and Theorem 1,
[DOI 10.1090/S0025-5718-1975-0457373-7](https://doi.org/10.1090/S0025-5718-1975-0457373-7).

## Existing source and verification status

The inspected upstream revision is
`calr3/ternary-goldbach@ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.
[`zero_free` in ZeroFreeRegion.lean](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L540)
states only

\[
 \beta\le1-\frac1{11\log|\gamma|}\qquad(|\gamma|\ge10^9).
\]

That theorem does not imply the target. `ZeroFree.lean` and
`ZeroFreeRegion.lean` were inspected here; they were **not freshly compiled
or transitively axiom-audited in this audit**. `XiPartial` was built as a
dependency of the checked `PolynomialLeftRemainder` module. The latter's
coarse left-line estimate is freshly checked, but is not the sharp gamma
estimate required below. The checked quartic explicit-formula work likewise
does not prove the zero-free target.

## Dependency map

| Component | Reusable source | Required change or missing proof |
|---|---|---|
| Zero sums and symmetry | [`XiPartial.xi_partial_approx`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/XiPartial.lean#L776), [`ZeroFree.pair_approx`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFree.lean#L111), `xiF_zero_re`, `xiF_zero_one_sub_conj` | No new global Hadamard product or contour theory is needed for the Stechkin step. |
| Stechkin pair inequality | [`stechkin_alg`, `Phi_stechkin`, `stechkin_xi`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFree.lean#L30) | Specialize to the paper's variable \(\sigma_0=(1+\sqrt{8\sigma^2-4\sigma+1})/2\), \(\kappa=(2\sigma-1)/(2\sigma_0-1)\). Prove its elementary parameter bounds and the distinguished-zero sharpening described below. Existing wrappers instead fix \(\sigma_0=1.6181\). |
| Cosine polynomial | [`trig_poly_nonneg`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L147) proves the different coefficients \((18,30,17,6,1)\) | Prove the exact RS75 factorization \(P(\theta)=8(0.9126+\cos\theta)^2(0.2766+\cos\theta)^2\), its coefficients and their nonnegativity. The exact factorization and coefficient positivity are now freshly checked in [`RS75Polynomial.lean`](../RSBounds/RS75Polynomial.lean); this does not yet prove the zero-free theorem. |
| Positivity of the Stechkin difference | [`hasSum_re_vM`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L140), `vM_positivity` | Apply polynomial positivity to \(-\Re\zeta'/\zeta(\sigma+ikt)+\kappa\Re\zeta'/\zeta(\sigma_0+ikt)\). Existing `vM_positivity` handles only the first term; existing `vM_term_le` subsequently pays a coarse error at every frequency. A general weighted-difference lemma is still needed. |
| Gamma contribution | [`Digamma.digamma_eq_integral`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/Digamma.lean#L259), recurrences, [`re_vM_eq`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L192) | Prove the explicit \(O(t^{-2})\) digamma remainder used in §1 and its two-point combination. Existing `half_re_digamma_half_le` has an additive `0.36`; `re_digamma_sub_le` retains a nonvanishing constant. These are not the paper's sharp estimate. |
| Real logarithmic derivatives | [`vM_real_le`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L282), Mathlib's real-axis Dirichlet series and regularized zeta at 1 | Certify the paper's near-pole bound (1.17), and the value/derivative bounds at the golden ratio used in (1.24)–(1.25). No certificates for these constants were found in the inspected upstream source. Qualitative Mathlib asymptotics do not supply them. |
| Finite range and final numerics | Existing finite-RH target, zeta/xi zero equivalence, conjugation | For \(21\le|t|\le1894439\), show the proposed boundary is strictly above \(1/2\), then apply finite RH. Above this height, combine the sharpened inequalities, parameter bounds and certified rational/log/square-root calculations. The final strict zero inequality must exclude equality on the stated closed boundary. |

## Two useful reductions

The paper's variable parameters satisfy
\(\sigma_0(\sigma_0-1)=\sigma(2\sigma-1)\). For \(0\le\beta\le1\),

\[
\kappa\left(\frac1{\sigma_0-\beta}
 +\frac1{\sigma_0+\beta-1}\right)
=\frac{2\sigma-1}{\sigma(2\sigma-1)+\beta(1-\beta)}
\le\frac1\sigma\le\frac1{\sigma+\beta-1}.
\]

Consequently, the existing `stechkin_xi` yields the needed full
\(1/(\sigma-\beta)\) distinguished-zero contribution after elementary
algebra. Its pair-positivity hypothesis also holds for these parameters.
These observations have been mathematically checked, but this specialization
has not yet been encoded in Lean.

The new difference-positivity proof can reuse the existing `HasSum` results:
each integer contributes
\(\Lambda(n)(n^{-\sigma}-\kappa n^{-\sigma_0})P(t\log n)\ge0\).
This avoids replacing every shifted logarithmic derivative by a separate
coarse real-axis bound.

## Numerical and low-zero issues

Changing only the final number in the existing theorem cannot suffice. For
its current cosine coefficients, even the ideal limiting Stechkin coefficient
gives

\[
\frac{(1-1/\sqrt5)54}{2(\sqrt{30}-\sqrt{18})^2}
\approx9.7921758524>9.645908801.
\]

This is a diagnostic calculation, not a certified Lean numerical result.

A literal port of the paper's proof of (1.17) also uses the lower bound
on the first zero's ordinate. `FiniteRH 1894439` alone does not encode that
lower bound. One must prove it separately, or instead prove the real-axis
inequality directly with certified series/remainder estimates. The latter
would avoid adding a first-zero assumption to the standalone target.

The outstanding analytic work is therefore the sharp gamma and real-axis
estimates, followed by the numerical assembly. The optimized polynomial is now checked. The Stechkin specialization and
difference positivity remain smaller algebraic components. None of these outstanding obligations is being hidden behind a
new axiom or represented here as completed.

The Gauss-series representation for digamma is now reused directly from
IEANTN's proved `GammaAsymptotics.v2` solution. Its eight proof modules compile
unchanged apart from imports on the present toolchain, and their exported
results pass the transitive axiom audit. See [the port record](IEANTNGammaPort.md).
This supplies an existing representation for the gamma work; the sharp
uniform remainder needed by RS75 remains to be proved.
