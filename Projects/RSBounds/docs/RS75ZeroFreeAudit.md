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

## Current checked components

The separate zero-free theorem remains unfinished. The completed
[b = 23 psi proof](PsiTable1975.md) does not depend on it: that proof bounds
its high-zero tail by reflection, the ordinary critical strip, and Rosser's
zero-count estimate.

Four additional modules have compiled and passed their transitive axiom audits,
with only `propext`, `Classical.choice`, and `Quot.sound`:

| Component | Exact checked result | Receipt |
|---|---|---|
| [Real-axis numerics](../RSBounds/RS75RealAxisNumerics.lean) | Odd reciprocal-square sum at most .23391; first-29 rational head coefficient at least .03414 | [9 audits](../verification/rs75-real-axis-numerics-run.json) |
| [Actual xi increment](../RSBounds/RS75XiIncrement.lean) | `Re logDeriv xiF s - Re logDeriv xiF 1 >= .03414*(s-1)` for `1 <= s <= 1.03`; unconditional | [8 audits](../verification/rs75-xi-increment-run.json) |
| [Actual Gamma increment](../RSBounds/RS75RealAxisGamma.lean) | For `G(s)=1/s + Re(digamma(s/2))/2`, `G(s)-G(1) <= .23391*(s-1)` for every `s >= 1` | [3 audits](../verification/rs75-real-axis-gamma-run.json) |
| [RS75 parameters](../RSBounds/RS75Parameters.lean) | Variable Stechkin parameters, reflected-zero payment, cubic lower bound for kappa, and golden-ratio transfer slope 1.34424 | [21 audits](../verification/rs75-parameters-run.json) |

The xi result uses the already certified first 29 zeros and the proved actual
partial-fraction approximation. Its accompanying `xi_zero_height_lower`
also proves that every xi zero has absolute ordinate greater than 14.13;
no separate first-zero assumption is introduced.

The intended near-pole coefficient is the sufficient weaker value .2,
obtained from `.23391 - .03414 = .19977 < .2` after exact normalization at 1.
The final normalization wrapper is still being checked at this checkpoint.
The golden-ratio zeta estimates, weighted-difference positivity, frequency
assembly, final scalar proof, and full zero-free conclusion remain unfinished.
The [residual audit](RS75ResidualAudit.md) explains why the weaker real-axis
constants suffice; its exact-rational diagnostic is not a Lean proof.

## Existing source and verification status

The inspected upstream revision is
`calr3/ternary-goldbach@ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.
[`zero_free` in ZeroFreeRegion.lean](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L540)
states only

\[
 \beta\le1-\frac1{11\log|\gamma|}\qquad(|\gamma|\ge10^9).
\]

That theorem does not imply the target. The unchanged `ZeroFree.lean` has
now freshly compiled; the full `ZeroFreeRegion.lean` check and targeted
transitive audit are still in progress at this checkpoint. `XiPartial` is
already checked as part of the completed psi proof. The quantitative
Gamma estimate needed for the frequency bound is separately available in
`BacklundGammaModulus.abs_digamma_re_sub_log_le`; combining it at two points
is a remaining RS75 step.

## Dependency map

| Component | Reusable source | Required change or missing proof |
|---|---|---|
| Zero sums and symmetry | [`XiPartial.xi_partial_approx`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/XiPartial.lean#L776), [`ZeroFree.pair_approx`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFree.lean#L111), `xiF_zero_re`, `xiF_zero_one_sub_conj` | No new global Hadamard product or contour theory is needed for the Stechkin step. |
| Stechkin pair inequality | [`stechkin_alg`, `Phi_stechkin`, `stechkin_xi`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFree.lean#L30) | Specialize to the paper's variable \(\sigma_0=(1+\sqrt{8\sigma^2-4\sigma+1})/2\), \(\kappa=(2\sigma-1)/(2\sigma_0-1)\). Prove its elementary parameter bounds and the distinguished-zero sharpening described below. Existing wrappers instead fix \(\sigma_0=1.6181\). |
| Cosine polynomial | [`trig_poly_nonneg`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L147) proves the different coefficients \((18,30,17,6,1)\) | Prove the exact RS75 factorization \(P(\theta)=8(0.9126+\cos\theta)^2(0.2766+\cos\theta)^2\), its coefficients and their nonnegativity. The exact factorization and coefficient positivity are now freshly checked in [`RS75Polynomial.lean`](../RSBounds/RS75Polynomial.lean); this does not yet prove the zero-free theorem. |
| Positivity of the Stechkin difference | [`hasSum_re_vM`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L140), `vM_positivity` | Apply polynomial positivity to \(-\Re\zeta'/\zeta(\sigma+ikt)+\kappa\Re\zeta'/\zeta(\sigma_0+ikt)\). Existing `vM_positivity` handles only the first term; existing `vM_term_le` subsequently pays a coarse error at every frequency. A general weighted-difference lemma is still needed. |
| Gamma contribution | [`Digamma.digamma_eq_integral`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/Digamma.lean#L259), recurrences, [`re_vM_eq`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L192) | The explicit \(O(t^{-2})\) remainder is checked in `BacklundGammaModulus.abs_digamma_re_sub_log_le`; its two-point combination remains to be checked. Existing `half_re_digamma_half_le` has an additive `0.36`; `re_digamma_sub_le` retains a nonvanishing constant. These are not the paper's sharp estimate. |
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
The parameter identities and the reflected-pair payment are now proved in
`RS75Parameters.lean`; their final application to the xi inequality remains
a separate assembly step.

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

The paper's proof of (1.17) uses a lower bound on the first zero's ordinate.
`FiniteRH 1894439` alone does not encode it. This issue is now discharged
unconditionally by `RS75XiIncrement.xi_zero_height_lower`, using the existing
complete height-100 certificate.

The remaining analytic work includes the golden-ratio real-axis estimates
and their connection to the frequency and polynomial inequalities, followed
by the final scalar and finite-height assembly. The optimized polynomial,
real-axis increments, and elementary Stechkin parameters are checked.
Outstanding obligations are not hidden behind new axioms.

The Gauss-series representation for digamma is now reused directly from
IEANTN's proved `GammaAsymptotics.v2` solution. Its eight proof modules compile
unchanged apart from imports on the present toolchain, and their exported
results pass the transitive axiom audit. See [the port record](IEANTNGammaPort.md).
This representation has already supplied the checked real-axis Gamma
increment and the quantitative vertical digamma remainder. Their use in the
full RS75 zero-free argument is tracked above.
