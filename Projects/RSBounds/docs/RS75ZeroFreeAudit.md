# RS75 zero-free region: proved theorem and dependencies

The public theorem
[RS75ZeroFree1975.zero_free](../RSBounds/RS75ZeroFree1975.lean) proves

\[
\operatorname{FiniteRH}(1894439),\quad |t|\ge21,\quad
\sigma\ge1-\frac1{9.645908801\log(|t|/17)}
\quad\Longrightarrow\quad \zeta(\sigma+it)\ne0.
\]

FiniteRH A means that every actual zero of Mathlib's Riemann zeta function
in the open critical strip with absolute ordinate at most A has real part
1/2. There is no additional count, low-zero, numerical, or analytic-estimate
hypothesis. The zero-free region is closed: zeros are excluded on the
boundary itself as well.

The stronger high-height component **zero_free_high is unconditional**
for absolute ordinate at least 1894439. Its zero form xi_zero_re_lt gives
a strict real-part inequality for every actual xi zero, with no simplicity
assumption. Finite RH is used only on the closed interval from 21 to 1894439.

Primary reference: Rosser–Schoenfeld (1975), Theorem 1 and its proof,
[DOI 10.1090/S0025-5718-1975-0457373-7](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
The paper's finite verification height is A = 1894438.51224.... The
formal hypothesis uses the integer height 1894439 > A, so it assumes
slightly more than the verification the paper relied on. This is immaterial
in practice, since RH has since been verified to far greater heights, but it
is not literally the paper's input.

## Verification status

The final source freshly compiled. All four public transitive axiom audits
passed with only propext, Classical.choice, and Quot.sound:

* analytic_inequality;
* xi_zero_re_lt;
* zero_free_high;
* zero_free.

The exact source hashes, commands, and object hash are in the
[final receipt](../verification/rs75-zero-free-1975-run.json).
See also the [axiom log](../verification/rs75-zero-free-1975-axioms.log)
and [reproduction driver](../verification/run_rs75_zero_free_1975_check.py).
An independent native Comparator replay for this theorem has since passed,
on 6 November 2026, run by Claude inside a bubblewrap process sandbox. It
covered statement and definition matching against
[`comparator/RSZeroFreeChallenge.lean`](../comparator/RSZeroFreeChallenge.lean),
the three-axiom check, and full replay with Lean's default kernel, ending
with `Your solution is okay!`. See the
[independent check](../verification/RS75ZeroFreeIndependentCheck.md). This is
a local check, not an official IEANTN receipt.

## Proof components

| Component | Checked result | Record |
|---|---|---|
| Unchanged upstream Stechkin theory | Actual xi partial fractions, reflected pairing, pair nonnegativity and distinguished-zero contribution | [Reuse guide](RS75StechkinReuse.md) |
| Variable parameters | Variable sigma0 and kappa, reflected-pair payment and cubic lower bound for kappa | [Parameters](../RSBounds/RS75Parameters.lean) |
| Near-pole real-axis bound | Negative real zeta logarithmic derivative less than 1/(sigma-1)-gamma+0.2*(sigma-1), for 1<sigma<1.03 | [Guide](RS75RealAxisLogDerivative.md) |
| Golden-ratio bounds | Actual logarithmic derivative at phi less than -1.1398; actual derivative less than 2.5; shifted bound -1.1398+3.3606*(sigma-1) | [Guide](RS75GoldenRatio.md) |
| Infinite moment tails | Proved summability, convexity, trapezoidal bounds and exact improper integrals, bound to finite certificates | [Guide](RS75MomentTails.md) |
| Cosine polynomial | Exact nonnegative polynomial 8*(0.9126+cos theta)^2*(0.2766+cos theta)^2 | [Polynomial](../RSBounds/RS75Polynomial.lean) |
| Weighted Dirichlet difference | Actual von Mangoldt series and nonnegativity of its five-frequency polynomial combination | [Source](../RSBounds/RS75DirichletPositivity.lean) |
| Vertical Gamma and poles | Frequency bound (1-kappa)/2*log(t/(2*pi))+15/t^2-X(t) for actual logarithmic derivatives | [Guide](RS75Frequency.md) |
| Exact residual | Sole premise t>=1894439; optimized residual less than -0.0009 | [Guide](RS75ZeroFreeScalars.md) |
| Optimization | Exact radical identity and strict zero-boundary implication; R1<9.645908801 | [Source](../RSBounds/RS75ZeroFreeOptimization.lean) |
| Low-height handoff | Boundary strictly above 1/2 for absolute ordinate at least 21; finite RH excludes zeros up to A | [Source](../RSBounds/RS75FiniteHandoff.lean) |

The near-pole estimate uses the already certified complete first-29 zero
table through height 100: its xi increment is at least .03414*(sigma-1),
while the Gamma increment is at most .23391*(sigma-1). Their difference
is .19977<.2. Every xi zero has absolute ordinate greater than 14.13,
proved from the same complete low-height certificate. No assumed first-zero
location is inserted.

The golden-ratio calculation encloses ordinary Dirichlet moments at rational
points 55/34 < phi < 233/144, using 63 finite terms and proved tails from
64 onward. Monotonicity and a derivative bound transfer these finite
calculations to the actual golden ratio and then to sigma0.

## Final inequality and strictness

Let D(t) be the actual Stechkin difference of zeta logarithmic derivatives,
and X(t) the corresponding xi difference. The polynomial yields
sum a_k D(k*t) >= 0. Stechkin gives X(k*t)>=0, with the full
1/(sigma-beta) contribution at the chosen zero's ordinate. The reflected
partner pays for the shifted pair; multiplicities are handled by the upstream
theorem rather than discarded.

With x=sigma-1=v/log(t/17) the checked frequency and real-axis inequalities
reduce to

\[
\frac{a_1}{1+x-\beta}
 < (a_0/v+h)\log(t/17).
\]

The exact identity (a0/v+h)*(v+1/R1)=a1 gives the strict R1 boundary.
The certified R1<9.645908801 preserves strictness at the stated closed
boundary. Conjugation handles negative ordinates; zeros with real part at
most 1/2 and the zero-free half-plane Re(s)>=1 are handled explicitly.

The formal proof keeps the historical polynomial and final zero-free
constant, while using sufficient weaker intermediate real-axis and Gamma
bounds. A sharper cubic parameter enclosure supplies the remaining numerical
margin. The [residual guide](RS75ResidualAudit.md) records these choices.

## Relation to the completed b=23 psi theorem

The completed [b=23 psi proof](PsiTable1975.md) does **not** import this
quantitative zero-free theorem. Its high-zero tail uses quartic smoothing,
reflection, the ordinary critical strip, and the proved Rosser zero-count
bound. This yields the fixed relative error needed there. The new theorem
is a separate analytic input for estimates whose relative error decreases
with x; it is not an unmentioned assumption of the published psi result.
