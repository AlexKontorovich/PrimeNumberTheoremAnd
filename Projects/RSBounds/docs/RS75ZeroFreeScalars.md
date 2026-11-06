# The RS75 zero-free scalar assembly

**Verification status: freshly compiled; all 16 public transitive axiom audits
passed using only `propext`, `Classical.choice`, and `Quot.sound`.**
The [completed verification record](../verification/rs75-zero-free-scalars-final-run.json)
binds the exact source and the reused base/numeric objects to this check.
The separate elementary [parameter module](../RSBounds/RS75Parameters.lean)
has already compiled and passed 21 transitive axiom audits.

The main interface is
[`RS75ZeroFreeScalars.lean`](../RSBounds/RS75ZeroFreeScalars.lean), in namespace
`TernaryGoldbach.RSBounds.RS75ZeroFreeScalars`. It proves the
following statements about actual real expressions, without scalar hypotheses:

| API | Statement |
|---|---|
| `R1_upper` | The exact radical expression \(R_1<9.645908801\) |
| `v_lower`, `v_upper` | \(0.339<v<0.34\), for the exact radical choice of \(v\) |
| `chosen_x_bounds` | \(0<v/\log(t/17)<0.029172\) for \(t\ge1894439\) |
| `D_lower` | \(\sum_{k=1}^4 a_k\log(2\pi/k)>52.38865\) |
| `H_upper` | \(\sum_{k=1}^4 a_k/k^2<22.584\) |
| `gamma_lower` | The previously proved \(\gamma\ge0.5772156646\) enclosure |
| `frequency_tail_lt` | \(15H/t^2<10^{-10}\) for \(t\ge1894439\) |
| `rawResidual_le` | The actual variable-kappa/Euler residual is bounded by the cubic-substitution polynomial |
| `chosen_residual_lt` | At \(x=v/\log(t/17)\), the actual residual plus \(15H/t^2\) is strictly below \(-0.0009\) |

Here \(a_0,a_1,\ldots,a_4\) are the exact RS75 cosine-polynomial coefficients,
\(A_0=\sum_{k=1}^4a_k\), and

\[
k_0=1/\sqrt5,\qquad h=(1-k_0)A_0/2,
\]
\[
v=\frac{2\sqrt{a_0}(\sqrt{a_1}-\sqrt{a_0})}{(1-k_0)A_0},\qquad
R_1=\frac{(1-k_0)A_0}{2(\sqrt{a_1}-\sqrt{a_0})^2}.
\]

The scalar theorem concerns the exact choices above; rounded substitutes are
used only as proved interval bounds. The interval generator produces
[103 expression nodes and nine certificates](../RSBounds/RS75ZeroFreeNumerics.lean).
Its output is rechecked by the ordinary Lean kernel, using `decide +kernel`.
The [small square-root extension](../RSBounds/RS75ScalarNumericsBase.lean)
reuses the existing `Bounds` arithmetic soundness and `LogCert` logarithm
certificates. A root enclosure is accepted only after its rational endpoints
are nonnegative and their squares bracket the radicand. There is no numerical
oracle, custom axiom, or native-decision axiom in this design.

The residual uses the actual `RS75Parameters.kappa (1+x)` and Mathlib's actual
Euler–Mascheroni constant. Replacing kappa by the checked cubic lower bound has
the right direction because its coefficient is proved negative. The previously
proved gamma enclosure is imported from `SmallTotientProduct.gamma_bounds`.
The five polynomial coefficient bounds then give the final rational margin.
See the [derivation and exact-rational diagnostic](RS75ResidualAudit.md) for the
formula and its arithmetic organization.

These scalar results do **not** prove the zeta bounds that feed the residual.
The analytic estimates to combine with it are the near-pole estimate with slope 0.2,
the golden-ratio value/derivative estimates giving
\(\zeta'/\zeta(\sigma_0)<-1.1398+3.3606x\), the frequency estimate with remainder
\(15/t^2\), and their Stechkin/positivity assembly. The final zero-free theorem
also needs the finite-RH handoff. The exact optimized-parameter algebra is
separately checked in
[`RS75ZeroFreeOptimization`](../RSBounds/RS75ZeroFreeOptimization.lean), with
[eight standard-axiom audits](../verification/rs75-zero-free-optimization-run.json).
No such analytic obligation is a hidden hypothesis of the scalar statements.

Primary source: [Rosser–Schoenfeld (1975), §1, Lemma 2 and Theorem 1](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
This assembly uses the sharper cubic kappa bound proved here to accommodate
weaker real-axis constants than those in the paper.

The completed analytic interface separates an **unconditional high-height theorem**
for \(|t|\ge1894439\) from the full \(|t|\ge21\) theorem, which uses
`FiniteRH 1894439` only in the closed finite-height handoff. Neither complete
zero-free theorem is asserted by this scalar module; both are now proved in
[`RS75ZeroFree1975`](../RSBounds/RS75ZeroFree1975.lean).

The optimization module proves `h_mul_v`, `v_mul_R1`, and the exact identity

\[
(a_0/v+h)(v+1/R_1)=a_1.
\]

Its `beta_lt_of_optimized_inequality` theorem takes only \(w>0\),
\(\beta\le1\), and the displayed optimized scalar inequality
\(a_1/(1+v/w-\beta)<(a_0/v+h)w\), and concludes
\(\beta<1-1/(R_1w)\). The actual zeta argument now establishes that inequality
in `RS75ZeroFree1975.xi_zero_re_lt_pos`.
