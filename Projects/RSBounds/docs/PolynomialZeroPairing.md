# Finite zero pairing for the quartic formula

`RSBounds/PolynomialZeroPairing.lean` works with the actual rectangle zeros
`zerosRectD zetaF T` and their actual analytic multiplicities. It supplies the
finite pairing step needed between the quartic explicit formula and the
positive-ordinate weighted zero estimates.

The main high-zero bound is

\[
\left\|\sum_{\substack{\rho\in\mathrm{zerosRectD}(T)\\A<|\Im\rho|}}
 m_\rho K(\rho)\right\|
\le C(x+1)\sum_{\substack{0<\Im\rho\le T\\A<\Im\rho}}
 \frac{m_\rho}{(\Im\rho)^5},
\]

provided `T` is positive and a good height, `x ≥ 1`, `C ≥ 0`, and the
coefficient satisfies `‖K ρ‖ ≤ C x^(Re ρ) / |Im ρ|^5` on these zeros.
Conjugation gives twice the positive-ordinate sum. Reflection
`ρ ↦ 1 − conj ρ` preserves that positive finite set and its multiplicities.
The elementary inequality
`x^β + x^(1−β) ≤ x+1`, for `0 ≤ β ≤ 1` and `x ≥ 1`, then gives the
factor `x+1`. The strip and multiplicity facts are proved properties of the
actual zeta zeros; they are not additional assumptions.

For `C = R4 δ / δ^4`, the two last exports apply this result directly to
`PolynomialAveraged.zeroCoefficient x (δ*x) ρ` and
`PolynomialAveraged.zeroCoefficient (x−4*(δ*x)) (δ*x) ρ`.
After division by `x`, the high-zero factor is `1+1/x`.

The low-zero bridge controls the norm of the actual finite sum on
`|Im ρ| ≤ A` by twice the sum of coefficient norms over
`closedPositiveZeros A`, retaining analytic multiplicities exactly. It needs
`0 < A < T` and conjugation invariance of the coefficient norm. It does not
need a good-height hypothesis at `A` or `T`.

| Export | Content |
|---|---|
| `sum_eq_two_sum_positive` | Generic conjugation-invariant finite real sum |
| `sum_ordinate_weight_eq_two` | Arbitrary ordinate weights with multiplicities |
| `sum_norm_low_eq_two_closed` | Exact low-cutoff norm-sum identity |
| `norm_low_sum_le_two_closed` | Triangle-inequality version for a complex sum |
| `rpow_pair_le` | Elementary critical-strip power inequality |
| `sum_rpow_ordinate_weight_le` | General nonnegative ordinate weight and reflection |
| `sum_rpow_high_le_weightedSum` | Fifth-power high-zero weight in the inclusive count convention |
| `norm_zeroCoefficient_upper_le_high` | Actual upper coefficient pointwise estimate |
| `norm_zeroCoefficient_lower_le_high` | Actual lower coefficient pointwise estimate |
| `norm_high_sum_le_of_bound` | Generic complex-coefficient high-sum estimate |
| `norm_high_sum_upper_le` | Actual upper quartic high-sum estimate |
| `norm_high_sum_lower_le` | Actual lower quartic high-sum estimate |

This module uses no RH hypothesis, quantitative zero-free region, simplicity
hypothesis, or assumed symmetry. It does not itself prove the finite low-zero
bound under finite RH or the final psi table row.

The module compiled successfully, and all twelve public theorem audits use
only `propext`, `Classical.choice`, and `Quot.sound`. Verification is recorded in `verification/polynomial-zero-pairing-run.json`,
with build and axiom logs alongside it. The intended check uses direct Lean
against existing checked object files, without rebuilding numerical zero
certificates. There is no separate native Comparator for this module.
