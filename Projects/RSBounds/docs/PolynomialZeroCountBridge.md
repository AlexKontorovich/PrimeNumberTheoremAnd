# Polynomial contour zeros and the actual zeta count

[`PolynomialZeroCountBridge.lean`](../RSBounds/PolynomialZeroCountBridge.lean)
has been compiled successfully. All sixteen public declarations passed a
fresh transitive axiom audit with exactly `propext`, `Classical.choice`,
and `Quot.sound`. No theorem assumes RH, simple zeros, a zero-count bound,
or a numerical certificate.

The module connects the finite zero sums in the checked polynomial explicit
formula to the actual zeta zeros and multiplicities used by the proved
Rosser counting theorem. It does not itself bound a weighted zero sum or
prove the psi table entry.

## Objects and endpoint conventions

- `zerosRectD zetaF T` consists of zeros of the entire regularization
  `zetaF`, strictly inside the rectangle with real sides `-1/2` and `3/2`
  and imaginary sides `-T` and `T`. At a zero it agrees with
  `(s-1)*riemannZeta s`.
- `multRectD zetaF T ρ` is the natural multiplicity obtained from the
  analytic divisor on the containing closed ball.
- `positiveZeros T` uses **strict** positive ordinates `0 < Im ρ < T`.
- `closedPositiveZeros D` uses **inclusive** positive ordinates
  `0 < Im ρ ≤ D`.
- `N_le D` sums `(analyticOrderAt riemannZeta ρ).toNat` on
  `closedPositiveZeros D`; multiplicities are retained.

For `0 < D < T`, the inclusive cutoff lies strictly inside the contour,
so no zero-avoidance assumption at `D` or `T` is needed. To identify the
strict and inclusive sets at the *same* height `T`, the module explicitly
requires `zetaGoodHeight T`. It also proves that the heights supplied by the
existing polynomial contour construction satisfy this condition.

## Public API

All declarations are in the namespace
`TernaryGoldbach.RSBounds.PolynomialZeroCountBridge`.

| Declaration | Statement and assumptions |
|---|---|
| `mem_zerosRectD_zetaF_iff_xi` | For `T > 0`, rectangle membership is equivalent to `xiF ρ = 0` and `abs(Im ρ) < T`. |
| `mem_zerosRectD_zetaF_iff` | For `T > 0`, membership is equivalent to `riemannZeta ρ = 0`, `Im ρ ≠ 0`, and `abs(Im ρ) < T`. |
| `analyticOrderAt_zetaF_eq_zeta` | For `ρ ≠ 1`, the regularized and actual zeta analytic orders agree. |
| `multRectD_zetaF_eq_analyticOrder` | For a rectangle member and `T > 0`, the contour's multiplicity equals zeta's analytic order converted to a natural number. |
| `positive_filter_eq` | Filtering rectangle zeros by `0 < Im ρ` gives `positiveZeros T`. |
| `closed_filter_eq` | For `0 < D < T`, filtering by `0 < Im ρ ∧ Im ρ ≤ D` gives `closedPositiveZeros D`. |
| `positiveZeros_eq_closed_of_goodHeight` | At `T > 0` satisfying `zetaGoodHeight T`, the strict and inclusive positive zero sets agree. |
| `positive_filter_eq_closed_of_goodHeight` | The corresponding same-height equality for the positive filter of the polynomial rectangle. |
| `zetaGoodHeight_of_goodHeights` | Every member of a `PolynomialExplicit.GoodHeights zetaF Bz T` sequence is a `zetaGoodHeight`. |
| `sum_multRectD_closed_filter_eq` | For `0 < D < T`, the sum of contour multiplicities in the inclusive positive cutoff equals `N_le D`. |
| `sum_multRectD_closed_filter` | The same conversion for any real weight `w : ℂ → ℝ`, including the multiplicity factor. |
| `conj_mem_zerosRectD` | Conjugation preserves membership in the full symmetric rectangle. |
| `multRectD_conj` | Conjugate rectangle zeros have equal contour multiplicities. |
| `reflect_mem_zerosRectD` | Critical-line reflection `ρ ↦ 1 - conj ρ` preserves rectangle membership. |
| `multRectD_reflect` | Reflected rectangle zeros have equal contour multiplicities. |
| `reflect_mem_closedPositiveZeros` | Critical-line reflection preserves every inclusive positive cutoff. |

Conjugation reverses the ordinate sign; critical-line reflection preserves
the ordinate. The latter therefore preserves `closedPositiveZeros D`.
Neither multiplicity statement assumes that the zeros are simple.

## Proof dependencies

The membership proof reuses upstream `zerosRectD_zetaF_cases` and
`mem_zerosIn_of_zeroD`, together with the already checked xi/zeta zero
equivalence and real-axis nonvanishing from `BacklundCountRealAxis` and
`BacklundCountMultiplicity`. There is no new zero-free-region argument.

The multiplicity conversion uses the local identity
`zetaF s = (s-1)*riemannZeta s`, with the analytic factor `s-1` nonzero
at the point under consideration. The divisor API then identifies the
natural contour multiplicity with the actual analytic order.

Conjugation and reflection multiplicities reuse the already replayed
analytical theorems `Zeta23.analyticOrderAt_zeta_conj` and
`Zeta23.zeta_mult_reflect` from
[`vendor/rh100/Zeta23/ZetaReflect.lean`](../vendor/rh100/Zeta23/ZetaReflect.lean).
These results have no RH or numerical hypotheses. Their transitive proof
dependencies are included in the sixteen audits.

The finite-set formulation is intended for uniform bounds on the finite
zero sums along the existing `GoodHeights` sequence. Once such bounds are
proved, the already checked averaged explicit formula supplies the limit;
this bridge does not require constructing a separate infinite zero series.

## Verification record

The successful commands, run from the project root after sourcing the
workspace Lean environment, were:

```sh
lake build RSBounds.PolynomialZeroCountBridge
lake env lean -j1 verification/PolynomialZeroCountBridgeAudit.lean
```

The first command also refreshed several analytical dependency objects
whose Lake traces were stale or absent. It did not rebuild RH numerical
box certificates, and no pre-existing Lean source was edited. The module
itself passed its first compilation.

- [Build log](../verification/polynomial-zero-count-bridge-build.log)
- [Sixteen-theorem audit source](../verification/PolynomialZeroCountBridgeAudit.lean)
- [Transitive axiom results](../verification/polynomial-zero-count-bridge-axioms.log)
- [Timestamped record and source hashes](../verification/polynomial-zero-count-bridge-run.json)

These are ordinary Lean compilation and axiom-audit results. They do not
assert that a later aggregate or independent Comparator run has already
checked this new module.
