# Public finite-height certificate for the Rosser handoff

## Source found; local replay still pending

The current public tree of [teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab),
pinned at `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, contains a complete
height-100 theorem and explicit rational brackets for all 29 zeros. The
99-file non-Mathlib import closure of `RHHeight100.Main100` has been
materialized at `sources/zeta-lab-rh100`. Every file matches its upstream
Git blob hash; `source-manifest.json` additionally records SHA-256 hashes.
These files have **not** been compiled locally against this project's
Mathlib. A source audit is not a kernel replay.

Upstream pins Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Its
[RESULTS.md](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/hunts/rh_height_lean/RESULTS.md)
reports a clean source build and standard-three-axiom audit, plus an
independent `con-ron --verified` replay. The underlying raw logs and
receipts are described there as retained locally rather than published;
we have not inspected those unpublished artifacts. The source build
report covers approximately 2 hours 8 minutes. Its build script gates on
30 GiB free memory, exceeding this workspace's available memory, so the
script cannot simply be run unchanged here.

## Actual declarations

[Main100.lean](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/hunts/rh_height_lean/lean/RHHeight100/Main100.lean)
contains, without theorem hypotheses:

* `RHHeight100.ncount_three_hundred : Zeta23.Ncount 3 100 = 29`.
  This counts zeros of Mathlib's `riemannZeta` with multiplicity,
  `0 < Re rho < 1` and `3 < Im rho <= 100`.
* `RHHeight100.rh_height_hundred`: every such nontrivial zero with
  `0 < Im rho <= 100` has real part `1/2` and
  `analyticOrderAt riemannZeta rho = 1`.
* `RHHeight100.zero_count_hundred`: the set of distinct zeros with
  `0 < Re rho < 1` and `0 < Im rho <= 100` has cardinality 29.

`RHHeight.low_height` excludes zeros with `0 < Im rho <= 3`. The count
comes from an exact folded argument-principle identity, verified
positivity on the horizontal legs at heights 3 and 100, and an integrated
gamma bound. The 29 individual bracket theorems give distinct zeros on
the line. Matching those 29 zeros with the total multiplicity count
establishes completeness and simplicity.

No active `axiom`, `sorry`, or `native_decide` was found in the inspected
closure. Two `axiom` lines in the additive-combination tactic file are
inside a documentation example, not declarations. This textual fact
does not replace the pending transitive axiom audit.

## Brackets and scalar handoff

The complete list of open rational brackets is:

| Index | Lower | Upper |
|---:|---:|---:|
| 1 | 14.13 | 14.14 |
| 2 | 21.02 | 21.03 |
| 3 | 25.01 | 25.02 |
| 4 | 30.42 | 30.43 |
| 5 | 32.93 | 32.94 |
| 6 | 37.58 | 37.59 |
| 7 | 40.91 | 40.92 |
| 8 | 43.32 | 43.33 |
| 9 | 48.00 | 48.01 |
| 10 | 49.77 | 49.78 |
| 11 | 52.97 | 52.98 |
| 12 | 56.44 | 56.45 |
| 13 | 59.34 | 59.35 |
| 14 | 60.83 | 60.84 |
| 15 | 65.11 | 65.12 |
| 16 | 67.075 | 67.085 |
| 17 | 69.54 | 69.55 |
| 18 | 72.06 | 72.07 |
| 19 | 75.70 | 75.71 |
| 20 | 77.14 | 77.15 |
| 21 | 79.33 | 79.34 |
| 22 | 82.91 | 82.92 |
| 23 | 84.73 | 84.74 |
| 24 | 87.42 | 87.43 |
| 25 | 88.80 | 88.81 |
| 26 | 92.49 | 92.50 |
| 27 | 94.65 | 94.66 |
| 28 | 95.865 | 95.875 |
| 29 | 98.83 | 98.84 |

The first bracket is `HardyFirstZero.first_zero_on_line`; brackets 2–10
are `HardyTenZeros.zero_in_*`, and 11–29 are `RHHeight100.zero_in_*`.
Each asserts existence of a zero in that open interval. They are actual
proved declarations in the inspected source, not data placeholders.

Write

\[
 F(t)=\frac{t}{2\pi}\log\frac{t}{2\pi}-\frac{t}{2\pi}+\frac78.
\]

For every bracket `(a_n,b_n)`, the scalar conditions

\[
 n-1<F(a_n),\qquad F(b_n)<n
\]

hold. `scripts/check_low_height_scalar_conditions.py` checks sufficient
**exact rational** inequalities using `3.14 < pi < 22/7` and precisely
the 12-term artanh enclosures already proved as
`SmallTotientProduct.q_bounds`. Its output is
`verification/low-height-scalar-conditions.json`. The smallest certified
margins exceed 0.145 and 0.156 respectively; it also certifies
`28 < F(100) < 30`. These particular scalar checks have not yet been
instantiated in Lean.

Once the imported zero closure has been replayed and the scalar checks
formalized, monotonicity of `F` above `2*pi`, together with completeness
and simplicity, gives `|N(T)-F(T)|<1` for `14.13 <= T <= 100`, including
heights inside the narrow zero brackets. Below the first bracket the
count is zero; `x log x-x >= -1`, and monotonicity above `x=1`, bound
`F` between `-1/8` and a value below 1. Finally the Rosser envelope is
greater than 1 for `T >= 2`. This closes the finite-height part if the
analytic argument is established for `T >= 100`.

The inspected PNT+/gersh sources did not supply an unconditional finite
enumeration; their large-height numerical inputs remain external
assumptions. The bounded current public search did not locate the
user-mentioned forthcoming Lean verification through `10^8`; that is
not evidence that it is unpublished or nonexistent.

## Attribution

The root zeta-lab license is MIT, copyright 2026 Thomas Lince. The
vendored `Zeta23` portion is Apache-2.0 and retains its original notices.
Both license texts and upstream build metadata accompany the local
source snapshot.
