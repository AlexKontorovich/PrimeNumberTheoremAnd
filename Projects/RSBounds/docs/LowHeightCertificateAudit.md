# Public finite-height certificate for the Rosser handoff

## Checked scalar certificates; zero-certificate replay in progress

The current public tree of [teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab),
pinned at `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, contains a complete
height-100 theorem and explicit rational brackets for all 29 zeros. The
99-file non-Mathlib import closure of `RHHeight100.Main100` has been
materialized at `sources/zeta-lab-rh100`. Every file matches its upstream
Git blob hash; `source-manifest.json` additionally records SHA-256 hashes.
This directory preserves the original upstream snapshot. Local replay against
this project's Lean and Mathlib is now in progress from the separate working
copy at `vendor/rh100`. Compatibility edits are recorded, with original and
adapted hashes and patch files, in `verification/rh100-adaptations.json`.
They include explicit imports, namespaces avoiding duplicate PNT+/Mathlib
helper names, and replacement of an obsolete proof-producing tactic API.
The original snapshot is not changed to conceal these adaptations.

`verification/rh100-replay-run.json` records the sequential 99-module replay,
and `verification/rh100-replay/` contains per-module logs and resource data.
At this update the replay is still running: successful intermediate modules
are not a completed replay of `RHHeight100.Main100`, its transitive axiom
audit, or the final finite-height handoff. The independent scalar part of
that handoff is already checked, as detailed below.

Upstream pins Lean `v4.35.0-rc2` and Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Its
[RESULTS.md](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/hunts/rh_height_lean/RESULTS.md)
reports a clean source build and standard-three-axiom audit, plus an
independent `con-ron --verified` replay. The underlying raw logs and
receipts are described there as retained locally rather than published;
we have not inspected those unpublished artifacts. The source build
report covers approximately 2 hours 8 minutes. Its build script gates on
30 GiB free memory, exceeding this workspace's available memory, so the
script cannot simply be run unchanged here. The local replay instead compiles
modules sequentially and records actual memory use; it uses Lean `4.35.0`
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

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

For the Rosser finite-height handoff, the critical-line conclusion is
unnecessary. The relevant output is the certified cumulative zero count,
including multiplicity, together with a complete enumeration and the
ordinate brackets. One could use equally strong cumulative-count
certificates without locating real parts at all. In this available source,
line-zero witnesses and the total multiplicity count provide the needed
enumeration and simplicity; the handoff does not require an independent RH
assumption, at height 100 or at any larger height.

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

are now **proved in Lean**, as is `28 < F(100) < 30`.
`RSBounds/BacklundLowScalarBase.lean` proves a rational certificate checker
sound using Mathlib's `3.14 < pi < 22/7` and the existing twelve-term
artanh enclosures `SmallTotientProduct.q_bounds`.
`RSBounds/BacklundLowScalarData.lean` contains 59 certificates: the two
endpoints of each of the 29 brackets and height 100. Its
`certificates_checked` theorem verifies all rows by `decide +kernel`, and
`certificate_bounds` returns the corresponding strict real inequalities.
The Python generator only chooses rational witnesses; it is not trusted
as a proof of their inequalities.

These modules were freshly compiled on 2026-11-06, with source hashes and
successful exit codes recorded in `verification/backlund-scalar-run.json`.
The associated axiom audit, `verification/backlund-scalar-axioms.log`,
reports only `propext`, `Classical.choice`, and `Quot.sound`. The earlier
Python exploration in `verification/low-height-scalar-conditions.json`
is no longer the sole evidence for these scalar inequalities.

The remaining finite handoff must connect the replayed zero enumeration
and multiplicities to this project's right-closed count
`N(T) = sum_{0 < Im rho <= T} multiplicity(rho)`, and combine it with the
checked scalar inequalities. Monotonicity of `F` above `2*pi` then gives
`|N(T)-F(T)|<1` for `14.13 <= T <= 100`, including zero ordinates and
heights inside the narrow brackets. Below the first bracket the count is
zero; `x log x-x >= -1`, and monotonicity above `x=1`, bound `F` between
`-1/8` and a value below 1. Finally the Rosser envelope is greater than 1
for `T >= 2`. This paragraph describes the remaining mathematical assembly;
it does not assert that the count-convention bridge or full finite theorem
has already passed Lean.

The independent analytic theorem for `T >= 100` is now freshly compiled
and axiom-audited, including heights equal to zero ordinates. Its public
export is `Rosser1941.zero_count_bounds_high` in
`RSBounds/BacklundHighCount.lean`, for the actual zeta zero count defined
by `Rosser1941.positiveZeroCount`. It uses no numerical information about
zeta zeros: its inputs are proved analytic estimates and checked scalar
inequalities. `verification/backlund-high-count-run.json` records the
successful builds and five standard-three-axiom audits, and
`verification/aggregate-backlund-high-run.json` records the successful
root-module build. Combining this checked theorem with the still-pending
finite handoff would give the full range `T >= 2`; the existence of a
source file for that final assembly is not itself a successful build.

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
