# Public finite-height certificate for the Rosser handoff

## Checked zero-certificate replay and count bridge

The pinned source of [teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab/tree/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534),
commit `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, has now been replayed
locally: **all 99 modules compiled**, and **all 28 final theorem closures**
have only `propext`, `Classical.choice`, and `Quot.sound`. The final audit
completed on 2026-11-06 at 13:00:07 UTC. It pins the conclusions to
Mathlib's actual `riemannZeta`, including completeness, simplicity and the
29 individual ordinate brackets. No numerical certificate literals or
bracket statements were changed.

`RSBounds.BacklundRH100Bridge` was then freshly compiled and all **five**
exported theorem closures were audited, again with exactly the standard
three axioms. It identifies the upstream zero set with this project's
inclusive positive-ordinate count and proves `N_le 100 = 29`, including
analytic multiplicities. The scalar assembly in `BacklundLowCount` has also
compiled and passed all twelve associated axiom audits. Its public theorem
proves the strict error less than one at every `0 <= T <= 100`.
`ZetaZeroTable.first29` packages the complete table for reuse and has passed
its seven export audits. The full Rosser theorem for `T >= 2` has now
compiled, and its five public axiom audits have passed; the independent
Comparator stage remains pending at this update.

The replay uses Lean `4.35.0` and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. Upstream pins Lean
`v4.35.0-rc2` and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
Seven source files needed compatibility adaptations: explicit imports,
isolation of generic PNT+/Hardy-Z helpers to avoid name collisions, a
rational-identity normalization, and replacement of an obsolete
proof-producing tactic API. Original and adapted hashes and exact unified
patches are in `verification/rh100-adaptations.json`. The original working
snapshot remains unchanged at `../sources/zeta-lab-rh100`.

The portable published sources are under `vendor/rh100`, together with the
original source manifest, licenses, and upstream version pins. The six
library roots are registered in `lakefile.lean`; their globs cover exactly
the checked 99 modules. No duplicate raw snapshot or compiled objects are
required for publication. The replay runner uses the preserved external
snapshot for additional source-hash checks when available; without it,
the runner records its absence and freshly checks the vendored Lean proofs.

Verification evidence:

| Artifact | Content |
|---|---|
| `verification/rh100-replay-run.json` | Complete 99-module ledger, source/dependency/output hashes, commands and successful final audit |
| `verification/rh100-replay/receipts/` | Individual validated receipts for all 99 modules |
| `verification/rh100-replay/CheckMain100.log` | All 28 transitive axiom reports |
| `verification/rh100-replay-slot-{b,c,d,e,f}.json` | Independent worker records for selected box modules |
| `verification/backlund-rh100-bridge-run.json` | Fresh count-bridge build and five successful audits |
| `verification/backlund-rh100-bridge-axioms.log` | Standard-three-axiom reports for every bridge export |

The default runner is sequential. Selected independent box modules were
also checked by workers using exclusive per-module locks and atomic
receipts; the main ledger validated every reused source, dependency and
object hash. The largest observed per-process peak RSS was 4,363,908 KiB.
The upstream build script's 30-GiB memory gate was not used. A receipt
alone is never accepted as a proof cache: a matching local compiled object
must also be present, otherwise the module is compiled again.

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

The completed transitive axiom audit, rather than a textual source scan,
is the evidence that the final theorem closures contain no additional
axioms or admissions. All 28 reported closures use only the standard
three axioms.

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

The count-convention bridge is already checked. Its exports in
`TernaryGoldbach.RSBounds.BacklundCountIdentity` are:

| Theorem | Conclusion |
|---|---|
| `coe_closedPositiveZeros_eq_stripZerosUpTo` | Exact equality of this project's finite zero set and the upstream strip-zero set |
| `zero_simple_below_hundred` | Every actual zeta zero with `0 < Im rho <= 100` lies on the line and has analytic order one |
| `closed_count_eq_card` | Multiplicity count equals distinct-zero cardinality for `0 < T <= 100` |
| `closed_count_hundred` | `N_le 100 = 29` |

No strip-location hypothesis is left on the simplicity conclusion:
`zeta_zero_re_strip` proves the required strip restriction for every
nonreal zeta zero using the already checked xi bridge.

The completed finite handoff combines these checked results with the
29 brackets, the checked scalar inequalities, and monotonicity of `F`.
Its public result is `Rosser1941.zero_count_error_lt_one_to_100`, asserting
`|N(T)-F(T)| < 1` for `0 <= T <= 100`, including zero ordinates and the
continuous-extension value at zero. Fresh compilation and all twelve
associated axiom audits passed; see
`verification/backlund-low-count-run.json`. The Rosser envelope is greater
than one for `T >= 2`, so this finite bound supplies the lower range of the
full Rosser theorem. The reusable table and its seven successful audits are
documented in [CertifiedZeroTable.md](CertifiedZeroTable.md).

The independent analytic theorem for `T >= 100` is now freshly compiled
and axiom-audited, including heights equal to zero ordinates. Its public
export is `Rosser1941.zero_count_bounds_high` in
`RSBounds/BacklundHighCount.lean`, for the actual zeta zero count defined
by `Rosser1941.positiveZeroCount`. It uses no numerical information about
zeta zeros: its inputs are proved analytic estimates and checked scalar
inequalities. `verification/backlund-high-count-run.json` records the
successful builds and five standard-three-axiom audits, and
`verification/aggregate-backlund-high-run.json` records the successful
root-module build. The combined public theorem
`Rosser1941.zero_count_bounds`, in `RSBounds/Rosser1941.lean`, has now
compiled with the full range `T >= 2` and no additional premise. Its five
public axiom audits passed with only the standard three axioms. The
successful build and audits are recorded in `verification/zero-count-run.json`;
the independent Comparator stage in that same run is still pending at this
update. The earlier joint-import namespace collision was resolved by
isolating local gamma helper names, without changing certificate literals
or mathematical statements.

The inspected PNT+/gersh sources did not supply an unconditional finite
enumeration; their large-height numerical inputs remain external
assumptions. The bounded current public search did not locate the
user-mentioned forthcoming Lean verification through `10^8`; that is
not evidence that it is unpublished or nonexistent.


## Separate reusable target through height 280

Rosser (1941), Theorem 17, p. 223, states the stronger finite-range result
`abs(N(T)-F(T)) < 1` for `0 <= T <= 280`, using the same inclusive upper
endpoint convention. The actual printed page was inspected, not merely
its OCR. At zero, `F(0)=7/8` is understood by continuous extension, which
agrees with the Lean expression. Rosser attributes the computation to
J. I. Hutchinson, *On the roots of the Riemann zeta function*, Transactions
of the AMS 27 (1925), pp. 49–60. Theorem 18 is a different result: an error
less than 2 through `A` defined by `F(A)=1041`, with
`A = 1467.47747...`, together with a complete count and critical-line
verification there.

This sharper finite theorem is independently useful. Chirre–Helfgott,
[*Optimal bounds for sums of non-negative arithmetic functions*,
arXiv:2512.15709v1](https://arxiv.org/pdf/2512.15709), Appendix B, Lemma B.1,
p. 43, uses the error less than 1 through 280. Corollary B.3 uses it to
bound counts in short ordinate intervals, including intervals reaching
below height 1. The separate bound `abs(N(t)-F(t)) <= (1/5)*log(t)+2` in
that lemma also uses a finite computation through 5400; the height-280
result alone does not supply that second assertion.

The height-280 theorem is **not part of the presently checked finite
certificate**. Exploratory floating-point computation locates 126 zeros
below 280, with the 126th near `279.2292509277` and the 127th near
`282.4651147651`. A formal extension of the current approach would need a
complete count through 280 and 126 disjoint ordinate brackets, then 253
scalar certificates (two endpoints per bracket and height 280). These
exploratory zero values are not proof evidence. Critical-line location is
still unnecessary for the resulting counting theorem.

There is a concrete scalar-precision issue to address before extending
the certificate list. The current `MainCert.Valid` checker deliberately
weakens the available pi bounds to `3.14 < pi < 22/7`. Even with exact
logarithms, its lower envelope at `t=279.229` is approximately
`124.940886`, too small to certify `125 < F(t)`, although the actual value
is approximately `125.049143`. More rows in the unchanged checker cannot
fix that loss.

A small improvement is sufficient in this example: use the existing
Mathlib theorems `Real.pi_gt_d4` and `Real.pi_lt_d4` directly, giving
`3.1415 < pi < 3.1416`. At the lower bracket endpoint `279.22`, the same
scalar lower envelope is then approximately `125.041900`. Thus no new
pi computation is needed. A separate finer checker would preserve the
already checked 59-row artifact; its complete extended list must still
be generated and kernel-checked. The decimal evaluations in this
paragraph diagnose certificate precision only and are not formal claims
that all 253 prospective rows already succeed.

## Attribution

The root zeta-lab license is MIT, copyright 2026 Thomas Lince. The
vendored `Zeta23` portion is Apache-2.0 and retains its original notices.
Both license texts and the upstream toolchain, Mathlib manifest and source
manifest are included in the portable `vendor/rh100` directory. The seven
exact adaptation patches are included under `verification/rh100-replay`.
