# Backlund center: exact bound and numerical discrepancy

The exact Euler-product comparison for `sigma > 1` is

\[
 \frac{\zeta(2\sigma)}{\zeta(\sigma)}
 \le |\zeta(\sigma+it)|.
\]

At each prime, writing `a = p^(-sigma)` and `z = p^(-sigma-it)`,
the inequality follows from `|1-z| <= 1+a` and
`1-a^2 = (1-a)(1+a)`. The convergent Euler products preserve the
inequality. `RSBounds/BacklundCenter.lean` implements this argument using
Mathlib's `riemannZeta_eulerProduct_hasProd`, and specializes it to
`sigma = 5/4`. The numerical ratio is not introduced as an assumption.

Both declarations were freshly compiled and axiom-audited on
2026-11-06. Each uses only `propext`, `Classical.choice`, and `Quot.sound`.
The exact source hash and logs are recorded in
`verification/backlund-center-run.json`.

## Numerical bound now proved in Lean

`RSBounds/BacklundCenterNumerics.lean` now proves both

\[
 3.425 < \frac{\zeta(5/4)}{\zeta(5/2)} < 3.426,
 \qquad
 \frac1{3.426}\le|\zeta(5/4+it)|\quad(t\in\mathbb R).
\]

The Lean proof uses 625 terms of each Dirichlet series and the integral
test. `BacklundCenterNumericsBase.lean` proves the real series identity,
both infinite-tail bounds, and the soundness of integer root enclosures.
`BacklundCenterNumericsData.lean` contains 1,250 generated term bounds;
every bound is checked with `decide +kernel`. No `native_decide`, custom
axiom, external numerical input, or `sorry` is used.

The resulting bounds before division are

\[
 4.59486862\le\zeta(5/4)\le4.59527487,
 \quad
 1.34144158\le\zeta(5/2)
 \le1.34144783+\frac2{46875}.
\]

These deliberately modest enclosures suffice to separate the two
three-decimal constants. The upper numerator tail at 625 is exactly
`4/5`; its lower tail is bounded by `4 * 0.1999`. The denominator upper
tail is `2/46875`, and its lower tail is bounded by zero.

The generator is `scripts/gen_backlund_center_numerics.py`. The fresh
sequential compilation and eight axiom audits are reproduced by
`verification/run_backlund_center_numerics_check.py`; the run record is
`verification/backlund-center-numerics-run.json`.

## Printed constant

[Rosser (1941), Theorem 19, p. 224](https://doi.org/10.2307/2371291)
prints `|zeta(5/4 + iT)| >= 1/3.425` and cites his reference (5), p. 26.
The page was inspected directly in the
[issue scan](https://archive.org/details/sim_american-journal-of-mathematics_1941-01_63_1).
The decimal `3.425` is in the scan; it is not an OCR transcription.

The exact Euler-product ratio is **larger** than `3.425`.
The independently reproducible rational computation
`verification/check_backlund_center_rational.py` proves the enclosure

\[
 3.425382 < \frac{\zeta(5/4)}{\zeta(5/2)} < 3.425390.
\]

Thus the Euler-product argument supports `1/3.426`; it does not support
the printed `1/3.425`. This audit establishes a discrepancy between that
printed constant and the exact Euler-product route. It does not by itself
assert a counterexample to Rosser's displayed inequality at a specified
height, or a failure of his final zero-count theorem.

The earlier, tighter independent rational computation is **not a Lean proof**.
The separate Lean proof above supplies all numerical facts needed for
the denominator `3.426`. The independent computation sums 10,000 terms
of each positive Dirichlet series and bounds the tails between their
integrals from `N+1` and `N`. Every term and endpoint power is enclosed
using exact integer square/fourth roots at denominator `2^80`; all
subsequent arithmetic uses rational numbers. Its machine-readable output
is `verification/backlund-center-rational.json`.

Replacing the printed denominator by `3.426` increases the center
contribution in Rosser's displayed Jensen bound by

\[
 \frac{\log(3.426/3.425)}{2\log(1.76)}
 \approx 0.00025820012.
\]

This increment must be accounted for when deriving the final rounded
zero-count constant; it should not be silently discarded.

## Reuse audit

The inspected gersh source pinned at
`27df23af6a712895f22204d0d81102baa74f0ebe`,
`ZetaInterlacingAssembly.lean`, proves only
`riemannZeta_norm_lower_five_fourths : 1/8 <= |zeta(s)|`
when `Re(s) >= 5/4`. It then uses center denominator `8`.
No proof of the numerical denominator `3.425` or `3.426` was found in the
locally audited files. Mathlib supplies the exact convergent Euler product,
which suffices for the short symbolic comparison above.
