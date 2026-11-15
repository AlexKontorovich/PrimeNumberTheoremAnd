# Elementary correction between the prime product and the Mangoldt sum

Status: **both source checks and all eight transitive axiom audits passed**
on 2026-11-06. The final correction is checked, with only `propext`,
`Classical.choice`, and `Quot.sound` in the axiom footprints. Its source
SHA256 is `8cc94ccee57dfb2d95207509585eed05ab11a10be58013c23270993330c50080`.

The target public theorem is
`MertensProductCorrection.primeProduct_correction_bounds`. For every natural
`n ≥ 100000`, it states

\[
0\le
\log\left(\prod_{p\le n}\frac p{p-1}\right)
-\sum_{d\le n}\frac{\Lambda(d)}{d\log d}
\le\frac{5.6}{\sqrt n\log n}.
\]

The expression uses the existing `Totient.primeProduct` definition and the
literal Mangoldt sum over `Finset.Ioc 0 n`. Thus it can be combined directly
with the already established second Mertens identity and the existing
prime-product-to-totient reduction.

The proof is unconditional and elementary. Put `K = Nat.log p n`. The
finite Taylor sum through exponent `K` is reindexed exactly as the
Mangoldt sum. The omitted logarithmic series is nonnegative and at most

\[
\frac{p^{-(K+1)}}{(K+1)(1-1/p)}.
\]

For `p ≤ y = √n`, the inequalities `p^(K+1)>n`,
`1/(K+1) ≤ log p/log n`, and `p/(p−1)≤2` give the bound
`2 log p/(n log n)`. Summing and applying Mathlib's elementary
`Chebyshev.theta_le_log4_mul_x` yields `2 log4/(y log n)`.

For `y<p≤n`, at least the first prime power is included. The omitted part
is therefore at most `1/(2p(p−1))`. Since `log n≤2 log p`, this is bounded
by `log p/(log n · p(p−1))`. The finite Abel theorem in `PrimeLogTail`
bounds its sum by `2 log4/((y−1)log n)`.

Finally, `y≥316` and `log4≤1.39` imply

\[
\frac{2\log4}{y\log n}
+\frac{2\log4}{(y-1)\log n}
\le\frac{5.6}{y\log n}.
\]

There is no RH, Büthe, Möbius-sum, or PNT assumption, and no passage to an
infinite-height or infinite-endpoint limit. The finite Taylor-tail proof
reuses the elementary argument in `neg_log_le'` from
`calr3/ternary-goldbach@ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`,
`TernaryGoldbach/Prelim/MertensProduct.lean`; that file's conditional
analytic results are not imported.

The replay script is
`verification/run_mertens_product_correction_check.py`. Exact input hashes,
compiler exit status, object hashes, and declaration-level axiom footprints
are recorded in `verification/prime-log-tail-run.json` and
`verification/mertens-product-correction-run.json`.
