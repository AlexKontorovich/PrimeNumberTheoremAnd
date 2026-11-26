# Backlund's critical-strip estimate

The target is Backlund (1918), equation (56), pp. 363–368:

\[
|\zeta(\sigma+it)|\le
\frac{t^2}{t^2-4}\left(\frac{t}{2\pi}\right)^{(1-\sigma)/2}\log t,
\qquad 0\le\sigma\le1,\ t\ge50.
\]

The local source scan is `sources/backlund1918.pdf`. Its proof normalizes a
completed-zeta expression with a square root of sine, proves the three
boundary estimates (including a genuine finite calculation at height 50),
and applies Phragmén–Lindelöf on an upper half-strip.

The formalization uses the same domain and modulus loss, with the simpler
holomorphic normalizer

\[
\Phi(s)=\frac{\zeta(s)}{\log(-is)}
 \exp\!\left(\frac{s-1}{2}\log\frac{-is}{2\pi}-\frac s2\right).
\]

All logarithms here are evaluated in the right half-plane when `Im s > 1`.
For `s=σ+it`, set

\[
E=\frac{\sigma-1}{4}\log(1+(\sigma/t)^2)
   +\frac t2\arctan(\sigma/t)-\frac\sigma2,
\quad
D=\sqrt{\left(\log t+\tfrac12\log(1+(\sigma/t)^2)\right)^2
             +\arctan(\sigma/t)^2}.
\]

Then the exact modulus correction is `q=exp(E) log(t)/D`:

\[
|\Phi(\sigma+it)|=
\left(\frac{t}{2\pi}\right)^{(\sigma-1)/2}
\frac{|\zeta(\sigma+it)|}{\log t}\,q.
\]

The elementary bounds `x−x³/3≤arctan x≤x`, `log(1+x)≤x` show
`−1/t²≤E≤0` and `log t≤D≤log t+1/t²`, giving
`1−4/t²≤q≤1` for `t≥3`. Thus `|Φ|≤1` recovers exactly the target loss.

`BacklundHalfStrip.norm_le_one` proves the required upper half-strip maximum
principle directly from Mathlib's rectangle maximum modulus principle.
Multiplication by `exp(εs²)` controls the top edge under quadratic growth;
letting `ε→0+` removes this factor. The lower horizontal edge is retained as a
real proof obligation.

The concrete boundary inputs are separated by ownership:

- `BacklundZetaBoundary`: actual second-order Euler–Maclaurin, its regularized
  extension to `Re s>0`, and the right boundary `|ζ|≤log t−0.048`.
- `BacklundFunctionalMultiplier`: exact imaginary-axis multiplier, giving
  `|ζ(it)|≤sqrt(t/(2π)) |ζ(1+it)|`.
- Gamma horizontal estimates: the small error needed to reflect the lower
  half of the bottom edge and obtain uniform growth.
- `BacklundBottomCertificates`: the finite height-50 sum with `N=20`, using
  calr3's existing logarithm walk, Mathlib's complex exponential Taylor bound,
  and rational root certificates. The exploratory margins are not proof
  inputs; all values must pass the kernel checker.

Status: equation (56) is established unconditionally by
`TernaryGoldbach.RSBounds.BacklundStrip.norm_zeta_strip_le`, in
`RSBounds/BacklundStrip.lean`. Its only hypotheses are `0 ≤ σ`, `σ ≤ 1`, and
`50 ≤ t`. There is no RH, zero-count, PNT, or unproved boundary hypothesis.

Both `BacklundHalfStrip.lean` and `BacklundStripNormalizer.lean` passed fresh
Lean compilation, and all nine audited exports use only `propext`,
`Classical.choice`, and `Quot.sound`; see
`verification/backlund-strip-core-run.json` (2026-11-06, 12:13:48 UTC).
After the finite bottom certificate was checked, `BacklundStrip.lean` passed
its own fresh compilation and both public theorem audits with exactly the
same three axioms; see `verification/backlund-strip-run.json` (2026-11-06,
12:24:54 UTC). The source hash is
`db6bea567f2b44eaf08a7e4b988486d374b26ad3bee35e1905381af1cc8ac592`.

The boundary and growth assembly uses the already-proved calr3 theorem
`TernaryGoldbach.Explicit.norm_zetaF_le` for polynomial growth on the right
half of the strip. Functional-equation and Gamma estimates supply the left
half. The actual lower horizontal boundary follows from the verified uniform
estimate `|ζ(σ+50i)| ≤ 3.75` on `1/2 ≤ σ ≤ 1`, and reflection on the remaining
half. The saved `0.048` in the right-edge bound absorbs the Gamma quotient's
small exponential error.

The maximum-principle proof adapts the rectangle/damping argument in Mathlib's
`Mathlib/Analysis/Complex/PhragmenLindelof.lean`, pinned at
`56a005855ea17e0b0958f73ec801ae140b0a1679`; the original copyright is Yury
Kudryashov (2022), Apache 2.0. The source header preserves this attribution.
The elementary normalizer and its explicit correction bounds are new proofs.
