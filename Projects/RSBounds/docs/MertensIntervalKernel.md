# Finite-interval Mellin kernel

`RSBounds/MertensIntervalKernel.lean` proves the elementary kernel identities
needed for the finite-interval form of the signed-integral argument in
Rosser–Schoenfeld (1962), §8, before any passage to infinity.

For positive real `a,b`, put

\[
w_{a,b}(u)=\max(1/u-1/b,0)-\max(1/u-1/a,0).
\]

The checked theorem `hasMellin_weight` asserts convergence and the exact
Mellin transform, for `Re(s)>1`:

\[
\int_0^\infty u^{s-1}w_{a,b}(u)\,du
=M_{a,b}(s),\qquad
M_{a,b}(s)=\frac{b^{s-1}-a^{s-1}}{s(s-1)}.
\]

The definition actually uses `M(s)=H(s)/s`, where `H` is the holomorphic
divided difference at `s=1` of `b^(s-1)-a^(s-1)`. This avoids assigning a
spurious pole to the cancelled denominator at one. The source proves that
`H` is entire and that

\[
H(0)=1/a-1/b,\qquad H(1)=\log b-\log a.
\]

It also proves continuity of the weight at every positive argument. No
ordering of `a,b` is needed for these analytic identities. The positive
ordered case is the one used by the prime-sum/integral bridge.

`MertensIntervalDecay.lean` supplies the explicit quadratic decay constant

\[
K=16\bigl(a^{-3/2}+a^{1/2}+b^{-3/2}+b^{1/2}\bigr).
\]

Its `decayTwo_kernel` export is designed for the inverse-square contour
theorem in `QuadraticContourLimit.lean`.

These modules do not assert an infinite signed tail, an Euler-constant
normalization, an estimate on that tail, or either final RS62 inequality.
They use no RH premise, finite-zero computation, zero-free region, or
prime-number theorem.

The core source and ten transitive axiom audits passed in one fresh-source
Lean process; see `verification/mertens-interval-kernel-run.json`. The decay
check has its separate receipt `verification/mertens-interval-decay-run.json`.
Only receipts reporting success establish checked status.

Primary reference: J. Barkley Rosser and Lowell Schoenfeld, *Approximate
formulas for some functions of prime numbers*, Illinois J. Math. 6 (1962),
64–94, §8, <https://doi.org/10.1215/ijm/1255631807>.
