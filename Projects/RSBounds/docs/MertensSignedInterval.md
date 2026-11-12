# Finite-interval foundation for the RS62 signed tails

This work targets the common signed-integral input behind Rosser and Schoenfeld
(1962), Section 8, Lemmas 7 and 8. It does not assume a prime-number estimate or
finite RH. It is the unconditional foundation of the now checked
[full-range Mertens/totient derivations](RS62Global.md), which retain their
separate finite-RH premise.

## Checked arithmetic checkpoint

`RSBounds/MertensIntervalSum.lean` proves, for `1 ≤ a ≤ b`,

\[
\sum_{n\ge0}\Lambda(n)
 \left(\max\{1/n-1/b,0\}-\max\{1/n-1/a,0\}\right)
 =\int_a^b\frac{\psi(t)}{t^2}\,dt.
\]

The value of the weight at `n=0` is immaterial because `Λ 0=0`. The proof first
reduces each ramp to its finite support, then reuses the exact Abel identities
from `RSBounds/Mertens.lean`. The centered version subtracts exactly
`log b - log a`.

The fresh source check and seven transitive axiom audits passed; every audited
declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

- Source SHA-256: `65d702fb141e34d19d7c27c563a08d594e39eb1d894d819b8a1daca54cf61d9b`.
- Receipt: `verification/mertens-interval-sum-run.json`.
- Exact audit commands: `verification/MertensIntervalSumAudit.lean`.
- Reproduction: source `../lean-env.sh` from the project root, then run
  `python verification/run_mertens_interval_sum_check.py`.

## Checked analytic construction

The finite-interval numerator

\[
F_{a,b}(s)=b^{s-1}-a^{s-1}
\]

vanishes at `s=1`. Its entire divided difference
`H = dslope F 1` gives the kernel `M(s)=H(s)/s`; away from `0,1`,

\[
M(s)=\frac{b^{s-1}-a^{s-1}}{s(s-1)}.
\]

The right-line Mellin transform, inverse-square contour limit, subtraction of
the pole at one, and final assembly are now proved in new modules. For
`1 ≤ a ≤ b`, `MertensSignedInterval.explicit_formula` proves the existence of
unconditional good heights `T_k ∈ [k+1,k+2]` such that

\[
\lim_k\sum_{\rho\in Z(T_k)}m_\rho
\frac{b^{\rho-1}-a^{\rho-1}}{\rho(\rho-1)}
=-\int_a^b\frac{\psi(t)-t}{t^2}\,dt
 -L(a,b)-\log(2\pi)(1/a-1/b).
\]

Here `Z(T)` is the existing actual rectangle-zero set, `mρ` is its actual
analytic multiplicity, and `L(a,b)` is the explicit normalized integral on
`Re s = -1/2`. Its integrability is also proved. The exact formula makes no
finite-RH, Euler-normalization, or limiting-tail assumption.

The new modules and their standard-three transitive axiom audit counts are:

| Module | Audited declarations |
|---|---:|
| `MertensIntervalSum` | 7 |
| `MertensIntervalKernel` | 10 |
| `MertensIntervalDecay` | 6 |
| `QuadraticContourLimit` | 9 |
| `QuadraticSubOne` | 7 |
| `MertensIntervalMellin` | 3 |
| `MertensSignedInterval` | 4 |

Final assembly receipt: `verification/mertens-signed-interval-run.json`.
Reproduce it with `python verification/run_mertens_signed_interval_check.py`
after sourcing `../lean-env.sh`.

The left remainder now has the checked bound
`‖L(a,b)‖ ≤ 6000 (a^(-3/2) + b^(-3/2))` in
`MertensIntervalLeftBound` (eight standard-three audits). The separate
`MertensCenteredNormalization.centered_limit_eq` theorem also identifies any
limit of `D(x)=E₁Λ(x)-ψ(x)/x` as `-γ-1`, using its proved Mellin transform.
Neither result assumes finite RH or a pointwise PNT.

`MertensEndpointLeft` now also proves `L(a,b)=F(b)-F(a)`,
`‖F(c)‖≤6000 c^(-3/2)`, and `F(c)→0` (ten standard-three audits).
`MertensZeroPotential` now proves absolute convergence of the actual
multiplicity-weighted degree-two series, its decay at infinity, and its
rectangle-sum limit (17 standard-three audits; see `MertensZeroPotential.md`).
`MertensSignedLimit` now also proves existence and the exact zero-potential
formula for the improper signed tail (five standard-three audits; see
`MertensSignedLimit.md`). The Euler-normalized first-Mertens identity is in
its separate assembly check; the numerical RS62 goals still require their
quantitative estimates and final range handoffs. The original
RS62 numerical inequalities are not proved by the finite-interval formula
alone. Any later corollary using finite RH must keep it visible; the original
RS62 target is unconditional.

Source: J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois J. Math. **6** (1962), 64–94,
[doi:10.1215/ijm/1255631807](https://doi.org/10.1215/ijm/1255631807).

Final assembly source SHA-256: `7782ac59b035f6db7b43fcbae0806c1ff647e74d36e5a91384c76c67a2d2b9df`.
