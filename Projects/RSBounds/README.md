# Explicit Rosser–Schoenfeld estimates: partial formalization

This standalone Lean 4.35 project contains checked progress toward explicit
Rosser–Schoenfeld estimates. **The four requested global estimates are not yet
proved.**

| Result | Freshly checked status |
| --- | --- |
| RS62 totient coefficient 2.50637 for at most twenty distinct prime factors | Proved |
| Its corollary for 3 ≤ q ≤ 10^27 | Proved |
| Exact finite-anchor Abel identities for weighted prime and von Mangoldt sums | Proved |
| Finite weighted zero-sum partial summation and envelope transfers | Proved; the actual zeta zero-count bound remains an input |
| Backlund's phase-aligned subsequence for powers of a nonzero complex number | Proved |
| Quartic kernel bounds, fourth-difference identities, and the upper/lower psi sandwich | Proved |
| Mellin transform of the truncated quartic, with its exact five-factor denominator | Proved for Re(s) > 0 |
| Fourfold integral identity and low/high bounds for an individual zero's quartic contribution | Proved |
| Finite rectangular residue identity, including the quartic kernel's pole at zero | Proved |
| Prime-sum Mellin inversion using only hypotheses on the right vertical line | Proved |
| Fourfold integrated explicit formula for the actual finite sum Psi4, using one common sequence of rectangle heights | Proved, with the left vertical remainder explicit |
| Upper and lower averaged explicit formulas, including the exact main terms and constant at zero | Proved, with the left remainders explicit |
| Logarithmic bound for zeta'/zeta on Re(s) = -1/2 | Proved; integration of the remainder bound remains unfinished |
| Lower kernel bounds and a sharper cancellation bound for both smoothing signs on a finite ordinate band | Proved; does not certify the total numerical row |
| RS75 Theorem 1: zero-free region with R = 9.645908801 and log(abs(t)/17) | Separate target; not proved |
| RS75's exact degree-four cosine polynomial and its nonnegativity | Proved |
| Scalar reduction from stated RS62 analytic inputs to the totient product bound | Proved as an implication; those inputs remain unproved |
| Moderate-error psi row b = 23; full RS62 Mertens/totient bounds; requested theta estimate | Unfinished |

The totient results assume neither RH, Buethe nor Ramare's sum estimate.
The finite arithmetic through the twentieth prime, 71, is checked by the
ordinary Lean kernel. The checked theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

## The b = 23 proof

The chosen method is RS75's **four integrations**, equivalently a degree-four
truncated-power smoothing. The threshold remains `exp 23`.

`Psi4(y) = (1/24) sum_n Lambda(n) max(y-n,0)^4`.

Normalized fourth differences at x and x−4h give upper and lower smoothings
of psi(x), with main terms x+2h and x−2h. The zero contribution has denominator
`rho*(rho+1)*(rho+2)*(rho+3)*(rho+4)`. The parameters remain `m = 4`,
`delta = 0.0000211`, with finite RH through 1894439. The polynomial smoothing
and its finite psi comparisons are checked, as are the bounds for an individual
zero's contribution, for both smoothing signs. The contour is an ordinary fixed rectangle with vertical
sides at Re(s) = -1/2 and Re(s) = 3/2; no quantitative zero-free boundary is
used for it. The integrated formula is now checked, with the residue at zero
evaluated and the left vertical remainder retained. Quantitative estimates for
that remainder and the zero sums remain to be completed. See
[the exact formula and its remaining inputs](docs/QuarticProof.md).

RS75's zero-free region is now a separate target in `RSBounds/Targets.lean`:
assuming the finite RH verification through 1894439, zeta has no zeros where
`abs(t) >= 21` and `sigma >= 1 - 1/(9.645908801 * log(abs(t)/17))`.
This is Theorem 1 of RS75, whose proof uses the finite verification. Its use
in the high-zero tail is distinct from the ordinary contour calculation.
The zero-free theorem itself remains unproved here. Its exact trigonometric
polynomial is checked in `RS75Polynomial.lean`; the remaining analytic inputs
are tracked separately in [the zero-free-region audit](docs/RS75ZeroFreeAudit.md).

The needed zero-count estimate exists in Rosser (1941), Theorem 19, p. 223:

`abs(N(T)-F(T)) < .137 log(T) + .443 log(log(T)) + 1.588`, for T ≥ 2,

where `F(T) = T/(2*pi)*log(T/(2*pi)) - T/(2*pi) + 7/8`.
Its proof cites Backlund. Our weighted-sum lemmas do not prove this estimate.
The older RS75 row uses a finite head of 57 zeros; the improved 1976 row uses
a larger head. These numerical zero certificates also remain to be formalized.

## Reproduction

Run from this directory, using its own toolchain:

```sh
lake exe cache get
lake build
lake comparator
```

`RSBounds.lean` imports completed modules only. `RSBounds/Targets.lean` defines
propositions, not proofs or axioms. Other source files may be under development.

The independent Comparator challenge covers the two restricted totient
statements, not the four unfinished goals. Fresh build logs, axiom audits,
and exact source hashes are in `verification/`. Comparator outcomes and any
sandbox limitation are recorded there.

The dependency `calr3/ternary-goldbach` is pinned at
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`; all revisions are in
`lake-manifest.json`. See `THIRD_PARTY_NOTICES.md` for attribution.

## Sources

- [Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).
- [Backlund, Acta Mathematica 41, pp. 345–375](https://doi.org/10.1007/BF02422950).
- [Rosser–Schoenfeld (1975), Lemmas 7–9 and Theorem 4](https://doi.org/10.1090/S0025-5718-1975-0457373-7).
- [Schoenfeld (1976)](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
- [Rosser–Schoenfeld (1962)](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
