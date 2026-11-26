# Exact Schoenfeld II targets and dependencies

Source: L. Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and
ψ(x), II*, Math. Comp. 30 (1976), 337–360,
[doi:10.1090/S0025-5718-1976-0457374-X](https://doi.org/10.1090/S0025-5718-1976-0457374-X).
The statements were checked against the supplied scan, not OCR alone.

`RSBounds/Schoenfeld1976Targets.lean` records specifications only. None of the
four target propositions is yet proved. The earlier proposed constant 0.1 is
superseded by these targets; any checked auxiliary estimate remains usable.

Put `X = sqrt(log x / 9.645908801)` and
`epsilon0(x) = sqrt(8/(17*pi)) * sqrt(X) * exp(-X)`.

| Target | Statement | Printed page |
|---|---|---|
| Theorem 11, (7.2) | `abs(psi(x)-x) < x*epsilon0(x)` for `x >= 17` | 342 |
| Theorem 11, (7.3) | `abs(theta(x)-x) < x*epsilon0(x)` for `x >= 101` | 342 |
| Theorem 7*, (5.6*) | `abs(theta(x)-x) < 0.0239922*x/log(x)` for `x >= 758711` | 357 |
| Theorem 7*, (5.6b*) | Both errors `< 0.0077629*x/log(x)` for `x >= exp(22)` | 357 |

All four proposed formal statements expose `Goals.FiniteRH 1894439`. This is
the finite certificate left to the caller; it is not full RH. The historical
paper incorporates its finite zero computation into its unconditional results.
The current formal proofs must keep any unverified numerical inputs visible.

## Completed inputs

- The RS75 closed zero-free boundary
  `1 - 1/(9.645908801*log(abs(t)/17))`, unconditionally for
  `abs(t) >= 1894439`. Its extension down to 21 uses the finite RH premise.
- Rosser's actual multiplicity-count estimate
  `abs(N(T)-F(T)) < .137*log(T)+.443*log(log(T))+1.588` for `T >= 2`.
- The complete first 29 zeros through height 100, including their simplicity,
  rational enclosures and exhaustion.
- The RS75 quartic-smoothed b=23 result with coefficient `.00020211`, under
  finite RH through 1894439. This result does **not** use the quantitative
  zero-free region.
- Weighted zero partial summation and actual zero-sum/multiplicity bridges.

## Theorem 11 proof to implement

Section 7 uses quadratic smoothing (`m=2`) and splits at
`T2 = 17*exp(v*X)`. The elementary bounds behind (7.11) and (7.18) must retain
the paper's coefficients, followed by the choice of `v` and `delta` in
(7.24)–(7.30), and the explicit residual estimates through (7.41).

The critical-line term uses Rosser 1941, Lemma 17: first ordinate greater than
14.13 and the all-ordinate reciprocal-square sum less than .0463. The latter
bound is a separate active formalization task; it is not inferred from finite
RH alone. The theta transfer uses the RS62 bound `psi-theta < 1.43*sqrt(x)`.

The analytic argument proves the displayed error for `x >= exp(1737)`.
Theorem 11's full smaller ranges require the paper's additional table and
finite checks. Proving only the analytic range is an intermediate result,
not completion of Theorem 11.

## Table route to (5.6b*)

The published proof uses rows b=22,23,35,400,550,650,700,750,800,850,900,950,
1000,1050,1150,1350 and then Theorem 11 beyond `exp(1950)`.
There is no required prime enumeration below `exp(22)` for this target.

The improved 1976 b=23 row is `.00020171`, distinct from our proved 1975
row `.00020211`. Its published recipe uses a head of 12555 positive zeros,
far more than the first 100. Numerical planning checks indicate that the
older rows at b=22,23,35 still suffice for (5.6b*); these checks are not Lean
proofs. For b>=40 the paper says that the larger head does not improve its
table values. At b=800 the interval budget is tight:
`9.1328e-6 * 850 = .00776288`, leaving only `2e-8` before the stated constant.

RS75's historical A is the real solution of `F(A)=3502500`, approximately
1894438.51224, with `N(A)=F(A)`. The integer 1894439 covers its RH requirement,
but a fresh table proof must retain and bound its own boundary-count terms;
it must not silently transfer that historical equality to the integer.

## Additional work for (5.6*)

The threshold 758711 needs further moderate rows and finite prime/prime-power
checks. A modern finite certificate can replace the Appel–Rosser and Lehmer
tables cited on pp.357–359. It must be checked, not taken from the historical
tables without a formal certificate.

## IEANTN submission

The first submission is the already proved RS75 b=23 result, as a new
conditional node/version. It must not overwrite the existing unconditional
zero-free-region node. Our native Comparator receipt belongs to the existing
Lean 4.35 build. IEANTN currently pins Lean 4.34.0-rc2 and its own Mathlib
revision; its integration and official verification are separate obligations.
