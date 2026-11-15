# Zero-count estimates available for reuse

Audit date: 2026-11-06. Repository refs were read afresh through GitHub.

| Repository | Inspected revision |
|---|---|
| `teorth/IEANTN` | `466b41b28ecc224398cf53a99c5fe9618131398b` (`main`, unchanged from the previous audit) |
| `AlexKontorovich/PrimeNumberTheoremAnd` (canonical PNT+) | `127b50e33f6033e2147921167a117af96d9ba4ea` (`main`, Lean 4.35.0) |
| `Garald1/PrimeNumberTheoremAnd` | `00737ce40d3ba12a58e63d7eca65563fb9860f7c` (`main`, an older fork) |
| `Garald1/PrimeNumberTheoremAnd`, our progress branch | `53493158fe933704fee8f5e594a84a479022666d` (`rs-bounds-progress-2026-11-06`, at the time of this read) |

**PNT+ does have a proved global estimate for N(T).** It is a crude polynomial
majorant, not an explicit Riemann--von Mangoldt error estimate. Saying that these
projects have no zero-count estimates would be too broad.

## Actual results and their strength

Write `F(T) = (T/(2*pi))*log(T/(2*pi)) - T/(2*pi) + 7/8`.

| Source and declaration | Actual statement | Proof status and use |
|---|---|---|
| PNT+ [`Backlund.zetaCounting_crude_majorant`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Backlund/ZeroCountCrude.lean#L1101) | `exists A > 0, forall T >= 2, abs(N(T)) <= A*T^(3/2)` | Unconditional proof body; `A` is existential. Counts multiplicities, with `0 < Im rho < T`. Sufficient for inverse-square zero-tail convergence; insufficient for the sharp Rosser error budget. |
| PNT+ [`Backlund.zetaSurrogate_zeros_in_closedBall₀_count`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Backlund/ZeroCountCrude.lean) | Polynomial bound for the divisor mass of the entire patched `(s-1)*zeta(s)` in closed balls | The underlying Jensen/Hadamard count. The global majorant above is derived from it; no argument-principle assumption. |
| PNT+ [`Kadiri.zetaCountingDyadic_abs_N_le_geometric`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean#L1776) | `exists E > 0, forall k, abs(N(2^(k+1))) <= E*3^k` | Proved consequence of the crude majorant. |
| PNT+ [`Kadiri.weighted_zeroImagSquareTail_summable`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/KadiriZeroCounting.lean#L2223) and `weighted_zeroImagSquareTail_shifted_summable` | Summability of the multiplicity-weighted inverse-square ordinate tail, including shifted ordinates | Unconditional proof bodies using the crude majorant. These supersede a need to assume a sharp RvM count merely to obtain convergence. |
| IEANTN [`ZetaZeroes.v1.finite_zeroes_on_compact`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/ZetaZeroes.v1/Solution.lean) and `exists_ordinate_free_height` | Finiteness on compact sets and existence of ordinate-free heights | Actual solution proofs with Comparator receipts. Useful count infrastructure, not quantitative estimates. |
| IEANTN [`CH2Section81Hardin.window_count_le`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/CH2.v1/Section81Hardin.lean#L92) | For `T >= 1000`, count in `(T-3/4,T]` is at most `0.52*log T+4` | The proof explicitly assumes `ZeroCount.v1.rvm_error_bound`; it is not an independent unconditional local count. Other CH2 local-count and zero-sum estimates likewise retain their stated RvM inputs. |

PNT+'s `riemannZeta.N` is explicitly defined using `Set.Ioo 0 T`. The opening
comment of `ZeroCountCrude.lean` mentions a closed upper endpoint, but the theorem
itself uses that open-endpoint definition. IEANTN's `ZeroCount.v1.zetaNClosed`
uses `Set.Ioc 0 T`. An endpoint bridge remains necessary when combining them.

## Explicit RvM estimates that are still statements, not proofs

At the inspected canonical PNT+ commit, the following declarations contain
literal `sorry` terms:

- [`RS.theorem_19`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/RosserSchoenfeld/RosserSchoenfeldZeta.lean): Rosser's `(0.137,0.443,1.588)` error bound, now stated for `T >= 1467`.
- [`Kadiri.backlund_bound`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/Kadiri.lean#L2618): `(0.137,0.443,6.1)` for `T >= 2`.
- [`TMEEMT`'s named source bounds](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/TMEEMT.lean#L1792): `Rosser1941.N_bound`; `Trudgian2014_argument.N_bound` with `(0.112,0.278,2.510)`; `HSW2022.N_bound_v1` and `N_bound_v2` with `(0.1038,0.2573,8.3675)` and `(0.1095,0.2042,3.0305)`.
- [`HSW.main_theorem` and `HSW.corollary_1_2`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/IEANTN/ZetaSummary.lean).

IEANTN's [`ZeroCount.v1`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/IEANTN/Nodes/ZeroCount/v1/formalization.yaml)
is expressly a literature-backed stub: `abs(Nclosed(T)-F(T)) <= log(T)/5+2`
for `T >= 1`, and `abs(Nclosed(T)-F(T)) < 1` for `0 < T <= 280`. No solution
or Comparator receipt discharges these inputs. Its CH2 receipts record them as
imported hypotheses; a receipt for a downstream implication does not prove them.

The older `Garald1/main` likewise has `RS.theorem_19` and its HSW estimate as
`sorry`. Our separate progress branch contains the explicitly documented partial
Rosser development, not a completed upstream RvM theorem.

## Small-height completeness

No verified numerical count up to 50, 200, 280, or 1467, and no complete first-zero
list usable for this purpose, was found at these revisions. This conclusion was
checked against actual count declarations and targeted code searches, not inferred
from filenames alone.

IEANTN [`LowZeroes.v1`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/IEANTN/Nodes/LowZeroes/v1/Conclusions.lean)
states the first-ordinate lower bound `14.134725` and the reciprocal-ordinate sum
below `2*10^4` as computationally sourced propositions; they are not accompanied
by Lean verification certificates. PNT+'s `Platt_theorem`, `GW_theorem`, and
`PT_theorem_1` in `ZetaSummary.lean` are also literal `sorry` declarations.
Moreover an RH-up-to-height location premise alone does not supply the exact
number, multiplicities, or completeness of an enumerated zero list.

## Reuse for the active proof

- PNT+ [`rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/RectangleArgumentPrinciple.lean#L275) proves the normalized rectangle integral equals the finite divisor sum, under meromorphy, finite orders, and no boundary zeros/poles. Its PNT+ source import closure has only four files. `rectangle_argumentChange_eq_two_pi_sum_meromorphicOrderAt` then packages an already-identified argument change. It is not yet the zeta-specific `N = theta/pi + 1 + arg/pi` identity.
- PNT+ [`Complex.hasSum_digamma`, `Complex.digamma_eq_tsum`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/DigammaSeries.lean) prove the Gauss series away from every nonpositive integer. The same file proves `exists_norm_digamma_le_log` on right-half-plane vertical strips. Its `logGammaSeq` proof constructs a logarithm limit and its derivative internally; no explicit gamma-phase `O(1/T)` remainder or exported arctangent-integral limit was found.
- PNT+ [`Complex.gamma_half_vertical_norm_sq`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Gamma/CriticalLineDecay.lean) proves `norm(Gamma(1/2+i*t))^2 = pi/cosh(pi*t)` and the exponential norm bound. This is a modulus estimate, not a phase estimate.
- PNT+ [`RiemannZetaConvexity.lean`](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Mathlib/NumberTheory/LSeries/RiemannZetaConvexity.lean) actually proves the Euler-product lower ratio at `sigma>1`, Abel's `norm(zeta(s)) <= 1+norm(1/(s-1))+norm(s)/re(s)`, and `norm(zeta(s)) < 8+2*abs(im(s))` on `1/2 <= re(s)<3`, `abs(im(s))>=1`. The filename does not imply the sharp convexity exponent or Rosser's circle-integral bound.

## Verification scope

The current source was read and inspected; no new Lean build or kernel axiom audit
was run for PNT+ in this audit. A complete recursive crawl of its own source imports
for the crude-count, rectangle, gamma-strip, convexity, and gamma-factor roots
covered 58 files. After removing comments, these files contain no `sorry`, `admit`,
new `axiom`, or `native_decide` terms. The crude-count root alone has 37 PNT+ files
in its source import closure. External imports are Mathlib, Architect, and a
Batteries tactic module. This is strong source evidence, but does not replace a
fresh transitive `#print axioms` check.

Repository code search for `riemannZeta.N` returned eight files, all inspected;
search for `Riemann_vonMangoldt` located the additional stub in `Kadiri`. Relevant
small-height and gamma/phase declarations were checked separately. Therefore the
safe conclusion is: **a real, unconditional coarse global count is available;
the sharp explicit RvM error bound and finite-height count certificates needed
for this task are not supplied by the inspected completed proofs.**
