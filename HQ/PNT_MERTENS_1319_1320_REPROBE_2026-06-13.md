# Mertens #1319/#1320 re-probe, 2026-06-13

Status: MIXED. The stale `aeroplugin` claims remain locally claimable, and one
clean infrastructure slice now compiles. The bare endpoints are not closed on
this pin because #1319 still needs a log-zeta Dirichlet-series package.

Worktree:

- Path: `/Users/robsneiderman/Desktop/AI4MATH/PrimeNumberTheoremAnd-mertens-finish-codex1-20260613`
- Branch: `codex/mertens-finish-codex1-20260613`
- Base: `5693c63 feat(FKS2): extended Table 4 mid-range interpolation for Epi (towards #721) (#1563)`

Contention check:

- `#1319` and `#1320` are open and assigned to `aeroplugin`.
- Last issue activity is the May 10 claim comment on both issues.
- Open PR search for `1319 OR 1320 OR Mertens OR Euler-Mascheroni OR log_zeta_eq OR log zeta OR Mangoldt` found no open `aeroplugin` PR for either target.
- Only returned PR was Rob's unrelated `#1558 IEANTN: bilateral Laplace inversion (#1535)`.

Targets:

```lean
private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s : ℂ)).re =
      - log (s - 1) + deriv Gamma 1 + γ +
        (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s)

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant
```

What landed locally:

```lean
private noncomputable abbrev logZetaCoeff (n : ℕ) : ℝ :=
  Λ n / (n * log n)

private theorem logZetaCoeff_LSeries_eq_integral (s : ℝ) (hs : 1 < s) :
    LSeries (fun n : ℕ ↦ (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ)) =
      (((s - 1 : ℝ) : ℂ)) *
        ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, (logZetaCoeff k : ℂ)) *
            (t : ℂ) ^ (-((((s - 1 : ℝ) : ℂ)) + 1))

private lemma zeta_log_cancel_tendsto_zero :
    Tendsto (fun s : ℝ => log (riemannZeta (s : ℂ)).re + log (s - 1))
      (𝓝[>] 1) (𝓝 0)
```

The earlier "missing summatory-to-Mellin theorem" diagnosis is corrected:
`Mathlib.NumberTheory.LSeries.SumCoeff` already provides
`LSeries_eq_mul_integral_of_nonneg`, and the local `logZetaCoeff` helper now
instantiates it.

Axiom probes after the helper slice:

```text
Mertens.E₂Λ.abs_le:
  [propext, Classical.choice, Quot.sound]

Mertens.γ.eq_eulerMascheroni:
  [propext, sorryAx, Classical.choice, Quot.sound]

Mertens.sum_mangoldt_div_log_eq:
  [propext, sorryAx, Classical.choice, Quot.sound]
```

Dependency result:

`sum_mangoldt_div_log_eq` is not a separate source sorry. It is a direct consumer:

```lean
theorem sum_mangoldt_div_log_eq (x : ℝ) :
  ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) =
    log (log x) + eulerMascheroniConstant + E₂Λ x := by
  grind [γ.eq_eulerMascheroni]
```

Closing `γ.eq_eulerMascheroni` should clean this downstream theorem.

Existing useful API:

```lean
LSeries_eq_mul_integral_of_nonneg
  (f : ℕ → ℝ) {r : ℝ} (hr : 0 ≤ r) {s : ℂ} (hs : r < s.re)
  (hO : (fun n => ∑ k ∈ Finset.Icc 1 n, f k) =O[atTop] fun n => ↑n ^ r)
  (hf : ∀ n, 0 ≤ f n) :
  LSeries (fun n => ↑(f n)) s =
    s * ∫ t in Set.Ioi 1, (∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ↑(f k)) * ↑t ^ (-(s + 1))

riemannZeta_eulerProduct_exp_log
  {s : ℂ} (hs : 1 < s.re) :
  Complex.exp (∑' p : Nat.Primes, -Complex.log (1 - ↑↑p ^ (-s))) =
    riemannZeta s

Complex.hasSum_taylorSeries_neg_log
  {z : ℂ} (hz : ‖z‖ < 1) :
  HasSum (fun n => z ^ n / ↑n) (-Complex.log (1 - z))

tsum_eq_tsum_primes_of_support_subset_prime_powers
tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers

ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right :
  Tendsto (fun s : ℝ => riemannZeta s - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 Real.eulerMascheroniConstant)

Real.eulerMascheroniConstant_eq_neg_deriv :
  Real.eulerMascheroniConstant = -deriv Real.Gamma 1
```

Remaining #1319 package:

1. Real-log extraction from the Euler product for real `s > 1`.

```lean
Real.log (riemannZeta (s : ℂ)).re =
  (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re
```

This needs the real-valued branch proof: each Euler factor is positive real,
the sum has zero imaginary part, and `Complex.exp sum = riemannZeta s` can be
converted to a real `log`.

2. Prime-power reindex from Euler factors to von Mangoldt coefficients.

```lean
(∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re =
  (LSeries (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ))).re
```

The route is to expand `-log(1 - p^-s)` by
`Complex.hasSum_taylorSeries_neg_log`, then use the prime-power support
reindex theorem and compute
`Λ (p^(k+1)) / (p^(k+1) * log (p^(k+1)))`.

3. Real-integral cleanup after `logZetaCoeff_LSeries_eq_integral`.

Unfold `E₂Λ`, replace `Icc 1` by `Ioc 0`, and compute the two scalar
integrals:

```lean
(s - 1) * ∫ x in Set.Ioi 1, log (log x) * x ^ (-s) =
  -log (s - 1) + deriv Gamma 1

(s - 1) * ∫ x in Set.Ioi 1, x ^ (-s) = 1
```

Remaining #1320 package, after #1319:

1. The zeta-side limit is now locally proved as
`zeta_log_cancel_tendsto_zero`.

2. The remaining limit is the Abelian tail from `E₂Λ.bound'`:

```lean
Tendsto
  (fun s : ℝ =>
    (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
  (𝓝[>] 1) (𝓝 0)
```

This should be a split-at-`X` proof: use `E₂Λ = o(1)` on the tail, compute
`(s - 1) * ∫_X^∞ x^(-s)`, and let the compact interval term vanish as
`s -> 1+`.

Conclusion:

#1319 and #1320 are not clean leaf fills on this pin. They are still claimable
under stale-claim policy, but the next honest work unit is the log-zeta
Dirichlet-series package above. Adding the analytic majorants as hypotheses
would be a no-carry violation.
