# Reusable certified zero table

`RSBounds/ZetaZeroTable.lean` provides an interface designed for reuse by
future explicit-formula and zero-sum proofs. It passed fresh Lean compilation
and all seven theorem-closure axiom audits on 2026-11-06 at 13:16:13 UTC. Every
audited export uses only `propext`, `Classical.choice`, and `Quot.sound`; see
[`verification/zeta-zero-table-run.json`](../verification/zeta-zero-table-run.json)
and [`verification/zeta-zero-table-axioms.log`](../verification/zeta-zero-table-axioms.log).
The source SHA-256 is
`137118d7d016bf126819e8c3709e3cd02c51326b87f047585e6738c9865ffcb5`.

The instance `ZetaZeroTable.first29 : CertifiedTable 29 100` packages:

- rational open brackets and exact ordinates in increasing order;
- the actual equation `riemannZeta (1/2 + iγ) = 0` for each entry;
- analytic multiplicity exactly one;
- completeness for **all** zeros with `0 < Im ρ ≤ 100`, with no real-part
  hypothesis in the completeness theorem.

The table length and certified height are parameters of `CertifiedTable`, so
larger certified tables can use the same interface. This file constructs only
the height-100 instance. It does not assert a first-1000 table or a result
through height 280.

| Export | Meaning |
|---|---|
| `first29_bracket` | Entry `i` lies strictly between its rational endpoints. |
| `first29_simple` | The actual analytic zero order is one. |
| `zero_iff_exists_index` | Every zero in the certified height window is an entry. |
| `positiveZeroCount_eq_table` | Inclusive multiplicity count equals the number of listed ordinates at most the threshold. |
| `lowerCount` | Computable number of upper bracket endpoints at most a rational threshold. |
| `upperCount` | Computable number of lower bracket endpoints strictly below a rational threshold. |
| `bracket_count_bounds` | Those two integer counts bound the actual count for rational thresholds in `[0,100]`. |
| `positiveZeroCount_hundred` | The inclusive count at height 100 is 29. |

The endpoint directions are intentional: every bracket is open, while the
zero count includes zeros at its upper threshold. The rational bounds require
only finite rational comparisons; they do not evaluate the exact real
ordinates or rerun the zero-location certificates.

The exact rational data and original declaration names are also available in
[`data/zeta-zeros-to-100.json`](../data/zeta-zeros-to-100.json). Lean indices
are `0` through `28`; the JSON uses the customary zero numbers `1` through
`29`. The JSON contains no floating-point main-term diagnostics. The Lean
interface and its finite-height dependencies have passed their recorded checks;
the JSON is a readable presentation of the rational input data.

No certificate proof is duplicated. `BacklundLowZeros` now retains its
bracket bounds in `exists_certified_zeros_with_brackets`; the prior
`exists_certified_zeros` is a projection of that same witness. Likewise,
`BacklundLowCount.listed_zeros_eq_closedPositiveZeros` exposes the finite-set
identity already used to prove its count formula. The table uses these
exports and `BacklundCountIdentity.zero_simple_below_hundred`.

## Exact certified brackets

Each row gives the open interval `lower < γₙ < upper` for the zero
`1/2 + iγₙ`. Every displayed decimal is an exact terminating rational,
not a rounded zero approximation; all 58 endpoints were checked to
round-trip exactly to the rational values in the JSON data. Every entry
is simple, and the Lean table proves that these are all zeros with
`0 < Im ρ ≤ 100`, including their multiplicities.

| Zero number `n` | Lower endpoint | Upper endpoint |
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

# Larger-table source audit

The three current main revisions below were checked on 2026-11-06. This is a
source audit, not an additional replay of those projects.

| Project and revision | Relevant finding |
|---|---|
| IEANTN, `466b41b28ecc224398cf53a99c5fe9618131398b` | `LowZeroes.v1` records numerical claims as unproved propositions; its generated page labels the node a stub and says the underlying zero data is absent. |
| PNT+, `127b50e33f6033e2147921167a117af96d9ba4ea` | The previously audited zero-count theory supplies qualitative/global bounds, but this source search found no certified located first-1000 table. |
| zeta-lab, `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534` | The formal finite-height result supplies the complete 29-zero table through 100. The repository also has `data/zeros_1000.json`, but that cache is produced by `mpmath.zetazero`, not by a Lean certificate. Its formal result report explicitly limits the result to height 100. |

Primary source links:

- [IEANTN LowZeroes status and limitations](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/docs/nodes/LowZeroes-v1.md).
- [PNT+ crude count theorem](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/127b50e33f6033e2147921167a117af96d9ba4ea/PrimeNumberTheoremAnd/Backlund/ZeroCountCrude.lean).
- [zeta-lab finite-height formalization report](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/hunts/rh_height_lean/RESULTS.md).
- [zeta-lab numerical cache generator](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/zeta/zeros.py), function `first_n_zeros`.
- [zeta-lab numerical first-1000 cache](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/data/zeros_1000.json).

The absence claim is limited to these audited sources and search results; it
does not exclude unpublished work or certificates in other repositories.
