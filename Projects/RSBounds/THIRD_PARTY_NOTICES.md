# Attribution

`RSBounds/Totient.lean` adapts the exchange and comparison arguments in
`TernaryGoldbach/Prelim/MertensProduct.lean` from
`calr3/ternary-goldbach`, commit
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.
`RSBounds/SmallTotientProduct.lean` and its generator/template adapt that
revision's `Prelim/SmallMertensProd.lean` and generation code, reducing the
finite range to 71. The upstream MIT copyright and license are included in
`LICENSE`. Existing source notices are retained.

The pinned dependency contains code from `PrimeNumberTheoremAnd`; its Apache
license is retained in `licenses/PrimeNumberTheoremAnd-LICENSE`. Mathlib and
other dependencies retain their own licenses in their pinned repositories.

The new proof modules cite the mathematical literature in their documentation.
Statements of historical theorems are not substitutes for formal proofs.

`RSBounds/IEANTNGamma/` vendors the eight-module dependency closure of the
Gauss-series theorem from `teorth/IEANTN`, commit
`466b41b28ecc224398cf53a99c5fe9618131398b`, solution
`GammaAsymptotics.v2`. These files retain their original author and Apache 2.0
notices and are governed by that license, included alongside the sources and
in `licenses/IEANTN-LICENSE`. Only import paths were changed. The provenance
record is `verification/ieantn-gamma-provenance.json`; fresh verification is
documented in `docs/IEANTNGammaPort.md`.
