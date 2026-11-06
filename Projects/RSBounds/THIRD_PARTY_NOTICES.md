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

`RSBounds/BacklundJensen.lean` adapts the divisor comparison from Mathlib's
`Analysis/Complex/JensenFormula.lean`, copyright 2025 Stefan Kebekus, under
Apache 2.0. Its source header retains that attribution; the local extension
retains an angular majorant and passes to phase-aligned powers.

`RSBounds/BacklundFirstCrossing.lean` and
`RSBounds/BacklundReflection.lean` contain proofs adapted from
`gersh/ternary-goldbach-lean`, commit
`27df23af6a712895f22204d0d81102baa74f0ebe`.
Copyright (c) 2026 Gershon Bialer. Licensed under Apache 2.0; the complete
license is included at `licenses/Gersh-LICENSE`. Original author headers are
retained. The selective extraction and fresh audits are described in
`docs/BacklundReflectionReuse.md` and
`verification/backlund-reflection-provenance.json`.

`RSBounds/IEANTNDigammaDifference.lean` reuses the two proved lemmas
`hasSum_telescope_inv` and `norm_digamma_sub_le` from
`Solutions/CH2.v1/Section81Titch.lean` in `teorth/IEANTN`, commit
`466b41b28ecc224398cf53a99c5fe9618131398b`. The original author header
(Terence Tao; copyright 2026 IEANTN contributors) is retained. Apache 2.0
applies, with the license text in `licenses/IEANTN-LICENSE`. Only imports
were adapted to the already-vendored Gauss-series proof.
