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

`vendor/rh100/` contains the exact 99-module dependency closure of the
height-100 certificate from `teal-sea/zeta-lab`, pinned at
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, with the documented compatibility
adaptations. The zeta-lab portions are MIT, copyright 2026 Thomas Lince;
the embedded Zeta23 files retain their original Apache-2.0 notices.
Both license texts, the original manifest, and adaptation patches are retained
beside the sources. See `docs/RH100Replay.md` and `vendor/rh100/README.md`.
The reusable table and count theorems reuse these certificates without
repeating their numerical proofs.

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
`RSBounds/BacklundReflection.lean`, `RSBounds/BacklundGammaPhaseBase.lean`,
`RSBounds/BacklundGammaPhaseArctan.lean`, and `RSBounds/BacklundAnchor.lean`
contain proofs adapted from
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

`RSBounds/BacklundDigammaStirling.lean` adapts the `Seq` section of
[`Zeta23/GammaFacts/StirlingVert.lean`](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/lean/vendor/zeta23/Zeta23/GammaFacts/StirlingVert.lean)
from `teal-sea/zeta-lab`, commit
`b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`.
Copyright (c) 2026 Anthropic, PBC; Apache 2.0. The original copyright and
license notice are retained in the module, and the complete license text is
included in `licenses/Zeta23-Apache-2.0`. The local
`BacklundDigammaSeriesAdapter.lean` supplies the shifted series from the
already-proved IEANTN Gauss formula. No Zeta23 analytic hypothesis is assumed.
The adapted proof, its horizontal Gamma-modulus consequences, and their
fresh axiom audits are documented in `docs/BacklundGammaModulusAudit.md`.
This small quantitative Gamma port is independent of the separate, completed
local replay of the height-100 finite zero certificate from the same repository.

`RSBounds/BacklundHalfStrip.lean` adapts the rectangle-and-Gaussian-damping
argument from Mathlib's
[`Analysis/Complex/PhragmenLindelof.lean`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/Complex/PhragmenLindelof.lean),
at the project's pinned Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`.
Copyright (c) 2022 Yury Kudryashov; Apache 2.0. The source header retains the
author and license attribution. A copy of the Apache 2.0 license is retained
at `licenses/PrimeNumberTheoremAnd-LICENSE`; Mathlib also retains its own
license in the pinned dependency. The local extension keeps the lower
horizontal edge and proves the upper half-strip principle from a quadratic
growth bound. Its use for zeta includes the checked finite bottom-edge
certificate; no interpolation principle or boundary estimate is assumed.

The mathematical sources for the completed analytic zero-count chain are
[Backlund (1918), equations (54), (56), and (77)](https://doi.org/10.1007/BF02422950)
and [Rosser (1941), Theorem 19](https://doi.org/10.2307/2371291).
The implementation uses a proved center denominator of `3.426` and verifies
the final numerical budget in Lean. These literature citations identify the
estimates and method; the local proofs and transitive axiom audits establish
the formal results.
