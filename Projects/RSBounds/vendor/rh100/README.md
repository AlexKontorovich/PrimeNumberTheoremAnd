# Verified height-100 zeta certificate

This directory contains the exact 99-module dependency closure of
`RHHeight100.Main100` from
[teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab/tree/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534),
commit `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, with seven documented
compatibility adaptations. It proves completeness and simplicity of the
29 nontrivial zeta zeros of positive ordinate at most 100, and gives
explicit rational brackets for all 29 ordinates. No RH or zero-count
assumption is added.

All 99 modules were compiled locally on 2026-11-06. The original
`CheckMain100.lean` pins the final conclusions to Mathlib's `riemannZeta`;
all 28 final axiom reports contain only `propext`, `Classical.choice` and
`Quot.sound`. The numerical certificate literals and bracket statements
were preserved. The additional checked project bridge proves the
inclusive multiplicity count `N_le 100 = 29` without a strip-location
hypothesis on the counted zeros.

| Item | Purpose |
|---|---|
| `upstream-source-manifest.json` | Original repository, commit, module paths, Git blob and SHA-256 hashes |
| `upstream-lean-toolchain` | Original Lean 4.35.0-rc2 pin; metadata only, not this project's active toolchain |
| `upstream-lake-manifest.json` | Original dependency pins, including Mathlib 065356127b1d… |
| `upstream-lakefile.toml` | Original package metadata |
| `LICENSE-MIT-zeta-lab` | Root-project MIT license, copyright 2026 Thomas Lince |
| `LICENSE-Apache-2.0-zeta23` | License for the Zeta23 portion and its retained source notices |
| `CheckMain100.lean` | Original exact-statement and transitive-axiom check |
| `zero-brackets.json` | Extracted bracket metadata; its labelled floating-point diagnostics are not proof evidence |

The local replay uses Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`, as pinned by the surrounding
project. The six source roots are registered in its `lakefile.lean`; no
unchecked additional upstream modules are included by those library globs.

The seven changes are completely described in
[`verification/rh100-adaptations.json`](../../verification/rh100-adaptations.json),
with original/adapted hashes and unified patches. They consist of explicit
imports made necessary by Mathlib's module visibility, isolation of the
old Euler–Maclaurin and Hardy-Z helper names, a rational-identity proof
normalization, and replacement of the obsolete additive-combination tactic
API by Mathlib's current proof-producing tactic. No theorem hypotheses or
numerical input are weakened.

For the complete replay ledger, individual receipts, logs, resource
measurements and reproduction instructions, see
[`docs/RH100Replay.md`](../../docs/RH100Replay.md). The ledger and receipts
cover all 99 source/dependency/output hashes. Compiled artifacts are not
shipped: a clean checkout must replay the proofs. Existing local objects
are reused only when their recorded hashes and dependency signatures match.
The external original snapshot is optional; the vendored manifest and
sources suffice for fresh proof checking.

The original manifest's historical source-audit status is preserved. The
separate local replay ledger, rather than an altered upstream manifest,
records successful proof verification. The 29-zero certificate and the
project count bridge are checked independently of the subsequent scalar
assembly of Rosser's full counting bound.
