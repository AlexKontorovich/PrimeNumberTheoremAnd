# Replay of the public height-100 zero certificate

Verified locally on 2026-11-06T13:00:07.525367+00:00: all 99 modules compiled, and
all 28 final theorem closures have only `propext`, `Classical.choice`, and
`Quot.sound`. The original numerical certificate literals and all 29 bracket
statements were preserved.

The vendored source is the exact 99-module dependency closure of
`RHHeight100.Main100` from
[teal-sea/zeta-lab](https://github.com/teal-sea/zeta-lab/tree/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534),
commit `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`.
The working checkout retains the unchanged original snapshot under
`../sources/zeta-lab-rh100`. The published project includes its exact manifest,
original toolchain and Mathlib pins, licenses, and unified adaptation patches,
without duplicating the raw source tree. Adaptations for this project's
Lean/Mathlib pin are separated under `vendor/rh100`, with upstream copyright and licenses
retained.

The fresh-check record is `verification/rh100-replay-run.json`; consult its
`status` field before treating the replay as complete. A partial resource
probe or successful source audit is not a proof replay. The pinned vendored
manifest is always the source of the module list and original hashes. When
the external original snapshot is present, the runner also checks all
99 original hashes; otherwise it explicitly records
`pristine_snapshot_verified: false` and uses the vendored upstream manifest.
The kernel proof replay itself does not require that external source tree.
The runner compiles one module at a time, in exact dependency order, with
the upstream module options and this project's existing Mathlib object files. It does not invoke
the upstream script's 30-GiB memory gate. Every successful object is tied to
source, toolchain, Mathlib pin, options, and transitive dependency hashes.

From the project root, with the pinned Lean toolchain and Lake dependencies
installed, resume with:

```sh
lake env python3 verification/replay_rh100.py
```

To force all 99 modules to be checked again, add `--fresh`. Published
receipts do not skip compilation unless matching local object files also
exist; compiled artifacts are not included in the source publication. The original
`CheckMain100.lean` is then compiled to pin the final conclusions to Mathlib's
`riemannZeta` and print their transitive axioms. Successful completion
requires every printed axiom set to be a subset of
`{propext, Classical.choice, Quot.sound}`.

The final upstream conclusions are simplicity and critical-line location of
every zeta zero in `0 < Re ρ < 1`, `0 < Im ρ ≤ 100`, together with exactly 29
distinct zeros in that set. The 29 interval-existence results give the
individual brackets. These are finite conclusions; no global RH hypothesis
is used.

`RSBounds.BacklundRH100Bridge` identifies the upstream zero set with this
project's inclusive positive-ordinate set. It removes the explicit strip
restriction using the already checked nonreal-zero/xi bridge, identifies
multiplicity with one on this finite range, and concludes `N_le 100 = 29`.
Its separate compilation and all five standard-three-axiom audits completed
on 2026-11-06 at 13:01:25 UTC and are recorded in
`verification/backlund-rh100-bridge-run.json`.

For a separately allocated second compiler slot, the final box modules can
be checked independently after `RHHeight100.Support` is built. Use the same
runner with `--only` (comma-separated module names) and a distinct `--record`
path. Each module has an exclusive file lock and an atomic receipt. The
main sequential runner reads completed receipts only after validating its
source/dependency signature and the output hash; the worker never writes
the main run record. The default invocation remains sequential.

The six staged source roots are registered in `lakefile.lean`, with exactly
the checked 99 modules and the upstream per-library Lean options. The
default `RSBounds` target and comparator libraries are unchanged.

The complete main ledger and `verification/rh100-replay/receipts/` each
record all 99 module source, transitive-dependency, and output hashes.
Seven compatibility changes are listed in
`verification/rh100-adaptations.json`, with their exact unified patches.
The original manifest's historical source-audit status is retained unchanged;
the separate replay record is the evidence of local proof verification.
