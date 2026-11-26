# Independent check of the full-range RS62 Mertens and totient theorems

Checked on 7 November 2026 by Claude (Anthropic), at Harald Helfgott's
request, independently of the session that wrote the proofs, following the
handoff package `RS62-Claude-Handoff.zip` prepared from that session.

## Verdict

The native Comparator passed, inside a bubblewrap process sandbox:
`Lean default kernel accepts the solution`, `Your solution is okay!`, exit
code 0. The frozen run record is
[`rs62-global-comparator/20261107T050844.506452Z/run.json`](rs62-global-comparator/20261107T050844.506452Z/run.json),
with `status: passed`, `exit_code: 0`, `sandbox_disabled: false` and
`official_ieantn_receipt: false`. This is a local Lean 4.35 check, not an
official IEANTN receipt.

## Statements

From [`comparator/RS62GlobalChallenge.lean`](../comparator/RS62GlobalChallenge.lean),
which imports Mathlib only:

* `RS62MertensFromFiniteRH.mertens_lower_of_finiteRH`: assuming
  `FiniteRH 1894439`, for every real `x > 1`,
  `log x + E - 1/(2 log x) < ∑_{p ≤ x} (log p)/p`, where
  `E = -γ - ∑_p log p / (p (p - 1))`.
* `RS62TotientFromFiniteRH.totient_bound_of_finiteRH`: assuming
  `FiniteRH 1894439`, for every integer `q ≥ 3`,
  `q/φ(q) < e^γ log log q + 2.50637 / log log q`.

`FiniteRH A` says that every zero `ρ` of Mathlib's `riemannZeta` with
`0 < Re ρ < 1` and `|Im ρ| ≤ A` has `Re ρ = 1/2`. It is a hypothesis of both
theorems. Nothing here proves it.

## What was checked

Source: `Garald1/PrimeNumberTheoremAnd`, branch
`rs-bounds-progress-2026-11-06`, project `Projects/RSBounds`. The check ran
on the source checkpoint in the handoff package. All 292 project and vendor
files of the two theorems' import closure, together with `lake-manifest.json`,
`lean-toolchain`, `lakefile.lean`, both comparator wrappers,
`comparator-rs62-global.json` and the three verification scripts, are
byte-identical to the branch at `f653ba0` (and `0920c04`). The other 38 files
of the closure are TernaryGoldbach sources at the pinned revision
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`.

Environment: Lean 4.35.0, whose `lean`, `lake`, `leanexport` and
`leanchecker` binaries match the handoff's recorded SHA-256s; Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` from its prebuilt cache;
bubblewrap 0.9.0; Linux x86-64 with 2 cores and 8 GB RAM.

| Step | Result |
|---|---|
| Build | `lake build RSBounds.RS62MertensFromFiniteRH RSBounds.RS62TotientFromFiniteRH`: "Build completed successfully (9377 jobs)", 02:50–04:55 UTC. All 330 modules of the local closure were compiled from source in this check, with no `declaration uses 'sorry'`. |
| Mertens audit, `verification/run_rs62_mertens_from_finite_rh_check.py`, unchanged | Exit 0. One declaration; only `propext`, `Classical.choice`, `Quot.sound`. Source SHA-256 `7cab9f56a2e264be53c30ed14e443f2e9c6dc5d7a8021da070c8c23233f2fc9f`. The fresh `.olean` has SHA-256 `964bc6bead911a7d…`, byte-identical to the one in the previously published receipt. |
| Totient audit, `verification/run_rs62_totient_from_finite_rh_check.py`, unchanged | Exit 0. Seven declarations; only the same three axioms. Source SHA-256 `cdfb8f02676c1a8d0bfbf14386db0119b1417ca9d54792db5aac8191fdca9c8d`. The fresh `.olean` (`92ca367e01b7…`) is byte-identical to the previously published one. |
| Comparator runner, `verification/run_rs62_global_comparator.py --execute --compiler-slot-allocated`, unchanged, without `--inadvisably-no-sandbox` | Checked the two audit receipts and hashed 532 sources, 1295 imported objects and the 4 tool binaries before and after the run. Built fresh wrappers; the solution wrapper's own axiom audit lists only the three axioms for both theorems. Definition holes were not permitted. |
| Exports | Challenge: 351,367,306 bytes, SHA-256 `dfdb94d164a296553cd8cc82cb29d6537dd92cb2c0f0d4b235b6e15a1c3bac11`. Solution: 823,524,935 bytes, SHA-256 `23699d3f6d5f8ca06e7676c841711b962b456a8ef6ea4b1e48282825694e1ef7`. |
| `lake comparator`, sandboxed | Statement and definition matching, the three-axiom check, and full replay of the solution with Lean's default kernel: passed in 3293.5 s. The whole runner took 3960 s. |

All five acceptance criteria of the handoff are met: both fresh audits passed
with the expected declaration counts, axioms and hashes; both wrapper builds
and exports completed, with sizes and checksums recorded; the Comparator
exited 0 with `Your solution is okay!`; the run record has `status: passed`,
`exit_code: 0`, a completion time, and its pre- and post-run hash checks
succeeded; and its isolation mode is recorded, with no official attestation
claimed.

## Departures from the handoff

* **Build route.** The handoff's module builder, `scripts/rebuild_rs62.py`,
  compiles each module with a bare `lean -o`, without Lake's module setup. It
  failed at module 239 of 328, `RSBounds.RS75RealAxisNumerics`, with
  "compiler IR check failed … depends on declaration
  'Finset.sum._at_.ZetaLean.Interval.expSum.spec_1._redArg', which has no
  executable code". This is a code-generation error, not a rejected proof.
  For the dependency `ZetaLean.IntervalExp`, a bare compile produces a
  different `.ir` file from Lake's (27,464 against 27,528 bytes), and
  `RS75RealAxisNumerics` compiles cleanly against Lake-built dependencies.
  The 330 modules were therefore built with Lake, as above. The two audits
  and the Comparator runner, which do the verification, ran unchanged, with
  the builder's environment.
* **An interrupted first attempt.** A Comparator run started at
  2026-11-07T04:56:36Z was stopped by a restart of the machine during the
  kernel replay. Its record, left as it was with `status: running`, is not
  published here. Its two exports were byte-identical to those of the passed
  run, which was started afresh at 05:08:44Z.

## Not done

* No checker independent of Lean's kernel has replayed these exports. nanoda
  needed more than about 28 GiB for the smaller zero-free export (see
  [RS75ZeroFreeIndependentCheck.md](RS75ZeroFreeIndependentCheck.md)), more
  than either machine available had free.
* No IEANTN submission or official receipt. IEANTN requires its own pinned
  toolchain, Lean 4.34.0-rc2, and receipts from its own verification
  workflow.
