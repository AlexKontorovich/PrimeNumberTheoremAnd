# Independent check of the RS75 zero-free region

Checked on 6 November 2026 by Claude (Anthropic), at Harald Helfgott's request,
independently of the session that wrote the proof.

## Scope

Repository `Garald1/PrimeNumberTheoremAnd`, branch
`rs-bounds-progress-2026-11-06`, commit
`7cd0fdd408890a719a7b7a0e8dfc8af16c0e3e3c`, project `Projects/RSBounds`. The
later commits `eece7af` and `f653ba0` change none of the 195 files in the
theorem's import closure, nor `lake-manifest.json`, `lean-toolchain` or
`lakefile.lean`, so the results also apply at `f653ba0`.

The two public theorems in `RSBounds/RS75ZeroFree1975.lean` (namespace
`TernaryGoldbach.RSBounds.RS75ZeroFree1975`):

* `zero_free_high`: if `1894439 ≤ |Im s|` and
  `1 - 1/(9.645908801 * log(|Im s|/17)) ≤ Re s`, then `riemannZeta s ≠ 0`.
  There are no other hypotheses.
* `zero_free`: the same conclusion for `21 ≤ |Im s|`, assuming
  `FiniteRH 1894439`, i.e. every zero `ρ` of `riemannZeta` with
  `0 < Re ρ < 1` and `|Im ρ| ≤ 1894439` has `Re ρ = 1/2`.

## Environment

Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`); Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (prebuilt cache);
`calr3/ternary-goldbach` `ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`; both as
pinned in `lake-manifest.json`. Linux x86-64, 2 cores, 8 GB RAM.
SHA-256 of `RSBounds/RS75ZeroFree1975.lean`:
`e09f31b984976d75c0a773b6c41d3d671ee2ac7aebe2c5466212ba1253a768cb`, the same as
recorded in `verification/rs75-zero-free-1975-run.json`.

## Results

| Check | Result |
|---|---|
| Source scan of the 195 non-Mathlib modules in the theorem's import closure (RSBounds, `vendor/rh100`, TernaryGoldbach) | Outside comments: no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `opaque`, `addDecl`, `#eval` or `run_cmd`. One tactic macro (`additive_combination`). About 5,500 `decide +kernel` calls, which add no axioms. |
| `lake build RSBounds.RS75ZeroFree1975` | "Build completed successfully (9242 jobs)". All 195 modules compiled from source in this check, with no `declaration uses 'sorry'`. |
| Statement audit (`RS75ZeroFreeIndependentCheck.lean`) | Both statements, written from scratch with Mathlib's `riemannZeta` and `Real.log` and with finite RH spelled out, are proved by the project's two theorems. |
| `#print axioms` | `propext`, `Classical.choice`, `Quot.sound` only, for the two audit theorems, `zero_free` and `proved`. |
| Export (`leanexport`, lean4export 3.1.0) of the dependency closure of `zero_free`, `zero_free_high` and `Goals.FiniteRH` | 717,961,701 bytes, 13,437,946 lines, SHA-256 `293deb8b608b4e5e328e8db6c5ed12d95fb5adbda1a18056166e489513dc3cdc`. It contains the first-29-zero certificates of `vendor/rh100`, so the replays below check them too. |
| Lean's kernel on that export (`leanchecker --from-export`), from an empty environment | "Lean default kernel accepts the solution", exit code 0, 2271 s. |
| Independent reproduction of the build and export | Harald Helfgott rebuilt the project on his own Linux laptop from a fresh clone of the branch at `f653ba0` (`lake exe cache get`, `lake build RSBounds.RS75ZeroFree1975`, then the export command in "Reproduction" below). His export has the same SHA-256, `293deb8b…3dc3cdc`: byte-identical. |
| nanoda 0.4.19 on that export | Not completed. Here, with the default 8 MB stack it overflowed; with an unlimited stack it was killed twice by this machine's memory limit, at about 5–6 GB. On the laptop it was killed twice by the kernel's out-of-memory killer (exit code 137), with about 27.5 GiB and 23.6 GiB of anonymous memory in use, according to the kernel log. This says nothing about the proof; nanoda needs more than about 28 GiB for this export. |
| Lean 4.35's native Comparator, sandboxed with bubblewrap 0.9.0: `lake comparator --config comparator-zero-free.json`, with `--challenge-from-export` and `--solution-from-export` | "Lean default kernel accepts the solution", "Your solution is okay!", exit code 0. Its exports were made from the compiled `comparator/RSZeroFreeChallenge.lean` and `comparator/RSZeroFreeSolution.lean`, with the two theorems, the three axioms and the builtin and primitive roots the Comparator requires (the list in `verification/run_rs62_global_comparator.py`). Challenge: 351,182,668 bytes, SHA-256 `b912a126c0b6598609058b60e2334269fb8bfcb9d59ae4dec1f236e905f1ed91`. Solution: 717,861,092 bytes, SHA-256 `17cb324f58685780d25be0e15465d6d64fc40d88630bae5dc378f0278d93cf3a`. Total time including both exports: 3432 s. |

The Comparator run is a local check, not an official IEANTN receipt.

### Not done

* No checker independent of Lean's kernel has accepted the export yet: nanoda
  needs more memory than either machine provided. The other checkers bundled with
  Lean 4.35 (`lean4lean`, `con-leche`, `con-ron`) were not run.

## Relation to Rosser–Schoenfeld (1975)

Theorem 1 (p. 250, display (1.27)): ζ has no zeros for
σ ≥ 1 − 1/(R log|t/17|), |t| ≥ 21, with R = 9.645908801. The formal statements
match it. The paper's proof disposes of zeros with |γ| ≤ A, where
A ≈ 1,894,438.51 is the height reached by the verification that the first
3,502,500 zeros lie on the critical line, and treats |γ| > A analytically. The
formalization makes the same split.

* **Where the content is.** For 21 ≤ |t| ≤ 1894439 the conclusion follows at
  once from the hypothesis, since the boundary lies to the right of σ = 1/2
  when |t| ≥ 21. All the analytic content is in `zero_free_high`, which is
  unconditional. It relies on the certified table of the first 29 zeros
  (vendored from `teal-sea/zeta-lab` and compiled here).
* **The height.** `FiniteRH 1894439` assumes slightly more than the 1975
  verification gave, because 1894439 > A. `docs/RS75ZeroFreeAudit.md` says the
  integer height "covers" A; the inclusion goes the other way. This is
  immaterial in practice, since RH has since been verified far beyond this
  height, but it is not literally the paper's input.

## Reproduction

From `Projects/RSBounds`:

```sh
lake exe cache get
lake build RSBounds.RS75ZeroFree1975
lake env lean verification/RS75ZeroFreeIndependentCheck.lean

mkdir -p /tmp/rs
lake env leanexport RSBounds.RS75ZeroFree1975 -- \
  TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free_high \
  TernaryGoldbach.RSBounds.RS75ZeroFree1975.zero_free \
  TernaryGoldbach.RSBounds.Goals.FiniteRH > /tmp/rs/solution.ndjson
sha256sum /tmp/rs/solution.ndjson
ulimit -s unlimited
lake env leanchecker --from-export /tmp/rs/solution.ndjson
```

The checksum should be the one in the table above. The export checked here was
made from `comparator/RSZeroFreeSolution.lean`, which only imports
`RSBounds.RS75ZeroFree1975`. Exporting straight from that module, as above,
gives a byte-identical file.

The sandboxed Comparator needs `bwrap` (bubblewrap) on the `PATH` and exports
of the compiled challenge and solution wrappers that include the builtin and
primitive roots:

```sh
mkdir -p /tmp/rs/cmp
for m in RSZeroFreeChallenge RSZeroFreeSolution; do
  lake env lean -R comparator -o /tmp/rs/cmp/$m.olean comparator/$m.lean
done
NS=TernaryGoldbach.RSBounds.RS75ZeroFree1975
ROOTS="Quot Quot.mk Quot.lift Quot.ind $NS.zero_free_high $NS.zero_free \
  propext Classical.choice Quot.sound Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd \
  Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft \
  Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk \
  Char optParam autoParam semiOutParam outParam"
for m in RSZeroFreeChallenge RSZeroFreeSolution; do
  lake env bash -c "LEAN_PATH=/tmp/rs/cmp:\$LEAN_PATH leanexport $m -- $ROOTS" > /tmp/rs/cmp/$m.export
done
lake comparator --config comparator-zero-free.json \
  --challenge-from-export /tmp/rs/cmp/RSZeroFreeChallenge.export \
  --solution-from-export /tmp/rs/cmp/RSZeroFreeSolution.export
```

(The challenge wrapper contains `sorry` by design, so compiling it warns.)

To run nanoda, which ships with the Lean 4.35 toolchain as `nanoda_bin`, first
make the export as above. Then use a machine with well over 28 GB of free
memory and a stack larger than 8 MB:

```sh
cat > /tmp/rs/nanoda.json <<'EOF'
{ "export_file_path": "/tmp/rs/solution.ndjson",
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true, "string_extension": true,
  "print_success_message": true }
EOF
ulimit -s unlimited
lake env nanoda_bin /tmp/rs/nanoda.json
```
