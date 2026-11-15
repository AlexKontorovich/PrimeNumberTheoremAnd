# Independent check of the finite ψ bounds

Checked on 14 November 2026 by Claude (Anthropic), at Harald Helfgott's request,
independently of the session that wrote the proof.

## Scope

Repository `Garald1/PrimeNumberTheoremAnd`, branch `psi-finite-check`, commit
`b34da46670d2b9c6d23716e7ae30bda9217944ed`, project `Projects/RSBounds`, cloned
afresh for this check.

The three theorems (namespace `PsiFinite`):

* `psi_abs_sub_le_four_fifths_sqrt` (`RSBounds/PsiFinite/Final.lean`): if
  `1500 ≤ x` and `x ≤ 10 ^ 10`, then `|Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x`.
* `psi_abs_sub_le_sqrt` (same file): if `8 < x` and `x ≤ 10 ^ 10`, then
  `|Chebyshev.psi x - x| ≤ Real.sqrt x`.
* `buthe_eq_6_2_le_1e10` (`RSBounds/PsiFinite/Buthe.lean`): if `100 ≤ t` and
  `t ≤ 10 ^ 10`, then `-0.8 ≤ (t - Chebyshev.psi t) / Real.sqrt t` and
  `(t - Chebyshev.psi t) / Real.sqrt t ≤ 0.81`.

`x` and `t` are real, and `Chebyshev.psi x` is Mathlib's `∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n`.
There are no other hypotheses. The bibliographic sources are as the project cites them
(`Final.lean`: Ramaré, Acta Arith. 159 (2013), eq. (3.2); `docs/PsiFiniteCheck.md`:
Büthe, Math. Comp. 87 (2018), eq. (6.2)); this check did not consult the papers.

## Environment

Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`), installed from
the official release archive on GitHub; Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679` (prebuilt cache, `lake exe cache get`);
`calr3/ternary-goldbach` `ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`; all as
pinned in `lean-toolchain` and `lake-manifest.json`. Linux x86-64, 2 cores,
8 GB RAM, no swap.

## Results

| Check | Result |
|---|---|
| Generated sources | All 996 files under `RSBounds/PsiFinite/Campaign/T1` listed in `verification/psi-finite-campaign/T1-sha256.txt` (the 955 modules `M0..M954`, the 39 modules `Asm/G0..G38`, `Assembly.lean`, `segments.txt`) have the recorded SHA-256. |
| Source scan of the 1,015 non-Mathlib modules in the import closure of `RSBounds.PsiFinite.Buthe` (1,012 in `RSBounds`, 3 in TernaryGoldbach: `Prelim.LogWalk`, `Prelim.RamareHarm`, `Prelim.SmallMertensLower`) | Outside comments and strings: no `sorry`, `admit`, `axiom`, `native_decide`, `decide +native`, `ofReduceBool`, `trustCompiler`, `implemented_by`, `extern`, `unsafe`, `opaque`, `csimp`, `skipKernelTC`, `addDecl`, `Environment`, `#eval`, `run_cmd`, `elab`, `macro`, `syntax` or `initialize`. 38,215 `decide +kernel` calls in 959 files, which add no axioms. Options set: `Elab.async false` (955 files), `maxRecDepth 100000` (1 file). |
| `lake build RSBounds.PsiFinite.Buthe RSBounds.PsiFinite.Final` | "Build completed successfully (10062 jobs)". All 1,015 non-Mathlib modules were compiled from source in this check, so the kernel checked every declaration in them. Timings below. |
| Statement check (`PsiFiniteIndependentStatements.lean`, `PsiFiniteIndependentCheck.lean`) | The three statements were written from scratch in a file that imports only Mathlib, and again with ψ written out as `∑ n ∈ Icc 1 ⌊x⌋₊, Λ n` (proved equal to `Chebyshev.psi`). The project's theorems prove all six. |
| `#print axioms` | `propext`, `Classical.choice`, `Quot.sound` only, for the six check theorems. The project's `verification/PsiFiniteCheckAudit.lean` gives the same, and its output is identical to the recorded `verification/psi-finite-campaign/audit-output.txt`. |
| Comparator exports (`leanexport`, commands and roots as in `docs/PsiFiniteCheck.md`) | Challenge: 68,768,385 bytes, SHA-256 `2a8d33fde025e1defe63198e4afe01a4793bd33dee2790ba6e85f2e8c65f9423`. Solution: 329,500,827 bytes, SHA-256 `29a61d005a43d72b954f58f09f81c4c0fbb064f894f77b8a7b88dfd9dc7598a5`. Both are byte-identical to the exports that passed the sandboxed Comparator on 9 November 2026 ("Lean default kernel accepts the solution", "Your solution is okay!"), so that verdict applies to this build. |

Build timings on this machine:

| step | wall | peak RSS |
|---|---|---|
| `Campaign/T1/M0..M954`, two at a time | 9.4 h in total; 20–157 s per module, median 72 s | ≤ 1.76 GB per pair, except the first build (M0 alone): 4.95 GB |
| `Campaign/T1/Asm/G0..G38`, one at a time | 28–142 s each, 24 min in total | 4.53–4.71 GB |
| `Assembly`, `Final`, `Buthe` | 31 s, 37 s, 42 s | ≤ 4.72 GB |
| Challenge and solution: compile and export | 2 min 43 s | |

### What the Comparator verdict covers

The Comparator configuration (`comparator-psi-finite.json`) names only the two
bounds on [1500, 10^10] and (8, 10^10]. For those two, its kernel replay of the
solution export re-checked every declaration they depend on, Mathlib's included,
from an empty environment. `buthe_eq_6_2_le_1e10` is not in that export: it was
checked by the kernel during this build and by `#print axioms`, with Mathlib
taken from the prebuilt cache.

### Not done

* The Comparator was not rerun here; the recorded run took about 18 CPU-hours of
  kernel replay. Byte-identical exports make a rerun redundant, unless one wants a
  second machine.
* No checker independent of Lean's kernel (nanoda, lean4lean) has been run on
  the solution export.
* The generated modules were not regenerated from `tools/psi_planner`; only
  their recorded hashes were checked. This does not affect soundness, since the
  kernel checked the files as they are.
* `Campaign/E6` and `E6Check` are outside the theorems' import closure and were
  not built.

## Reproduction

From `Projects/RSBounds`:

```sh
lake exe cache get
lake build RSBounds.PsiFinite.Buthe RSBounds.PsiFinite.Final

mkdir -p /tmp/psi
lake env lean -R verification -o /tmp/psi/PsiFiniteIndependentStatements.olean \
  verification/PsiFiniteIndependentStatements.lean
lake env bash -c 'LEAN_PATH=/tmp/psi:$LEAN_PATH lean verification/PsiFiniteIndependentCheck.lean'
lake env lean verification/PsiFiniteCheckAudit.lean

(cd RSBounds/PsiFinite/Campaign/T1 && sha256sum -c ../../../../verification/psi-finite-campaign/T1-sha256.txt | grep -vc ': OK$')
```

The last command should print `0`. For the exports and their checksums, run the
commands under "Reproduce" in `docs/PsiFiniteCheck.md`; the checksums should be
the ones in the table above.

On a machine with 8 GB of memory, name at most two campaign modules per
`lake build` call (`lake build RSBounds.PsiFinite.Campaign.T1.M0
RSBounds.PsiFinite.Campaign.T1.M1`, and so on) and one `Asm` module per call,
before the final `lake build`: each `Asm` module took about 4.7 GB here.
