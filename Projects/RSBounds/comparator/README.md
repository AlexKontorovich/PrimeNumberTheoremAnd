# Independent theorem statements

Each challenge imports only Mathlib and states its target propositions using
fully specified definitions. Deliberate `by sorry` theorem stubs occur only in
the challenge; solutions do not import them, and `sorryAx` is not permitted.
The solution files import the actual proofs.

| Configuration | Challenge and solution | Targets |
|---|---|---|
| `comparator.json` | `RSTotientChallenge`, `RSTotientSolution` | The two restricted totient results |
| `comparator-zero-count.json` | `RSZeroCountChallenge`, `RSZeroCountSolution` | Rosser's bound for every `T >= 2`, and the strict error `< 1` for `0 <= T <= 100` |
| `comparator-psi.json` | `RSPsiChallenge`, `RSPsiSolution` | `abs(psi(x)-x) < 0.00020211*x` for `x >= exp 23`, assuming finite RH through 1894439 |
| `comparator-rs62-global.json` | `RS62GlobalChallenge`, `RS62GlobalSolution` | Exact weighted Mertens for every real x > 1, and totient for every integer n >= 3, both under finite RH through 1894439 |

The zero-count challenge independently defines the actual positive-ordinate
zeta zero count, with analytic multiplicities and the inclusive condition
`0 < Im rho <= T`. It has no definition hole or RH hypothesis. The psi
challenge independently specifies finite RH for the actual zeta function;
that definition is compared along with the psi theorem statement. All three
configurations permit only `propext`, `Classical.choice`, and `Quot.sound`,
with no definition holes.

From the package directory, run:

```sh
lake comparator --config comparator.json
lake comparator --config comparator-zero-count.json
python verification/run_psi_check.py
```

Comparator checks statement and definition matching, the allowed axioms, and
the exported proof with Lean's kernel. `--paranoid` adds optional independent
kernels; no such additional replay is claimed here.

For the recorded zero-count run, `verification/run_zero_count_check.py`
builds the public assembly, audits five exports, creates proof exports, and
invokes Comparator on those exports. This avoids redundantly rebuilding the
large finite certificates. It records hashes and every command in
`verification/zero-count-run.json`. Process sandboxing is disabled in this
workspace because `bwrap` cannot mount its temporary filesystem; statement,
definition, axiom, and kernel checks remain enabled. This is not a sandboxed
attestation.

The full zero-count theorem has compiled, and all five public axiom audits
have passed. Both zero-count targets also passed Comparator's statement and
definition matching, allowed-axiom checks, and full replay with Lean's
default kernel. Only `propext`, `Classical.choice`, and `Quot.sound` were
permitted. The native Comparator command exited 0 after 2747.55 seconds;
this duration excludes the preceding Lean builds, axiom audit, and exports.
See the [completed receipt](../verification/zero-count-run.json) and
[final log](../verification/zero-count-comparator.log).
The zero-count configuration covers its two displayed theorems, not every
export of `ZetaZeroTable` or the separate psi target. It does not claim the
stronger height-280 bound, a first-1000-zero certificate, or the remaining
theta/Mertens goals.

The [b = 23 psi theorem](../docs/PsiTable1975.md) has compiled, and its public
transitive axiom audit uses only the standard three axioms. Its separate
Comparator has passed exact statement and definition matching, the allowed
axioms, and full replay with Lean's default kernel. The
[psi runner](../verification/run_psi_check.py) directly compiles the challenge
and solution modules, exports their exact environments, and invokes Comparator
on those exports, after the recorded dependency closure has been built.
It avoids an extra Lake library registration and a redundant rebuild of the
numerical certificates. Commands and source/object/export hashes are recorded
in [psi-run.json](../verification/psi-run.json). Process sandboxing is disabled
for the same bwrap limitation described above; no sandboxed attestation is
claimed. The independent mathematical checks are complete.

The first psi replay left no final verdict after session loss. The original
log is retained; `verification/resume_psi_comparator.py` validates the saved
source/object/export hashes and restarts only the final Comparator. Its
successful result is recorded separately in
[psi-resume-run.json](../verification/psi-resume-run.json): exit code 0 after
3143.89 seconds. The [final log](../verification/psi-comparator-resume.log)
ends with `Lean default kernel accepts the solution` and
`Your solution is okay!`. All recorded source/object/export hashes were
validated before that replay.
# RS75 zero-free Comparator preparation

`RSZeroFreeChallenge.lean` states both the unconditional high-height theorem
and the finite-RH theorem independently, importing Mathlib only. The matching
solution imports the proved RS75 module. Both sources compile and both solution
axiom audits pass with only the standard three axioms. Configuration:
`../comparator-zero-free.json`; preparation receipt:
`../verification/zero-free-comparator-prep-run.json`.

**The native Comparator replay for these two targets has since passed,**
on 6 November 2026, run by Claude inside a bubblewrap process sandbox. It
ended with `Lean default kernel accepts the solution` and
`Your solution is okay!`. See
[`../verification/RS75ZeroFreeIndependentCheck.md`](../verification/RS75ZeroFreeIndependentCheck.md)
for the exports, checksums and commands. This is a local check, not an
official IEANTN receipt.


## Full-range RS62 comparison

Both final RS62 solution modules have completed their fresh source checks
and standard-three-axiom audits. The independent Mathlib-only challenge
specifies finite RH, the exact Mertens constant, and both full-range target
propositions without definition holes. The prepared Python runner validates
the exact completed audit records and source/object hashes before exporting
the proofs and invoking the native Comparator.

**The joint RS62 Comparator workflow is currently running locally. No
completed native verdict is claimed yet.** This status is separate from
the successful earlier count and b23 psi replays. The runner is
`verification/run_rs62_global_comparator.py`; its immutable completed verdict
record will be published separately after the process returns.
