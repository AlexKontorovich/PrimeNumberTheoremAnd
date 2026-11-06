# Independent theorem statements

Each challenge imports only Mathlib and states its target propositions using
fully specified definitions. Deliberate `by sorry` theorem stubs occur only in
the challenge; solutions do not import them, and `sorryAx` is not permitted.
The solution files import the actual proofs.

| Configuration | Challenge and solution | Targets |
|---|---|---|
| `comparator.json` | `RSTotientChallenge`, `RSTotientSolution` | The two restricted totient results |
| `comparator-zero-count.json` | `RSZeroCountChallenge`, `RSZeroCountSolution` | Rosser's bound for every `T >= 2`, and the strict error `< 1` for `0 <= T <= 100` |

The zero-count challenge independently defines the actual positive-ordinate
zeta zero count, with analytic multiplicities and the inclusive condition
`0 < Im rho <= T`. It has no definition hole or RH hypothesis. Both
configurations permit only `propext`, `Classical.choice`, and `Quot.sound`.

From the package directory, run:

```sh
lake comparator --config comparator.json
lake comparator --config comparator-zero-count.json
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
The zero-count configuration covers its two displayed
theorems, not every export of `ZetaZeroTable`. It does not claim the stronger
height-280 bound, a first-1000-zero certificate, or any unfinished
psi/theta/Mertens goal.
