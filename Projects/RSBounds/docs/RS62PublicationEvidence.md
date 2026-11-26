# Evidence for the global RS62 bounds

The final source checks passed on 2026-11-06 with Lean 4.35.0. The two
[independent targets](../comparator/RS62GlobalChallenge.lean) retain the explicit
finite-RH hypothesis through inclusive height 1894439. The weighted Mertens
inequality covers every real `x > 1`; the totient inequality covers every integer
`n >= 3`.

| Final module | Source SHA256 | Completed audit |
| --- | --- | --- |
| [RS62MertensFromFiniteRH](../RSBounds/RS62MertensFromFiniteRH.lean) | `7cab9f56a2e264be53c30ed14e443f2e9c6dc5d7a8021da070c8c23233f2fc9f` | [Build and one declaration](../verification/rs62-mertens-from-finite-rh-run.json) |
| [RS62TotientFromFiniteRH](../RSBounds/RS62TotientFromFiniteRH.lean) | `cdfb8f02676c1a8d0bfbf14386db0119b1417ca9d54792db5aac8191fdca9c8d` | [Build and seven declarations](../verification/rs62-totient-from-finite-rh-run.json) |

Both final build exit codes are zero. Each audited declaration depends only on
`propext`, `Classical.choice`, and `Quot.sound`; finite RH is a theorem hypothesis.
The recorded source and object hashes and the actual axiom-log entries were
checked against the current files before preparing this publication.

The independent Comparator workflow has started locally; its native replay
verdict is pending. The publication includes its Mathlib-only challenge,
import-only solution, configuration, and
[runner](../verification/run_rs62_global_comparator.py). Its actively changing
timestamped run directory is excluded. A later update can publish a frozen
completed record and log. These local checks are not IEANTN verification receipts.

The prerequisite build records do not all contain a historical log digest. The
Comparator runner therefore validates current log bytes against the exact audit
declarations and freezes their hashes as new evidence; it does not invent an
earlier log hash.

## Two preserved provenance details

The dedicated [AdaptiveHighBudget record](../verification/rs75-adaptive-high-budget-run.json)
has overall exit code 130: its source build succeeded, but its separate axiom
audit was interrupted before output. That record is preserved unchanged and is
not presented as a successful dedicated audit. The theorems actually used in the
global bounds are covered by the later successful
[WeakPsiTail audit](../verification/weak-psi-tail-run.json) and the final global
transitive-axiom audits above.

The [finite-walk record](../verification/mertens-finite-walk-run.json) uses the
historical sibling path
`../ternary-goldbach/TernaryGoldbach/Prelim/SmallMertensProd.lean`. Its bytes match
`TernaryGoldbach/Prelim/SmallMertensProd.lean` in the pinned dependency at commit
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`, with SHA256
`ac74a9aacb156f36bcf71a08db2319733a126fd68a8eec8bbdd11ace6fe4760f`.
The historical record is preserved without rewriting its paths. No external
source tree is copied into this publication.

The finite computation is reproducible from the checked
[generator](../verification/gen_mertens_finite_100000.py),
[JSON witnesses](../verification/mertens-finite-100000-witnesses.json), and
[CSV witnesses](../verification/mertens-finite-100000-witnesses.csv). Its
[completed Lean certificate check](../verification/mertens-finite-100000-run.json)
is included; no new replay is claimed for the publication step itself.
