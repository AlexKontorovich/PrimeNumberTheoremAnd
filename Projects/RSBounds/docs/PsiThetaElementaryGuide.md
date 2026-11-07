# Elementary theta transfer and RS62 scalar budgets

Status: checked. Fresh-source compilation and all fourteen transitive
axiom audits passed on 2026-11-06 at 21:01:24 UTC. Only `propext`,
`Classical.choice`, and `Quot.sound` occur; the source remained unchanged
during the successful check.

`RSBounds/PsiThetaElementary.lean` imports only Mathlib. Its namespace is
`TernaryGoldbach.RSBounds.PsiThetaElementary`.

The transfer export `psi_sub_theta_le hx`, for `100000 ≤ x`, states
`Chebyshev.psi x - Chebyshev.theta x ≤ 6.5 * Real.sqrt x`.
It reuses Mathlib's
`Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi` and
`Chebyshev.psi_le_const_mul_self`. The coefficient is bounded by
`5.4 * (1 + .15 + .04) = 6.426 < 6.5`. The two power comparisons follow
from `(20/3)^6 < 100000` and `25^10 < 100000^3`. The logarithmic constant
uses Mathlib's certified bound for log 2.

The three numerical exports are:

| Export | Hypotheses | Relative allowance |
|---|---|---|
| `moderate_theta_budget` | `100000 ≤ x`, `log x ≤ 23` | `.0023 + 12.5 / sqrt x ≤ 1 / (2 * log x)` |
| `b23_theta_budget` | `exp 23 ≤ x`, `log x ≤ 2400` | `.00020211 + 6.5 / sqrt x ≤ 1 / (2 * log x)` |
| `large_theta_budget` | `exp 2400 ≤ x` | `.1 / log x + 6.5 / sqrt x ≤ 1 / (2 * log x)` |

The stronger scalar-only `large_theta_budget_of_log` needs only `0 < x`
and `20 ≤ log x`. None of these lemmas assumes or proves a psi error
estimate; the global assembly must supply the actual checked psi results.

The monotonic comparison is Mathlib's `Real.log_div_sqrt_antitoneOn`.
For the moderate interval, split at `log x = 12`; the two rational
upper bounds after multiplying by log x are
`.0023 * 12 + 12.5 * (11.52 / 316)` and
`.0023 * 23 + 12.5 * (12 / 400)`, each below .5.
For b=23 through log x=2400, the rational upper bound is
`.00020211 * 2400 + 6.5 * (20 / 20000) = .491564 < .5`.

The verification command, after sourcing `../lean-env.sh`, is
`python verification/run_psi_theta_elementary_check.py`. It directly
compiles the exact source with fourteen appended axiom queries in one
process. The successful receipt is
`verification/psi-theta-elementary-run.json`, with log
`verification/psi-theta-elementary-build-audit.log`.

The successful source SHA-256 is
`704af7aa172d2a5c0d7a1d908b6fd51fd0edbc64c3ce539bf8d469497ce67b82`;
the object SHA-256 is
`6a581d879151ab9fbd1a1c41648407d4c3b895827fe901c7090ad684e5b46c0a`.
The check took 87.55 seconds. Two earlier failed elaboration attempts
remain archived under the `psi-theta-elementary-attempt1` and
`psi-theta-elementary-attempt2` verification prefixes.
