# Tasks: `development/Consequences.lean` warning cleanup

This file documents the task breakdown requested for addressing linter warnings in `development/Consequences.lean`.

## Simp / Decide / ZetaDelta (flexible tactic) warnings

- [x] Task 1 — Replace flexible `simp`/`simp_all` calls with `simp?`/`simp_all?` to obtain stable `simp only [...]` suggestions.
- [x] Task 2 — Apply the suggested `simp only [...]` / `simp_all only [...]` rewrites and re-run `lake build development.Consequences` to confirm the flexible-tactic warnings are gone.

## Multi-goal (focus) warnings

- [x] Task 3 — Resolve “multiple goals” style warnings by splitting goals with `·` and ensuring tactics are applied per-goal (no tactics run across multiple goals unintentionally).

## `refine'` replacements (one task per occurrence)

- [x] Task R1 — Replace `refine' Nat.Coprime.dvd_of_dvd_mul_right ...` with `apply`/`refine` (and explicit subgoal bullets).
- [x] Task R2 — Replace `refine' Nat.Coprime.dvd_of_dvd_mul_left ...` with `apply`/`refine` (and explicit subgoal bullets).
- [x] Task R3 — Replace `refine' Finset.sum_congr ...` in the divisor-sum block with `refine`/`intro` structure.
- [x] Task R4 — Replace `refine' Finset.sum_congr ...` in `sum_mu_div_sq_isLittleO` with `refine`/`intro` structure.
- [x] Task R5 — Replace `refine' le_trans ...` chaining in `lambda_pnt` with `refine le_trans ?_ ...` and explicit bullets.

## Remaining warnings

- [ ] `development/Consequences.lean` still contains a `by sorry` placeholder (`chebyshev_asymptotic_pnt`), which produces a `declaration uses 'sorry'` warning during builds.
- [ ] `PrimeNumberTheoremAnd/Wiener.lean` contains several `sorry`s, which also produce `declaration uses 'sorry'` warnings when building `development.Consequences`.

