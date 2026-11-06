# Finite zero-certificate performance

This is a read-only audit of the existing certificate design and its local
replay on 2026-11-06. No numerical source was changed for this audit, and
no completed proof was rerun to obtain a performance profile. The
99-module replay subsequently completed, including 28 transitive axiom
checks; see its [receipt](../verification/rh100-replay-run.json).

## Measured compilation costs

The following are actual successful module compilations. User CPU time is
reported separately from elapsed time. Peak RSS includes imported Lean
environments and shared mappings; summing these RSS figures across workers
does not give total physical memory consumption. Several compilations ran
concurrently, so these observations are not a controlled benchmark.

| Module | Elapsed seconds | User CPU seconds | Peak RSS, GiB |
|---|---:|---:|---:|
| `RHHeight100.Box8291` | 318.57 | 315.05 | 4.16 |
| `RHHeight100.Box7206` | 229.94 | 224.04 | 3.42 |
| `RHHeight100.Box7570` | 268.29 | 245.51 | 2.99 |
| `RHHeight100.Box7714` | 291.48 | 263.80 | 3.03 |
| `RHHeight100.Box9883` | 357.19 | 340.46 | 3.04 |

The exact measurements are in the corresponding
[`verification/rh100-replay/`](../verification/rh100-replay/) files named
`RHHeight100.Box<number>.resources.json`.
[Slot D's receipt](../verification/rh100-replay-slot-d.json) records the
three fresh checks of `Box7206`, `Box7570`, and `Box7714`, followed by reuse
of the already completed `Box9883` receipt. The runner uses per-module
locks and signatures of source, dependencies, toolchain, and options to
avoid duplicating completed work.

## Recorded Comparator verification

The native Comparator command for the full Rosser count bound and the
strict error bound through height 100 completed successfully in
**2747.55 elapsed seconds**. Both targets passed statement and definition
matching, allowed-axiom checks, and full replay with Lean's default kernel.
Only `propext`, `Classical.choice`, and `Quot.sound` were permitted.
The [final receipt](../verification/zero-count-run.json) records each stage
separately, and the [final log](../verification/zero-count-comparator.log)
records acceptance.

This is the elapsed time of the native Comparator command, including its
matching, axiom checks, and kernel replay. It is not an import-time or
tactic-elaboration measurement, and it excludes the preceding compiler,
axiom-audit, and export commands. The kernel replay starts from the exported
proof declarations and checks their dependency closure, including numerical
proof terms; it does not simply reuse acceptance of the compiled modules.
No per-declaration timing breakdown was collected during this run.

Process sandboxing was disabled because `bwrap` cannot mount its required
filesystem in this workspace. Statement, definition, axiom, and default-kernel
checks all ran and passed, but this is not a sandboxed attestation. No optional
additional kernel replay (`--paranoid`) is claimed.

## What one box checks

[`Box8291.lean`](../vendor/rh100/RHHeight100/Box8291.lean) is a generated
134,304-byte, 2,530-line certificate. It proves the existence of a zeta
zero on the critical line with ordinate strictly between 82.91 and 82.92.
It checks two Euler–Maclaurin endpoint tables, truncated at 152 and 62.

| Static source count | Number |
|---|---:|
| Literal nontrivial term boxes | 212 |
| Full prime-term logarithm/exponential evaluations | 54 |
| Composite-term interval products | 158 |
| Actual `decide +kernel` calls | 267 |
| `norm_num` occurrences | 712 |

The 54 full evaluations comprise 36 prime terms at the lower endpoint and
18 at the upper endpoint. Composite terms already reuse the boxes for
their factors, through proved multiplicativity; they do not independently
evaluate logarithms and exponentials. Each literal box has two endpoint
ordering proofs. The final kernel decision checks the sign of a product
formed from the two inflated Euler–Maclaurin enclosures.

For a prime $m$, the certificate checks

```lean
dirichletTermBox2 36 16 80 kL 10 m (ptBox t) = table m
```

Here `kL` is the bit length of `m`. This computation uses a 36-term
logarithm series, a 16-term complex-exponential Taylor sum, ten halvings
and squarings, and outward rounding to an 80-bit dyadic grid after the
small exponential and after each squaring. Its containment theorem is
proved independently of the generated numerical values.
Definitions: [`IntervalCExp.lean`](../vendor/rh100/ZetaLean/IntervalCExp.lean),
[`IntervalExp.lean`](../vendor/rh100/ZetaLean/IntervalExp.lean).

## Cost mechanisms visible in the source

These observations identify avoidable work, but they are **not a measured
breakdown of the 318.57 seconds**. No declaration-level timing profile was
collected, so percentages cannot be assigned to kernel evaluation,
`norm_num`, elaboration, or imported-environment overhead.

1. `expSumC` calls `powI x i` separately for every $i=0,\ldots,15$.
   The definition therefore requests 120 power-stage complex
   multiplications, compared with 15 for a running sequence of powers.
   It also performs the term scalings and additions. Each complex
   rectangle product reduces to four real interval products, whose
   endpoints use minimum and maximum of four corner products. Reduction
   caching may share intermediate results, so this count is not itself
   a measurement of the kernel's work or a promised speedup.
2. The small Taylor sum uses exact rational arithmetic before its first
   dyadic rounding. An exact-rational diagnostic using the same logarithm
   formulas gives 340-bit denominators for the log-151 enclosure, and up
   to 356 bits after multiplication by the endpoint and range reduction.
   Powers in the Taylor polynomial consequently produce multi-thousand-bit
   rational intermediates. The upstream `IntervalCExp` documentation also
   identifies this denominator growth; its split logarithm and exponential
   orders already mitigate it.
3. The logarithm table is not shared between endpoint certificates.
   Across the 19 generated `RHHeight100.Box*` modules, there are 38 endpoint
   tables and 840 full prime evaluations, but only 36 distinct prime
   logarithms. Each call also expands the same `log2I 36` definition.
4. The stored dyadic precision is much finer than the resulting interval
   widths. In `Box8291`, the literal component widths range from about
   $3.15\cdot10^{-9}$ to $9.41\cdot10^{-8}$, whereas the 80-bit grid
   step is about $8.27\cdot10^{-25}$. These width figures are diagnostics
   from the exact rational literals, not additional Lean theorems.

The observed cost is therefore a property of this evaluator and proof
encoding. It is not evidence that certifying 29 zeros intrinsically
requires several minutes per interval.

## Improvements that preserve the trust model

These are proposals for a future implementation, not claimed or benchmarked
speedups of the current proof.

* Prove one reusable table enclosing the 36 prime logarithms and $\log2$,
  and pass those enclosures to a generic term-containment theorem.
* Replace separately recomputed powers by a proved running-term or Horner
  evaluator. Introduce outward rounding within the Taylor computation,
  with a containment proof for every rounding step.
* Generate an arithmetic computation trace with checked intermediate
  values, so the kernel checks small reusable operations rather than
  repeatedly reducing a large recursive expression.
* Test a lower working precision against the final sign margins, then
  certify every resulting enclosure. The width comparison above motivates
  this experiment; it does not by itself prove that a particular smaller
  precision is sufficient.
* Preserve the checked theorem modules and their receipts. Downstream
  work should import the complete zero table, completeness theorem, and
  count bridge, rather than regenerate the endpoint computations.

The last item is already supported by the replay cache and the public
[zero-count interface](ZeroCountTheorems.md). Redesigning arithmetic during
the completed replay would have discarded useful checked work; no such
restart was performed.
