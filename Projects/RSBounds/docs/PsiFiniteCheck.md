# Kernel-checked |ψ(x) − x| ≤ (4/5)√x on [1500, 10^10]: record

Status on 7 November 2026, branch `psi-finite-check` (from
`rs-bounds-progress-2026-11-06` at `24554b9`). Phases A–F of
`PsiCert-Claude-Handoff/CLAUDE_HANDOFF.md` are done. Phase G (Comparator) passed
on 9 November 2026 (below). The stretch goal (5·10^10) was not attempted.

Proved, kernel-checked, axioms `propext`, `Classical.choice`, `Quot.sound`
only (`RSBounds/PsiFinite/Final.lean`):

```lean
theorem PsiFinite.psi_abs_sub_le_four_fifths_sqrt {x : ℝ}
    (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x          -- T1
theorem PsiFinite.psi_abs_sub_le_sqrt {x : ℝ}
    (h₁ : 8 < x) (h₂ : x ≤ 10 ^ 10) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x                         -- T2
```

`verification/PsiFiniteCheckAudit.lean` restates both from scratch and prints
their axioms; its output is in `verification/psi-finite-campaign/audit-output.txt`.
No file the theorems depend on uses `native_decide`, `Lean.ofReduceBool`,
`Lean.trustCompiler`, `implemented_by`, `extern`, `sorry` or a new axiom.

The bounds hold for every real `x` in the range, not just integers: each block
`[A, A']` is closed by `psi_block_abs_le_of_guards` (upper guard: an upper
bound for ψ(A') against the left end A; lower guard: a lower bound for ψ(A)
against the right end A'; `x − k√x` is increasing), and each unit gap of the
small walk by `psi_gap_abs_le` (lower guard with the pre-jump value ψ(n) at
n + 1).

Earlier milestones, still in the tree: `E6Check.psi_abs_sub_le_four_fifths_sqrt_le_1e6`
(phase C: T1 on [1500, 10^6]) and `SmallRange.small_sqrt`.

## Design

### The checker (`RSBounds/PsiFinite/Kernel.lean`, no Mathlib)

`checkSegK num den lo w B s : Option St` handles the odd numbers
`lo, lo+2, …, lo+2(L−1)`, `L = 2^w·B`, in `B` blocks of `W = 2^w` bits. Block k
is the real interval `[A, A+2W]`, with `A = lo − 1 + 2Wk`. The state
`St = ⟨plo, phi, llo, lhi⟩` encloses `D·ψ(A)` and `D·log A`, `D = 10^30`. The
checker works as follows.

1. **Sieve.** For each base prime `d` with `d² ≤ hi`, taken from the
   increasing list `basePrimes` and stopping at the first `d² > hi`, it ORs
   into the composite mask a comb with period `d`. The comb starts at the
   first odd multiple of `d` that is `≥ max(lo, d²)` (`startPos`) and is built
   by doubling (`repK`): O(log(L/d)) whole-segment operations per prime.
2. **Prime powers.** The same walk collects the pairs `(d^j, j)`, `j ≥ 2`,
   that lie in `[lo, top]`, together with the powers of 2.
3. **Counts.** `w` SWAR rounds (`swarK`) leave each block's prime count in
   its W-bit field.
4. **Blocks.** For each block, `blockStep` checks the two integer guards of
   `PsiSieveBlockReduction.psi_block_abs_le_of_guards` and updates the state:
   - **ψ, lower:** `plo += c·llo + Σ_pp ⌊llo/j⌋`, using
     `c·log A ≤ Σ_{A<p≤A'} log p`.
   - **ψ, upper:** `phi += c·lhi' + Σ_pp (⌊lhi'/j⌋+1)`, using
     `Σ_{A<p≤A'} log p ≤ c·log A'`.
   - **log:** `llo/lhi += logIncLo/Hi(A, 2W)`, from three terms of the
     artanh series in `y = h/(2A+h)` plus a geometric tail.

   There is no logarithm per prime and no moment sum. The handoff's
   `S = Σ(p − a)` refinement turned out to be unnecessary once block lengths
   are capped (see the planner below).

Kernel-efficiency rules found while benchmarking:

- Use raw recursors (`Nat.rec`, `List.rec`, `Bool.rec`, `Option.rec`). The
  `brecOn` of structural recursion is about 5× slower per step.
- Call `Nat.*` directly.
- Branch at the call site, and force each new bitset with `Nat.beq _ 0`. An
  accumulator passed as an unevaluated `ite` made `whnf_core` re-walk the
  whole chain, which was quadratic.
- Wrap every recursive call in `brk := id`. This returns control to the
  kernel's `whnf` loop; without it the raw `List.rec` hit "deep recursion".
- Write the base list as one literal under `maxRecDepth`. The kernel
  reduces `List.append` of 20 chunks hundreds of times more slowly.
- Put `set_option Elab.async false` in campaign modules. With asynchronous
  elaboration the kernel memory of every theorem in a module is retained
  until the module ends: 8 theorems at 10^10 peaked at 7.2 GB instead of
  1.5 GB.

`RSBounds/PsiFinite/Gen.lean` is a compiled twin (`runSegG`). It counts primes
with a byte sieve and applies the same `blockStep`. It is untrusted: it only
proposes the outputs that the kernel then recomputes.

### Soundness (Mathlib modules)

| module | content |
|---|---|
| `Bits` | `testBit_repK`, `combK_testBit`, `startPos_spec`, `sieveK_fst_testBit`, `primeBits_testBit` (bit i < L survives ⇔ lo+2i prime) |
| `Swar` | fields, no-carry addition, `swarK_fld`, `swarK_block` |
| `Pows` | `powsK_spec`, `sieveK_snd_spec` (the prime-power list, pairwise distinct) |
| `LogBounds` | `logInc_bounds`, from `TernaryGoldbach.Prelim.RamPf.log_one_add_inv_bounds` |
| `Block` | `blockStep_sound` (via `psi_block_abs_le_of_guards`) |
| `Segment` | `checkSegK_sound`, `seg_chain` |
| `BaseCert` | `baseFacts`: `basePrimes` is exactly the odd primes ≤ 99991, checked by kernel sieve, ~3 s |
| `SmallWalk`, `SmallWalkData`, `SmallRange` | the walk n = 1…10^4 (reuses `LogWalk.incr_bounds` and `MertWalk.lamB_spec`), with guard k = 1 below 1500 and 4/5 from 1500; ten kernel chunks, 52 s |
| `Campaign/E6/M0, M1` | 8 segments 10^4 → 10^6, no Mathlib, `decide +kernel`, 46 s |
| `Campaign/E6/Assembly`, `E6Check` | the chain and the phase C theorem |

The walk's state at 10^4 agrees digit for digit with TernaryGoldbach's
independent `MertWalk.inv_10000`.

## Phase A: planner (`tools/psi_planner/psi_planner.c`)

The planner is derived from `reference/psisieve.c`. It walks exactly the
generator's segments and picks the largest block exponent `w` for which a
floating-point model of the Lean enclosures passes both guards with slack
≥ 1. It also caps the block length at `c·√lo + 16`, with `c = 0.03` below
1.3·10^8 and `0.15` above.

The cap is necessary. The enclosure width grows like `c√x/log x`. Greedy
maximal blocks made the plan fail at 1.0985·10^8 even with `w = 0`.

Cross-check with `reference/results.txt` (run to N = 10^10 from A0 = 10^4):

| quantity | planner | expected |
|---|---|---|
| odd primes in (10^4, 10^10] | 455,051,282 | π(10^10) − π(10^4) = 455,052,511 − 1229 ✓ |
| proper prime powers in (10^4, 10^10] | 10,033 | 10,084 − 51 ✓ |
| ψ(10^10) − 10^10 | 42,119.8335 | 42,119.8335 ✓ |
| ψ(10^6) − 10^6 | −413.4025 | independent Python fsum: −413.4025 ✓ |

Plan with 2^18-bit segments: 19,074 segments, 2.73·10^6 blocks. The smallest
slack in (10^8, 1.2·10^8) is 32.4, in 64-number blocks.

Commands:

    gcc -O2 -march=native -o psi_planner tools/psi_planner/psi_planner.c -lm
    ./psi_planner 10000000000 10000 10013.396693263160 10013.396693262983 18 plan.txt

The generator `tools/psi_planner/GenCampaign.lean` reads such a plan. It
lowers `w` when the exact twin rejects a segment, and writes the Mathlib-free
campaign modules and the assembly. It produced `Campaign/E6` (greedy, no
plan file). Running it under the interpreter costs about 0.2 s per segment.

## Phase D: benchmark gate

Machine: Harald's laptop, `nice -n 19 taskset -c 0-5`, with the zeta-zero
certification running alongside (three Lean processes of ~3.5 GB). The times
are therefore somewhat noisy.

Method: `/usr/bin/time -v lake env lean <file>`, one `checkSegK` theorem per
file, produced by `tools/psi_planner/GenBench.lean`. The guard constant is
10^6/1 and the input state is zero, so that the guards pass. Apart from the
guard values the kernel does the same work as in the campaign: same sieve,
SWAR, block loop and arithmetic. `w` is the planner's value at that point.

Baseline (same import, no theorem): 0.65–0.96 s user, 0.81 GB max RSS.

| lo | w | 2^16 bits: user s / RSS GB | 2^17 | 2^18 | 2^19 |
|---|---|---|---|---|---|
| 1,058,577 | 4 | 3.2 / 0.85 | 6.4 / 1.54 | 16.4 / 3.78 | |
| 10,495,761 | 5 | 1.4 / 0.81 | 2.1 / 0.85 | 4.4 / 1.43 | |
| 109,586,193 | 5 | 1.3 / 0.81 | 2.1 / 0.92 | 3.9 / 1.46 | |
| 109,061,905 | 7 | 0.9 / 0.81 | 1.5 / 0.81 | 1.6 / 0.99 | |
| 1,000,351,505 | 11 | 1.1 / 0.81 | 1.2 / 0.95 | 1.6 / 1.39 | |
| 5,000,144,657 | 12 | 1.5 / 0.93 | 1.9 / 1.30 | 2.5 / 2.17 | |
| 9,999,230,737 | 12 | 2.2 / 1.10 | 2.2 / 1.54 | 2.7 / 2.67 | 3.7 / 5.04 (lo 9,998,951,425) |

Eight 2^17 theorems at 10^10 in one module, with `Elab.async false`: 13.1 s
user, 1.53 GB.

Observations:

* Near 10^10, cost per segment ≈ 0.26 s + 1.7·10^-4 s × π(√hi) at 2^18, plus
  0.2–0.3 ms per block. Memory grows with π(√hi)·L.
* Below ~10^7 every block scans the segment's whole prime-power list, so cost
  grows with L². There I will use 2^16-bit segments: about 80 segments,
  ~0.1 CPU-h.

### Extrapolation to 10^10

The cost model, summed over the actual plan segments:

| layout | segments | kernel CPU | other CPU | total | peak RSS / process |
|---|---|---|---|---|---|
| 2^18 bits (2^16 below 10^7) | 19,074 | 7.5 h | ~0.6 h | **≈ 8 CPU-h** | 2.7 GB (at 10^10) |
| 2^17 bits (2^16 below 10^7) | 38,147 | 12.5 h | ~0.7 h | **≈ 13 CPU-h** | 1.5 GB |

"Other" covers module start-up and assembly. Assembly is about 0.05 s per
segment, in Mathlib modules that each take ~6 s to load. Mathlib modules show
6.7 GB of RSS, but that is the memory-mapped `.olean` files, shared between
processes.

Wall time on 6 cores: 2^17 with 6 jobs is ≈ 2.2 h at ≤ 9.2 GB in total. 2^18
with 4 jobs is ≈ 2 h at ≤ 10.7 GB. Both are under 24 CPU-hours and 8 GB per
process.

Generated source: about 250 bytes per segment theorem, plus about 200 per
assembly step. That is ≈ 9 MB at 2^18 and ≈ 17 MB at 2^17.

### Extrapolation to 5·10^10 (stretch goal, not planned)

This needs base primes up to 223,607 (19,909 odd primes, and a new
certification). Cost is about **70 CPU-h** at 2^18, with ~5.5 GB per process
near 5·10^10, or about 116 CPU-h at 2^17. That exceeds the 24 CPU-hour limit,
so it would need a faster sieve first: for example a 6k±1 wheel (1/3 of the
bits instead of 1/2), and fewer kernel steps per prime.

## Phase E: campaign

Layout: 2^16-bit segments below 10^7, 2^17 above (Harald's choice at the
gate). Plan and generation (scratch paths abbreviated as `$P`):

    gcc -O2 -march=native -o $P/psi_planner tools/psi_planner/psi_planner.c -lm
    $P/psi_planner 10000000000 10000 10013.396693263160 10013.396693262983 17 $P/planT1.txt \
        0.8 1.0 0.03 1.3e8 0.15 16 10000000
    lake build psi_gen
    .lake/build/bin/psi_gen T1 10001 10000000000 17 40 \
        10013396693262983521053440538486993 10013396693263160145856910841316409 \
        9210340371976077481578637322766 9210340371976219110227839171900 \
        $P/planT1.txt 16 10000000 1000

The four numbers are `stTenK` (`SmallRange.lean`), the walk's enclosures of
`D·ψ(10^4)` and `D·log 10^4`. The compiled generator (`lean_exe psi_gen`,
added to `lakefile.lean`) took about 2 minutes. The exact twin accepted every
planned `w`: 0 retries.

Result: 38,186 segments (w from 2 to 12; 26,813 segments at w = 12), in 955
Mathlib-free modules `Campaign/T1/M0..M954` of 40 theorems each, 39 assembly
modules `Campaign/T1/Asm/G0..G38` of 1000 segments each, and
`Campaign/T1/Assembly.lean`. The segments used are in
`Campaign/T1/segments.txt` (`lo w B`). Generated source: 32.6 MB (M: 15.7 MB,
Asm: 16.8 MB).

End state at 10^10, scale D = 10^30:

    ψ(10^10) ∈ [10000041663.657…, 10000042576.031…]

so the kernel enclosure of ψ(10^10) − 10^10 is [41,663.66, 42,576.03]; the
reference value is 42,119.83.

Assembly: `Chain.lean` defines `Step a s b t := Encl a s → Encl b t ∧ BoundOn 4 5 a b`
and `Step.comp`. Each `Asm/G<g>` has one theorem `st<i>` per segment
(`step_of_seg baseFacts seg<i> rfl rfl (by decide)`), chunks of 40 composed
steps and a group theorem; `Assembly.chain : Step 10000 stTenK 10^10 ⟨…⟩`. A
first version, one tactic proof per group, ran into the heartbeat limit
(context growing with each step).

## Phase F: build

All under `nice -n 19 taskset -c 0-5`, with the zeta-zero certification
running alongside.

| step | wall | CPU | peak RSS / process |
|---|---|---|---|
| M0..M954 (`tools/psi_planner/build_campaign.sh T1 955 <log> 6 9`) | 4 h 25 min | 24.3 h user + 0.5 h sys | 5.3 GB |
| Asm/G0..G38, 6 per `lake build` | 4 min 12 s | 0.3 h | 6.9 GB (mostly mmapped Mathlib) |
| Assembly, Final | 10 s | | 7.0 GB (same) |
| audit | 4 s | | |

Logs: `verification/psi-finite-campaign/build-M.log` (160 batches, all status
0), `build-M.time`, `build-Asm.log`.

The module build cost about 1.9× the gate's estimate of ≈ 13 CPU-h. Per
module (40 segments) the kernel took 85–125 s, rising with x, against the
≈ 50–90 s implied by the single-theorem benchmarks. The concurrent zeta-zero
job and the per-module overhead may account for part of it; I did not isolate
the cause.

Hashes: `verification/psi-finite-campaign/T1-sha256.txt` lists the SHA-256 of
all 996 generated files (`*.lean`, `segments.txt`) relative to
`Campaign/T1`; the SHA-256 of that list is
`0331653addba5ac169a789982058e517bf6b06032b9f034854aec1472848c2ce`.

## Phase G: Comparator

Lean 4.35's native Comparator, sandboxed with bubblewrap (never with
`--inadvisably-no-sandbox`), at commit `23b8bc9` (PsiFinite sources identical
to `ca08607`).

* Challenge `comparator/PsiFiniteChallenge.lean`: imports only Mathlib and
  states both theorems with `sorry`. Solution `comparator/PsiFiniteSolution.lean`:
  `import RSBounds.PsiFinite.Final`. Config `comparator-psi-finite.json`:
  the two theorem names; permitted axioms `propext`, `Classical.choice`,
  `Quot.sound`.
* Exports (`leanexport`, roots as in `verification/RS75ZeroFreeIndependentCheck.md`):

  | export | bytes | SHA-256 |
  |---|---|---|
  | challenge | 68,768,385 | `2a8d33fde025e1defe63198e4afe01a4793bd33dee2790ba6e85f2e8c65f9423` |
  | solution | 329,500,827 | `29a61d005a43d72b954f58f09f81c4c0fbb064f894f77b8a7b88dfd9dc7598a5` |

* Result (`verification/psi-finite-campaign/comparator.out`): "Lean default
  kernel accepts the solution", "Your solution is okay!", exit code 0.
* Time: 20 h 32 min wall, 8 Nov 08:51 to 9 Nov 05:23, on one core at nice 19
  beside other heavy jobs; this includes a 16-minute suspend and a 70-minute
  pause (SIGSTOP) while the machine was overloaded. Kernel replay ≈ 18 CPU-h.
  Peak resident memory of `leanchecker` ≈ 1.4 GB (sampled every 10–15 min).
* Ubuntu 24.04 restricts unprivileged user namespaces, so bubblewrap needed an
  AppArmor profile for `/usr/bin/bwrap` (`userns,`); without it the run fails
  at once with `bwrap: loopback: Failed RTM_NEWADDR`, reported misleadingly as
  "Lean default kernel rejected the solution". The run could not be started
  from inside Claude Code's own command sandbox; Harald started it.

Reproduce, from `Projects/RSBounds`, after `lake build RSBounds.PsiFinite.Final`:

```sh
O=/tmp/psicmp; mkdir -p $O
for m in PsiFiniteChallenge PsiFiniteSolution; do
  lake env lean -R comparator -o $O/$m.olean comparator/$m.lean
done
ROOTS="Quot Quot.mk Quot.lift Quot.ind PsiFinite.psi_abs_sub_le_four_fifths_sqrt \
  PsiFinite.psi_abs_sub_le_sqrt propext Classical.choice Quot.sound Nat.add Nat.sub \
  Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor \
  Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String \
  String.mk Char optParam autoParam semiOutParam outParam"
for m in PsiFiniteChallenge PsiFiniteSolution; do
  lake env bash -c "LEAN_PATH=$O:\$LEAN_PATH leanexport $m -- $ROOTS" > $O/$m.export
done
sha256sum $O/*.export
ulimit -s unlimited
lake comparator --config comparator-psi-finite.json \
  --challenge-from-export $O/PsiFiniteChallenge.export \
  --solution-from-export $O/PsiFiniteSolution.export
```

## Büthe (6.2) on [100, 10^10]

`RSBounds/PsiFinite/Buthe.lean`, axioms `propext`, `Classical.choice`,
`Quot.sound` only:

```lean
theorem PsiFinite.buthe_eq_6_2_le_1e10 {t : ℝ} (h₁ : 100 ≤ t) (h₂ : t ≤ 10 ^ 10) :
    -0.8 ≤ (t - Chebyshev.psi t) / Real.sqrt t ∧
      (t - Chebyshev.psi t) / Real.sqrt t ≤ 0.81
```

This is Büthe, Math. Comp. 87 (2018), eq. (6.2), i.e. IEANTN
`ButheNumerics.v1.eq_6_2`, with the range cut from 5·10^10 down to 10^10.
The audit file restates it in IEANTN's form (`∀ t : ℝ, 100 ≤ t → t ≤ 10 ^ (10 : ℕ) → …`).

* [1500, 10^10]: from T1.
* [100, 1500): `walkBK`, the small walk of `SmallWalk` (same `pstep`, same
  `WInv`) with asymmetric guards `ψ(n) − n ≤ (4/5)√n` and
  `n + 1 − ψ(n) ≤ (81/100)√(n+1)` for 100 ≤ n < 1500; one `decide +kernel`
  theorem (`walkB_ok`; the whole file takes 25 s of CPU time). `gap_two_sided` is the one-gap lemma with
  separate upper and lower constants.

The module builds in about 70 s (mostly the Mathlib import). It is not covered by
the Comparator run of phase G; a Comparator run for it would replay the whole
campaign again (≈ 18 CPU-h), since it depends on T1.

## Not done

* Independent kernels (`--paranoid`: nanoda, lean4lean, …) were not run;
  nanoda needed more than 28 GB on the comparable RS75 export.
* (6.2) on (10^10, 5·10^10]: only on request; see the extrapolation above (≈ 70+
  CPU-h with the present sieve, so it would need a faster sieve first).
* The deprecation and unused-tactic warnings in the PsiFinite modules were fixed
  after the campaign (`if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
  `cond_true` → `Bool.cond_true`, `push_neg` → `push Not`). `Kernel.lean`
  was not touched, so the 955 campaign modules were not rebuilt; the rest
  rebuilt in a few minutes and the audit output is unchanged. Remaining: three
  notices that `Bits.lean` imports Mathlib, which uses the module system,
  without `module`. Switching to the module system would need changes beyond
  this project's conventions, so I left it.

## Reproduce

    cd Projects/RSBounds
    (cd RSBounds/PsiFinite/Campaign/T1 && find . -type f \( -name '*.lean' -o -name '*.txt' \) \
        | LC_ALL=C sort | xargs sha256sum) | diff - verification/psi-finite-campaign/T1-sha256.txt
    tools/psi_planner/build_campaign.sh T1 955 /tmp/build-M.log 6 9   # ≈ 25 CPU-h; or simply:
    lake build RSBounds.PsiFinite.Final
    lake env lean verification/PsiFiniteCheckAudit.lean

An independent checker needs only the last two commands (the first build does
everything, ~25 CPU-h, ~5.3 GB per job plus mmapped Mathlib). The planner and
generator are untrusted and need not be rerun; rerunning them with the
commands of phase E reproduces the files byte for byte (checked once for the
M modules).
