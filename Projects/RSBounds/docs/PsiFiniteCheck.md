# Kernel-checked |ψ(x) − x| ≤ (4/5)√x on [1500, 10^10]: record

Status on 7 November 2026, branch `psi-finite-check` (from
`rs-bounds-progress-2026-11-06` at `24554b9`). Phases A–D of
`PsiCert-Claude-Handoff/CLAUDE_HANDOFF.md` are done. **The campaign (phase E)
has not been started**; it waits for Harald's go-ahead after the benchmark
gate below.

Proved so far, kernel-checked, axioms `propext`, `Classical.choice`,
`Quot.sound` only:

```lean
theorem PsiFinite.psi_abs_sub_le_four_fifths_sqrt_le_1e6 {x : ℝ}
    (h₁ : 1500 ≤ x) (h₂ : x ≤ 10 ^ 6) :
    |Chebyshev.psi x - x| ≤ (4 / 5 : ℝ) * Real.sqrt x      -- RSBounds/PsiFinite/E6Check.lean
theorem PsiFinite.small_sqrt {x : ℝ} (h1 : 8 ≤ x) (h2 : x < 10000) :
    |Chebyshev.psi x - x| ≤ Real.sqrt x                     -- RSBounds/PsiFinite/SmallRange.lean
```

`psi_abs_sub_le_four_fifths_sqrt_le_1e6` is the phase C target: T1 restricted
to [1500, 10^6]. It uses every component of the final proof.

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

## Not done

* Phase E (campaign) and phase F (T1, T2, audit file): waiting for approval.
* The generator runs interpreted (`lake env lean --run`), about 1 h for the
  full plan. A `lean_exe` target in `lakefile.lean` would make it much faster
  (one added target; nothing existing changes).
* Comparator (phase G): only on request.

## Reproduce (current state)

    cd Projects/RSBounds
    lake build RSBounds.PsiFinite.E6Check          # phases B–C
    lake env lean <file with: import RSBounds.PsiFinite.E6Check
                   #print axioms PsiFinite.psi_abs_sub_le_four_fifths_sqrt_le_1e6>
    lake env lean --run tools/psi_planner/GenBench.lean <dir>   # gate files
