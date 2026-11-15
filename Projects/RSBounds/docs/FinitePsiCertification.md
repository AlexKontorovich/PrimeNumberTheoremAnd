# Finite square-root error for psi: feasibility and reusable code

The target is the unconditional statement

\[
1500\le x\le10^{10}\quad\Longrightarrow\quad
|\psi(x)-x|\le\tfrac45\sqrt{x}.
\]

This target is **not proved in this project yet**. No complete computation
through 10^10 has been run here. The reusable
[prime-power endpoint reduction](../RSBounds/PsiSieveEndpointReduction.lean)
is now proved: directed integer guards and actual psi enclosures on a gap
imply the bound at every real point in that gap. All ten declarations pass
the standard-three-axiom audit; see the
[receipt](../verification/psi-sieve-endpoint-run.json). The integer
normalization proof adapts attested-compute with its MIT notice retained.
The finite integer-cover transfer and actual terminal check are also proved.
Complete gap coverage and numerical enclosures remain to be supplied by
the finite computation.

The stronger [block reduction](../RSBounds/PsiSieveBlockReduction.lean) is
also proved and passes three standard-axiom audits. For any positive block
endpoints a<=b, it suffices to certify

\[
\psi(b)-a\le\tfrac45\sqrt a,\qquad
b-\psi(a)\le\tfrac45\sqrt b.
\]

Monotonicity then proves the desired bound for every real x in [a,b], with
no prime-power-free hypothesis and no check at each internal jump. There
are generic rational fixed-point guards as well as the 4/5 specialization;
see the [block receipt](../verification/psi-sieve-block-run.json).

The 400 MiB estimate sometimes associated with 10^10 describes PrimeCert's
current global wheel bitset only. It is not a memory requirement for a
streaming segmented calculation. The intended computation retains one
segment, the small base-prime roster through 10^5, and running psi enclosures.
Kernel reduction and proof construction must be arranged to avoid retaining
all intermediate segment states; that implementation has not been benchmarked.

The original paper statement is Ramaré,
*Explicit estimates for the summatory function of Λ(n)/n from the one of
Λ(n)*, Acta Arith. 159 (2013), equation (3.2), p. 116,
[DOI](https://doi.org/10.4064/aa159-2-2),
[primary PDF](https://www.impan.pl/shop/en/publication/transaction/download/product/82334).

## Existing formalizations inspected

* [PrimeCert's sieve correctness](https://github.com/b-mehta/PrimeCert/blob/d84a15cacfdc45ae1e96e56dd58158f871787870/PrimeCert/SieveCorrect.lean)
  proves `sieveK_testBit_iff`: the surviving bits represent exactly the primes
  coprime to 6. `isSieve_of_sieveK_eq` packages a checked sieve output, with a
  size cap of 12884901888, which includes the desired bound. The separate
  primes 2 and 3 must be included by the consumer.
* [The 10^8 test](https://github.com/b-mehta/PrimeCert/blob/d84a15cacfdc45ae1e96e56dd58158f871787870/PrimeCertTest/SieveVerify1e8.lean)
  calls `run_sieve 100000000`. The
  [exact-commit upstream CI](https://github.com/b-mehta/PrimeCert/actions/runs/42196032084/job/127819389276)
  reports this module built in 20 seconds. This is upstream evidence, not a
  local replay or a timing prediction for a psi computation. The implementation
  uses a global Nat bitset and checked intermediate batch equalities. It is not
  a segmented bounded-memory sieve. It uses Lean 4.36.0-rc2, so integration
  with this project's 4.35 toolchain needs a compatibility check.
* [calr's SmallMertensLower](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Prelim/SmallMertensLower.lean)
  provides `PPL_complete`, `lamB_spec`, `Inv_step`, and `walkM_spec`: a
  complete small prime-power table and directed fixed-point accumulation of
  actual von Mangoldt sums through 10002. Its trial-division enumeration is
  not the proposed large-range algorithm; the arithmetic invariants are useful.
* [IEANTN's ButheNumerics metadata](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/IEANTN/Nodes/ButheNumerics/v1/formalization.yaml)
  records the related asymmetric bound
  `-0.8 <= (t-psi(t))/sqrt(t) <= 0.81` on `[100,5e10]`, but explicitly marks
  the node `status: stub`. Its challenge has `sorry`. It is not a completed
  finite certificate.
* [attested-compute's prime-power framework](https://github.com/gersh/attested-compute/blob/028462066f8537e3b90fcd83c32194f1cd526e46/SparkInterval/TernaryGoldbach/PsiPrimePowerCertificate.lean)
  has a useful implication `sourceClaim_of_gap_evidence`, with explicit
  coverage, state, directed-log and endpoint premises. Those premises are
  not discharged by a closed 10^10 computation there. The separate registered
  computation route uses `accepted_run_certificate_sound`; that route is not
  an ordinary kernel-checked finite calculation.

No completed proof of the exact target was found in these inspected sources.

## Endpoint reduction

For a constant nonnegative value C, the function

\[
g_C(x)=\frac{C-x}{\sqrt{x}}
\]

is decreasing on the positive real axis: its derivative is
`-(C+x)/(2*x^(3/2))`. Consequently, on each prime-power gap the upper
error is controlled at the left endpoint and the lower error at the right
left-limit. At a prime power n it suffices to check

\[
\psi(n)-n\le\tfrac45\sqrt n,\qquad
n-\psi(n-1)\le\tfrac45\sqrt n.
\]

The second comparison uses n, not n-1. The initial and terminal truncated
gaps must also be covered, including the actual value at 10^10. Each event
`n=p^k` adds `log p` once, regardless of k. Proper prime powers can be
generated from primes at most 10^5 and merged with the segmented prime stream.

## Exact arithmetic interface

Maintain certified integer numerators l,u with `l/D <= psi <= u/D`.
The two directed tests can use integers only:

\[
25\max(u-Dn,0)^2\le16nD^2,\qquad
25\max(Dn-l,0)^2\le16nD^2.
\]

Here u refers to the post-jump upper sum and l to the pre-jump lower sum.
No square-root approximation is required. Integer differences must be signed
or explicitly use the displayed positive part; silent unsigned wraparound is
not permitted.

If each log enclosure has width at most 1/D, there are at most 10^10 events,
so total enclosure width is at most 10^10/D. For D=2^64 this is less than
5.5e-10. Establishing such log enclosures efficiently is an implementation
obligation, not an assumption to insert into the final theorem. The endpoint
squares exceed 128-bit capacity at this scale; arbitrary precision or proved
wider arithmetic is needed.

## Work remaining

1. Reuse the sieve marking invariants in a proved segmented enumerator,
   starting with the certified base-prime list through 10^5.
2. Prove complete ordered prime-power merging and exact block handoffs.
3. Connect directed logarithm arithmetic and the two endpoint tests to the
   actual Chebyshev psi function.
4. Benchmark kernel verification, generated proof size, and memory on a
   representative block before attempting the full run.
5. Check all blocks and assemble the real-variable theorem, with a final
   transitive axiom audit and independent Comparator statement.

The sieve arithmetic is near-linear up to logarithmic factors in a standard
segmented implementation. This alone does not establish near-linear Lean
verification time: logarithm certification, kernel reduction, and retained
proof data must be measured. The existing 10^8 sieve test is encouraging,
but no full-runtime estimate is claimed here.
