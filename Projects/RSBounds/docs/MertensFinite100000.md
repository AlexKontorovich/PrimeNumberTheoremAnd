# Exact finite weighted-prime Mertens certificates

This is the finite part of the original Rosser–Schoenfeld weighted-prime
lower bound (RS62, equation (3.21)):

\[
\sum_{p\le x}\frac{\log p}{p}
>\log x+E-\frac1{2\log x},\qquad 1<x\le100000,
\]

with the exact constant `Goals.mertensE`, not a redefined finite constant.
It is distinct from the previously replayed finite **prime-product**
certificate in `SmallMertensProd.lean`.

## Proof components

* `MertensFiniteScalars.lean` proves `E < -1.3` from Euler's constant and
  ten prime terms, then proves a real-interval block reduction. Its fresh
  source check and four standard-axiom audits passed; see
  `verification/mertens-finite-scalars-run.json`.
* `MertensFiniteWalk.lean` proves the soundness of a three-integer walk.
  It reuses `LogWalk.incr_bounds`, `LogWalk.floor_div_bounds`, and
  `MertProd.isP_iff`. The latter is a complete trial-division checker, with
  no limited validity range. The argument for `1 < x ≤ 2` is separate;
  all remaining real points are covered by their integer interval. Its
  fresh-source check and all seven standard-axiom audits passed. The source
  SHA256 is
  `a5d401a75cd26f410897cdbdcdff5e18456416b3615dbcd8b301b73a842b42a8`.
* `MertensFinite100000.lean` contains 101 exact witness equalities, each
  proved with `decide +kernel`, and a final real-variable theorem
  `MertensFiniteWalk.mertens_lower_le_100000`. Its fresh-source replay
  completed successfully on 2026-11-06 in 622.54 seconds, including all
  five transitive axiom audits. The source SHA256 is
  `12dcadb5808237ae8fdcafa7ec277d18ee1669f096847c706dccbe9fb492f911`.
  The two audited individual walk equalities depend only on `propext`;
  the final invariant and real-variable conclusions use only `propext`,
  `Classical.choice`, and `Quot.sound`.

The walk scale is the exact integer `D=10^30`. At the start of a step `n`,
its state means

\[
L_{lo}\le D\log n\le L_{hi},\qquad
S_{lo}\le D\sum_{p\le n}\frac{\log p}{p}.
\]

For `H = Lhi + incrHi n`, the comparison

\[
20H^2<20H S_{lo}+26DH+10D^2
\]

certifies

\[
\log(n+1)-1.3-\frac1{2\log(n+1)}
<\sum_{p\le n}\frac{\log p}{p}.
\]

The left main term is increasing for arguments greater than one, and the
prime sum is nondecreasing. Hence this covers the entire real block
`[n,n+1]`, including its endpoints. Running through the state at 100001
therefore includes the requested closed endpoint 100000.

## Readable witness data

`verification/mertens-finite-100000-witnesses.json` records the scale,
state convention, interval comparison, generator hash, Lean source hash,
and all 101 start/end states. The matching CSV is
`verification/mertens-finite-100000-witnesses.csv`.
Large state fields are exact decimal integers; JSON encodes them as
strings so a reader cannot silently lose precision in floating point.

`verification/gen_mertens_finite_100000.py` is an untrusted witness
producer. Its exact-integer checks passed; the subsequent Lean kernel
replay also passed. The successful fresh-source receipt
`verification/mertens-finite-100000-run.json` records the standard axiom
audit and matching source, generator, JSON, CSV, audit, and runner hashes.
The generic walk has its own receipt
`verification/mertens-finite-walk-run.json`. The readable witness files
retain their explicit distinction between generation checks and the
formal replay, pointing to this receipt for the latter.

The finite conclusion is unconditional. No RH verification, Büthe result,
Ramaré Möbius-sum estimate, or prime-number asymptotic is an input. A global
Mertens result still needs a separately proved analytic tail above the
finite range. The exported `mertensLower_of_tail` makes this dependency
explicit and returns `Goals.MertensLower` once the same inequality is
supplied for every real `x ≥ 100000`.
