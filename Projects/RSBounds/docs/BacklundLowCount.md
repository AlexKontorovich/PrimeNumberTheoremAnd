# Finite zero-count handoff through height 100

The checked theorem concerns the actual inclusive count, including analytic multiplicities:

\[
  |N_{\leq}(T)-F(T)|<1\qquad(0\leq T\leq100),
\]
where \(F(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}-\frac{T}{2\pi}+7/8\).
The right side is strictly below
\(0.137\log T+0.443\log\log T+1.588\) whenever \(T\geq2\).

The public reusable theorem is
`Rosser1941.zero_count_error_lt_one_to_100`, using the shared
`Rosser1941.positiveZeroCount` definition and an explicit formula for
the main term. This finite certificate establishes the range through
100 only; it makes no claim for the stronger range through 280.

The modules have the following distinct responsibilities.

* `BacklundLowMainTerm`: elementary monotonicity of \(F\) above \(2\pi\),
  the global lower bound \(F\geq-1/8\), the bound \(F<1\) through 14.13,
  and the error-envelope lower bound.
* `BacklundLowCountGeneric`: a generic finite ordered-list argument. Its
  count includes a listed point exactly at the threshold. If the \(i\)-th
  listed point has \(i<F<i+1\), the two adjacent points enclose the error
  strictly between \(-1\) and \(1\). The first and final intervals use
  separate endpoint estimates.
* `BacklundLowZeros`: retains the actual zero witnesses from the 29 public
  interval certificates in `RHHeight100.TwentyNineZeros`, and applies the
  exact rational logarithm checks from `BacklundLowScalarData` to both
  endpoints of each bracket.
* `BacklundLowCount`: uses `BacklundRH100Bridge` to prove the listed 29
  distinct zeros exhaust the closed set below 100, and simplicity to
  identify cardinality with analytic multiplicity. It then applies the
  generic finite argument to the actual count.

The height-100 input is a theorem proved in the replayed public source
`teal-sea/zeta-lab@b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, not an RH
hypothesis. Its exact completeness and simplicity exports are
`RHHeight100.zero_count_hundred` and `RHHeight100.rh_height_hundred`.
The bracket witnesses and the completeness proof are independent: the
interval certificates alone would not exclude further zeros.

The numerical diagnostic values in `vendor/rh100/zero-brackets.json` do
not occur in the Lean argument. All scalar enclosures used in the proof
come from rational certificates checked by the Lean kernel.

All four modules compiled under Lean 4.35.0. The twelve audited exports,
including the public theorem, use exactly `propext`, `Classical.choice`,
and `Quot.sound`. Fresh source hashes, build results, and the axiom audit
are recorded in `verification/backlund-low-count-run.json`.
