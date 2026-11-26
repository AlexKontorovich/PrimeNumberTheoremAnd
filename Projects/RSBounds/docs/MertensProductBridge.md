# From the signed Mertens error to the actual prime product

Status: **fresh source check and all three transitive axiom audits passed**
on 2026-11-06. The footprints contain only `propext`, `Classical.choice`,
and `Quot.sound`. Source SHA256:
`eeb5bf305c99222533ce25175dc9db3b2956befb189d02f1247824ae14774c41`.

`MertensProductBridge.log_primeProduct_le` binds the existing signed-error
identity and the elementary prime-power correction to
`Totient.primeProduct n`. Its hypotheses are explicit:

* `n ≥ 100000`;
* `|ψ(n)−n| ≤ e n`;
* `|J(u)| ≤ j` for every real `u ≥ n`.

Here `J` is the actual signed-tail function from `MertensSecondSigned`,
not a newly introduced error variable. With `L = log n`, the conclusion is

\[
\log\prod_{p\le n}\frac p{p-1}
\le \gamma+\log L+\frac eL
+2j\left(\frac1L+\frac1{L^2}\right)
+\frac{5.6}{\sqrt n\,L}.
\]

The second public theorem, `primeProduct_lt_of_errors`, additionally takes
the concrete scalar inequality

\[
\frac eL+2j\left(\frac1L+\frac1{L^2}\right)
+\frac{5.6}{\sqrt n\,L}
<\log\left(1+\frac1{2L^2}\right).
\]

It concludes

\[
\prod_{p\le n}\frac p{p-1}
<e^\gamma\left(L+\frac1{2L}\right).
\]

The Euler constant is the actual `Real.eulerMascheroniConstant`: the proof
uses the existing `PNTMertens.γ.eq_eulerMascheroni` normalization explicitly.
The bridge proves an implication from the stated error estimates and
budget; it does not claim these estimates or the global totient inequality
without their separate proofs.

The exact-source runner is `verification/run_mertens_product_bridge_check.py`.
Its receipt is `verification/mertens-product-bridge-run.json`, and the three
audited declarations are listed in `verification/MertensProductBridgeAudit.lean`.
