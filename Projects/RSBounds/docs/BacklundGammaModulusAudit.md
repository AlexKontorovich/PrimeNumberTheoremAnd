# Backlund Gamma modulus proof

Current status: all five Gamma-modulus modules were freshly compiled on 2026-11-06, then all seven public endpoint declarations were audited. Every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The receipt is `verification/backlund-gamma-modulus-run.json`; its recorded end time is 11:53:11 UTC. The separate final zeta assembly was also freshly compiled and audited at 11:54:56 UTC; its receipt is `verification/backlund-left-zeta-boundary-run.json`.

The quantitative input is the actual proof of `TernaryGoldbach.RSBounds.BacklundZeta23.StirlingVert.digamma_stirling`, adapted from `Zeta23.StirlingVert.digamma_stirling` in `teal-sea/zeta-lab` at commit `b09fa4dd2f2182cf14b248e7ffc64ff03df2c534`, file `Zeta23/GammaFacts/StirlingVert.lean`. The port preserves the Apache 2.0 copyright notice and reuses only its `Seq` section. Its original series dependency has been replaced by two adapters to the already checked IEANTN Gauss series. No upstream analytic hypothesis is assumed.

The local port now uses the isolated namespace
`TernaryGoldbach.RSBounds.BacklundZeta23`, so it can be imported together
with the independently replayed RH100 certificate and its original
`Zeta23` declarations. This is a namespace-only adaptation: proof
derivations and the vendored numerical certificates are unchanged.
[The adaptation record](../verification/backlund-namespace-adaptation.json)
contains before/after hashes and confirms that reversing the namespace
replacement recovers each original file exactly. The affected 11-module
analytic closure and root aggregate were freshly rebuilt, then all 21
axiom checks passed, including a combined import of the high- and
low-height proofs. Every audited declaration has only the three standard
axioms. See the
[integration receipt](../verification/backlund-namespace-integration-run.json)
and [reproduction script](../verification/run_backlund_namespace_integration_check.py).
No RH100 numerical certificate module was rebuilt for this change.

The result is `‖ψ(w) − log w + 1/(2w)‖ ≤ 3/(Im w)²` whenever `Re w > 0` and `|Im w| ≥ 1/2`. Consequently, on `1/2 ≤ a ≤ 3/2`, `t ≥ 50`, the checked local chain proves:

* `|Re ψ(a+it) − log t| ≤ 9/(2t²)`;
* `|log |Γ(a+it)| − log |Γ(1+it)| − (a−1) log t| ≤ 9/(4t²)`;
* `|Γ(a+it)| ≤ |Γ(1+it)| t^(a−1) exp(9/(4t²))`.

The exact baseline Gamma reflection identity and the functional-equation algebra are developed separately in `BacklundGammaBaseline.lean` by the Gamma baseline owner. Their checked multiplier allowance is `exp(5/(2t²))`. The final theorem `BacklundLeftZetaBoundary.norm_zeta_left_strip_lt` now proves (77) unconditionally with only the three standard Lean axioms. This looser allowance than Backlund’s literal `1+1/(2t²)` gives exactly his final estimate, since

`exp(5/(2t²)) (log t − 0.048) < log t` for `t ≥ 50`.

Indeed `log t ≤ t/2`, hence `(5/(2t²)) log t ≤ 5/(4t) ≤ 0.025 < 0.048`, and `exp(−u) ≥ 1−u`. The explicit right-half-plane saving is the independent Backlund (54) formalization.

All pointwise estimates are unconditional. Source fingerprints and adaptation notes are recorded in `verification/backlund-gamma-modulus-source.json`. This adapted chain has now been compiled and its transitive axioms checked; see the separate verification receipt and axiom log.

The upstream Apache 2.0 license is retained at `licenses/Zeta23-Apache-2.0`; the port retains the upstream Anthropic PBC copyright notice and pinned source attribution.
