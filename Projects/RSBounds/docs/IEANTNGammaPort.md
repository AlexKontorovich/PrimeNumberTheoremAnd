# IEANTN Gauss-series reuse

The eight modules in `RSBounds/IEANTNGamma/` are vendored from
[`teorth/IEANTN`, commit `466b41b28ecc224398cf53a99c5fe9618131398b`](https://github.com/teorth/IEANTN/tree/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/GammaAsymptotics.v2).
The original author and Apache 2.0 headers are retained. The license is copied
to `licenses/IEANTN-LICENSE` and beside the vendored sources.

The original proof is reused; this is not a new derivation of the Gauss
representation. The adaptation changes only local import paths in the eight
vendored modules; their proof bodies compile unchanged.
Original and initially adapted hashes are recorded in
`verification/ieantn-gamma-provenance.json`.

The dependency closure is:

- `Analytic` imports `RealIdentity`.
- `RealIdentity` imports `Oscillation` and `Periodic`.
- `Oscillation` imports `Recurrence` and `ComplexToReal`.
- `Recurrence` imports `GaussSeries`.
- `ComplexToReal` imports `RealAsymptotic`.
- `GaussSeries`, `Periodic`, and `RealAsymptotic` import only Mathlib.

The public wrapper `RSBounds/IEANTNDigamma.lean` states the Gauss series and
its summability for `Re(s)>0`. No IEANTN challenge or unproved node conclusion
is imported. This is an ingredient for the sharp gamma estimates; it does not
assert the RS75 zero-free region or its sharp digamma remainder.

Fresh verification on Lean 4.35.0 passed on 2026-11-06:

- `lake build RSBounds.IEANTNDigamma` exited 0.
- `lake env lean verification/IEANTNDigammaAudit.lean` exited 0.
- The Gauss-series theorem, real digamma error bound, real-to-complex digamma
  identity, and both wrapper theorems have only `propext`, `Classical.choice`,
  and `Quot.sound` in their printed axiom sets.

The exact commands, timestamps, source hashes, and exit codes are in
`verification/ieantn-gamma-run.json`; the complete output is in
`verification/ieantn-gamma-build.log` and
`verification/ieantn-gamma-axioms.log`. The reproducible runner is
`verification/run_ieantn_gamma_check.py`.

The upstream package also has a Comparator receipt on its own Lean
4.34.0-rc2 toolchain. The fresh local check above independently verifies this
adaptation; it is not a new receipt for the full upstream asymptotic node.
