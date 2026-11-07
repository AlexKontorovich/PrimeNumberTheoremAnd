# Checked improper signed Mertens tail

`RSBounds/MertensSignedLimit.lean` has passed its exact-source build and all
five transitive axiom audits, using only `propext`, `Classical.choice`, and
`Quot.sound`.

For every real \(a\ge1\), the actual improper signed integral exists:

\[
\lim_{b\to\infty}\int_a^b\frac{\psi(t)-t}{t^2}\,dt
=\operatorname{Re} I(a),\qquad
I(a)=P(a)+F(a)-\frac{\log(2\pi)}a.
\]

Here `P` is the checked absolutely convergent series over actual nonreal zeta
zeros with their analytic multiplicities. `F` is the actual endpoint left-line
integral from `MertensEndpointLeft`. The theorem also proves `I(a).im = 0`.
There is no finite-RH, quantitative zero-free-region, or pointwise PNT premise.

The public results are `finite_integral_eq`,
`tendsto_signed_integral_complex`, `tendsto_signed_integral`,
`signedLimit_im_eq_zero`, and `norm_signedLimit_le`. The last gives

\[
|I(a)|\le |P(a)|+6000a^{-3/2}+\frac{\log(2\pi)}a.
\]

This is an improper-integral limit statement. This module does not assert
absolute integrability of the signed psi integrand on the infinite interval.
The separate normalized first-Mertens identity and numerical RS62 inequalities
have their own proof obligations and verification receipts.

Source SHA-256:
`00d70ff96edcca9e0fa937267b81c6c6ee90f40c0ebdcf00c0cd0c2a43aa3cd1`.

Receipt: `verification/mertens-signed-limit-run.json`.
Audit: `verification/MertensSignedLimitAudit.lean`.
Reproduce after sourcing `../lean-env.sh` with
`python3 verification/run_mertens_signed_limit_check.py`.
The failed first elaboration pass is retained separately; the current receipt
binds the exact successful source, input, log, and output object.
