# Checked actual degree-two zero potential

`RSBounds/MertensZeroPotential.lean` has passed a fresh exact-source compilation
and all 17 transitive axiom audits. Every audited declaration uses only
`propext`, `Classical.choice`, and `Quot.sound`.

The indexing type consists of actual nonreal zeros of the Riemann zeta
function. Each term uses the natural analytic order of the actual zeta
function at that zero. Both signs of the ordinate are included, each zero
once with its multiplicity.

Writing this multiplicity as \(m_\rho\), the checked results include

\[
\sum_\rho \frac{m_\rho}{|\operatorname{Im}\rho|^2}<0.0463,
\qquad
P(x)=\sum_\rho \frac{m_\rho x^{\rho-1}}{\rho(\rho-1)}.
\]

The potential is absolutely convergent for every real `x ≥ 1`, and
`potential_tendsto_zero` proves \(P(x)\to0\) as \(x\to\infty\).
The proof uses the strict critical strip and the summable majorant above,
via Mathlib's dominated convergence theorem for series. It does not assume
finite RH, a quantitative zero-free region, or a pointwise PNT.

The common finite moment allowance is reused from
`SchoenfeldReciprocalSquare.finite_xi_reciprocal_square_sum_le`; its strict
numerical bound is applied after passing to the infinite sum. Thus strict
`< 0.0463` is preserved correctly, rather than inferred from a sequence of
strict finite inequalities alone. The checked height-100 zero certificate
used inside that imported theorem is an actual proof, not a premise.

`sum_tendsto_potential` also identifies the limit of the existing rectangle
zero sums, with their actual contour multiplicities, along any of the
existing good-height sequences. No enumeration or simplicity assumption
on zeros is introduced.

This supplies the zero-sum side of the signed Mertens-tail assembly. The
separate signed-integral assembly and numerical RS62 inequalities require
their own checked modules; this result alone does not assert those goals.

Source SHA-256:
`5bdf231ca3d884aaa0e4d9bc486f3e7010200f60d077748832cb06e98274fa98`.

Receipt: `verification/mertens-zero-potential-run.json`.
Audit: `verification/MertensZeroPotentialAudit.lean`.
Reproduce after sourcing `../lean-env.sh` with
`python3 verification/run_mertens_zero_potential_check.py`.
The two failed elaboration passes are archived separately; the current
successful receipt binds the exact source, input, log, and output object.
