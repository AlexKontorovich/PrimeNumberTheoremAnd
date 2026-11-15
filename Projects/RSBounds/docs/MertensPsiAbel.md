# Normalizing the signed integral without a pointwise PNT

The interface in `MertensPsiAbel.lean` uses only Chebyshev's unconditional
bound `ψ(x)≤(log 4+4)x` and Mathlib's summatory L-series integral formula.
For real `s>1`, it establishes the averaged identity

\[
(s-1)\int_1^\infty \frac{\psi(x)}x x^{-s}\,dx
=-\frac{s-1}{s}\operatorname{Re}\frac{\zeta'}{\zeta}(s).
\]

Together with `MertensAbelIdentity.error_abel_identity`, this gives the
normalization-ready formula for

\[
D(x)=E_{1\Lambda}(x)-\psi(x)/x:
\qquad
(s-1)\int_1^\infty D(x)x^{-s}\,dx
=-\frac{\operatorname{Re}(\zeta'/\zeta)(s)+1/(s-1)+1}{s}.
\]

The Laurent remainder in the numerator tends to `γ+1`. Hence any finite
limit of `D(x)` supplied by the signed-integral formula is identified as
`-γ-1` using an Abelian averaging theorem. A pointwise asymptotic
`ψ(x)/x→1` is unnecessary for this normalization step.

Public auxiliary interfaces include actual integrability for every `s>1`,
measurability of `D`, and the elementary bounds on `x≥1`

\[
|\psi(x)/x|\le\log4+4,
\qquad |D(x)|\le2(\log4+4).
\]

No RH, Büthe estimate, numerical prime-number theorem, or convergence of
`D` is an input to these identities. The limit argument itself belongs to
the separate `MertensCenteredNormalization` module.

Fresh direct-Lean source compilation succeeded on 2026-11-06, and all ten
transitive axiom audits contain only `propext`, `Classical.choice`, and
`Quot.sound`. The receipt is `verification/mertens-psi-abel-run.json`;
the source SHA256 is
`cc8893163358c92be6c8b0ad9786a3d060d36ba78ae96b1c95e01169865be018`.
Its source dependency `MertensAbelIdentity.lean` has a separate eight-export
audit. The first failed elaboration pass is archived separately; the
successful receipt guards the exact final source and output object.
