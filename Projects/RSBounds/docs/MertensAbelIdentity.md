# Abel identity for the first Mangoldt error

The proved public export in `RSBounds/MertensAbelIdentity.lean` is, for
every real `s>1`,

\[
(s-1)\int_1^\infty E_{1\Lambda}(x)x^{-s}\,dx
=-\operatorname{Re}\frac{\zeta'}{\zeta}(s)-\frac1{s-1},
\qquad
E_{1\Lambda}(x)=\sum_{n\le x}\frac{\Lambda(n)}n-\log x.
\]

This is the normalization interface: if the signed-tail argument first
establishes that `E₁Λ(x)` tends to some finite real limit, an Abelian averaging
theorem and the Laurent expansion at one identify that limit with `-γ`.
Neither convergence of `E₁Λ` nor its value at infinity is assumed in the
identity itself.

The source reuses:

- `PNTMertens.sum_mangoldt_div_eq_log'`: the elementary asymptotic equivalence
  of the weighted Mangoldt sum with `log x`;
- `Mathlib.LSeries_eq_mul_integral_of_nonneg`, applied to `Λ(n)/n` at `s-1`;
- `LSeries_vonMangoldt_eq_deriv_riemannZeta_div`;
- `RS75MomentCalculus.hasDerivAt_neg_tailPrimitive` and
  `tendsto_tailPrimitive`, for the exact logarithmic moment
  `∫₁∞ log(x)x⁻ˢ dx = 1/(s-1)^2`;
- `PNTMertens.E₁Λ.bounded'`, for actual integrability of the error average.

No RH, Büthe estimate, numerical PNT input, or asserted value of the first
Mertens limit is introduced. The separate finite prime-product certificate
has no role in this analytic identity.

The exact fresh source compiled successfully, with all eight exported
theorems audited transitively using only `propext`, `Classical.choice`, and
`Quot.sound`. The successful receipt is
`verification/mertens-abel-identity-run.json`; source SHA256 is
`743f7aff4f26e7344e3cbef14fe811c22802b0ee8a56fa3e6f7267bade38df8e`.
The runner appends the audit commands to the source in the same Lean process.
Earlier launcher stalls and unsuccessful elaboration passes have separately
named diagnostic logs and receipts; they are not the successful receipt.
