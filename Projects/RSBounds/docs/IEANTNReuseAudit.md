# IEANTN reuse audit for the remaining RS bounds

The checkout inspected is `teorth/IEANTN` at
`466b41b28ecc224398cf53a99c5fe9618131398b`. A fresh GitHub ref read confirmed
that this was also `main`. Its toolchain is Lean `4.34.0-rc2` and Mathlib
`71a80585ee495fc24472fd0eaffc89d94e4fd8d6`; this project uses Lean 4.35.0.
The original IEANTN checkout was left unchanged. Reusing a proof
requires its solution source, not its generated challenge or a definition of
the target proposition.

## Actual reusable proofs

| Ingredient | Exact source and status | Relevance and limits |
|---|---|---|
| Global `psi(x) < 1.03883*x`, `x > 0` | [`RS_prime.theorem_12`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/RosserSchoenfeld1962.v1/RS12/Proof.lean), exported by that solution's `Solution.lean`. [Comparator receipt](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/receipts/RosserSchoenfeld1962.v1.equation_3_35.json), recorded 2026-11-02. | Unconditional, with kernel-checked finite certificates. Useful for coarse prime-power and initial-range bounds. It is not the moderate relative-error row. The proof includes 32 finite-certificate shards and a pinned LeanCert dependency; avoid rebuilding this proof unnecessarily. |
| Gauss series for digamma on `Re s > 0` | [`GammaSolution.digamma_eq_gaussSum`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/GammaAsymptotics.v2/Analytic.lean), line 235. The package's [Comparator receipt](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/receipts/GammaAsymptotics.v2.digamma_sub_log_isBigO_strip.json) is recorded 2026-09-07. | Reuse if the sharp gamma argument needs the Gauss representation. The series identity is already proved; do not rederive it. The current direct source closure is eight files and 1086 lines, before the final strip-bound file. |
| Real digamma error at every `x > 0` | [`GammaSolution.abs_deriv_log_Gamma_sub_log_le`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/GammaAsymptotics.v2/RealAsymptotic.lean), line 109, and [`digamma_ofReal`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/GammaAsymptotics.v2/ComplexToReal.lean), line 74. | Gives `norm(digamma(x)-log(x)) <= 1/x`. These two files total 198 lines and depend only on Mathlib. They form a much smaller reusable subset than the whole Gauss-series proof. |
| Conversion from a psi bound to a theta bound | [`FKS2Sol.classicalBound_theta_of_psi`](https://github.com/teorth/IEANTN/blob/466b41b28ecc224398cf53a99c5fe9618131398b/Solutions/FKS2.v2/PsiToTheta.lean), line 226; elementary `Etheta_le_Epsi_add` at line 65. | These are implications: the explicit psi bound and prime-power comparison remain arguments. Useful after those inputs are available; not a proof of them. |

The gamma package's final theorem bounds the error on a **bounded-height
horizontal strip**, with a constant depending on that height. It cannot be
used as a uniform large-imaginary-part estimate. In particular, it does not
by itself supply RS75's sharp inverse-square remainder. The existing calr
`digamma_eq_integral` is another already-proved representation, valid for
`Re s > 1/2`; that should also be considered before choosing a port.

Following this audit, the eight-file Gauss-series closure was vendored into
`RSBounds/IEANTNGamma/`. All eight proof bodies compiled unchanged on
Lean 4.35.0; only their local import paths were adapted. The wrapper
`RSBounds.IEANTNDigamma` and its axiom audit passed on 2026-11-06, with only
`propext`, `Classical.choice`, and `Quot.sound`. See
[`IEANTNGammaPort.md`](IEANTNGammaPort.md) for exact provenance and evidence.

## Current integral and totient work

No matching quartic-kernel or averaged left-vertical remainder estimate was
found in the inspected IEANTN solutions. CH2's Fourier weights and L-shaped
contour deformation solve different problems. Its elementary integral helpers
either use exponential decay or simply wrap existing Mathlib integrability
lemmas. The present finite-difference integral identity should reuse the
already-checked calr contour integrability and Mathlib integral linearity;
the remaining rational majorant should use Mathlib's power and logarithm
integrals directly.

No proof of the unrestricted RS62 Mertens-product/totient estimates was
identified in IEANTN's Lean sources. A relevant earlier development is
already available locally: `TernaryGoldbach/Prelim/PNTMertens.lean` is an
attributed port of PNT+'s `IEANTN/Mertens.lean`, not a new proof to redo.
Its `sum_mangoldt_div_log_eq` identifies Euler's constant and `E₂Λ.eq`
gives the tail-integral formula. The useful integral helpers
`integrable_const_div_mul_log_sq`, `integrable_E₁Λ_div_mul_log_sq`, and
`integ_div_mul_log_sq` are public. The neighboring `MertensProduct.lean`
contains reusable conditional reductions, but its later estimates use
inputs such as Büthe; those hypotheses must not be silently inherited.

## Statements that are not available as proofs

- `ZeroCount.v1` remains a literature-backed stub, including the weaker
  `(1/5)*log(T)+2` bound. It is not a substitute for a proved count envelope.
- `RosserSchoenfeld.v1.zero_free_region` remains literature-backed. Its
  conversion to a weaker classical shape is a proved bridge **assuming**
  the region.
- `LowZeroes.v1` records numerical claims, including reciprocal-ordinate
  sums and the first-zero lower bound; these are not Lean-verified certificates.

Thus reuse removes genuine work on coarse psi bounds, gamma representations,
and Mertens constant identification. It does not close the sharp count,
RS75 zero-free-region, or full numerical totient gaps by itself.
