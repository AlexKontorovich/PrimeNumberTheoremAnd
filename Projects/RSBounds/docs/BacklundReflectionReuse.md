# Backlund reflection and crossing reuse

Source: [gersh/ternary-goldbach-lean at
27df23af6a712895f22204d0d81102baa74f0ebe](https://github.com/gersh/ternary-goldbach-lean/tree/27df23af6a712895f22204d0d81102baa74f0ebe),
`MathExtras/NumberTheory/LSeries/`.

This is a selective source port, not an import of that project's complete
zero-count development. The new files import Mathlib only.

- `BacklundFirstCrossing.lean` reuses all nine proofs from
  `FirstCrossingLevels.lean`, with namespace and license-pointer changes.
  These construct actual first and last crossings, ordered crossing families,
  and half-turn levels; they do not merely assume a crossing count.
- `BacklundReflection.lean` extracts the differentiated functional equation,
  the real logarithmic derivative of the pi factor, the gamma-factor
  decomposition, and the exact pointwise reflection from `BacklundEBound`,
  `BacklundCompletedZetaConj`, `ZetaInterlacingAssembly`, and
  `BacklundEBoundGamma`. It uses Mathlib 4.35's existing
  `completedRiemannZeta_conj` and `deriv_conj_conj` in place of the older
  external conjugation proof. It also exposes the result directly in digamma.
  Lean 4.35's pointwise function multiplication/division syntax required two
  explicit `change` statements before rewriting logarithmic derivatives.

The main exact result, for `T != 0` and nonvanishing at the two evaluated
points, is

\[
\Im\frac{\zeta'}{\zeta}(\sigma+iT)
-\Im\frac{\zeta'}{\zeta}(1-\sigma+iT)
=\frac12\Im\left(\operatorname{digamma}((1-\sigma+iT)/2)
-\operatorname{digamma}((\sigma+iT)/2)\right).
\]

The formal export is
`TernaryGoldbach.RSBounds.BacklundReflection.im_logDeriv_zeta_reflect_digamma`.
It does not assume RH or a zero-free region. At an ordinate-free height the
nonvanishing hypotheses hold along the whole horizontal line. The numerical
`8/T` estimate is a separate gamma-factor bound; it is not asserted here.

## Further external reuse identified

`ZetaInterlacingAssembly.zeta_interlacing_core` actually constructs the paired
crossings, via first/last crossing families and an offset
`D = 1 + ceil(N E / pi)`, obtaining `1 - c(k+D) <= l(k)`.
`ZetaSharpArgVarExplicit.zeta_interlacing_core_param` carries out the same
construction for an arbitrary positive `E`. Its count/Jensen assumptions and
hard-coded circle geometry must be adapted to Rosser's constants; its exported
count is not the requested 0.137/0.443/1.588 theorem.

`BacklundGTPowHpair.backlundGTPow_jensen_sum_lower` proves the weighted Jensen
contribution of genuine distinct paired zeros. The simpler
`BacklundReflectionPairing` declarations are mostly arithmetic implications;
they alone do not establish the existence of the reflected crossings.

`ZetaPerDeltaTight.zeta_per_delta_reflection_tight` gives a constant bound
`E = 3*pi/8 + 177/70` for `T >= 1` and `0 < delta <= 3/4`. This is not the
sharp `8/T` bound required by the historical argument. The exact cancellation
used in its proof is reused here.

The external comments about inherited Fiori axioms and native certificates are
not a reliable transitive axiom audit: some are stale. In particular the current
`zeta_convexity_wide` invokes `vertical_strip_polynomial_dyadic_closed`, which
uses a proved midpoint/dyadic chain. No claim about the axiom set of the complete
external count is made without fresh compilation. The two local extracts are
audited independently.

## Verification

Fresh Lean 4.35.0 compilation and twelve axiom audits passed on 2026-11-06,
finishing at 10:14:33 UTC. Both module builds and the audit exited 0. Every
printed axiom set is exactly `propext`, `Classical.choice`, `Quot.sound`;
there is no `sorryAx`, native evaluation axiom, or new analytic axiom.

The audited exact results are the differentiated functional equation,
completed-zeta conjugation and reflection, both zeta reflection formulations,
first/last crossing existence, first/last crossing families, first/last
half-turn levels, and the vanishing of cosine at those levels.

Evidence: `verification/backlund-reflection-run.json`,
`verification/backlund-reflection-build.log`, and
`verification/backlund-reflection-axioms.log`. The reproducible runner is
`verification/run_backlund_reflection_check.py`. Exact original source-file
hashes and the adaptation description are in
`verification/backlund-reflection-provenance.json`.

This verifies the extracted proofs, not the entire external Riemann--von
Mangoldt development. The exact external count identity is exported as
`MathExtras.Helfgott.BacklundRvM.backlundArgVarIdentity_holds` in
`BacklundZetaRealAxisProof.lean`; its dependency closure includes the rectangle
argument principle, xi symmetry, gamma-phase integration, and zero-count
multiplicity bridges. It has not been ported or freshly audited here.
That external count uses `0 < Im(rho) < T`, so a separate endpoint bridge is
needed for the requested `0 < Im(rho) <= T` convention. The sharp boundary
integral, small-height estimates, and endpoint extension remain separate
parts of the Rosser theorem.

## Attribution for third-party notices

`RSBounds/BacklundFirstCrossing.lean` and
`RSBounds/BacklundReflection.lean` contain proofs adapted from
`gersh/ternary-goldbach-lean`, commit
`27df23af6a712895f22204d0d81102baa74f0ebe`.
Copyright (c) 2026 Gershon Bialer. Licensed under Apache 2.0; the complete
license is included at `licenses/Gersh-LICENSE`. Original author headers are
retained. Adaptations are described above and in the provenance JSON.
