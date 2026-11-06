# Continuous zeta phase and reflected Jensen bridge

The module `RSBounds/BacklundZetaPhase.lean` selectively reuses the actual
integrating-factor proof in Gershon Bialer's
[`BacklundArgSweep.lean`](https://github.com/gersh/ternary-goldbach-lean/blob/27df23af6a712895f22204d0d81102baa74f0ebe/MathExtras/NumberTheory/LSeries/BacklundArgSweep.lean),
sections 0–2. The source commit is
`27df23af6a712895f22204d0d81102baa74f0ebe`.

Small prerequisites come from `BacklundArgVarAssembly.lean` and
`BacklundArgVarVertical.lean` at the same commit. Anchor-independent increments
and continuity come from `ZetaInterlacingAssembly.lean`, section 1. The large
external zero-count closure is not imported. The source copyright and Apache
2.0 license are retained; see `licenses/Gersh-LICENSE`.

The definition is

\[
H_{T,a}(\sigma)=\arg\zeta(a+iT)+
 \int_a^\sigma\Im\frac{\zeta'}{\zeta}(u+iT)\,du.
\]

For `T ≠ 0` at an ordinate-free height (`BacklundCountIdentity.zetaGoodHeight T`),
the module proves continuity, the derivative formula, and the exact polar
identity

\[
\zeta(\sigma+iT)=|\zeta(\sigma+iT)|e^{iH_{T,a}(\sigma)}.
\]

It then proves that every zero of `cos(n H)` is a genuine zero of the symmetric
zeta-power function. This is the actual analytic bridge used by the constructive
paired-crossing theorem, not a zero-forcing premise.

The new integration bridge reuses `BacklundGammaReflection` to obtain, for
`T ≥ 1` and `0 ≤ δ ≤ 3/4`,

\[
\left|H(\tfrac12+\delta)-2H(\tfrac12)+H(\tfrac12-\delta)\right|
 \le \frac{4\delta^2}{T}\le\frac4T.
\]

Finally `horizontal_argument_bound` specializes the already-proved generic
`BacklundPairedPower.argument_bound` to actual zeta translates, discharging
analyticity, the phase lift, zero-forcing, and reflected crossings. For
`3/4 < R < T`, it retains only a common nonnegative circle-integrable angular
majorant `B` for `log |ζ(z±iT)|` and concludes

\[
\frac1\pi\left|\int_{1/2}^{5/4}\Im\frac{\zeta'}{\zeta}(\sigma+iT)\,d\sigma\right|
\le \frac{\langle B\rangle-\log|\zeta(5/4+iT)|}{2\log(R/(3/4))}
 +\frac2{\pi T}.
\]

This is a horizontal argument estimate. The principal phase at the horizontal
anchor is not assumed to equal the integrated vertical phase. A separate
Euler-log bound at real part `5/4` supplies that vertical estimate in the
zero-count argument.

Validation: fresh direct Lean 4.35 build and all eleven axiom audits passed on
2026-11-06 at 11:42:18 UTC. Every audited export depends only on
`propext`, `Classical.choice`, and `Quot.sound`. The receipt is
`verification/backlund-zeta-phase-run.json`; exact source hashes and commands
are recorded there.

Suggested third-party notice addition: `RSBounds/BacklundZetaPhase.lean` reuses
Gershon Bialer's Apache-2.0 phase-lift and anchor-increment proofs from
`BacklundArgSweep`, `BacklundArgVarAssembly`, `BacklundArgVarVertical`, and
`ZetaInterlacingAssembly`, source commit above. The original source files are
recorded in `verification/backlund-zeta-phase-provenance.json`.
