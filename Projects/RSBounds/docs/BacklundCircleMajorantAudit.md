# Actual circle majorant and count bound

All five local modules were freshly compiled on 2026-11-06, finishing at 12:30:15 UTC. Seven public endpoint declarations were audited; every declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The machine-readable receipt is `verification/backlund-circle-majorant-run.json`, and the complete axiom output is `verification/backlund-circle-majorant-axioms.log`.

The main declaration is

`TernaryGoldbach.RSBounds.BacklundCircleMajorant.count_le_roundedEnvelope`.

Its only hypotheses are `100 ≤ T` and the actual `BacklundCountIdentity.zetaGoodHeight T` condition. Its conclusion bounds the actual positive-ordinate multiplicity count `N T` minus `mainTerm T` by `BacklundFinalScalar.roundedEnvelope T`. It has no assumed circle majorant, zeta-strip bound, gamma bound, zero-count estimate, or RH hypothesis. Removing the zero-avoidance condition at endpoint heights is the separate endpoint-count step.

The majorant is an actual function of the real part of a point on the circle centered at 5/4 with radius 33/25. Write

* H = log(log(T + 33/25));
* L = log((T + 33/25)/(2π));
* V = log((T − 33/25)² / ((T − 33/25)² − 4)).

For σ≥5/4 the majorant is log|ζ(σ)|. Below that line it is

`H + (L/2)(max(1−σ,0) + max(−σ,0)) + 1_{0≤σ<1} V`.

The proof establishes global nonnegativity and circle integrability, and proves both `|ζ(z+iT)|≤exp(B(z))` and `|ζ(z−iT)|≤exp(B(z))` for every point on the circle. It uses the checked Euler/Dirichlet comparison on the right, Backlund (54) on Re≥1, the actual checked (56) in the critical strip, and the actual checked (77) on the left. Conjugation handles negative ordinates. All heights occurring on the circle exceed 50.

The full-circle average is exactly the upper-semicircle integral divided by π. `BacklundAngularAssembly` evaluates the actual four-sector integral; `BacklundAngularNumerics` supplies the numerical coefficients and intercept. The final bound is

`0.1361 log(T+33/25) + 0.4423 log(log(T+33/25)) + 1.5803 + V + 2/(πT) + 1/(4πT)`.

The replacement of the exact V coefficient by 1 is proved from `0≤alpha`, `beta≤π`, and `q≥0.5653`. This is exactly the envelope used by the independently checked final scalar comparison at T≥100.

Source files:

* `RSBounds/BacklundCircleMajorantDef.lean` — definition only;
* `RSBounds/BacklundCircleMajorantGeometry.lean` — positivity, geometry, and monotonic scalar factors;
* `RSBounds/BacklundCircleMajorantBounds.lean` — actual zeta bounds on both translated circles;
* `RSBounds/BacklundCircleSymmetry.lean` — generic full-circle symmetry and integration;
* `RSBounds/BacklundCircleCount.lean` — application to the actual count/Jensen theorem.
