# Rosser circle: checked angular estimates

The five modules `BacklundRightArc`, `BacklundRightArcNumericsBase`,
`BacklundRightArcNumerics`, `BacklundAngularCoefficients`, and
`BacklundAngularNumerics` have been compiled. Their 23 exported proof checks
depend only on `propext`, `Classical.choice`, and `Quot.sound`; see
`backlund-angular-run.json` and `backlund-angular-axioms.log`.

For radius (r=33/25), the actual right-arc integral satisfies

\[
\frac1{2\pi}\int_0^{\pi/2}
 \log\lvert\zeta(5/4+r\cos\theta)\rvert\,d\theta
 <0.1361.
\]

This is an unconditional theorem about the Riemann zeta function. The proof
uses its absolutely convergent Euler-product logarithm in the half-plane
\(\sigma>1\), convexity, and sixteen trapezoids. It uses no prime-number
theorem, zero-free region, RH assumption, or numerical-integration axiom.
Each of the seventeen node values is bounded using sixteen terms of the
Dirichlet series and an integral-test tail. Integer power certificates,
cosine doubling, and finite exponential Taylor bounds are checked by Lean's
kernel. The final rational trapezoid bound is exactly

\[
17410189/128000000=0.1360171015625.
\]

The numerical construction follows the right-arc trapezoidal method on
Backlund's 1918 page 373, with more panels to leave adequate room for exact
rational estimates. Local source images are `sources/backlund-p371.png`,
`sources/backlund-p372.png`, and `sources/backlund-p373.png`.

Set \(q=\log(44/25)\),
\(\alpha=\arccos(-25/132)\), and
\(\beta=\arccos(-125/132)\). The exact angular coefficients are

\[
A=\frac{r\sin\alpha-(\pi-\alpha)/4+
             r\sin\beta-5(\pi-\beta)/4}{4\pi q},
\qquad B=\frac1{4q}.
\]

The checked inequalities are

\[
0.1359\le A\le0.1361,\qquad B\le0.4423,
\]

and

\[
\frac{0.1361}{q}-A\log(2\pi)
 +\frac{\log(3.426)}{2q}+\frac12\le1.5803.
\]

`BacklundAngularAssembly` has also been compiled and its nine exported
proofs audited with the same three axioms. It proves the actual piecewise
majorant is interval-integrable on the upper semicircle, derives all four
sector formulas, and evaluates its integral in terms of the coefficients
above. Equality on open intervals handles the artificial sector endpoint
jumps. Its separate record is `backlund-angular-assembly-run.json`.

These results do not alone constitute a zero-count theorem. They are inputs
to the separately formalized Jensen, phase/reflection, gamma, and actual
boundary-majorant arguments.
