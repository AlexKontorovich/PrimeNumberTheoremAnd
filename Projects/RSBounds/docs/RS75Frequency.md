# The nonzero-frequency input

The source in [`RS75Frequency.lean`](../RSBounds/RS75Frequency.lean) has
compiled successfully. The public theorem's full transitive axiom audit uses
only `propext`, `Classical.choice`, and `Quot.sound`. See the
[completed verification record](../verification/rs75-frequency-run.json) and
[axiom output](../verification/rs75-frequency-axioms.log).

The target is the following estimate for the actual zeta and xi functions.
Put \(s=\sigma+it\), \(s_0=\sigma_0+it\), and

\[
D(t)=-\Re\frac{\zeta'}\zeta(s)
       +\kappa\Re\frac{\zeta'}\zeta(s_0),\qquad
X(t)=\Re\frac{\xi'}\xi(s)
       -\kappa\Re\frac{\xi'}\xi(s_0).
\]

For the independent real parameters

\[
1<\sigma\le\frac54,\quad 1<\sigma_0\le3,\quad
0\le\kappa\le\frac12,\quad t\ge100,
\]

the proved public theorem `RS75Frequency.logDeriv_difference_le` is

\[
D(t)\le\frac{1-\kappa}{2}\log\frac{t}{2\pi}
          +\frac{15}{t^2}-X(t).
\]

These ranges include the separately specified RS75 parameters. The theorem
is stated with literal logarithmic derivatives, so it does not depend on the
new Dirichlet-series positivity module or the scalar parameter module.
There is no RH, zero-count, or quantitative zero-free-region hypothesis.

## The two contributions to 15

The existing checked theorem
[`BacklundGammaModulus.abs_digamma_re_sub_log_le`](../RSBounds/BacklundGammaModulusDigamma.lean)
gives, after scaling by two,

\[
\left|\Re\operatorname{digamma}\frac{a+it}{2}
             -\log\frac t2\right|\le\frac{18}{t^2}
\quad(1\le a\le3,\ t\ge100).
\]

That estimate reuses the proved IEANTN Gauss series and the checked vertical
digamma remainder. The two Gamma terms, each carrying the factor \(1/2\),
therefore contribute at most
\(9(1+\kappa)/t^2\le13.5/t^2\).

The rational terms are

\[
P_a(t)=\frac{a}{a^2+t^2}
        +\frac{a-1}{(a-1)^2+t^2}.
\]

For \(a\ge1\), they are nonnegative and satisfy
\(P_a(t)\le(2a-1)/t^2\). Consequently
\(P_\sigma(t)-\kappa P_{\sigma_0}(t)\le1.5/t^2\).
Adding the two estimates yields the constant 15.

The actual xi/zeta/Gamma identity is reused from
[`Explicit.re_vM_eq`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean#L192),
with Mathlib's convergent von Mangoldt identity converting its left side to
the logarithmic derivative. See the
[unchanged upstream check](RS75StechkinReuse.md) for provenance and exact
assumptions. Bounding \(X(t)\) by Stechkin and applying the RS75 trigonometric
polynomial are separate steps in the final zero-free-region argument.

## Reproduction

After building the recorded dependencies, run
`python verification/run_rs75_frequency_check.py`. It compiles the exact
proof source and appends the public `#print axioms` command in the same
process, using Lean's documented `--stdin` option with the original filename.
The receipt records the exact combined input hash. The separate audit file
can also be run independently. No incremental snapshot cache is used.

The first pass succeeded. Its measured total was 890.76 seconds; the Lean
profile records 825 seconds for imports and 1.1 seconds for tactic execution.
Those measurements describe this run, not a general performance guarantee.
