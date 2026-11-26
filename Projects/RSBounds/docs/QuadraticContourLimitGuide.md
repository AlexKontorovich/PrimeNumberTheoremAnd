# Degree-two contour passage for the RS62 signed integral

The new modules are `RSBounds/QuadraticContourLimit.lean` and
`RSBounds/QuadraticSubOne.lean`. They reuse the finite-rectangle residue
theorem in `PolynomialExplicitFormula.lean` and its multiplicity convention:
each sum is over `zerosRectD f T`, with weight `multRectD f T u`.

## Analytic inputs proved here

`DecayTwo M K` requires continuity on the vertical lines
`Re s = -1/2, 3/2`, a bound `K/(1+|t|)^2` there, and a bound
`K/|Im s|^2` throughout the strip when `|Im s| >= 1`.

1. `log_weighted_integrable_of_decay_two` proves integrability after
   multiplication by `1 + log(max 1 |t|)`. It uses the elementary bound
   `log y <= 2 sqrt(y)` and Mathlib's integrability of
   `(1 + |t|)^(-3/2)`.
2. `integrable_contour_right` uses the already proved bounded logarithmic
   derivative in an `LDatum`.
3. `integrable_zetaF_contour_left` applies the actual unconditional estimate
   `norm_logDeriv_zetaF_left_log` from `PolynomialLeftRemainder.lean`.
4. `tendsto_HkD_BPz2_div_sq` uses the actual polynomial datum and
   `XiPartial.HkD_BPz2_le`, proving that the horizontal integral bounds
   tend to zero. No merely assumed horizontal limit remains.

The generic theorem `contour_limit_of_residue_formula_at_heights` explicitly
accepts vertical integrability, horizontal decay, a `GoodHeights` sequence,
and a finite rectangle identity. The actual-zeta specialization discharges
the first two inputs. Its pole-zero export
`explicit_formula_pole_zero_at_heights` also discharges the finite rectangle
identity and the nonvanishing at zero.

Writing `zetaF(s)=(s-1)zeta(s)`, the last theorem proves

\[
\lim_k\sum_{\rho\in\mathrm{zerosRect}(T_k)}
 m_\rho\frac{H(\rho)}{\rho}x^\rho
 =\frac{1}{2\pi}(I_{3/2}-I_{-1/2})
  -\frac{\mathrm{zetaF}'(0)}{\mathrm{zetaF}(0)}H(0),
\]

where each `I_sigma` is the actual vertical ordinate integral of
`(zetaF'/zetaF)(s) H(s)/s x^s`. The hypotheses are `x>0`,
holomorphic `H` on `Re s>-1`, `DecayTwo (H/s) K`, and a supplied actual
zeta `GoodHeights zetaF BPz2 T`. Existence of such heights is already
proved by `PolynomialExplicit.exists_goodHeights ldatum_zeta2`.

## Removing the pole at one

`QuadraticSubOne.sub_one_contour_difference` supplies the analogous exact
identity for `s-1`, with its zero sum evaluated as `H(1)*x`. It uses no
external zero information. Any heights in `[k+1,k+2]` work for this factor.
The auxiliary constant `poleB` is only a horizontal envelope for
`GoodHeights`; it is not claimed to be an `LDatum` bound on circles.
`integrable_sub_one_contour_left` and the generic right-line theorem
permit subtraction of the two integrals to obtain the actual zeta formula.

## What is not established by these modules

These are the contour and integrability portion of the finite-interval
explicit formula used in the RS62 Section 8 route. They do not themselves
evaluate its Mellin kernel, identify the prime sum with the integral of
psi, take the interval endpoint to infinity, establish Euler-constant
normalization, or prove either final RS62 inequality. No RH hypothesis,
numerical zero certificate, or new axiom is present.

## Verification

Run `source ../lean-env.sh` and
`python verification/run_quadratic_contour_checks.py` from `recovery/`.
The runner compiles each exact source through `--stdin`, appending the
public theorem axiom checks in the same process. It runs only one Lean
compiler at a time and rejects any axiom outside `propext`,
`Classical.choice`, and `Quot.sound`. Receipts record source and input
hashes, selected dependency hashes, object hashes, timing, exit status,
and the axiom result in `verification/quadratic-contour-limit-run.json`
and `verification/quadratic-sub-one-run.json`.
