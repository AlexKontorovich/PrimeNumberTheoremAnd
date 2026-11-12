# Reusing the actual Stechkin and zeta identities

Both unchanged upstream files have freshly compiled successfully. All
eighteen transitive axiom audits passed, using only `propext`,
`Classical.choice`, and `Quot.sound`. The
[completed receipt](../verification/rs75-stechkin-reuse-run.json) records the
commands, source and object hashes, and pinned revision. The
[axiom output](../verification/rs75-stechkin-reuse-axioms.log) is also retained.

The source inputs are calr3/ternary-goldbach at commit
`ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0`:

- [`TernaryGoldbach/Explicit/ZeroFree.lean`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFree.lean)
- [`TernaryGoldbach/Explicit/ZeroFreeRegion.lean`](https://github.com/calr3/ternary-goldbach/blob/ce82a5b2a4ed5039c4750c0d062f0b0f2b833be0/TernaryGoldbach/Explicit/ZeroFreeRegion.lean)

They use the already checked `Explicit.XiPartial` and `Explicit.Digamma`.
The verification driver compiles the existing sources directly, without changing them or
rebuilding the older count/psi dependency closure. The only package option
needed beyond defaults is `linter.unusedSectionVars=false`; the second file
also contains its own local heartbeat setting for a later theorem.

The namespace of the reusable declarations is
`TernaryGoldbach.Explicit`. Import
`TernaryGoldbach.Explicit.ZeroFreeRegion` to access all of them.

## Parameters and exact scope

For `s` and `s1` with equal imaginary parts, the Stechkin statements use

\[
1<\Re s<\Re s_1,\qquad
\frac32\le(\Re s-\tfrac12)^2+(\Re s_1-\tfrac12)^2,\qquad
\kappa=\frac{\Re s-\tfrac12}{\Re s_1-\tfrac12}.
\]

The paired kernel is

\[
\Phi_s(u)=\Re\frac1{s-u}+\Re\frac1{s-(1-\overline u)}.
\]

`Phi_stechkin` proves `κ * Phi s1 u ≤ Phi s u` when `0 < Re u < 1`.
`stechkin_xi_nonneg` proves

\[
0\le\Re\frac{\xi'}\xi(s)-\kappa\Re\frac{\xi'}\xi(s_1).
\]

For an actual xi zero `ρ` with `Re ρ ≠ 1/2`, `stechkin_xi` retains its
distinguished pair and proves

\[
\Phi_s(\rho)-\kappa\Phi_{s_1}(\rho)
\le\Re\frac{\xi'}\xi(s)-\kappa\Re\frac{\xi'}\xi(s_1).
\]

The off-critical-line condition is explicit and ensures that the paired
zeros are distinct. No RH, zero-free region, zero-count bound, simplicity
claim, or numerical certificate is a premise of these three theorems.
`pair_approx` is the finite-sum approximation lemma; its explicitly stated
approximation hypothesis is discharged by the proved `xi_partial_approx`
in the xi inequalities.

For the RS75 choice

\[
\sigma_0=\frac{1+\sqrt{8\sigma^2-4\sigma+1}}2,
\qquad
\kappa=\frac{2\sigma-1}{2\sigma_0-1},
\]

the ratio agrees with the existing API. Its squared-distance condition is
also compatible: the left side minus \(3/2\) is
\((\sigma-1)(3\sigma+1)\), positive for \(\sigma>1\).
The corresponding Lean parameter specialization is now proved in
`RS75Parameters` and applied to the actual xi difference in
`RS75ZeroFree1975.xiDifference_ge_reciprocal`.

`hasSum_re_vM` proves the actual convergent von Mangoldt series for `σ > 1`.
Together with Mathlib's logarithmic-derivative identity, `re_vM_eq` gives

\[
\Re\!\left(-\frac{\zeta'}\zeta(s)\right)
=-\Re\frac{\xi'}\xi(s)+\Re\frac1s+\Re\frac1{s-1}
-\frac12\log\pi+\frac12\Re\operatorname{digamma}(s/2),
\qquad \Re s>1.
\]

The literal left side in `re_vM_eq` is the real part of
`LSeries (fun n => (Λ n : ℂ)) s`; the preceding von Mangoldt identity
identifies it with the displayed logarithmic derivative.

The accompanying positivity theorem uses the coefficients `(18,30,17,6,1)`
and the nonnegative trigonometric polynomial
`18 + 30 cos θ + 17 cos(2θ) + 6 cos(3θ) + cos(4θ)`.
The digamma estimates concern the actual `Complex.digamma` function.

## Targeted public audit

| Declaration | Purpose |
|---|---|
| `pair_approx` | Actual finite paired-zero approximation |
| `Phi_eq`, `Phi_nonneg`, `Phi_stechkin` | Algebraic paired kernel and Stechkin comparison |
| `xiF_zero_re` | Actual xi zeros lie in the open critical strip |
| `re_logDeriv_xiF_nonneg` | Xi logarithmic-derivative positivity |
| `stechkin_xi`, `stechkin_xi_nonneg` | Distinguished-zero and nonnegative Stechkin bounds |
| `re_term_vM`, `hasSum_re_vM` | Real von Mangoldt terms and their convergent sum |
| `trig_poly_nonneg`, `vM_positivity`, `re_vM_le` | Trigonometric and Dirichlet-series inequalities |
| `re_vM_eq` | Actual xi/zeta/digamma identity |
| `re_digamma_real_le`, `re_digamma_sub_le` | Real and horizontal digamma estimates |
| `zero_free_pos`, `zero_free` | Existing unconditional region above height \(10^9\) |

The audit driver is
[`RS75StechkinReuseAudit.lean`](../verification/RS75StechkinReuseAudit.lean).
The sequential compile/audit runner is
[`run_rs75_stechkin_reuse_check.py`](../verification/run_rs75_stechkin_reuse_check.py).
The fresh build and audit status is recorded in
`verification/rs75-stechkin-reuse-run.json`. These reusable
lemmas do not themselves assert the requested RS75 zero-free region with
constant `9.645908801`; its parameter specialization, numerical estimates,
and contradiction argument remain separate work.

The existing source's final theorem has the exact statement

```lean
TernaryGoldbach.Explicit.zero_free {ρ : ℂ}
  (hρ : xiF ρ = 0) (ht : (1e9 : ℝ) ≤ |ρ.im|) :
  ρ.re ≤ 1 - 1 / (11 * Real.log |ρ.im|)
```

Its only premises are that `ρ` is an actual xi zero and the displayed
height range. Its boundary inequality is non-strict. This is distinct from
the requested RS75 region with constant `9.645908801`, shifted logarithm
`log (abs t / 17)`, and finite-RH handoff down to height 21.

