# The all-integer RS62 totient theorem from finite RH

Status: **fresh source check and all seven transitive axiom audits passed**
on 2026-11-06. The successful pass took 159.83 seconds; the axiom footprints
contain only `propext`, `Classical.choice`, and `Quot.sound`. Source SHA256:
`cdfb8f02676c1a8d0bfbf14386db0119b1417ca9d54792db5aac8191fdca9c8d`.

The public declaration is
`RS62TotientFromFiniteRH.totient_bound_of_finiteRH`. Its checked
type is

```lean
(hRH : Goals.FiniteRH 1894439) : Goals.TotientBound
```

The conclusion is the original exact-constant inequality

\[
\frac{n}{\varphi(n)}
< e^\gamma\log\log n + \frac{2.50637}{\log\log n}
\qquad\text{for every natural }n\ge3.
\]

There is no upper restriction on `n`. The explicit premise says that
every zero of the actual Riemann zeta function with `0 < re < 1` and
`|im| ≤ 1894439` has real part `1/2`. This is a finite-RH conditional
formalization of the classical RS62 conclusion; it does not by itself
prove that finite-RH premise or remove it.

The proof first establishes two estimates at every natural prime-product cutoff
`x ≥ 100000`:

\[
\theta(x)\ge x\left(1-\frac1{2\log x}\right),\qquad
\prod_{p\le x}\frac p{p-1}
<e^\gamma\left(\log x+\frac1{2\log x}\right).
\]

The analytic ranges are joined without gaps:

| Range | Psi input | Signed-tail input |
|---|---|---|
| `100000 ≤ x`, `log x ≤ 23` | `ModeratePsi.psi_error_le` | Fixed-height bound |
| `23 ≤ log x ≤ 2400` | RS75 `b=23` entry | Fixed-height bound |
| `2400 ≤ log x` | `WeakPsiTail.psi_error_le` | Moving-cutoff `MertensLargeBudget.abs_J_lt` |

The product proof uses the checked signed second-Mertens identity and the
unconditional correction `5.6/(sqrt x * log x)` from
`MertensProductCorrection`. `TotientAnalyticReduction` then supplies the
exact `2.50637` prime-product bound. The kernel-replayed finite product
certificate covers prime cutoffs through `100000`. The existing exchange
argument completes the totient inequality for every `n ≥ 3`.

No Büthe estimate or Ramaré Möbius-sum estimate is an input. The successful
transitive audit confirms the final dependency footprint; its record is `verification/rs62-totient-from-finite-rh-run.json`.
The exact-source runner is
`verification/run_rs62_totient_from_finite_rh_check.py`.

Classical reference: Rosser–Schoenfeld (1962), Theorem 15,
<https://doi.org/10.1215/ijm/1255631807>.
