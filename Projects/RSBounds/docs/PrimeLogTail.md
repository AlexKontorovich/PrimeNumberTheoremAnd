# Elementary finite prime-log tails

Status: **fresh source check and all three transitive axiom audits passed**
on 2026-11-06. The audits use only `propext`, `Classical.choice`, and
`Quot.sound`. The receipt is `verification/prime-log-tail-run.json`;
source SHA256: `05a75c2df96480ae03d6a5fc37d821d85e643cbcd06bc0af71f1b84c543c390c`.

`RSBounds/PrimeLogTail.lean` imports only Mathlib and exposes three theorems
in namespace `TernaryGoldbach.RSBounds.PrimeLogTail`. For real endpoints
`0 < a ≤ b`, the first is the exact finite Abel identity

\[
\sum_{a<p\le b}\frac{\log p}{p^2}
=\frac{\theta(b)}{b^2}-\frac{\theta(a)}{a^2}
 +\int_a^b\frac{2\theta(t)}{t^3}\,dt.
\]

The finite sum is represented by
`(Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime`, so a nonintegral lower endpoint
and a prime upper endpoint have the intended strict/closed conventions.
Using Mathlib's unconditional `Chebyshev.theta_le_log4_mul_x` yields

\[
\sum_{a<p\le b}\frac{\log p}{p^2}
\le\frac{2\log 4}{a}.
\]

For `1 < a ≤ b`, the pointwise inequality
`p/(p−1) ≤ a/(a−1)` gives

\[
\sum_{a<p\le b}\frac{\log p}{p(p-1)}
\le\frac{2\log 4}{a-1}.
\]

The public names are `sum_prime_log_div_sq_eq`,
`sum_prime_log_div_sq_le`, and `sum_prime_log_div_mul_pred_le`.
There is no infinite sum, limit, prime-number asymptotic, or zero hypothesis.
The audited declaration list is in `verification/PrimeLogTailAudit.lean`.

Source APIs reused: Mathlib `NumberTheory/AbelSummation.lean`,
`sum_mul_eq_sub_sub_integral_mul` and `integrableOn_mul_sum_Icc`;
Mathlib `NumberTheory/Chebyshev.lean`, `theta_le_log4_mul_x` and
`theta_eq_sum_Icc`; the ordinary interval-integral fundamental theorem
of calculus.
