# Explicit zero-count theorems

This page gives the mathematical statements, endpoint conventions, Lean
names, and verification records for the project's reusable zero-count
results. Rosser's original estimate for every real $T\ge2$ and the stronger
error bound $|N(T)-F(T)|<1$ for $0\le T\le100$ are both proved and
axiom-audited. All logarithms are natural logarithms.

## Count and main term

Let

$$
 N(T)=\sum_{\substack{\zeta(\rho)=0\\0<\Im\rho\le T}}
       \operatorname{ord}_{\rho}\zeta.
$$

The upper endpoint is **inclusive**, and zeros are counted with their
analytic multiplicities. No half-weight convention is used at a zero
ordinate. The sum concerns Mathlib's actual Riemann zeta function, not an
abstract sequence of purported zeros. The project proves finiteness and
identifies this sum with its finite count. Every zero with nonzero
imaginary part lies in the open critical strip, so this agrees with the
usual positive-ordinate count of nontrivial zeros.
Sources: [count definition](../RSBounds/RosserCountDefinition.lean) and
[strip and finite-count bridges](../RSBounds/BacklundRH100Bridge.lean).

For $T>0$, set

$$
 F(T)=\frac{T}{2\pi}\log\frac{T}{2\pi}
       -\frac{T}{2\pi}+\frac78,
 \qquad F(0)=\frac78.
$$

Thus $F$ has its continuous extension at zero and $N(0)=0$. In the Lean
statement the same displayed expression is used at zero; Mathlib's
totalized `Real.log` and the factor `T` give precisely $F(0)=7/8$.

The public count is
`TernaryGoldbach.RSBounds.Rosser1941.positiveZeroCount`.
The theorem names below use the same namespace prefix
`TernaryGoldbach.RSBounds.Rosser1941`.

## Rosser's bound in the analytic range: checked

For every real $T\ge100$,

$$
 \boxed{\quad |N(T)-F(T)|
  <0.137\log T+0.443\log\log T+1.588.\quad}
$$

This is unconditional and includes heights that are zero ordinates. The
analytic proof imports no finite-height RH or zero certificate. Its only
theorem hypothesis is $100\le T$.

* Declaration: `zero_count_bounds_high`.
* Import: `RSBounds.BacklundHighCount`.
* [Lean source](../RSBounds/BacklundHighCount.lean).
* [Fresh build and axiom audit](../verification/backlund-high-count-run.json).

For example, a downstream Lean file can use the theorem directly:

```lean
import RSBounds.BacklundHighCount

open TernaryGoldbach.RSBounds.Rosser1941

example (T : ℝ) (hT : 100 ≤ T) :
    |positiveZeroCount T -
      (T / (2 * Real.pi) * Real.log (T / (2 * Real.pi)) -
        T / (2 * Real.pi) + 7 / 8)| <
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 :=
  zero_count_bounds_high T hT
```

The constants and inclusive convention are those of Rosser (1941),
Theorem 19, pp. 223–224,
[DOI: 10.2307/2371291](https://doi.org/10.2307/2371291).
The proof follows Rosser's refinement of Backlund's method; see the
[primary-source audit](BacklundCountAudit.md) and the
[checked circle-majorant assembly](BacklundCircleMajorantAudit.md).

## Complete certificates through height 100: checked

The pinned public certificates from `teal-sea/zeta-lab` have been replayed
locally: all 99 modules and all 28 final transitive axiom checks passed.
The additional bridge to this project's count passed five axiom checks.
These establish

$$
 N(100)=29,
$$

and, for every zero $\rho$ with $0<\Im\rho\le100$,

$$
 \Re\rho=\tfrac12,
 \qquad \operatorname{ord}_{\rho}\zeta=1.
$$

These are proved finite-height results, not RH assumptions. The relevant
bridge declarations are
`TernaryGoldbach.RSBounds.BacklundCountIdentity.closed_count_hundred`
and `TernaryGoldbach.RSBounds.BacklundCountIdentity.zero_simple_below_hundred`.
The former is stated for the finite count `N_le`; the proved
`Rosser1941.positiveZeroCount_eq` identifies it with the public count.

* [Bridge source](../RSBounds/BacklundRH100Bridge.lean).
* [99-module replay and 28 audits](../verification/rh100-replay-run.json).
* [Bridge build and five audits](../verification/backlund-rh100-bridge-run.json).
* [Complete table of 29 rational ordinate brackets](LowHeightCertificateAudit.md#brackets-and-scalar-handoff).
* [Pinned upstream theorem source](https://github.com/teal-sea/zeta-lab/blob/b09fa4dd2f2182cf14b248e7ffc64ff03df2c534/hunts/rh_height_lean/lean/RHHeight100/Main100.lean).

The table supplies open brackets for all 29 zeros, not merely a numerical
claim that 29 zeros were found. The argument-principle certificate proves
the total multiplicity count, which establishes completeness and simplicity.
Downstream applications can reuse the resulting theorems rather than
reimplementing the endpoint evaluations.

## Uniform error through height 100: checked

For every real $T$ with $0\le T\le100$, the checked theorem gives

$$
 \boxed{\quad |N(T)-F(T)|<1\qquad(0\le T\le100).\quad}
$$

* Declaration: `zero_count_error_lt_one_to_100`.
* Import: `RSBounds.BacklundLowCount`.
* [Lean source](../RSBounds/BacklundLowCount.lean).
* [Build and audit record](../verification/backlund-low-count-run.json).

The theorem's fresh compilation and all 12 associated transitive axiom
checks passed. Its only hypotheses are the displayed range conditions.
In particular, it includes zero ordinates and $T=0$; it assumes no RH
statement or numerical certificate.

## Rosser's full range: checked

Combining the analytic range with the finite-height estimate proves
Rosser's original statement for every real $T\ge2$:

$$
 \boxed{\quad |N(T)-F(T)|
  <0.137\log T+0.443\log\log T+1.588
  \qquad(T\ge2).\quad}
$$

* Declaration: `zero_count_bounds`.
* Import: `RSBounds.Rosser1941`.
* [Lean source](../RSBounds/Rosser1941.lean).
* [Fresh build and public axiom audit](../verification/zero-count-run.json).
* [Five public declarations' axiom output](../verification/zero-count-axioms.log).

The final theorem compiled, and its transitive axiom audit passed with
only `propext`, `Classical.choice`, and `Quot.sound`. Its only hypothesis
is $2\le T$: there is no RH, zero-count, finite-certificate, or
analytic-estimate premise.

Comparator also passed for both `zero_count_bounds` and
`zero_count_error_lt_one_to_100`: statement and definition matching,
allowed-axiom checks, and full replay with Lean's default kernel all
succeeded. Only the same three standard axioms were permitted. The native
Comparator command took 2747.55 seconds and exited 0; see the
[completed receipt](../verification/zero-count-run.json) and
[final log](../verification/zero-count-comparator.log).
Process sandboxing was disabled because `bwrap` could not mount its required
filesystem in this workspace; no sandboxed attestation is claimed. This timing
is for the Comparator command, not source imports or tactic elaboration.

## Reusable zero-table interface: checked

Import `RSBounds.ZetaZeroTable`. In namespace
`TernaryGoldbach.RSBounds.ZetaZeroTable`, the object

```lean
first29 : CertifiedTable 29 100
```

packages rational open brackets, strictly increasing exact ordinates,
simplicity, and completeness through height 100. Index `0` denotes the
first positive-ordinate zero. The exact ordinates are noncomputable real
numbers; the bracket endpoints and the count bounds below are rational
data usable for computation.

For $0\le T\le100$, `positiveZeroCount_eq_table` identifies the count with

$$
 N(T)=\#\{i: \gamma_i\le T\}.
$$

For rational $T$ in that range, put

$$
 L(T)=\#\{i:b_i\le T\},\qquad
 U(T)=\#\{i:a_i<T\},
$$

where $(a_i,b_i)$ is the certified open bracket containing $\gamma_i$.
The theorem `bracket_count_bounds` proves

$$
 L(T)\le N(T)\le U(T).
$$

Thus many exact count queries reduce to rational endpoint comparisons,
without evaluating the noncomputable ordinates or repeating a zeta
calculation. `positiveZeroCount_hundred` states $N(100)=29$ directly for
the public count. `zero_iff_exists_index` states completeness for every
zero with $0<\Im\rho\le100$, with no real-part premise.

See [the interface source](../RSBounds/ZetaZeroTable.lean) and
[its dedicated seven-declaration audit](../verification/zeta-zero-table-run.json),
as well as
[the public axiom audit](../verification/zero-count-axioms.log), which
includes `first29` and `bracket_count_bounds`.

## Scope and trust

The completed results listed above have transitive axiom sets contained in
`propext`, `Classical.choice`, and `Quot.sound`. Numerical certificates use
the ordinary Lean kernel; no numerical axiom, `sorry`, or `native_decide`
is part of these proofs. Local replay uses Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`; finite-certificate provenance and
compatibility adaptations are recorded in the
[finite-height audit](LowHeightCertificateAudit.md).

The estimate $|N(T)-F(T)|<1$ on the larger interval
$0\le T\le280$ is **not proved here**. A certificate for the first
1000 zeros is also **not proved here**. The complete table currently
replayed and connected to the public count stops at height 100 and
contains 29 zeros. The requested $b=23$ bound for $|\psi(x)-x|$
and the RS75 zero-free region remain separate unfinished results.
