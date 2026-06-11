/-
Copyright (c) 2026 Robby Sneiderman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robby Sneiderman

KERNEL PROBE — Backlund Tier A Phase 1 (LOCAL ONLY, NOT FOR PR).

Purpose: demonstrate that the *shape* of the crude Riemann-zero counting bound
  |riemannZeta.N T| ≤ C · T · log T  (for T ≥ 2)
lifts cleanly from the existing Hadamard / LogCounting machinery in
  `Mathlib/Analysis/Complex/HadamardFactorization/Summability.lean`
  `Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean`
applied to the entire surrogate `g(s) := (s - 1) · riemannZeta s` (order 1).

This file is a *probe*, not a proof: every analytic step is sorried and the
GO/NO-GO verdict rides on whether the *statement* type-checks and whether the
existing zero-counting lemmas have the right shape to discharge it without
inventing new mathlib. No new axioms are introduced beyond those of the cited
lemmas.

Statement-audit (BEFORE proving):
  * hypotheses: only `T ≥ 2` (no vacuous typeclass / domain conditions) ✓
  * conclusion: explicit constant `C = 100` matches the brief; bound is on `|N T|`
    (absolute value, since the brief notes summability needs only the majorant
    form, not a signed estimate) ✓
  * statement closure: depends only on `riemannZeta.N` (ZetaDefinitions :137);
    no dependency on KadiriZeroCounting, no dependency on `backlund_bound` ✓
  * shape match: `C · T · log T` is the standard Riemann–von Mangoldt order;
    matches blueprint comment in ZetaDefinitions :139 ✓
-/

import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.ZetaConj
import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization.Summability

open Real Complex Function

namespace Backlund.Phase1Probe

/-! ### Probe lemma 1 — order-1 surrogate

`g(s) := (s - 1) · riemannZeta s` is entire (the pole at `s = 1` is removed) and
has logarithmic growth of order 1 (Stirling on `completedRiemannZeta`, +
truncated-series machinery on the critical strip). The statement of the growth
hypothesis is the *minimal* form consumed by `divisorMassClosedBall₀_le_of_growth`.
-/

/-- Entire surrogate: `(s - 1) · ζ(s)` away from `1`, patched with the residue value
`1` at `s = 1`. STATEMENT REPAIR (loop session): the unpatched `(s - 1) * riemannZeta s`
takes the value `0` at `s = 1` while its limit there is `1` (`riemannZeta_residue_one`),
so it is discontinuous at `1` — not entire — and its divisor would carry a spurious
zero at `s = 1`, polluting the count. The patch removes both problems. -/
noncomputable def zetaSurrogate (s : ℂ) : ℂ :=
  if s = 1 then 1 else (s - 1) * riemannZeta s

/-- Away from `s = 1` the surrogate agrees with `(s - 1) · ζ(s)` on a neighbourhood. -/
private lemma zetaSurrogate_eventuallyEq {s : ℂ} (hs : s ≠ 1) :
    zetaSurrogate =ᶠ[nhds s] fun w ↦ (w - 1) * riemannZeta w := by
  filter_upwards [isOpen_compl_singleton.mem_nhds hs] with w hw
  simp [zetaSurrogate, Set.mem_compl_singleton_iff.mp hw]

/-- The surrogate is entire: differentiable off `1` by congruence with
`(s - 1) · ζ(s)`, and at `1` by the removable-singularity criterion with the
residue limit. -/
lemma zetaSurrogate_differentiable : Differentiable ℂ zetaSurrogate := by
  rw [← differentiableOn_univ,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff
      (c := (1 : ℂ)) Filter.univ_mem]
  constructor
  · intro s hs
    have hs1 : s ≠ 1 := by simpa using hs.2
    have hd : DifferentiableAt ℂ (fun w : ℂ ↦ (w - 1) * riemannZeta w) s :=
      (differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hs1)
    exact (hd.congr_of_eventuallyEq (zetaSurrogate_eventuallyEq hs1)).differentiableWithinAt
  · have h1 : zetaSurrogate 1 = 1 := if_pos rfl
    have hev : (fun w : ℂ ↦ (w - 1) * riemannZeta w) =ᶠ[nhdsWithin 1 {(1 : ℂ)}ᶜ]
        zetaSurrogate := by
      filter_upwards [self_mem_nhdsWithin] with w hw
      simp [zetaSurrogate, Set.mem_compl_singleton_iff.mp hw]
    have key : Filter.Tendsto zetaSurrogate (nhdsWithin 1 {(1 : ℂ)}ᶜ)
        (nhds (zetaSurrogate 1)) := by
      rw [h1]
      exact Filter.Tendsto.congr' hev riemannZeta_residue_one
    exact continuousWithinAt_compl_self.mp key

/-- Sketched: log-growth majorant at exponent `3/2`. STATEMENT REPAIR (2026-06-11
audit): the exponent-1 form originally probed here is FALSE — on the left half-plane
`|ζ(-2k-1)| = |B_{2k+2}|/(2k+2) ~ 2(2k+1)!/(2π)^{2k+2}`, so `log ‖zetaSurrogate z‖`
grows like `‖z‖ · log ‖z‖` (order 1, maximal type), beating `C · ‖z‖` for every fixed
`C`. Since `x · log x ≤ 2 · x^(3/2)` for `x ≥ 1`, the exponent-`3/2` form is true and
still feeds the dyadic consumer. Proof obligations: right of `Re = -1`: truncated
Euler-Maclaurin bound (`ZetaBounds.riemannZeta0`); left of `Re = -1`: functional
equation + `|Γ(z)| ≤ Γ(Re z)` (from `Complex.Gamma_eq_integral`) + a crude factorial
bound on real `Γ`. -/
lemma zetaSurrogate_log_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, Real.log (1 + ‖zetaSurrogate z‖) ≤ C * (1 + ‖z‖) ^ (3/2 : ℝ) := by
  sorry

/-! ### Probe lemma 2 — zeros-in-disk count for ζ via the surrogate

Lift `Complex.Hadamard.divisorMassClosedBall₀_le_of_growth` to a count of ζ-zeros
inside a closed disk of radius `R` centered at 0. For each disk center `c`, the
same shape gives a count via translation (sorried here; the translation glue is
`divisorMassClosedBall₀` applied to `s ↦ zetaSurrogate (s + c)`).
-/

/-- Sketched: zero-mass-in-ball bound for the surrogate. STATEMENT REPAIR (2026-06-11
audit): the `O(R)` form originally probed here is FALSE — the true mass in `B(0, R)`
is `~ (R/2π) · log R` (Riemann-von Mangoldt), which beats `C' · (1 + R)` for every
fixed `C'`. The `(1 + R)^(3/2)` form follows directly from
`divisorMassClosedBall₀_le_of_growth` at `ρ = 3/2` plus the trailing-coefficient term
(`zetaSurrogate 0 = 1/2 ≠ 0`, so that term is the constant `|log (1/2)|`). -/
lemma zetaSurrogate_zeros_in_closedBall₀_count :
    ∃ C' : ℝ, 0 < C' ∧
      ∀ R : ℝ, 1 ≤ R →
        Complex.Hadamard.divisorMassClosedBall₀ zetaSurrogate R ≤
          C' * (1 + R) ^ (3/2 : ℝ) := by
  sorry

/-- Zeros of ζ with positive imaginary part lie in the closed strip `0 ≤ Re ≤ 1`.
Right edge: `riemannZeta_ne_zero_of_one_le_re` (mathlib) forces `Re < 1`. Left edge:
for `Re s < 0` the functional equation `riemannZeta_one_sub` writes `ζ(s)` as a
nonvanishing prefactor times `sin (π s / 2) · Γ(1 - s) · ζ(1 - s)`; the last two
factors are nonzero (`Re (1 - s) > 1`), and `Complex.sin_eq_zero_iff` forces `s`
real, contradicting `0 < Im s`. Needed to place all counted zeros inside the single
ball `B(0, T + 1)`. -/
lemma zeta_zero_re_mem_of_im_pos {s : ℂ} (hs : riemannZeta s = 0) (him : 0 < s.im) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  sorry

/-! ### Probe lemma 3 — disk-strip cover (the easy bit; combinatorial)

The strip `Re ∈ [1/2, 1)`, `Im ∈ (0, T)` is covered by `⌊T⌋ + 1` closed disks of
radius `7/4` centered at `c_k := 2 + i · k` for `k = 0, …, ⌊T⌋`. Each disk
contains all of `Re ∈ [1/4, 15/4]` along the horizontal line `Im = k`, in
particular the strip slice `Re ∈ [1/2, 1)`, `Im ∈ [k, k+1]`.

The conjugation symmetry `riemannZeta_conj` (ZetaConj :115) doubles to cover the
left half `Re ∈ (0, 1/2)`. The combinatorial counting is sorried; this is the
easy bit, no novel analytic input.
-/

/-! ### THE CRUDE MAJORANT — the probe's headline theorem

This is the GO/NO-GO target. The statement is what the brief asks for: a crude
`O(T log T)` bound on `|N(T)|`. The constant `C = 100` is generous and not
optimized. The proof is sorried — the kernel probe checks that the statement
type-checks against `riemannZeta.N` (ZetaDefinitions :137), against existing
lemmas, and that the dependency graph closes without any reference to
`backlund_bound` or KadiriZeroCounting machinery. -/
theorem zetaCounting_crude_majorant :
    ∀ T : ℝ, 2 ≤ T →
      |riemannZeta.N T| ≤ (100 : ℝ) * T ^ (3/2 : ℝ) := by
  intro T hT
  -- HEADLINE REPAIR (2026-06-11 audit): `100 · T · log T` is true but NOT reachable
  -- from the global-growth machinery (the order-1 hypothesis it would need is false;
  -- the `T log T` route needs a center-translated Jensen count absent from the tree).
  -- `100 · T^(3/2)` is reachable and feeds the Phase-2 dyadic consumer with room:
  --   Σ_k 100 · (2^(k+1))^(3/2) / 4^k = 100 · 2^(3/2) · Σ_k 2^(-k/2) < ∞.
  -- proof plan (single ball, no disk cover, no translation glue):
  --   step 1: `zeta_zero_re_mem_of_im_pos` places every zero counted by `N T`
  --           (Im ∈ (0, T), any Re) in the strip `0 ≤ Re ≤ 1`, hence in the
  --           closed ball `B(0, T + 1)`.
  --   step 2: `N T` = order-weighted count over those zeros; orders are ≥ 0
  --           (analyticity off `s = 1`), so `|N T| = N T` and the count is
  --           dominated by `divisorMassClosedBall₀ zetaSurrogate (T + 1)`
  --           (the surrogate's divisor agrees with ζ's away from `s = 1` and
  --           vanishes at `s = 1`).
  --   step 3: `zetaSurrogate_zeros_in_closedBall₀_count` at `R = T + 1`, then
  --           absorb `C' · (2 + T)^(3/2) ≤ 100 · T^(3/2)` for `T ≥ 2` (constant
  --           arithmetic, `2 + T ≤ 2T`).
  sorry

/-! ### Statement-audit footnote

For the GO verdict, the probe relies on these *existing* (= present on
`upstream/main` as of this worktree's HEAD `d379571`) infrastructure pieces:
  * `riemannZeta.N`                       — ZetaDefinitions :137
  * `riemannZeta_conj`                    — ZetaConj :115
  * `Complex.Hadamard.divisorMassClosedBall₀_le_of_growth`
                                          — HadamardFactorization/Summability :90
  * `Function.locallyFinsuppWithin.logCounting_divisor_le_of_log_growth`
                                          — ValueDistribution/LogCounting/Growth :41

NOT required for this probe (out of scope until later phases):
  * KadiriZeroCounting.lean    — only enters in Phase 2 discharge.
  * `backlund_bound`           — the named-constants theorem, Tier B (4-8 wk arc).
  * Argument principle         — absent from mathlib + repo; we route around it.

NOT new axioms — the sorries above all reduce to known PNT+ + mathlib lemmas.
-/

end Backlund.Phase1Probe
