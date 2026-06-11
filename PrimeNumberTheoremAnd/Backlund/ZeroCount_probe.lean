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
import Mathlib.Analysis.Real.Pi.Bounds

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

/-- Elementary: `log x ≤ 2√x` for `x ≥ 1` (via `log √x ≤ √x - 1`). The helper that
absorbs every logarithm into the `3/2`-power below. -/
private lemma log_le_two_mul_sqrt {x : ℝ} (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt h0.le]; ring
  rw [h1]
  have h2 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr h0)
  nlinarith [Real.sqrt_nonneg x]

/-- Region `Re ≥ 2`: the Dirichlet series bounds `‖ζ‖` by an absolute constant, so the
surrogate's log-norm is linear in `‖z‖`. -/
private lemma surrogate_growth_right :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, 2 ≤ z.re →
      Real.log (1 + ‖zetaSurrogate z‖) ≤ B * (1 + ‖z‖) := by
  set M : ℝ := ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 with hM
  have hMsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hM0 : 0 ≤ M := tsum_nonneg fun n ↦ by positivity
  have hζ : ∀ z : ℂ, 2 ≤ z.re → ‖riemannZeta z‖ ≤ M := by
    intro z hz
    have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ = 1 / ((n : ℝ) + 1) ^ z.re := by
      intro n
      rw [norm_div, norm_one]
      congr 1
      have h1 : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [h1, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
      push_cast
      ring
    have hle : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
      intro n
      rw [hterm n]
      have hb1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hrw : ((n : ℝ) + 1) ^ (2 : ℕ) = ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
      have h2 : ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hb1 (by exact_mod_cast hz)
      rw [hrw]
      gcongr
    have hns : Summable (fun n : ℕ ↦ ‖1 / ((n : ℂ) + 1) ^ z‖) :=
      Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hMsum
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith : 1 < z.re)]
    calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ z‖
        ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ := norm_tsum_le_tsum_norm hns
      _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := Summable.tsum_le_tsum hle hns hMsum
  refine ⟨Real.log (1 + M) + 1, ?_, fun z hz ↦ ?_⟩
  · have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 1 + M)
    linarith
  · have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num [Complex.one_re] at hz
    have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hg : ‖zetaSurrogate z‖ ≤ M * (1 + ‖z‖) := by
      rw [zetaSurrogate, if_neg hz1, norm_mul]
      have h1 : ‖z - 1‖ ≤ 1 + ‖z‖ := by
        calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
          _ = 1 + ‖z‖ := by rw [norm_one]; ring
      calc ‖z - 1‖ * ‖riemannZeta z‖
          ≤ (1 + ‖z‖) * M :=
            mul_le_mul h1 (hζ z hz) (norm_nonneg _) (by linarith)
        _ = M * (1 + ‖z‖) := by ring
    have hMz : 1 + ‖zetaSurrogate z‖ ≤ (1 + M) * (1 + ‖z‖) := by
      nlinarith [hg, mul_nonneg hM0 hzn, norm_nonneg (zetaSurrogate z)]
    calc Real.log (1 + ‖zetaSurrogate z‖)
        ≤ Real.log ((1 + M) * (1 + ‖z‖)) :=
          Real.log_le_log (by positivity) hMz
      _ = Real.log (1 + M) + Real.log (1 + ‖z‖) :=
          Real.log_mul (by linarith) (by linarith)
      _ ≤ Real.log (1 + M) * (1 + ‖z‖) + (1 + ‖z‖) := by
          have hl1 : Real.log (1 + M) ≤ Real.log (1 + M) * (1 + ‖z‖) :=
            le_mul_of_one_le_right (Real.log_nonneg (by linarith)) (by linarith)
          have hl2 : Real.log (1 + ‖z‖) ≤ 1 + ‖z‖ := by
            have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + ‖z‖)
            linarith
          linarith
      _ = (Real.log (1 + M) + 1) * (1 + ‖z‖) := by ring

/-- Critical band `-1 ≤ Re ≤ 2`: polynomial bound on the surrogate via the truncated
Euler-Maclaurin representation (`ZetaBounds.riemannZeta0`) for `|Im| ≥ 1`, and
compactness of the box (the patch removes the pole) for `|Im| ≤ 1`; logs of
polynomials are linear via `log_le_two_mul_sqrt`. -/
private lemma surrogate_growth_band :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 2 →
      Real.log (1 + ‖zetaSurrogate z‖) ≤ B * (1 + ‖z‖) := by
  sorry

/-- The Euler integral bounds the complex `Γ` by the real `Γ` of the real part, on the
right half-plane. Not in Mathlib; the keystone for the left-region growth bound. -/
private lemma norm_Gamma_le_Gamma_re {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  rw [Complex.Gamma_eq_integral hz, Real.Gamma_eq_integral hz]
  unfold Complex.GammaIntegral
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  rw [Set.mem_Ioi] at hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp [Complex.sub_re, Complex.one_re]

/-- `Γ ≤ 2` on `[1, 2]`: the integrand is dominated by `e⁻ᵗ(t⁰ + t¹)`, whose integral
is `Γ(1) + Γ(2) = 2`. -/
private lemma Gamma_le_two_of_mem_Icc {x : ℝ} (h1 : 1 ≤ x) (h2 : x ≤ 2) :
    Real.Gamma x ≤ 2 := by
  have hx0 : 0 < x := by linarith
  have hΓ2 : Real.Gamma 2 = 1 := by
    norm_num
  rw [Real.Gamma_eq_integral hx0]
  have key : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1)) ≤
      ∫ t in Set.Ioi (0 : ℝ),
        (Real.exp (-t) * t ^ ((1 : ℝ) - 1) + Real.exp (-t) * t ^ ((2 : ℝ) - 1)) := by
    refine MeasureTheory.setIntegral_mono_on (Real.GammaIntegral_convergent hx0)
      ((Real.GammaIntegral_convergent one_pos).add (Real.GammaIntegral_convergent two_pos))
      measurableSet_Ioi fun t ht ↦ ?_
    rw [Set.mem_Ioi] at ht
    have he : (0 : ℝ) ≤ Real.exp (-t) := (Real.exp_pos _).le
    rcases le_total t 1 with htle | htge
    · have hpow : t ^ (x - 1) ≤ t ^ ((1 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_ge ht htle (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hpow he,
        mul_nonneg he (Real.rpow_nonneg ht.le ((2 : ℝ) - 1))]
    · have hpow : t ^ (x - 1) ≤ t ^ ((2 : ℝ) - 1) :=
        Real.rpow_le_rpow_of_exponent_le htge (by linarith)
      nlinarith [mul_le_mul_of_nonneg_left hpow he,
        mul_nonneg he (Real.rpow_nonneg ht.le ((1 : ℝ) - 1))]
  calc (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * t ^ (x - 1))
      ≤ ∫ t in Set.Ioi (0 : ℝ),
          (Real.exp (-t) * t ^ ((1 : ℝ) - 1) + Real.exp (-t) * t ^ ((2 : ℝ) - 1)) := key
    _ = Real.Gamma 1 + Real.Gamma 2 := by
        rw [MeasureTheory.integral_add (Real.GammaIntegral_convergent one_pos)
          (Real.GammaIntegral_convergent two_pos), Real.Gamma_eq_integral one_pos,
          Real.Gamma_eq_integral two_pos]
    _ = 2 := by rw [Real.Gamma_one, hΓ2]; norm_num

/-- Crude factorial bound: `Γ(x) ≤ 2 · (n+1)!` for `1 ≤ x ≤ n + 2`, by induction
through the recursion `Γ(x) = (x-1)Γ(x-1)`. -/
private lemma Gamma_le_two_mul_factorial :
    ∀ (n : ℕ) {x : ℝ}, 1 ≤ x → x ≤ n + 2 →
      Real.Gamma x ≤ 2 * ((n + 1).factorial : ℝ) := by
  intro n
  induction n with
  | zero =>
    intro x h1 h2
    push_cast at h2
    simpa using Gamma_le_two_of_mem_Icc h1 (by linarith)
  | succ m ih =>
    intro x h1 h2
    rcases le_total x ((m : ℝ) + 2) with hle | hge
    · refine (ih h1 hle).trans ?_
      have hf : ((m + 1).factorial : ℝ) ≤ (((m + 1) + 1).factorial : ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega)
      linarith
    · have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hx1ne : x - 1 ≠ 0 := by nlinarith
      have hrec : Real.Gamma x = (x - 1) * Real.Gamma (x - 1) := by
        have h := Real.Gamma_add_one hx1ne
        simpa using h
      have hih : Real.Gamma (x - 1) ≤ 2 * ((m + 1).factorial : ℝ) := by
        refine ih (by nlinarith) ?_
        push_cast at h2
        linarith
      have hxb : x - 1 ≤ (m : ℝ) + 2 := by
        push_cast at h2
        linarith
      have hΓnn : 0 ≤ Real.Gamma (x - 1) :=
        (Real.Gamma_pos_of_pos (by nlinarith)).le
      rw [hrec]
      calc (x - 1) * Real.Gamma (x - 1)
          ≤ ((m : ℝ) + 2) * (2 * ((m + 1).factorial : ℝ)) :=
            mul_le_mul hxb hih hΓnn (by positivity)
        _ = 2 * ((((m + 1) + 1)).factorial : ℝ) := by
            rw [Nat.factorial_succ (m + 1)]
            push_cast
            ring

/-- The cosine is dominated by the exponential of the norm, via the exponential
formula and `‖exp u‖ = exp (Re u)`. -/
private lemma norm_cos_le_exp (v : ℂ) : ‖Complex.cos v‖ ≤ Real.exp ‖v‖ := by
  have h1 : ‖Complex.exp (v * Complex.I)‖ ≤ Real.exp ‖v‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have him := Complex.abs_im_le_norm v
    have hre : (v * Complex.I).re = -v.im := by simp [Complex.mul_re]
    rw [hre]
    have : -v.im ≤ |v.im| := neg_le_abs v.im
    linarith
  have h2 : ‖Complex.exp (-v * Complex.I)‖ ≤ Real.exp ‖v‖ := by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr ?_
    have him := Complex.abs_im_le_norm v
    have hre : (-v * Complex.I).re = v.im := by simp [Complex.mul_re]
    rw [hre]
    have : v.im ≤ |v.im| := le_abs_self v.im
    linarith
  unfold Complex.cos
  calc ‖(Complex.exp (v * Complex.I) + Complex.exp (-v * Complex.I)) / 2‖
      = ‖Complex.exp (v * Complex.I) + Complex.exp (-v * Complex.I)‖ / 2 := by
        rw [norm_div]
        norm_num
    _ ≤ (‖Complex.exp (v * Complex.I)‖ + ‖Complex.exp (-v * Complex.I)‖) / 2 := by
        have := norm_add_le (Complex.exp (v * Complex.I)) (Complex.exp (-v * Complex.I))
        linarith
    _ ≤ Real.exp ‖v‖ := by linarith

/-- Splitting logs across products shifted by one. -/
private lemma log_one_add_mul_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.log (1 + a * b) ≤ Real.log (1 + a) + Real.log (1 + b) := by
  rw [← Real.log_mul (by linarith) (by linarith)]
  refine Real.log_le_log (by nlinarith) (by nlinarith)

/-- The uniform series bound on `Re ≥ 2`, packaged for reuse (the analogous bound is
inlined in `surrogate_growth_right`; deduplicate at promotion). -/
private lemma exists_zeta_bound_right :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ, 2 ≤ z.re → ‖riemannZeta z‖ ≤ M := by
  refine ⟨∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2, tsum_nonneg fun n ↦ by positivity, ?_⟩
  intro z hz
  have hMsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
    have h := (summable_nat_add_iff (f := fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) 1).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa using h
  have hterm : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ = 1 / ((n : ℝ) + 1) ^ z.re := by
    intro n
    rw [norm_div, norm_one]
    congr 1
    have h1 : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos n)]
    push_cast
    ring
  have hle : ∀ n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
    intro n
    rw [hterm n]
    have hb1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hrw : ((n : ℝ) + 1) ^ (2 : ℕ) = ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
    have h2 : ((n : ℝ) + 1) ^ ((2 : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le hb1 (by exact_mod_cast hz)
    rw [hrw]
    gcongr
  have hns : Summable (fun n : ℕ ↦ ‖1 / ((n : ℂ) + 1) ^ z‖) :=
    Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hMsum
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by linarith : 1 < z.re)]
  calc ‖∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ z‖
      ≤ ∑' n : ℕ, ‖1 / ((n : ℂ) + 1) ^ z‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 2 := Summable.tsum_le_tsum hle hns hMsum

/-- Left region `Re ≤ -1`: the functional equation with `|Γ(1-z)| ≤ Γ(1 - Re z)` and a
crude factorial bound; the `Γ`-growth is what forces the `3/2` exponent. -/
private lemma surrogate_growth_left :
    ∃ B : ℝ, 0 < B ∧ ∀ z : ℂ, z.re ≤ -1 →
      Real.log (1 + ‖zetaSurrogate z‖) ≤ B * (1 + ‖z‖) ^ (3/2 : ℝ) := by
  obtain ⟨M, hM0, hM⟩ := exists_zeta_bound_right
  refine ⟨2 + (Real.log 2 + Real.pi) + (Real.log (1 + 4 * M) + Real.log 2)
      + 3 * (Real.log 3 + 2) + 1, ?_, fun z hz ↦ ?_⟩
  · have l2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
    have l3 : (0 : ℝ) ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have l4 : (0 : ℝ) ≤ Real.log (1 + 4 * M) := Real.log_nonneg (by linarith)
    have := Real.pi_pos
    linarith
  · set w : ℂ := 1 - z with hw
    have hzn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    have hwre : 2 ≤ w.re := by
      rw [hw]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
      intro n h
      have h' := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at h'
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.one_re] at h'
      linarith
    have hz1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      norm_num [Complex.one_re] at hz
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : (1 : ℂ) - w = z := by rw [hw]; ring
    rw [h1w] at hfe
    have hwnorm : ‖w‖ ≤ 1 + ‖z‖ := by
      rw [hw]
      calc ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le 1 z
        _ = 1 + ‖z‖ := by rw [norm_one]
    have hpow_bound : ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ ≤ 1 := by
      have h2π : ((2 : ℂ) * (Real.pi : ℂ)) = (((2 * Real.pi : ℝ)) : ℂ) := by
        push_cast; ring
      rw [h2π, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
      refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
      · nlinarith [Real.pi_gt_three]
      · simp only [Complex.neg_re]
        linarith
    have hΓn : ‖Complex.Gamma w‖ ≤ Real.Gamma w.re :=
      norm_Gamma_le_Gamma_re (by linarith)
    set n : ℕ := ⌈w.re⌉₊ with hn
    have hΓfac : Real.Gamma w.re ≤ 2 * ((n + 1).factorial : ℝ) := by
      refine Gamma_le_two_mul_factorial n (by linarith) ?_
      have hceil := Nat.le_ceil w.re
      rw [← hn] at hceil
      push_cast
      linarith
    have hcos : ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ ≤
        Real.exp (Real.pi * ‖w‖ / 2) := by
      refine (norm_cos_le_exp _).trans ?_
      refine Real.exp_le_exp.mpr (le_of_eq ?_)
      rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      norm_num
    have hζw : ‖riemannZeta w‖ ≤ M := hM w hwre
    have hΓ2 : ‖Complex.Gamma w‖ ≤ 2 * ((n + 1).factorial : ℝ) := hΓn.trans hΓfac
    have hfacnn : (1 : ℝ) ≤ ((n + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hgz : ‖zetaSurrogate z‖ ≤
        (1 + ‖z‖) * ((4 * M * ((n + 1).factorial : ℝ)) *
          Real.exp (Real.pi * ‖w‖ / 2)) := by
      rw [zetaSurrogate, if_neg hz1, norm_mul]
      have hz1n : ‖z - 1‖ ≤ 1 + ‖z‖ := by
        calc ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ := norm_sub_le z 1
          _ = 1 + ‖z‖ := by rw [norm_one]; ring
      have hζz : ‖riemannZeta z‖ ≤ (4 * M * ((n + 1).factorial : ℝ)) *
          Real.exp (Real.pi * ‖w‖ / 2) := by
        rw [hfe, norm_mul, norm_mul, norm_mul, norm_mul]
        have e2 : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [e2]
        calc 2 * ‖((2 : ℂ) * (Real.pi : ℂ)) ^ (-w)‖ * ‖Complex.Gamma w‖ *
              ‖Complex.cos ((Real.pi : ℂ) * w / 2)‖ * ‖riemannZeta w‖
            ≤ 2 * 1 * (2 * ((n + 1).factorial : ℝ)) *
              Real.exp (Real.pi * ‖w‖ / 2) * M := by
              gcongr
            _ = (4 * M * ((n + 1).factorial : ℝ)) *
              Real.exp (Real.pi * ‖w‖ / 2) := by ring
      exact mul_le_mul hz1n hζz (norm_nonneg _) (by linarith)
    -- the log chain
    have hK1 : (1 : ℝ) ≤ (1 + ‖z‖) ^ (3/2 : ℝ) := by
      calc (1 : ℝ) = 1 ^ (3/2 : ℝ) := (Real.one_rpow _).symm
        _ ≤ _ := Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
    have hKlin : (1 + ‖z‖) ≤ (1 + ‖z‖) ^ (3/2 : ℝ) := by
      calc (1 + ‖z‖) = (1 + ‖z‖) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    have hFnn : (0 : ℝ) ≤ 4 * M * ((n + 1).factorial : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hM0) (Nat.cast_nonneg _)
    have hE1 : (1 : ℝ) ≤ Real.exp (Real.pi * ‖w‖ / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by positivity)
    have step1 : Real.log (1 + ‖zetaSurrogate z‖) ≤
        Real.log (1 + (1 + ‖z‖) * ((4 * M * ((n + 1).factorial : ℝ)) *
          Real.exp (Real.pi * ‖w‖ / 2))) := by
      refine Real.log_le_log (by positivity) ?_
      linarith [hgz]
    have step2 := log_one_add_mul_le (a := 1 + ‖z‖)
      (b := (4 * M * ((n + 1).factorial : ℝ)) * Real.exp (Real.pi * ‖w‖ / 2))
      (by linarith) (mul_nonneg hFnn (by linarith))
    have step3 := log_one_add_mul_le (a := 4 * M * ((n + 1).factorial : ℝ))
      (b := Real.exp (Real.pi * ‖w‖ / 2)) hFnn (by linarith)
    have p1 : Real.log (1 + (1 + ‖z‖)) ≤ 2 * (1 + ‖z‖) := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + (1 + ‖z‖) by linarith)
      linarith
    have p3 : Real.log (1 + Real.exp (Real.pi * ‖w‖ / 2)) ≤
        Real.log 2 + Real.pi * (1 + ‖z‖) / 2 := by
      have h1 : (1 : ℝ) + Real.exp (Real.pi * ‖w‖ / 2) ≤
          2 * Real.exp (Real.pi * ‖w‖ / 2) := by linarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at h2
      have h3 : Real.pi * ‖w‖ / 2 ≤ Real.pi * (1 + ‖z‖) / 2 := by
        have := Real.pi_pos
        nlinarith [hwnorm]
      linarith
    have p2 : Real.log (1 + 4 * M * ((n + 1).factorial : ℝ)) ≤
        Real.log (1 + 4 * M) + Real.log 2 +
          3 * (Real.log 3 + 2) * (1 + ‖z‖) ^ (3/2 : ℝ) := by
      have s1 := log_one_add_mul_le (a := 4 * M) (b := ((n + 1).factorial : ℝ))
        (by linarith) (Nat.cast_nonneg _)
      have s2 : Real.log (1 + ((n + 1).factorial : ℝ)) ≤
          Real.log 2 + Real.log ((n + 1).factorial : ℝ) := by
        have h1 : (1 : ℝ) + ((n + 1).factorial : ℝ) ≤
            2 * ((n + 1).factorial : ℝ) := by linarith
        have h2 := Real.log_le_log (by linarith) h1
        rwa [Real.log_mul two_ne_zero (by linarith)] at h2
      have s3 : Real.log ((n + 1).factorial : ℝ) ≤
          ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) := by
        have hle : ((n + 1).factorial : ℝ) ≤ (((n + 1) : ℕ) : ℝ) ^ ((n + 1) : ℕ) := by
          exact_mod_cast Nat.factorial_le_pow (n + 1)
        have h2 := Real.log_le_log (by linarith) hle
        rw [Real.log_pow] at h2
        push_cast at h2 ⊢
        linarith
      have hnb : ((n : ℝ) + 1) ≤ 3 * (1 + ‖z‖) := by
        have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ w.re by linarith)
        rw [← hn] at hceil
        have hre : w.re ≤ 1 + ‖z‖ := by
          have h1 : w.re ≤ |w.re| := le_abs_self _
          have h2 := Complex.abs_re_le_norm w
          linarith [hwnorm]
        linarith
      have hlogn_nn : (0 : ℝ) ≤ Real.log ((n : ℝ) + 1) := by
        refine Real.log_nonneg ?_
        have := Nat.cast_nonneg (α := ℝ) n
        linarith
      have hlogn : Real.log ((n : ℝ) + 1) ≤
          (Real.log 3 + 2) * (1 + ‖z‖) ^ ((1 : ℝ) / 2) := by
        have h1 : Real.log ((n : ℝ) + 1) ≤ Real.log (3 * (1 + ‖z‖)) := by
          refine Real.log_le_log ?_ hnb
          have := Nat.cast_nonneg (α := ℝ) n
          linarith
        rw [Real.log_mul (by norm_num) (by linarith)] at h1
        have h2 : Real.log (1 + ‖z‖) ≤ 2 * Real.sqrt (1 + ‖z‖) :=
          log_le_two_mul_sqrt (by linarith)
        rw [Real.sqrt_eq_rpow] at h2
        have h3 : (1 : ℝ) ≤ (1 + ‖z‖) ^ ((1 : ℝ) / 2) := by
          calc (1 : ℝ) = 1 ^ ((1 : ℝ) / 2) := (Real.one_rpow _).symm
            _ ≤ _ := Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
        nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 by norm_num)]
      have hs32 : ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) ≤
          3 * (Real.log 3 + 2) * (1 + ‖z‖) ^ (3/2 : ℝ) := by
        have hmul := mul_le_mul hnb hlogn hlogn_nn (by positivity)
        refine hmul.trans (le_of_eq ?_)
        rw [show (3 : ℝ)/2 = 1 + 1/2 by norm_num, Real.rpow_add (by linarith),
          Real.rpow_one]
        ring
      linarith [s1, s2, s3, hs32]
    -- final assembly
    have l2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg one_le_two
    have l4 : (0 : ℝ) ≤ Real.log (1 + 4 * M) := Real.log_nonneg (by linarith)
    have q1 : 2 * (1 + ‖z‖) ≤ 2 * (1 + ‖z‖) ^ (3/2 : ℝ) := by linarith [hKlin]
    have q2 : Real.log (1 + 4 * M) ≤
        Real.log (1 + 4 * M) * (1 + ‖z‖) ^ (3/2 : ℝ) :=
      le_mul_of_one_le_right l4 hK1
    have q3 : Real.log 2 ≤ Real.log 2 * (1 + ‖z‖) ^ (3/2 : ℝ) :=
      le_mul_of_one_le_right l2 hK1
    have q4 : Real.pi * (1 + ‖z‖) / 2 ≤ Real.pi * (1 + ‖z‖) ^ (3/2 : ℝ) := by
      have := Real.pi_pos
      nlinarith [hKlin]
    have hBK : (2 + (Real.log 2 + Real.pi) + (Real.log (1 + 4 * M) + Real.log 2)
        + 3 * (Real.log 3 + 2) + 1) * (1 + ‖z‖) ^ (3/2 : ℝ) =
        2 * (1 + ‖z‖) ^ (3/2 : ℝ) + Real.log 2 * (1 + ‖z‖) ^ (3/2 : ℝ)
        + Real.pi * (1 + ‖z‖) ^ (3/2 : ℝ)
        + Real.log (1 + 4 * M) * (1 + ‖z‖) ^ (3/2 : ℝ)
        + Real.log 2 * (1 + ‖z‖) ^ (3/2 : ℝ)
        + 3 * (Real.log 3 + 2) * (1 + ‖z‖) ^ (3/2 : ℝ)
        + (1 + ‖z‖) ^ (3/2 : ℝ) := by ring
    have hK0 : (0 : ℝ) ≤ (1 + ‖z‖) ^ (3/2 : ℝ) := by linarith [hK1]
    linarith [step1, step2, step3, p1, p2, p3, q1, q2, q3, q4, hBK, hK1]

/-- The exponent-`3/2` log-growth majorant for the surrogate. The exponent-1 form is
FALSE on the left half-plane (`|ζ(-2k-1)| ~ 2(2k+1)!/(2π)^{2k+2}` via Bernoulli
numbers: order 1 but maximal type), and `x log x ≤ 2 x^(3/2)` restores a true bound.
Assembled from the three region lemmas above. -/
lemma zetaSurrogate_log_growth :
    ∃ C : ℝ, 0 < C ∧
      ∀ z : ℂ, Real.log (1 + ‖zetaSurrogate z‖) ≤ C * (1 + ‖z‖) ^ (3/2 : ℝ) := by
  obtain ⟨B₁, hB₁0, hB₁⟩ := surrogate_growth_right
  obtain ⟨B₂, hB₂0, hB₂⟩ := surrogate_growth_band
  obtain ⟨B₃, hB₃0, hB₃⟩ := surrogate_growth_left
  refine ⟨B₁ + B₂ + B₃, by linarith, fun z ↦ ?_⟩
  have hz1 : (1 : ℝ) ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hpos : (0 : ℝ) < (1 + ‖z‖) ^ (3/2 : ℝ) :=
    Real.rpow_pos_of_pos (by linarith [norm_nonneg z]) _
  have hpow : (1 + ‖z‖) ≤ (1 + ‖z‖) ^ (3/2 : ℝ) := by
    calc (1 + ‖z‖) = (1 + ‖z‖) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (1 + ‖z‖) ^ (3/2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hz1 (by norm_num)
  rcases le_total z.re (-1) with h | h
  · refine (hB₃ z h).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hpos.le
    linarith
  · rcases le_total z.re 2 with h2 | h2
    · refine (hB₂ z h h2).trans ?_
      calc B₂ * (1 + ‖z‖)
          ≤ B₂ * (1 + ‖z‖) ^ (3/2 : ℝ) := mul_le_mul_of_nonneg_left hpow hB₂0.le
        _ ≤ (B₁ + B₂ + B₃) * (1 + ‖z‖) ^ (3/2 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le
    · refine (hB₁ z h2).trans ?_
      calc B₁ * (1 + ‖z‖)
          ≤ B₁ * (1 + ‖z‖) ^ (3/2 : ℝ) := mul_le_mul_of_nonneg_left hpow hB₁0.le
        _ ≤ (B₁ + B₂ + B₃) * (1 + ‖z‖) ^ (3/2 : ℝ) :=
            mul_le_mul_of_nonneg_right (by linarith) hpos.le

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
  obtain ⟨C, hC0, hC⟩ := zetaSurrogate_log_growth
  set K : ℝ := |Real.log ‖meromorphicTrailingCoeffAt zetaSurrogate 0‖| with hK
  refine ⟨(C * 2 ^ (3/2 : ℝ) + K) / Real.log 2, ?_, ?_⟩
  · refine div_pos ?_ (Real.log_pos one_lt_two)
    have h2 : (0 : ℝ) < 2 ^ (3/2 : ℝ) := Real.rpow_pos_of_pos two_pos _
    have hKnn : (0 : ℝ) ≤ K := abs_nonneg _
    nlinarith [mul_pos hC0 h2]
  · intro R hR
    have hmass := Complex.Hadamard.divisorMassClosedBall₀_le_of_growth
      zetaSurrogate_differentiable hC hR
    refine hmass.trans ?_
    rw [div_mul_eq_mul_div, div_eq_mul_inv, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr (Real.log_nonneg one_le_two))
    have habs : |2 * R| = 2 * R := abs_of_nonneg (by linarith)
    rw [habs]
    have h1R : (0 : ℝ) ≤ 1 + R := by linarith
    have hone : (1 : ℝ) ≤ (1 + R) ^ (3/2 : ℝ) := by
      calc (1 : ℝ) = (1 : ℝ) ^ (3/2 : ℝ) := (Real.one_rpow _).symm
        _ ≤ (1 + R) ^ (3/2 : ℝ) :=
          Real.rpow_le_rpow zero_le_one (by linarith) (by norm_num)
    have hpow : (1 + 2 * R) ^ (3/2 : ℝ) ≤ 2 ^ (3/2 : ℝ) * (1 + R) ^ (3/2 : ℝ) := by
      rw [← Real.mul_rpow (by norm_num) h1R]
      exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
    have hKnn : (0 : ℝ) ≤ K := abs_nonneg _
    calc C * (1 + 2 * R) ^ (3/2 : ℝ) + K
        ≤ C * (2 ^ (3/2 : ℝ) * (1 + R) ^ (3/2 : ℝ)) + K * (1 + R) ^ (3/2 : ℝ) :=
          add_le_add (mul_le_mul_of_nonneg_left hpow hC0.le)
            (le_mul_of_one_le_right hKnn hone)
      _ = (C * 2 ^ (3/2 : ℝ) + K) * (1 + R) ^ (3/2 : ℝ) := by ring

/-- Zeros of ζ with positive imaginary part lie in the closed strip `0 ≤ Re ≤ 1`.
Right edge: `riemannZeta_ne_zero_of_one_le_re` (mathlib) forces `Re < 1`. Left edge:
for `Re s < 0` the functional equation `riemannZeta_one_sub` writes `ζ(s)` as a
nonvanishing prefactor times `sin (π s / 2) · Γ(1 - s) · ζ(1 - s)`; the last two
factors are nonzero (`Re (1 - s) > 1`), and `Complex.sin_eq_zero_iff` forces `s`
real, contradicting `0 < Im s`. Needed to place all counted zeros inside the single
ball `B(0, T + 1)`. -/
lemma zeta_zero_re_mem_of_im_pos {s : ℂ} (hs : riemannZeta s = 0) (him : 0 < s.im) :
    0 ≤ s.re ∧ s.re ≤ 1 := by
  refine ⟨?_, ?_⟩
  · by_contra hre
    push_neg at hre
    set w : ℂ := 1 - s with hw
    have hwre : 1 < w.re := by
      rw [hw]
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hwn : ∀ n : ℕ, w ≠ -(n : ℂ) := by
      intro n h
      have h' := congrArg Complex.re h
      simp only [Complex.neg_re, Complex.natCast_re] at h'
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hw1 : w ≠ 1 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.one_re] at h'
      linarith
    have hfe := riemannZeta_one_sub hwn hw1
    have h1w : (1 : ℂ) - w = s := by
      rw [hw]; ring
    rw [h1w, hs] at hfe
    have hζw : riemannZeta w ≠ 0 := riemannZeta_ne_zero_of_one_le_re hwre.le
    have hΓ : Complex.Gamma w ≠ 0 := Complex.Gamma_ne_zero hwn
    have h2π : ((2 : ℂ) * (Real.pi : ℂ)) ^ (-w) ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero (by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨two_ne_zero, by exact_mod_cast Real.pi_ne_zero⟩)]
      exact Complex.exp_ne_zero _
    have hprod := hfe.symm
    simp only [mul_eq_zero] at hprod
    have hcos : Complex.cos ((Real.pi : ℂ) * w / 2) = 0 := by
      rcases hprod with ((((h | h) | h) | h) | h)
      · norm_num at h
      · exact absurd h h2π
      · exact absurd h hΓ
      · exact h
      · exact absurd h hζw
    rw [Complex.cos_eq_zero_iff] at hcos
    obtain ⟨k, hk⟩ := hcos
    have hπ : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * w = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination 2 * hk
    have hwk : w = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hπ h2
    have himw := congrArg Complex.im hwk
    simp [hw] at himw
    linarith
  · by_contra hre
    push_neg at hre
    exact riemannZeta_ne_zero_of_one_le_re hre.le hs

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
/-- Order transport: away from `s = 1`, the surrogate's divisor value is exactly the
ζ-order (the linear factor is analytic and nonvanishing there, and the patch is
invisible on a punctured neighbourhood). -/
private lemma divisor_surrogate_eq_order {ρ : ℂ} (hρ : ρ ≠ 1) :
    (MeromorphicOn.divisor zetaSurrogate Set.univ) ρ = riemannZeta.order ρ := by
  have hζan : AnalyticAt ℂ riemannZeta ρ :=
    riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr hρ)
  have hlin : AnalyticAt ℂ (fun w : ℂ ↦ w - 1) ρ := by fun_prop
  have hmero : MeromorphicOn zetaSurrogate Set.univ := fun x _ ↦
    (zetaSurrogate_differentiable.analyticAt x).meromorphicAt
  rw [MeromorphicOn.divisor_apply hmero (Set.mem_univ ρ)]
  have hcongr : meromorphicOrderAt zetaSurrogate ρ =
      meromorphicOrderAt (fun w ↦ (w - 1) * riemannZeta w) ρ :=
    meromorphicOrderAt_congr
      ((zetaSurrogate_eventuallyEq hρ).filter_mono nhdsWithin_le_nhds)
  have hmul : meromorphicOrderAt (fun w ↦ (w - 1) * riemannZeta w) ρ =
      meromorphicOrderAt (fun w : ℂ ↦ w - 1) ρ + meromorphicOrderAt riemannZeta ρ :=
    meromorphicOrderAt_mul hlin.meromorphicAt hζan.meromorphicAt
  have hlin0 : meromorphicOrderAt (fun w : ℂ ↦ w - 1) ρ = 0 := by
    rw [hlin.meromorphicOrderAt_eq]
    have h0 : analyticOrderAt (fun w : ℂ ↦ w - 1) ρ = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by simpa [sub_eq_zero] using hρ))
    simp [h0]
  rw [hcongr, hmul, hlin0, zero_add, riemannZeta.order]
  rfl

lemma zetaCounting_le_surrogate_mass :
    ∀ T : ℝ, 2 ≤ T →
      |riemannZeta.N T| ≤
        Complex.Hadamard.divisorMassClosedBall₀ zetaSurrogate (T + 1) := by
  intro T hT
  classical
  -- localization: the rect over `univ` equals the rect over the closed strip
  have hseteq : riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T) =
      riemannZeta.zeroes_rect (Set.Icc 0 1) (Set.Ioo 0 T) := by
    ext ρ
    simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq,
      Set.mem_univ, true_and, Set.mem_Icc, Set.mem_Ioo]
    constructor
    · rintro ⟨him, hzero⟩
      exact ⟨zeta_zero_re_mem_of_im_pos hzero him.1, ⟨him, hzero⟩⟩
    · rintro ⟨-, him, hzero⟩
      exact ⟨him, hzero⟩
  have hfin : (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)).Finite := by
    rw [hseteq, riemannZeta.zeroes_rect_eq]
    refine (riemannZeta.zeroes_on_Compact_finite' ?_).subset
      (Set.inter_subset_inter (Set.inter_subset_inter_right _
        (Set.preimage_mono Set.Ioo_subset_Icc_self)) le_rfl)
    exact Complex.equivRealProdCLM.toHomeomorph.isClosedEmbedding.isCompact_preimage
      (isCompact_Icc.prod isCompact_Icc)
  -- basic facts about rect members
  have hmem : ∀ ρ ∈ riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T),
      riemannZeta ρ = 0 ∧ 0 < ρ.im ∧ ρ.im < T ∧ 0 ≤ ρ.re ∧ ρ.re ≤ 1 ∧ ρ ≠ 1 := by
    intro ρ hρ
    rw [hseteq] at hρ
    simp only [riemannZeta.zeroes_rect, riemannZeta.zeroes, Set.mem_setOf_eq,
      Set.mem_Icc, Set.mem_Ioo] at hρ
    obtain ⟨⟨hre0, hre1⟩, ⟨him0, himT⟩, hzero⟩ := hρ
    refine ⟨hzero, him0, himT, hre0, hre1, fun h ↦ ?_⟩
    rw [h] at him0
    simp [Complex.one_im] at him0
  -- N T as a finite sum
  have hNT : riemannZeta.N T =
      ∑ ρ ∈ hfin.toFinset, ((riemannZeta.order ρ : ℤ) : ℝ) := by
    have h1 : riemannZeta.N T =
        ∑' (ρ : ↑(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T))),
          (fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) ↑ρ := by
      rw [riemannZeta.N, riemannZeta.zeroes_sum]
      simp
    calc riemannZeta.N T
        = ∑' (ρ : ↑(riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T))),
            (fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) ↑ρ := h1
      _ = ∑' (z : ℂ), (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)).indicator
            (fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) z :=
          tsum_subtype (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T))
            (fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ))
      _ = ∑ ρ ∈ hfin.toFinset,
            (riemannZeta.zeroes_rect Set.univ (Set.Ioo 0 T)).indicator
              (fun z : ℂ ↦ ((riemannZeta.order z : ℤ) : ℝ)) ρ :=
          tsum_eq_sum (fun b hb ↦
            Set.indicator_of_notMem (fun hmem ↦ hb (hfin.mem_toFinset.mpr hmem)) _)
      _ = ∑ ρ ∈ hfin.toFinset, ((riemannZeta.order ρ : ℤ) : ℝ) :=
          Finset.sum_congr rfl fun ρ hρ ↦ by
            rw [Set.indicator_of_mem (hfin.mem_toFinset.mp hρ)]
  -- order nonnegativity on the rect
  have hnn : ∀ ρ ∈ hfin.toFinset, (0 : ℝ) ≤ ((riemannZeta.order ρ : ℤ) : ℝ) := by
    intro ρ hρ
    obtain ⟨-, -, -, -, -, hρ1⟩ := hmem ρ (hfin.mem_toFinset.mp hρ)
    have hana : AnalyticAt ℂ riemannZeta ρ :=
      riemannZeta_analyticOn_compl_one _ (Set.mem_compl_singleton_iff.mpr hρ1)
    have hord := hana.meromorphicOrderAt_nonneg
    suffices h : (0 : ℤ) ≤ riemannZeta.order ρ by exact_mod_cast h
    rw [riemannZeta.order]
    cases horder : meromorphicOrderAt riemannZeta ρ with
    | top => exact le_rfl
    | coe n =>
      rw [horder] at hord
      change (0 : ℤ) ≤ n
      exact_mod_cast hord
  -- the divisor of the surrogate
  set D := MeromorphicOn.divisor zetaSurrogate Set.univ with hDdef
  have hterm : ∀ ρ ∈ hfin.toFinset,
      ((riemannZeta.order ρ : ℤ) : ℝ) = ((D ρ : ℤ) : ℝ) := by
    intro ρ hρ
    obtain ⟨-, -, -, -, -, hρ1⟩ := hmem ρ (hfin.mem_toFinset.mp hρ)
    rw [hDdef, divisor_surrogate_eq_order hρ1]
  have hDnn : 0 ≤ D := Differentiable.divisor_nonneg zetaSurrogate_differentiable
  -- assemble: |N T| = N T = Σ orders = Σ divisor values ≤ mass
  have habs : |riemannZeta.N T| = riemannZeta.N T := by
    rw [abs_of_nonneg]
    rw [hNT]
    exact Finset.sum_nonneg hnn
  rw [habs, hNT, Finset.sum_congr rfl hterm]
  -- drop zero terms, then dominate by the mass finset
  rw [← Finset.sum_filter_ne_zero]
  rw [Complex.Hadamard.divisorMassClosedBall₀,
    Function.locallyFinsuppWithin.massClosedBall₀]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro ρ hρ
    rw [Finset.mem_filter] at hρ
    obtain ⟨hρrect, hρne⟩ := hρ
    obtain ⟨-, him0, himT, hre0, hre1, -⟩ := hmem ρ (hfin.mem_toFinset.mp hρrect)
    have hDρ : D ρ ≠ 0 := by
      intro h
      exact hρne (by rw [h]; norm_num)
    have hnorm : ‖ρ‖ ≤ |T + 1| := by
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ T + 1)]
      calc ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
        _ ≤ 1 + T := by
            rw [abs_of_nonneg hre0, abs_of_nonneg him0.le]
            linarith
        _ = T + 1 := by ring
    have hsupp : ρ ∈ Function.locallyFinsuppWithin.support D :=
      Function.mem_support.mpr hDρ
    have hball :=
      Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
        hsupp hnorm
    refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hball, ?_⟩
    intro h
    rw [h] at him0
    simp at him0
  · intro z _ _
    exact_mod_cast hDnn z

/-- HEADLINE REPAIR 2 (loop session): the constant is existential, not the literal
`100` — the growth and ball-count inputs are existential, so a fixed numeric headline
constant is underivable until the growth constant is made explicit. The Phase-2
consumer is indifferent: the constant factors out of the dyadic summability. -/
theorem zetaCounting_crude_majorant :
    ∃ A : ℝ, 0 < A ∧ ∀ T : ℝ, 2 ≤ T →
      |riemannZeta.N T| ≤ A * T ^ (3/2 : ℝ) := by
  obtain ⟨C', hC'0, hC'⟩ := zetaSurrogate_zeros_in_closedBall₀_count
  refine ⟨C' * 4 ^ (3/2 : ℝ), mul_pos hC'0 (Real.rpow_pos_of_pos (by norm_num) _), ?_⟩
  intro T hT
  have h12 : |riemannZeta.N T| ≤ C' * (1 + (T + 1)) ^ (3/2 : ℝ) :=
    (zetaCounting_le_surrogate_mass T hT).trans (hC' (T + 1) (by linarith))
  have h3 : (1 + (T + 1) : ℝ) ^ (3/2 : ℝ) ≤ 4 ^ (3/2 : ℝ) * T ^ (3/2 : ℝ) := by
    rw [← Real.mul_rpow (by norm_num) (by linarith : (0 : ℝ) ≤ T)]
    exact Real.rpow_le_rpow (by linarith) (by linarith) (by norm_num)
  calc |riemannZeta.N T|
      ≤ C' * (1 + (T + 1)) ^ (3/2 : ℝ) := h12
    _ ≤ C' * (4 ^ (3/2 : ℝ) * T ^ (3/2 : ℝ)) := mul_le_mul_of_nonneg_left h3 hC'0.le
    _ = C' * 4 ^ (3/2 : ℝ) * T ^ (3/2 : ℝ) := by ring

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
