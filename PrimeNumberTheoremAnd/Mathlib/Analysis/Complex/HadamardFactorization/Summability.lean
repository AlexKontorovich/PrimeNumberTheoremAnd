/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/
module

public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.HadamardFactorization
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Growth
public import PrimeNumberTheoremAnd.Mathlib.Analysis.Meromorphic.DivisorHolomorphic
public import Mathlib.Analysis.Meromorphic.TrailingCoefficient
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.Dyadic
public import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Log.PosLog
public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Divisor summability from logarithmic growth

Dyadic shell summability for the zero divisor of an entire function with a logarithmic growth
bound. This is the zero-counting input for Tao's finite-order Hadamard theorem, not the
factorization conclusion itself.  It is step 1 of the intrinsic Hadamard pipeline
(`divisorCanonicalProduct`, `hadamard_factorization_of_growth`, `hadamard_factorization_of_order`).

## Main results

* `divisorMassClosedBall₀_le_of_growth` : zero mass in a ball is `O((1 + R)^ρ)` under
  log-growth of order `ρ`
* `summable_norm_inv_pow_divisorZeroIndex₀_of_growth` : growth implies convergence of the
  canonical product
* `jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff` : Hadamard alias for Jensen's
  formula (see also
  `Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable`)

Jensen's formula and log-counting growth bounds live in
`Analysis.Complex.ValueDistribution.LogCounting`.

Tao Notes 1 enters here through Theorem 2 (Jensen's formula) and Proposition 8 (zero counting from
growth).  The forward convergence input corresponding to Exercise 19 is used for the genus
`⌊ρ⌋` canonical product; the converse direction in Exercise 24 is not proved in this branch.

## References

* [tao246bComplexAnalysis], Theorem 2 and Proposition 8 (disk formulation; compare
  `divisorMassClosedBall₀` and `logCounting`)
* [MR886677], §1 for disk automorphisms and disk canonical factors used in the counting background
* [boas1954] and [levin1980] for the Jensen/counting estimates feeding the classical Hadamard
  product theorem
-/

@[expose] public section

noncomputable section

open Filter Topology Set Complex
open scoped BigOperators Topology

namespace Complex.Hadamard

/-!
### Lindelöf summability

A bound on `log (1 + ‖f z‖)` controls `logCounting` of the divisor and yields summability of
`‖a‖⁻¹^(m+1)` for the divisor-indexed canonical product.
-/

open scoped Real

/-- The total multiplicity of the nonzero divisor of `f` in the closed ball of radius `R`. -/
noncomputable def divisorMassClosedBall₀ (f : ℂ → ℂ) (R : ℝ) : ℝ :=
  Function.locallyFinsuppWithin.massClosedBall₀ (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R

/-- Hadamard-facing alias for Jensen's formula on the zero divisor. -/
theorem jensen_formula_logCounting_eq_circleAverage_sub_log_trailingCoeff {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : R ≠ 0) :
    Function.locallyFinsuppWithin.logCounting (MeromorphicOn.divisor f (Set.univ : Set ℂ)) R
      = Real.circleAverage (fun z : ℂ => Real.log ‖f z‖) 0 R
        - Real.log ‖meromorphicTrailingCoeffAt f 0‖ :=
  Function.locallyFinsuppWithin.logCounting_divisor_eq_circleAverage_sub_const_of_differentiable
    hf hR

lemma log_two_mul_divisorMassClosedBall₀_le_logCounting_two_mul {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) {R : ℝ} (hR : 1 ≤ R) :
    (Real.log 2) * divisorMassClosedBall₀ f R
      ≤ Function.locallyFinsuppWithin.logCounting
          (MeromorphicOn.divisor f (Set.univ : Set ℂ)) (2 * R) :=
  Function.locallyFinsuppWithin.log_two_mul_massClosedBall₀_le_logCounting
    (D := MeromorphicOn.divisor f (Set.univ : Set ℂ))
    (Differentiable.divisor_nonneg hf) hR

lemma divisorMassClosedBall₀_le_of_growth {f : ℂ → ℂ} {ρ C : ℝ}
    (hf : Differentiable ℂ f)
    (hC : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ)
    {R : ℝ} (hR : 1 ≤ R) :
    divisorMassClosedBall₀ f R
      ≤ (C * (1 + |2 * R|) ^ ρ + |Real.log ‖meromorphicTrailingCoeffAt f 0‖|) /
          Real.log 2 := by
  simpa [divisorMassClosedBall₀] using
    (Function.locallyFinsuppWithin.massClosedBall₀_divisor_le_of_log_growth
      (f := f) (ρ := ρ) (C := C) hf hC hR)

lemma divisorMassClosedBall₀_mono {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {R₁ R₂ : ℝ} (hR₁ : 0 ≤ R₁) (hR₁₂ : R₁ ≤ R₂) :
    divisorMassClosedBall₀ f R₁ ≤ divisorMassClosedBall₀ f R₂ := by
  simpa [divisorMassClosedBall₀] using
    Function.locallyFinsuppWithin.massClosedBall₀_mono
      (D := MeromorphicOn.divisor f (Set.univ : Set ℂ))
      (Differentiable.divisor_nonneg hf) hR₁ hR₁₂

lemma exists_r0_le_norm_divisorZeroIndex₀_val {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0) :
    ∃ r0 : ℝ, 0 < r0 ∧
      ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
  classical
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  have hzero : ∀ p : divisorZeroIndex₀ f U, f (divisorZeroIndex₀_val p) = 0 := by
    intro p
    set z : ℂ := divisorZeroIndex₀_val p
    have hneTop : meromorphicOrderAt f z ≠ ⊤ := by
      have hzAnal : AnalyticAt ℂ f z := hf.analyticAt z
      have hzA : analyticOrderAt f z ≠ ⊤ :=
        analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := z)
      intro htop
      have hm : meromorphicOrderAt f z = (analyticOrderAt f z).map (↑) :=
        hzAnal.meromorphicOrderAt_eq (𝕜 := ℂ)
      cases h : analyticOrderAt f z with
      | top =>
          exact hzA (by simp [h])
      | coe n =>
          have : (analyticOrderAt f z).map (↑) ≠ (⊤ : WithTop ℤ) := by
            simp [h]
          exact this (by simpa [hm] using htop)
    have hmon : MeromorphicOn f U := by
      intro w hw; exact (hf.analyticAt w).meromorphicAt
    have hdiv : MeromorphicOn.divisor f U z = (meromorphicOrderAt f z).untop₀ := by
      simpa [U] using (MeromorphicOn.divisor_apply (f := f) (U := U) (z := z) hmon (by aesop))
    have hDz : MeromorphicOn.divisor f U z ≠ 0 := by
      have hzsup : z ∈ (MeromorphicOn.divisor f U).support := by
        simp [z]
      simpa [Function.mem_support] using hzsup
    have hposZ : (0 : ℤ) < (meromorphicOrderAt f z).untop₀ := by
      have hge0 : 0 ≤ (meromorphicOrderAt f z).untop₀ := by
        have : 0 ≤ MeromorphicOn.divisor f U z := by
          simpa [D, U, z] using hDnonneg z
        simpa [hdiv] using this
      have hne0 : (meromorphicOrderAt f z).untop₀ ≠ 0 := by
        simpa [hdiv] using hDz
      exact lt_of_le_of_ne hge0 (by simpa [eq_comm] using hne0)
    have hpos : (0 : WithTop ℤ) < meromorphicOrderAt f z := by
      have : (0 : WithTop ℤ) < ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) :=
        WithTop.coe_lt_coe.2 hposZ
      simpa [WithTop.coe_untop₀_of_ne_top hneTop] using this
    have htend0 : Tendsto f (𝓝[≠] z) (𝓝 (0 : ℂ)) :=
      tendsto_zero_of_meromorphicOrderAt_pos (f := f) (x := z) hpos
    have hcontz : ContinuousAt f z := (hf z).continuousAt
    have htendz : Tendsto f (𝓝[≠] z) (𝓝 (f z)) :=
      (hcontz.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] z ≤ 𝓝 z))
    exact tendsto_nhds_unique htendz htend0
  by_cases h0 : f 0 = 0
  · have hD0 : D 0 ≠ 0 := by
      have hmero0 : MeromorphicAt f (0 : ℂ) := (hf.analyticAt 0).meromorphicAt
      have hneTop0 : meromorphicOrderAt f (0 : ℂ) ≠ ⊤ := by
        have hA0 : analyticOrderAt f (0 : ℂ) ≠ ⊤ :=
          analyticOrderAt_ne_top_of_exists_ne_zero (f := f) (hf := hf) hnot (z := 0)
        intro htop
        have hm : meromorphicOrderAt f (0 : ℂ) = (analyticOrderAt f (0 : ℂ)).map (↑) :=
          (hf.analyticAt 0).meromorphicOrderAt_eq (𝕜 := ℂ)
        cases h : analyticOrderAt f (0 : ℂ) with
        | top => exact Ne.elim hA0 h
        | coe n =>
            have : (analyticOrderAt f (0 : ℂ)).map (↑) ≠ (⊤ : WithTop ℤ) := by
              simp [h]
            exact this (by simpa [hm] using htop)
      have htend0 : Tendsto f (𝓝[≠] (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
        have : Tendsto f (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by simpa [h0] using hcont0.tendsto
        exact this.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℂ) ≤ 𝓝 (0 : ℂ))
      have hpos0 : (0 : WithTop ℤ) < meromorphicOrderAt f (0 : ℂ) :=
        (tendsto_zero_iff_meromorphicOrderAt_pos hmero0).1 htend0
      have hpos0' : (0 : ℤ) < (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have : (0 : WithTop ℤ) < ((meromorphicOrderAt f (0 : ℂ)).untop₀ : WithTop ℤ) := by
          simpa [WithTop.coe_untop₀_of_ne_top hneTop0] using hpos0
        simpa using (WithTop.coe_lt_coe.1 this)
      have hdiv0 : D 0 = (meromorphicOrderAt f (0 : ℂ)).untop₀ := by
        have hmon : MeromorphicOn f U := by
          intro w hw; exact (hf.analyticAt w).meromorphicAt
        simpa [D, U] using
          (MeromorphicOn.divisor_apply (f := f) (U := U) (z := (0 : ℂ))
            hmon (by aesop))
      exact by
        have : (meromorphicOrderAt f (0 : ℂ)).untop₀ ≠ 0 := ne_of_gt hpos0'
        simpa [hdiv0] using this
    have hmem0 : (0 : ℂ) ∈ D.support := by
      simp [Function.mem_support, hD0]
    have hdisc : IsDiscrete D.support := by
      simpa [D] using (D.discreteSupport)
    rcases Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc hmem0 with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have hp : divisorZeroIndex₀_val p ∈ D.support := by
      simp [D, divisorZeroIndex₀_val_mem_divisor_support (f := f) (U := U) p]
    have hnotBall : divisorZeroIndex₀_val p ∉ Metric.ball (0 : ℂ) r0 := by
      intro hball
      have : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 ∩ D.support := ⟨hball, hp⟩
      have : divisorZeroIndex₀_val p ∈ ({(0 : ℂ)} : Set ℂ) := by simp [hr0] at this
      have : divisorZeroIndex₀_val p = 0 := by simp [Set.mem_singleton_iff] at this
      exact (divisorZeroIndex₀_val_ne_zero p) this
    have : r0 ≤ ‖divisorZeroIndex₀_val p‖ := by
      have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
        intro hlt
        exact hnotBall (by simpa [Metric.mem_ball, dist_zero_right] using hlt)
      exact le_of_not_gt this
    exact this
  · have hcont0 : ContinuousAt f (0 : ℂ) := (hf 0).continuousAt
    have hne : ∀ᶠ z in 𝓝 (0 : ℂ), f z ≠ 0 := hcont0.eventually_ne h0
    rcases Metric.mem_nhds_iff.1 hne with ⟨r0, hr0pos, hr0⟩
    refine ⟨r0, hr0pos, ?_⟩
    intro p
    have : ¬ ‖divisorZeroIndex₀_val p‖ < r0 := by
      intro hlt
      have hzball : divisorZeroIndex₀_val p ∈ Metric.ball (0 : ℂ) r0 := by
        simpa [Metric.mem_ball, dist_zero_right] using hlt
      have : f (divisorZeroIndex₀_val p) ≠ 0 := hr0 hzball
      exact this (hzero p)
    exact le_of_not_gt this

/-!
### Dyadic-shell summability for divisor-indexed zeros
-/

open scoped BigOperators

/-- The number of divisor indices in a closed ball is bounded by the divisor mass there. -/
lemma card_ball_le_divisorMassClosedBall₀
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) {R : ℝ} (hR : 0 < R) :
    (Nat.card {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
      ≤ divisorMassClosedBall₀ f R := by
  set U : Set ℂ := (Set.univ : Set ℂ)
  set D : Function.locallyFinsuppWithin U ℤ := MeromorphicOn.divisor f U
  haveI :
      Fintype {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
    have : Finite {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} := by
      have : Metric.closedBall (0 : ℂ) R ⊆ U := by simp [U]
      simpa using (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := U) (B := R) this)
    exact Fintype.ofFinite _
  have hDnonneg : 0 ≤ D := by
    simpa [D, U] using (Differentiable.divisor_nonneg (f := f) hf)
  let SR : Finset ℂ :=
    (Function.locallyFinsuppWithin.finiteSupport (Function.locallyFinsuppWithin.toClosedBall R D)
          (isCompact_closedBall (0 : ℂ) |R|)).toFinset
  let S : Finset ℂ := SR.filter fun z : ℂ => z ≠ 0
  let T : Type :=
    Σ z : S, Fin (Int.toNat (D z.1))
  let φ :
      {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} → T := fun p =>
    let z0 : ℂ := divisorZeroIndex₀_val p.1
    have hz0_memSR : z0 ∈ SR := by
      have hz0_norm : ‖z0‖ ≤ |R| := by
        have : ‖z0‖ ≤ R := p.2
        simpa [abs_of_pos hR] using this
      have hz0_support : z0 ∈ (Function.locallyFinsuppWithin.toClosedBall R D).support := by
        have hz0_suppD : z0 ∈ D.support := by
          simp [z0, D]
        exact Function.locallyFinsuppWithin.mem_toClosedBall_support_of_mem_support_of_norm_le_abs
          hz0_suppD hz0_norm
      exact (Set.Finite.mem_toFinset
        (Function.locallyFinsuppWithin.finiteSupport
          (Function.locallyFinsuppWithin.toClosedBall R D)
            (isCompact_closedBall (0 : ℂ) |R|))).2 hz0_support
    have hz0_ne0 : z0 ≠ 0 := divisorZeroIndex₀_val_ne_zero p.1
    have hz0_memS : z0 ∈ S := Finset.mem_filter.2 ⟨hz0_memSR, hz0_ne0⟩
    ⟨⟨z0, hz0_memS⟩, by
        simpa [z0, divisorZeroIndex₀_val, D] using p.1.1.2⟩
  have hφ_inj : Function.Injective φ := by
    intro p q hpq
    have hσ := (Sigma.mk.inj_iff).1 hpq
    have hzS : (φ p).1 = (φ q).1 := hσ.1
    have hz : divisorZeroIndex₀_val p.1 = divisorZeroIndex₀_val q.1 := by
      simpa [φ] using congrArg Subtype.val hzS
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext
    · exact hz
    · simpa [φ] using hσ.2
  have hcard_le :
      Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} ≤ Fintype.card T :=
    Fintype.card_le_of_injective φ hφ_inj
  have hT_card :
      (Fintype.card T : ℝ) =
        (S.sum fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
    have hNat :
        Fintype.card T = ∑ z : S, Int.toNat (D z.1) := by
      have h1 :
          Fintype.card T = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1))) := by
        change Fintype.card (Sigma (fun z : S => Fin (Int.toNat (D z.1))))
            = ∑ z : S, Fintype.card (Fin (Int.toNat (D z.1)))
        exact (Fintype.card_sigma (ι := S) (α := fun z : S => Fin (Int.toNat (D z.1))))
      simpa using h1
    have hR :
        (Fintype.card T : ℝ) = ∑ z : S, (Int.toNat (D z.1) : ℝ) := by
      exact_mod_cast hNat
    have hR' :
        (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := by
      simpa [Finset.univ_eq_attach] using hR
    calc
      (Fintype.card T : ℝ) = S.attach.sum (fun z : S => (Int.toNat (D z.1) : ℝ)) := hR'
      _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := by
            simpa using (Finset.sum_attach (s := S) (f := fun z : ℂ => (Int.toNat (D z) : ℝ)))
  have htoNat_le : ∀ z ∈ S, (Int.toNat (D z) : ℝ) ≤ (D z : ℝ) := by
    intro z hz
    have hDz_nonneg : 0 ≤ D z := by simpa [D] using hDnonneg z
    have hEqZ : ((Int.toNat (D z) : ℕ) : ℤ) = D z := by
      simpa using (Int.toNat_of_nonneg hDz_nonneg)
    have hEqR : (Int.toNat (D z) : ℝ) = (D z : ℝ) := by
      exact_mod_cast hEqZ
    exact le_of_eq hEqR
  calc
    (Nat.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ)
        = (Fintype.card {p : divisorZeroIndex₀ f U // ‖divisorZeroIndex₀_val p‖ ≤ R} : ℝ) := by
          simp [Nat.card_eq_fintype_card]
    _ ≤ (Fintype.card T : ℝ) := by exact_mod_cast hcard_le
    _ = S.sum (fun z : ℂ => (Int.toNat (D z) : ℝ)) := hT_card
    _ ≤ S.sum (fun z : ℂ => (D z : ℝ)) := by
      refine Finset.sum_le_sum ?_
      intro z hz
      exact htoNat_le z hz
    _ = divisorMassClosedBall₀ f R := by
      rfl

/-- A finite family of divisor indices contained in a closed ball has cardinality bounded by the
divisor mass of that ball. -/
lemma card_subtype_le_divisorMassClosedBall₀_of_norm_le
    {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {s : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ))} [Fintype s]
    {R : ℝ} (hR : 0 < R) (hs : ∀ p : s, ‖divisorZeroIndex₀_val p.1‖ ≤ R) :
    (Fintype.card s : ℝ) ≤ divisorMassClosedBall₀ f R := by
  let Aball : Type :=
    {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) // ‖divisorZeroIndex₀_val p‖ ≤ R}
  haveI : Fintype Aball := by
    have : Finite Aball := by
      have : Metric.closedBall (0 : ℂ) R ⊆ (Set.univ : Set ℂ) := by simp
      simpa [Aball] using
        (finite_divisorZeroIndex₀_subtype_norm_le (f := f) (U := (Set.univ : Set ℂ))
          (B := R) this)
    exact Fintype.ofFinite _
  have hinj : Function.Injective (fun p : s => (⟨p.1, hs p⟩ : Aball)) := by
    intro p q hpq
    apply Subtype.ext
    exact congrArg (fun x : Aball => x.1) hpq
  have hcard_le : Fintype.card s ≤ Fintype.card Aball :=
    Fintype.card_le_of_injective _ hinj
  have hAball : (Nat.card Aball : ℝ) ≤ divisorMassClosedBall₀ f R := by
    simpa [Aball] using card_ball_le_divisorMassClosedBall₀ (f := f) hf hR
  calc
    (Fintype.card s : ℝ) ≤ (Fintype.card Aball : ℝ) := by exact_mod_cast hcard_le
    _ = (Nat.card Aball : ℝ) := by simp [Nat.card_eq_fintype_card]
    _ ≤ divisorMassClosedBall₀ f R := hAball

lemma divisorZeroIndex₀_dyadicShell_upper_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1) := by
  exact Real.dyadicShell_upper_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma divisorZeroIndex₀_dyadicShell_lower_bound
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    {k : ℕ} {p : divisorZeroIndex₀ f (Set.univ : Set ℂ)}
    (hp : ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k) :
    r0 * (2 : ℝ) ^ (k : ℝ) ≤ ‖divisorZeroIndex₀_val p‖ := by
  exact Real.dyadicShell_lower_bound (r0 := r0) (x := ‖divisorZeroIndex₀_val p‖)
    hr0pos (hr0 p) hp

lemma finite_divisorZeroIndex₀_dyadicShell
    {f : ℂ → ℂ} {r0 : ℝ}
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) :
    ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
      ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} : Set _).Finite := by
  have hsub :
      {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊ = k} ⊆
        {p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
          ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} := by
    intro p hp
    exact divisorZeroIndex₀_dyadicShell_upper_bound hr0pos hr0 hp
  have hfin :
      ({p : divisorZeroIndex₀ f (Set.univ : Set ℂ) |
        ‖divisorZeroIndex₀_val p‖ ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)} : Set _).Finite := by
    have :
        Metric.closedBall (0 : ℂ) (r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) ⊆
          (Set.univ : Set ℂ) := by
      simp
    simpa using
      (divisorZeroIndex₀_norm_le_finite (f := f) (U := (Set.univ : Set ℂ))
        (B := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) this)
  exact hfin.subset hsub

lemma tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
    {f : ℂ → ℂ} {ρ τ r0 Cgrow : ℝ}
    (hρ : 0 ≤ ρ) (hτpos : 0 < τ) (hf : Differentiable ℂ f)
    (hCgrow_pos : 0 < Cgrow)
    (hCgrow : ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ Cgrow * (1 + ‖z‖) ^ ρ)
    (hr0pos : 0 < r0)
    (hr0 : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ),
      r0 ≤ ‖divisorZeroIndex₀_val p‖)
    (k : ℕ) (hk_ge_one : 1 ≤ r0 * (2 : ℝ) ^ ((k : ℝ) + 1)) :
    let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
      fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
    let S : Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) := {p | kfun p = k}
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ k + B * qσ ^ k := by
  classical
  intro kfun S Ctrail A B q qσ
  let rk : ℝ := r0 * (2 : ℝ) ^ (k : ℝ)
  let Rk : ℝ := r0 * (2 : ℝ) ^ ((k : ℝ) + 1)
  have hrk_pos : 0 < rk := mul_pos hr0pos (Real.rpow_pos_of_pos (by norm_num) _)
  have hrk0 : 0 ≤ rk := le_of_lt hrk_pos
  haveI : Finite S := by
    simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
      (f := f) hr0pos hr0 k).to_subtype
  haveI : Fintype S := Fintype.ofFinite S
  have hk_upper : ∀ p : S, ‖divisorZeroIndex₀_val p.1‖ ≤ Rk := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [Rk, kfun] using
      divisorZeroIndex₀_dyadicShell_upper_bound (f := f) hr0pos hr0 hk'
  have hk_lower : ∀ p : S, rk ≤ ‖divisorZeroIndex₀_val p.1‖ := by
    intro p
    have hk' : kfun p.1 = k := p.2
    simpa [rk, kfun] using
      divisorZeroIndex₀_dyadicShell_lower_bound (f := f) hr0pos hr0 hk'
  have htsum_le :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ (Fintype.card S : ℝ) * (rk⁻¹ ^ τ) := by
    exact Real.tsum_inv_rpow_le_card_mul_of_lower_bound
      (a := fun p : S => ‖divisorZeroIndex₀_val p.1‖)
      hrk_pos hτpos (fun _ => norm_nonneg _) hk_lower
  have hmass_le_growth :
      divisorMassClosedBall₀ f Rk
        ≤ (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) := by
    simpa [Ctrail, Rk] using
      (divisorMassClosedBall₀_le_of_growth (f := f) (ρ := ρ) (C := Cgrow) hf hCgrow
        (R := Rk) hk_ge_one)
  have hcard_le_mass :
      (Fintype.card S : ℝ) ≤ divisorMassClosedBall₀ f Rk := by
    have hRk_pos : 0 < Rk := lt_of_lt_of_le (by norm_num) hk_ge_one
    exact card_subtype_le_divisorMassClosedBall₀_of_norm_le (f := f) hf hRk_pos hk_upper
  have htsum' :
      (∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
        ≤ ((Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2)) * (rk⁻¹ ^ τ) := by
    have hcard_le_growth :
        (Fintype.card S : ℝ) ≤
          (Cgrow * (1 + |2 * Rk|) ^ ρ + Ctrail) / (Real.log 2) :=
      le_trans hcard_le_mass hmass_le_growth
    exact le_trans htsum_le <|
      mul_le_mul_of_nonneg_right hcard_le_growth (Real.rpow_nonneg (inv_nonneg.2 hrk0) τ)
  have hpow_bound :
      (1 + |2 * Rk|) ^ ρ ≤ (1 + 4 * r0) ^ ρ * ((2 : ℝ) ^ ρ) ^ k := by
    simpa [Rk] using
      Real.one_add_abs_two_mul_dyadicRadius_rpow_le (r0 := r0) (ρ := ρ) k hr0pos hρ
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  simpa [A, B, q, qσ, rk, Ctrail, mul_assoc, mul_left_comm, mul_comm] using
    Real.dyadic_growth_mass_mul_inv_le_geometric
      (C := Cgrow) (L := Real.log 2) (M := (1 + 4 * r0) ^ ρ)
      (X := (1 + |2 * Rk|) ^ ρ)
      (T := ∑' p : S, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ)
      (Ctrail := Ctrail) (r0 := r0) (ρ := ρ) (τ := τ) (k := k)
      hlog2pos hCgrow_pos.le hr0pos.le hpow_bound
      (by simpa [rk] using htsum')

theorem summable_norm_inv_rpow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ τ : ℝ}
    (hρ : 0 ≤ ρ) (hτ : ρ < τ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) := by
  rcases hgrowth with ⟨Cgrow, hCgrow_pos, hCgrow⟩
  have hτpos : 0 < τ := lt_of_le_of_lt hρ hτ
  rcases exists_r0_le_norm_divisorZeroIndex₀_val (f := f) hf hnot with ⟨r0, hr0pos, hr0⟩
  have hr0ne : (r0 : ℝ) ≠ 0 := ne_of_gt hr0pos
  let kfun : divisorZeroIndex₀ f (Set.univ : Set ℂ) → ℕ :=
    fun p => ⌊Real.logb 2 (‖divisorZeroIndex₀_val p‖ / r0)⌋₊
  let S : ℕ → Set (divisorZeroIndex₀ f (Set.univ : Set ℂ)) :=
    fun k => {p | kfun p = k}
  have hS : ∀ p : divisorZeroIndex₀ f (Set.univ : Set ℂ), ∃! k : ℕ, p ∈ S k := by
    intro p
    refine ⟨kfun p, ?_, ?_⟩
    · simp [S]
    · intro k hk
      simpa [S] using hk.symm
  have hnonneg : 0 ≤ fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ := by
    intro p
    exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
  have hSk_summable : ∀ k : ℕ, Summable fun p : S k => ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    intro k
    haveI : Finite (S k) := by
      simpa [S, kfun] using (finite_divisorZeroIndex₀_dyadicShell
        (f := f) hr0pos hr0 k).to_subtype
    exact Summable.of_finite
  have hshell_summable :
      Summable fun k : ℕ => ∑' p : S k, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
    let q : ℝ := (2 : ℝ) ^ (ρ - τ)
    let qσ : ℝ := (2 : ℝ) ^ (-τ)
    have hq_nonneg : 0 ≤ q := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hq_lt_one : q < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (sub_neg.2 hτ)
    have hqσ_nonneg : 0 ≤ qσ := le_of_lt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)
    have hqσ_lt_one : qσ < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (x := (2 : ℝ)) (by norm_num : (1 : ℝ) < 2)
        (by simpa using (neg_neg_of_pos hτpos))
    have hgeom_q : Summable (fun k : ℕ => q ^ k) :=
      summable_geometric_of_lt_one hq_nonneg hq_lt_one
    have hgeom_qσ : Summable (fun k : ℕ => qσ ^ k) :=
      summable_geometric_of_lt_one hqσ_nonneg hqσ_lt_one
    let Ctrail : ℝ := |Real.log ‖meromorphicTrailingCoeffAt f 0‖|
    let A : ℝ := ((Cgrow / Real.log 2) * (1 + 4 * r0) ^ ρ) * (r0⁻¹) ^ τ
    let B : ℝ := ((Ctrail / Real.log 2) + 1) * (r0⁻¹) ^ τ
    rcases Real.exists_nat_le_two_pow (1 / r0) with ⟨k0, hk0⟩
    let A0 : ℝ := A * q ^ k0
    let B0 : ℝ := B * qσ ^ k0
    have hmajor : Summable (fun k : ℕ => A0 * q ^ k + B0 * qσ ^ k) :=
      (hgeom_q.mul_left A0).add (hgeom_qσ.mul_left B0)
    have hshell_summable_shift :
        Summable fun k : ℕ => ∑' p : S (k + k0), ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
      refine hmajor.of_nonneg_of_le
        (fun k => by
          have : ∀ p : S (k + k0), 0 ≤ ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ := by
            intro p; exact Real.rpow_nonneg (inv_nonneg.2 (norm_nonneg _)) _
          exact tsum_nonneg this)
        (fun k => by
          let kk : ℕ := k + k0
          let Rk : ℝ := r0 * (2 : ℝ) ^ ((kk : ℝ) + 1)
          have hRk_ge_one : (1 : ℝ) ≤ Rk := by
            have hkk : k0 ≤ kk + 1 := by
              simp [kk, Nat.add_assoc, Nat.add_comm]
            simpa [Rk] using
              Real.one_le_dyadicRadius_succ_of_inv_le_two_pow hr0pos hk0 hkk
          have hmain :
              (∑' p : S kk, ‖divisorZeroIndex₀_val p.1‖⁻¹ ^ τ) ≤ A * q ^ kk + B * qσ ^ kk := by
            simpa [S, kfun, Ctrail, A, B, q, qσ] using
              tsum_divisorZeroIndex₀_dyadicShell_inv_rpow_le_geometric_of_growth
                (f := f) (ρ := ρ) (τ := τ) hρ hτpos hf hCgrow_pos hCgrow hr0pos hr0 kk hRk_ge_one
          have : A * q ^ kk + B * qσ ^ kk = A0 * q ^ k + B0 * qσ ^ k := by
            simpa [A0, B0, kk] using Real.two_geometric_shift_add A B q qσ k k0
          simpa [kk] using (hmain.trans_eq this)
        )
    exact (summable_nat_add_iff k0).1 hshell_summable_shift
  have hpart :=
    (summable_partition (f := fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
        ‖divisorZeroIndex₀_val p‖⁻¹ ^ τ) hnonneg (s := S) hS)
  exact (hpart.2 ⟨hSk_summable, hshell_summable⟩)

/-- Natural-power form of the divisor summability theorem. -/
theorem summable_norm_inv_pow_divisorZeroIndex₀_of_growth {f : ℂ → ℂ} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hf : Differentiable ℂ f) (hnot : ∃ z : ℂ, f z ≠ 0)
    (hgrowth : ∃ C > 0, ∀ z : ℂ, Real.log (1 + ‖f z‖) ≤ C * (1 + ‖z‖) ^ ρ) :
    Summable (fun p : divisorZeroIndex₀ f (Set.univ : Set ℂ) =>
      ‖divisorZeroIndex₀_val p‖⁻¹ ^ (Nat.floor ρ + 1)) := by
  have hτ : ρ < (Nat.floor ρ + 1 : ℝ) := by
    simpa [Nat.cast_add, Nat.cast_one] using (Nat.lt_floor_add_one (a := ρ))
  have hs :=
    summable_norm_inv_rpow_divisorZeroIndex₀_of_growth (f := f) (ρ := ρ)
      (τ := (Nat.floor ρ + 1 : ℝ)) hρ hτ hf hnot hgrowth
  exact hs.congr fun p => by
    have hcast : ((Nat.floor ρ : ℝ) + 1) = ((Nat.floor ρ + 1 : ℕ) : ℝ) := by
      norm_num
    rw [hcast, Real.rpow_natCast]

end Complex.Hadamard
