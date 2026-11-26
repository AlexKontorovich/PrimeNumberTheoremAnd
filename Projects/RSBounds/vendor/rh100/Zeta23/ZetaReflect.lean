module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZetaReflect.lean — the two reflection seam obligations of ZetaSeam.

Paper [subsec:weil], verbatim: "The multiset {(γ_ρ, m_ρ)} is invariant under
γ ↦ γ̄ (i.e. ρ ↦ 1 − ρ̄; multiplicities agree because conj ξ(conj s) = ξ(s) =
ξ(1−s))".  These are CLASSICAL facts about ζ, not paper inputs.

Contents:
  • riemannZeta_conj : ζ(s̄) = ζ(s)̄ for s ≠ 1 (Schwarz reflection: Dirichlet
    series on Re s > 1 + the identity theorem on ℂ∖{1});
  • analyticOrderAt_conj_conj : vanishing order is invariant under z ↦ z̄
    conjugation of a function (general lemma);
  • analyticOrderAt_zeta_one_sub : order transport through the functional
    equation ζ(1−s) = 2(2π)^{−s}Γ(s)cos(πs/2)·ζ(s) (prefactor nonvanishing in
    the strip);
  • zeta_reflect_zero, zeta_mult_reflect : the ZetaSeam field shapes.
-/
public import Zeta23.Statement
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

open Complex
open scoped ComplexConjugate

namespace Zeta23

/-! ### 1. Schwarz reflection for ζ -/

private lemma zeta_conj_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    conj (riemannZeta (conj s)) = riemannZeta s := by
  have hs' : (1 : ℝ) < (conj s).re := by rwa [Complex.conj_re]
  rw [zeta_eq_tsum_one_div_nat_cpow hs', zeta_eq_tsum_one_div_nat_cpow hs]
  have hstar : star (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := tsum_star
  calc conj (∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ (conj s))
      = ∑' (n : ℕ), star ((1 : ℂ) / (n : ℂ) ^ (conj s)) := hstar
    _ = ∑' (n : ℕ), (1 : ℂ) / (n : ℂ) ^ s := by
        congr 1
        funext n
        have harg : ((n : ℂ)).arg ≠ Real.pi := by
          rw [Complex.natCast_arg]
          exact Ne.symm Real.pi_ne_zero
        have hpow : (n : ℂ) ^ (conj s) = conj ((n : ℂ) ^ s) := by
          have h := Complex.cpow_conj (n : ℂ) s harg
          rwa [Complex.conj_natCast] at h
        show star ((1 : ℂ) / (n : ℂ) ^ (conj s)) = 1 / (n : ℂ) ^ s
        rw [star_div₀, star_one, hpow]
        simp

/-- **Schwarz reflection for ζ**: ζ(s̄) = ζ(s)̄ away from the pole. -/
theorem riemannZeta_conj {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conj s) = conj (riemannZeta s) := by
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hU_conn : IsPreconnected ({(1 : ℂ)}ᶜ) :=
    (isPathConnected_compl_singleton_of_one_lt_rank hrank 1).isConnected.isPreconnected
  have hζ : AnalyticOnNhd ℂ riemannZeta ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    exact (differentiableAt_riemannZeta (by simpa using hz)).differentiableWithinAt
  have hζt : AnalyticOnNhd ℂ (fun z => conj (riemannZeta (conj z))) ({(1 : ℂ)}ᶜ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_compl_singleton
    have hz1 : conj z ≠ 1 := by
      intro h
      have h2 := congrArg (starRingEnd ℂ) h
      simp only [Complex.conj_conj, map_one] at h2
      exact (by simpa using hz : z ≠ 1) h2
    have hd : DifferentiableAt ℂ riemannZeta (conj z) := differentiableAt_riemannZeta hz1
    have h3 := hd.conj_conj
    rw [Complex.conj_conj] at h3
    exact h3.differentiableWithinAt
  have h2mem : (2 : ℂ) ∈ ({(1 : ℂ)}ᶜ : Set ℂ) := by
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hagree : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (2 : ℂ)] riemannZeta := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2 : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hopen.mem_nhds h2] with z hz
    exact zeta_conj_of_one_lt_re hz
  have heq := hζt.eqOn_of_preconnected_of_eventuallyEq hζ hU_conn h2mem hagree
  have h3 : conj (riemannZeta (conj s)) = riemannZeta s := heq (by simpa using hs)
  calc riemannZeta (conj s) = conj (conj (riemannZeta (conj s))) := (Complex.conj_conj _).symm
    _ = conj (riemannZeta s) := by rw [h3]

/-! ### 2. Vanishing order under conjugation -/

private lemma tendsto_conj_nhds (w : ℂ) :
    Filter.Tendsto (fun z => conj z) (nhds (conj w)) (nhds w) := by
  have h := (Complex.continuous_conj).tendsto (conj w)
  rwa [Complex.conj_conj] at h

private lemma analyticAt_conj_conj {f : ℂ → ℂ} {w : ℂ} (hf : AnalyticAt ℂ f w) :
    AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hf ⊢
  filter_upwards [(tendsto_conj_nhds w).eventually hf] with z hz
  have h2 := hz.conj_conj
  rw [Complex.conj_conj] at h2
  exact h2

/-- The vanishing order of z ↦ conj (f (conj z)) at conj w equals that of f at w. -/
theorem analyticOrderAt_conj_conj (f : ℂ → ℂ) (w : ℂ) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj w) = analyticOrderAt f w := by
  by_cases hf : AnalyticAt ℂ f w
  · by_cases htop : analyticOrderAt f w = ⊤
    · rw [htop, analyticOrderAt_eq_top]
      filter_upwards [(tendsto_conj_nhds w).eventually (analyticOrderAt_eq_top.mp htop)] with z hz
      simp [hz]
    · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
      rw [← hn]
      rw [Eq.comm, hf.analyticOrderAt_eq_natCast] at hn
      obtain ⟨g, hg, hgne, hfg⟩ := hn
      rw [(analyticAt_conj_conj hf).analyticOrderAt_eq_natCast]
      refine ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hgne, ?_⟩
      filter_upwards [(tendsto_conj_nhds w).eventually hfg] with z hz
      have : conj (f (conj z)) = conj ((conj z - w) ^ n * g (conj z)) := by rw [hz]; rfl
      rw [this]
      simp only [map_mul, map_pow, map_sub, Complex.conj_conj]
      rfl
  · have hf' : ¬ AnalyticAt ℂ (fun z => conj (f (conj z))) (conj w) := by
      intro hcon
      apply hf
      have h2 := analyticAt_conj_conj hcon
      rw [Complex.conj_conj] at h2
      exact h2.congr (Filter.Eventually.of_forall fun u => by
        simp only [Complex.conj_conj])
    rw [analyticOrderAt_of_not_analyticAt hf, analyticOrderAt_of_not_analyticAt hf']

/-- Order of ζ is conjugation-symmetric away from the pole. -/
theorem analyticOrderAt_zeta_conj {w : ℂ} (hw : w ≠ 1) :
    analyticOrderAt riemannZeta (conj w) = analyticOrderAt riemannZeta w := by
  have hne : conj w ≠ 1 := by
    intro h
    have h2 := congrArg (starRingEnd ℂ) h
    simp only [Complex.conj_conj, map_one] at h2
    exact hw h2
  have hcong : (fun z => conj (riemannZeta (conj z))) =ᶠ[nhds (conj w)] riemannZeta := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne :
      conj w ∈ ({(1 : ℂ)}ᶜ))] with z hz
    rw [riemannZeta_conj (by simpa using hz), Complex.conj_conj]
  calc analyticOrderAt riemannZeta (conj w)
      = analyticOrderAt (fun z => conj (riemannZeta (conj z))) (conj w) :=
        (analyticOrderAt_congr hcong).symm
    _ = analyticOrderAt riemannZeta w := analyticOrderAt_conj_conj _ _

/-! ### 3. Order transport through the functional equation -/

/-- The prefactor of [riemannZeta_one_sub]: E(s) = 2(2π)^{−s} Γ(s) cos(πs/2). -/
private noncomputable def Efac (s : ℂ) : ℂ :=
  2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s * Complex.cos ((Real.pi : ℂ) * s / 2)

private lemma two_pi_ne_zero' : (2 * (Real.pi : ℂ)) ≠ 0 := by
  simp only [ne_eq, mul_eq_zero, not_or]
  exact ⟨two_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩

private lemma Efac_ne_zero {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) : Efac s ≠ 0 := by
  have hsne : ∀ m : ℕ, s ≠ -m := by
    intro m h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) h0
  have hcpow : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero two_pi_ne_zero']
    exact Complex.exp_ne_zero _
  have hcos : Complex.cos ((Real.pi : ℂ) * s / 2) ≠ 0 := by
    intro hc
    rw [Complex.cos_eq_zero_iff] at hc
    obtain ⟨k, hk⟩ := hc
    have hπ : ((Real.pi : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
      linear_combination (2 : ℂ) * hk
    have hs_eq : s = ((2 * k + 1 : ℤ) : ℂ) := by
      have h3 := mul_left_cancel₀ hπ h2
      rw [h3]
      push_cast
      ring
    rw [hs_eq, Complex.intCast_re] at h0 h1
    have h0' : (0 : ℤ) < 2 * k + 1 := by exact_mod_cast h0
    have h1' : (2 * k + 1 : ℤ) < 1 := by exact_mod_cast h1
    omega
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero hsne
  unfold Efac
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hΓ) hcos

private lemma analyticAt_Efac {s : ℂ} (h0 : 0 < s.re) : AnalyticAt ℂ Efac s := by
  have h1 : AnalyticAt ℂ (fun z : ℂ => (2 * (Real.pi : ℂ)) ^ (-z)) s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    filter_upwards with z
    exact (differentiableAt_id.neg).const_cpow (Or.inl two_pi_ne_zero')
  have h2 : AnalyticAt ℂ Complex.Gamma s := by
    rw [analyticAt_iff_eventually_differentiableAt]
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds h0] with z hz
    refine Complex.differentiableAt_Gamma z fun m => ?_
    intro h
    rw [h] at hz
    simp only [Complex.neg_re, Complex.natCast_re] at hz
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg m))) hz
  have h3 : AnalyticAt ℂ (fun z : ℂ => Complex.cos ((Real.pi : ℂ) * z / 2)) s := by
    have hlin : AnalyticAt ℂ (fun z : ℂ => (Real.pi : ℂ) * z / 2) s := by
      apply AnalyticAt.div_const
      exact analyticAt_const.mul analyticAt_id
    exact Complex.analyticAt_cos.comp hlin
  have h4 : AnalyticAt ℂ (fun z : ℂ => 2 * (2 * (Real.pi : ℂ)) ^ (-z)) s :=
    analyticAt_const.mul h1
  exact (h4.mul h2).mul h3

/-- Order transport through the functional equation: for w in the open strip,
ord_{1−w} ζ = ord_w ζ. -/
theorem analyticOrderAt_zeta_one_sub {w : ℂ} (h0 : 0 < w.re) (h1 : w.re < 1) :
    analyticOrderAt riemannZeta (1 - w) = analyticOrderAt riemannZeta w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hev : (riemannZeta ∘ (fun z : ℂ => 1 - z)) =ᶠ[nhds w]
      (Efac * riemannZeta) := by
    filter_upwards [hopen.mem_nhds ⟨h0, h1⟩] with z hz
    have hzne : ∀ n : ℕ, z ≠ -n := by
      intro n h
      rw [h] at hz
      simp only [Complex.neg_re, Complex.natCast_re] at hz
      exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) hz.1
    have hzne1 : z ≠ 1 := by
      intro h
      rw [h] at hz
      simp only [Complex.one_re] at hz
      exact lt_irrefl 1 hz.2
    show riemannZeta (1 - z) = Efac z * riemannZeta z
    rw [riemannZeta_one_sub hzne hzne1]
    unfold Efac
    ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 - z) w := analyticAt_const.sub analyticAt_id
  have hg' : deriv (fun z : ℂ => 1 - z) w ≠ 0 := by
    have : deriv (fun z : ℂ => 1 - z) w = -1 := by
      rw [deriv_const_sub]
      simp
    rw [this]
    simp
  have hEfac := analyticAt_Efac h0
  have hEord : analyticOrderAt Efac w = 0 :=
    hEfac.analyticOrderAt_eq_zero.mpr (Efac_ne_zero h0 h1)
  calc analyticOrderAt riemannZeta (1 - w)
      = analyticOrderAt (riemannZeta ∘ (fun z : ℂ => 1 - z)) w := by
        rw [analyticOrderAt_comp_of_deriv_ne_zero hg hg']
    _ = analyticOrderAt (Efac * riemannZeta) w := analyticOrderAt_congr hev
    _ = analyticOrderAt Efac w + analyticOrderAt riemannZeta w := by
        by_cases hζw : AnalyticAt ℂ riemannZeta w
        · exact analyticOrderAt_mul hEfac hζw
        · exfalso
          exact hζw (by
            rw [analyticAt_iff_eventually_differentiableAt]
            have hne1 : w ≠ 1 := by
              intro h
              rw [h] at h1
              simp at h1
            filter_upwards [isOpen_compl_singleton.mem_nhds
              (by simpa using hne1 : w ∈ ({(1 : ℂ)}ᶜ))] with z hz
            exact differentiableAt_riemannZeta (by simpa using hz))
    _ = analyticOrderAt riemannZeta w := by rw [hEord, zero_add]

/-! ### 4. The ZetaSeam reflection fields -/

/-- H-symm (set): ρ ↦ 1 − ρ̄ maps nontrivial zeros to nontrivial zeros. -/
theorem zeta_reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ) := by
  rintro ρ ⟨hzero, h0, h1⟩
  have hρne : ∀ n : ℕ, ρ ≠ -n := by
    intro n h
    rw [h] at h0
    simp only [Complex.neg_re, Complex.natCast_re] at h0
    exact (not_lt.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))) h0
  have hρne1 : ρ ≠ 1 := by
    intro h
    rw [h] at h1
    simp at h1
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [this] at h0
    simp at h0
  have hrefl_eq : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  constructor
  · -- ζ(reflect ρ) = 0
    rw [hrefl_eq, riemannZeta_conj h1subne, riemannZeta_one_sub hρne hρne1, hzero]
    simp
  constructor
  · -- 0 < re
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  · -- re < 1
    unfold reflect
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith

/-- H-symm (multiplicity): m_{1−ρ̄} = m_ρ. -/
theorem zeta_mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ := by
  rintro ρ ⟨_, h0, h1⟩
  have h1subne : (1 : ℂ) - ρ ≠ 1 := by
    intro h
    have hρ0 : ρ = 0 := by
      have := congrArg (fun z => (1 : ℂ) - z) h
      simpa using this
    rw [hρ0] at h0
    simp at h0
  have hrefl_eq : reflect ρ = conj (1 - ρ) := by
    unfold reflect
    rw [map_sub, map_one]
  unfold zeroMult
  rw [hrefl_eq, analyticOrderAt_zeta_conj h1subne, analyticOrderAt_zeta_one_sub h0 h1]

end Zeta23
