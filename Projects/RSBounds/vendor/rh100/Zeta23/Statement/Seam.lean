module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement/Seam.lean — discharging the ζ-seam obligations of Zeta23.ZetaSeam from Mathlib. These are classical facts about riemannZeta, not inputs of the paper:
  * one_le_mult   : at a nontrivial zero the analytic order of ζ is finite and ≥ 1
                    (ζ analytic on ℂ ∖ {1}, which is connected, and ζ(2) ≠ 0 ⇒ identity theorem);
  * finite_window : finitely many nontrivial zeros with T₁ < Im ρ ≤ T₂
                    (zeros of ζ are locally finite on ℂ ∖ {1}; near 1 there are none because of the
                    pole; the closed box [0,1] × [T₁,T₂] is compact).
reflect_zero / mult_reflect (functional equation + conjugation) are proved elsewhere in the
repository.
-/
public import Zeta23.Statement
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.NumberTheory.LSeries.Nonvanishing

@[expose] public section

open Complex Set Filter Topology

noncomputable section

namespace Zeta23

/-- ζ is analytic on ℂ ∖ {1}. -/
lemma riemannZeta_analyticOnNhd_compl_one : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
  intro s hs
  exact (differentiableAt_riemannZeta hs).differentiableWithinAt

/-- ℂ ∖ {1} is connected. -/
lemma isConnected_compl_one : IsConnected ({1}ᶜ : Set ℂ) :=
  isConnected_compl_singleton_of_one_lt_rank (by simp [Complex.rank_real_complex]) 1

/-- ζ is not locally identically zero anywhere on ℂ ∖ {1}. -/
lemma analyticOrderAt_riemannZeta_ne_top {s : ℂ} (hs : s ≠ 1) :
    analyticOrderAt riemannZeta s ≠ ⊤ := by
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by norm_num
  refine riemannZeta_analyticOnNhd_compl_one.analyticOrderAt_ne_top_of_isPreconnected
    isConnected_compl_one.isPreconnected h2 hs ?_
  rw [(riemannZeta_analyticOnNhd_compl_one 2 h2).analyticOrderAt_eq_zero.mpr
    (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
  exact ENat.zero_ne_top

/-- Seam obligation H-fin. -/
theorem ZetaSeam.one_le_mult_holds : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ := by
  intro ρ h
  have hρ1 : ρ ≠ 1 := h.not_trivial.2
  have han : AnalyticAt ℂ riemannZeta ρ := riemannZeta_analyticOnNhd_compl_one ρ hρ1
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr h.1
  have hnetop := analyticOrderAt_riemannZeta_ne_top hρ1
  unfold zeroMult
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnetop
  rw [← hn] at hne0 ⊢
  simp only [ENat.toNat_coe, ne_eq, Nat.cast_eq_zero] at hne0 ⊢
  omega

/-- The zeros of ζ (away from 1) are locally finite on all of ℂ. -/
lemma riemannZeta_zeros_locallyFinite (z : ℂ) :
    ∃ t ∈ 𝓝 z, (t ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0}).Finite := by
  by_cases hz : z = 1
  · -- near the pole there are no zeros at all
    subst hz
    have hres := riemannZeta_residue_one
    have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 := by
      have : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) * riemannZeta s ≠ 0 :=
        hres.eventually_ne one_ne_zero
      exact this.mono fun s hs h => hs (by simp [h])
    rw [eventually_nhdsWithin_iff] at hev
    refine ⟨{s | s ∈ ({1}ᶜ : Set ℂ) → riemannZeta s ≠ 0}, hev, ?_⟩
    refine (Set.finite_empty).subset ?_
    rintro s ⟨hs, hs1, hz⟩
    exact hs hs1 hz
  · have hcod := (riemannZeta_analyticOnNhd_compl_one).eqOn_zero_or_eventually_ne_zero_of_preconnected
      isConnected_compl_one.isPreconnected
    rcases hcod with hzero | hcod
    · exfalso
      have : riemannZeta 2 = 0 := hzero (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      exact riemannZeta_ne_zero_of_one_lt_re (by norm_num) this
    · rw [Filter.Eventually, codiscreteWithin_iff_locallyFiniteComplementWithin] at hcod
      obtain ⟨t, ht, hfin⟩ := hcod z hz
      refine ⟨t, ht, hfin.subset ?_⟩
      rintro s ⟨hst, hs1, hs0⟩
      exact ⟨hst, hs1, by simpa using hs0⟩

/-- Seam obligation: local finiteness of the nontrivial zeros in ordinate windows. -/
theorem ZetaSeam.finite_window_holds (T₁ T₂ : ℝ) :
    ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite := by
  set K : Set ℂ := (Icc 0 1) ×ℂ (Icc T₁ T₂) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  choose t ht hfin using riemannZeta_zeros_locallyFinite
  obtain ⟨I, -, hcover⟩ := hKc.elim_nhds_subcover t (fun z _ => ht z)
  have hfinU : (⋃ z ∈ I, (t z ∩ {ρ : ℂ | ρ ≠ 1 ∧ riemannZeta ρ = 0})).Finite :=
    I.finite_toSet.biUnion fun z _ => hfin z
  refine hfinU.subset ?_
  rintro ρ ⟨hρ, hT₁, hT₂⟩
  have hρK : ρ ∈ K := by
    refine ⟨⟨hρ.2.1.le, hρ.2.2.le⟩, ⟨hT₁.le, hT₂⟩⟩
  obtain ⟨z, hzI, hρz⟩ := mem_iUnion₂.mp (hcover hρK)
  exact mem_iUnion₂.mpr ⟨z, hzI, hρz, hρ.not_trivial.2, hρ.1⟩

/-- With H-fin and finiteness discharged above, a ZetaSeam needs only the two reflection facts
(functional equation + conjugation symmetry). -/
theorem ZetaSeam.of_reflect
    (h₁ : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ))
    (h₂ : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ) : ZetaSeam :=
  ⟨ZetaSeam.one_le_mult_holds, h₁, h₂, ZetaSeam.finite_window_holds⟩

end Zeta23
