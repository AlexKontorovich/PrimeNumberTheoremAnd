module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/
public import Zeta23.Hypotheses
public import Zeta23.Defs.Counting
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Analytic.Order

@[expose] public section

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/

/-- ρ is a nontrivial zero of ζ: "ρ = β + iγ runs over the nontrivial zeros of ζ(s)" [Results],
rendered as ζ(ρ) = 0 with 0 < Re ρ < 1 (the critical strip). Mathlib's RiemannHypothesis phrases
"nontrivial" as "not of the form −2(n+1) and ≠ 1"; every strip zero is nontrivial in that sense
(lemma IsNontrivialZero.not_trivial below); the converse (all such zeros lie in the open strip) is
classical (nonvanishing on Re s ≥ 1 and, via the functional equation, on Re s ≤ 0) and is not
needed for the statements. -/
def IsNontrivialZero (ρ : ℂ) : Prop := riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1

/-- m_ρ, "the multiplicity of ρ" [Results]: the order of vanishing of ζ at ρ, via Mathlib's
analyticOrderAt (ℕ∞-valued; toNat sends ⊤ to 0, so 1 ≤ zeroMult ρ encodes BOTH "ζ is not locally
identically zero at ρ" and "ρ is a zero" — see ZetaSeam.one_le_mult). -/
def zeroMult (ρ : ℂ) : ℕ := (analyticOrderAt riemannZeta ρ).toNat

/-- {ρ nontrivial zero : T₁ < γ ≤ T₂}, γ = Im ρ  [Results] (positive-ordinate window; NOT |γ|). -/
def zerosIn (T₁ T₂ : ℝ) : Set ℂ := {ρ | IsNontrivialZero ρ ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}

/-- N(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} "(counted with multiplicity)"  [Results]. -/
def Ncount (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂, zeroMult ρ

/-- N_d(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂} "(each distinct point counted once)"  [Results]. -/
def Ndist (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂).ncard

/-- N₀(T₁,T₂) := "the number of zeros on the critical line with T₁ < γ ≤ T₂ counted with …
multiplicity"  [Results]. -/
def N0 (T₁ T₂ : ℝ) : ℕ := ∑ᶠ ρ ∈ zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}, zeroMult ρ

/-- N₀*(T₁,T₂) := same "without multiplicity"  [Results]. This is what Theorem A bounds. -/
def N0star (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2}).ncard

/-- N₀ˢ(T₁,T₂) := #{ρ : T₁ < γ ≤ T₂, β = 1/2, m_ρ = 1}  [Results]. -/
def N0simple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} ∩ {ρ | zeroMult ρ = 1}).ncard

/-- Nˢ(T₁,T₂) := "the number of simple zeros" with T₁ < γ ≤ T₂  [Results]. -/
def Nsimple (T₁ T₂ : ℝ) : ℕ := (zerosIn T₁ T₂ ∩ {ρ | zeroMult ρ = 1}).ncard

/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/

/-- Classical facts about ζ needed to instantiate Zeta23.ZeroConfig; these are established from
Mathlib elsewhere in the repository (identity theorem + ζ(2) ≠ 0 for one_le_mult; functional equation
riemannZeta_one_sub / completedRiemannZeta_one_sub + Γ-nonvanishing + conjugation symmetry at the
level of analyticOrderAt for the reflection facts; isolated zeros + the pole at 1 for finiteness),
and are not inputs of the paper. Paper [subsec:weil]: "The multiset {(γ_ρ,m_ρ)} is invariant under
γ ↦ γ̄ (i.e. ρ ↦ 1−ρ̄; multiplicities agree because conj ξ(conj s) = ξ(s) = ξ(1−s))". -/
structure ZetaSeam : Prop where
  /-- H-fin: at a nontrivial zero the analytic order is finite and ≥ 1. -/
  one_le_mult : ∀ ρ, IsNontrivialZero ρ → 1 ≤ zeroMult ρ
  /-- H-symm (set): ρ ↦ 1 − conj ρ preserves nontrivial zeros. -/
  reflect_zero : ∀ ρ, IsNontrivialZero ρ → IsNontrivialZero (reflect ρ)
  /-- H-symm (multiplicity). -/
  mult_reflect : ∀ ρ, IsNontrivialZero ρ → zeroMult (reflect ρ) = zeroMult ρ
  /-- local finiteness: finitely many nontrivial zeros with T₁ < γ ≤ T₂. -/
  finite_window : ∀ T₁ T₂ : ℝ, ({ρ | IsNontrivialZero ρ} ∩ {ρ | T₁ < ρ.im ∧ ρ.im ≤ T₂}).Finite

/-- The nontrivial zeros of ζ with their multiplicities, as an abstract zero configuration.
carrier := {ρ | IsNontrivialZero ρ} exactly, mult := zeroMult exactly (seam requirement: H-EF's
W then ranges over exactly the nontrivial zeros weighted by exactly the analytic order). -/
def zetaZeros (hs : ZetaSeam) : ZeroConfig where
  carrier := {ρ | IsNontrivialZero ρ}
  mult := zeroMult
  one_le_mult := hs.one_le_mult
  strip := fun _ h => ⟨h.2.1.le, h.2.2.le⟩
  reflect_mem := hs.reflect_zero
  mult_reflect := hs.mult_reflect
  finite_window := hs.finite_window

section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl
@[simp] lemma zetaZeros_simple : (zetaZeros hs).simple = {ρ | zeroMult ρ = 1} := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]
@[simp] lemma zetaZeros_Nd : (zetaZeros hs).Nd T₁ T₂ = Ndist T₁ T₂ := by
  simp [ZeroConfig.Nd, Ndist, zetaZeros_window]
@[simp] lemma zetaZeros_N0 : (zetaZeros hs).N0 T₁ T₂ = N0 T₁ T₂ := by
  simp [ZeroConfig.N0, N0, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0star : (zetaZeros hs).N0star T₁ T₂ = N0star T₁ T₂ := by
  simp [ZeroConfig.N0star, N0star, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0s : (zetaZeros hs).N0s T₁ T₂ = N0simple T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simple, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_Ns : (zetaZeros hs).Ns T₁ T₂ = Nsimple T₁ T₂ := by
  simp [ZeroConfig.Ns, Nsimple, zetaZeros_window]

end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/

/-- A strip zero is a "nontrivial zero" in the sense inlined in Mathlib's RiemannHypothesis:
not a trivial zero −2(n+1) (those have real part ≤ −2) and not the pole 1. -/
lemma IsNontrivialZero.not_trivial {ρ : ℂ} (h : IsNontrivialZero ρ) :
    (¬∃ n : ℕ, ρ = -2 * (n + 1)) ∧ ρ ≠ 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩
    have := h.2.1
    simp at this
    linarith
  · rintro rfl
    simpa using h.2.2

/-- Mathlib's RiemannHypothesis puts every nontrivial zero (in our sense) on the critical line. -/
theorem RH_implies_on_line (hRH : RiemannHypothesis) {ρ : ℂ} (h : IsNontrivialZero ρ) :
    ρ.re = 1 / 2 :=
  hRH ρ h.1 h.not_trivial.1 h.not_trivial.2

/-- Sanity anchor 1: under Mathlib's RiemannHypothesis all counted zeros are on the
line, so the on-line counts equal the full counts, with and without multiplicity. No other
hypotheses. -/
theorem RH_implies_all_on_line (hRH : RiemannHypothesis) (T₁ T₂ : ℝ) :
    N0 T₁ T₂ = Ncount T₁ T₂ ∧ N0star T₁ T₂ = Ndist T₁ T₂ := by
  have hset : zerosIn T₁ T₂ ∩ {ρ | ρ.re = 1 / 2} = zerosIn T₁ T₂ := by
    ext ρ
    simp only [mem_inter_iff, mem_setOf_eq, and_iff_left_iff_imp]
    exact fun hρ => RH_implies_on_line hRH hρ.1
  unfold N0 Ncount N0star Ndist
  rw [hset]
  exact ⟨rfl, rfl⟩

/-- Sanity anchor 2 [eq:trivialchain], verbatim: "trivially N₀ˢ ≤ N₀* ≤ N₀ ≤ N,
N₀ˢ ≤ Nˢ ≤ N_d ≤ N". Needs the seam facts (finiteness of the window; m_ρ ≥ 1), nothing from the
paper. -/
theorem trivial_chain (hs : ZetaSeam) (T₁ T₂ : ℝ) :
    N0simple T₁ T₂ ≤ N0star T₁ T₂ ∧ N0star T₁ T₂ ≤ N0 T₁ T₂ ∧ N0 T₁ T₂ ≤ Ncount T₁ T₂ ∧
    N0simple T₁ T₂ ≤ Nsimple T₁ T₂ ∧ Nsimple T₁ T₂ ≤ Ndist T₁ T₂ ∧ Ndist T₁ T₂ ≤ Ncount T₁ T₂ := by
  simpa using (zetaZeros hs).trivial_chain T₁ T₂

/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/

/-- The statement of Theorem A (2/3, dyadic ε-form) as a Prop, for reference; Zeta23.thmA proves it. -/
def ThmA_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (2 / 3 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0star T (2 * T)

/-- The statement of Theorem B (1/2, dyadic ε-form). -/
def ThmB_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (1 / 2 - ε) * (Ncount T (2 * T) : ℝ) ≤ N0simple T (2 * T)

/-- The statement of Theorem C (3/4, dyadic ε-form). -/
def ThmC_statement : Prop :=
  ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, (3 / 4 - ε) * (Ncount T (2 * T) : ℝ) ≤ Ndist T (2 * T)

end Zeta23
