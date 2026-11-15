module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/Backlund.lean — Backlund's bound for the horizontal variation of arg ζ, and the trivial
vertical side σ = 2. Consumed by Zeta23/RvM/Statement.lean, which proves
  N(T₁,T₂) = ∫_{T₁}^{T₂} μ + (1/π)·Im ∫_L ζ'/ζ ds,  L = ½+iT₁ → 2+iT₁ → 2+iT₂ → ½+iT₂
for non-ordinate heights and assembles RvM.main from GammaFacts.int_mu + the two bounds below.

* `backlund_horizontal` [Tit86 §9.4, Backlund 1918]: for T large and not the ordinate of a zero,
    |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ C log T.
  Route: g(z) := (ζ(z+iT) + conj ζ(z̄+iT))/2 is analytic near the disc |z−2| ≤ 1.9 and equals
  Re ζ(σ+iT) for real σ; g(2) = Re ζ(2+iT) ≥ 2 − π²/6 > 0; ZerosBound (PNT+ port, unit disc,
  r = 0.8, R = 0.9 after scaling by 1.9) + Zeta23.RvM.zeta_growth (δ = 0.2) give
  #{σ ∈ [½,2] : Re ζ(σ+iT) = 0} ≤ C log T; on each of the ≤ m+1 subintervals where Re ζ(σ+iT)
  has constant sign, Complex.log ∘ (±ζ(·+iT)) is a primitive of ζ'/ζ with |Im| ≤ π.
* `vertical_two`: |Im (I·∫_{T₁}^{T₂} ζ'/ζ(2+it) dt)| ≤ π — log ζ is a primitive on σ ≥ 2
  (‖ζ − 1‖ ≤ π²/6 − 1 < 1 there, Zeta23.RvM.norm_riemannZeta_sub_one_le), and
  |arg ζ(2+it)| ≤ π/2 since Re ζ(2+it) > 0.
-/
public import Zeta23.RvM.ZetaGrowth
public import Zeta23.RvM.BacklundDefs
public import Zeta23.RvM.ReZeroCount
public import Zeta23.Statement
public import Zeta23.FromPNTPlus.StrongPNTPrefix
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

open Complex Set MeasureTheory Real intervalIntegral

/- INSTANCE HYGIENE: `Zeta23.FromPNTPlus.StrongPNTPrefix` transitively imports
`Mathlib.Algebra.Lie.OfAssociative`, whose instance `LieAlgebra.ofAssociativeAlgebra` offers a second
(non-reducibly-defeq) route to `Module ℝ ℂ`; combined with this file's other imports that makes
`ContinuousSMul ℝ ℂ` — hence every `HasDerivAt (f : ℝ → ℂ)` — fail to synthesize (diagnosed
with `trace.Meta.synthInstance`).  Lie algebras are never used here. -/
attribute [-instance] LieAlgebra.ofAssociativeAlgebra

noncomputable section

namespace Zeta23
namespace RvM


/-! ## The horizontal side, calculus half: variation of the argument

Fix a height `T ≠ 0` with `ζ ≠ 0` on the segment `[1/2, 2] + iT`.  If `Re ζ(σ+iT)` has no zero on an
open subinterval `(u,v)`, it has constant sign `ε` there (IVT), `log(ε ζ(σ+iT))` is a primitive of
`ζ'/ζ(σ+iT)` on `[u,v]` (at the endpoints `ε ζ` is `≥ 0` in real part and `≠ 0`, so still in the
slit plane), hence `|Im ∫_u^v ζ'/ζ| ≤ 2π`.  Splitting `[1/2,2]` at the finitely many zeros of
`Re ζ(σ+iT)` (the set `reZeroSet T`, counted by the Jensen bound `reZeroSet_card_le`) gives
`|Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ 2π (#reZeroSet T + 1)` — by induction on the number of zeros inside
the interval (no sorting needed). -/

section Variation

variable {T : ℝ}

lemma ofReal_add_mul_I_ne_one (hT : T ≠ 0) (σ : ℝ) : (σ : ℂ) + T * I ≠ 1 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  exact hT this

/-- `σ ↦ ζ(σ+iT)` has derivative `ζ'(σ+iT)` in the real variable `σ`. -/
lemma hasDerivAt_riemannZeta_horizontal (hT : T ≠ 0) (σ : ℝ) :
    HasDerivAt (fun σ : ℝ => riemannZeta (σ + T * I)) (deriv riemannZeta (σ + T * I)) σ := by
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (σ + T * I)) (σ + T * I) :=
    (differentiableAt_riemannZeta (ofReal_add_mul_I_ne_one hT σ)).hasDerivAt
  have hγ : HasDerivAt (fun σ : ℝ => (σ : ℂ) + T * I) 1 σ := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 σ := Complex.ofRealCLM.hasDerivAt
    simpa using h1.add_const ((T : ℂ) * I)
  exact (hζ.comp σ hγ).congr_deriv (mul_one _)

lemma continuous_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => riemannZeta (σ + T * I)) :=
  continuous_iff_continuousAt.mpr fun σ => (hasDerivAt_riemannZeta_horizontal hT σ).continuousAt

lemma continuous_deriv_riemannZeta_horizontal (hT : T ≠ 0) :
    Continuous (fun σ : ℝ => deriv riemannZeta (σ + T * I)) := by
  have hγ : Continuous (fun σ : ℝ => (σ : ℂ) + T * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  exact hA.deriv.continuousOn.comp_continuous hγ (fun σ => ofReal_add_mul_I_ne_one hT σ)

/-- `σ ↦ ζ'/ζ(σ+iT)` is continuous on `[1/2,2]` when ζ has no zero on that segment. -/
lemma continuousOn_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0) :
    ContinuousOn (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) (Set.Icc (1/2 : ℝ) 2) := by
  have h : ContinuousOn (fun σ : ℝ => deriv riemannZeta (σ + T * I) / riemannZeta (σ + T * I))
      (Set.Icc (1/2 : ℝ) 2) :=
    (continuous_deriv_riemannZeta_horizontal hT).continuousOn.div
      (continuous_riemannZeta_horizontal hT).continuousOn hnz
  exact h.congr (fun σ _ => by rw [logDeriv_apply])

lemma intervalIntegrable_logDeriv_horizontal (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : u ∈ Set.Icc (1/2 : ℝ) 2) (hv : v ∈ Set.Icc (1/2 : ℝ) 2) :
    IntervalIntegrable (fun σ : ℝ => logDeriv riemannZeta (σ + T * I)) volume u v :=
  ((continuousOn_logDeriv_horizontal hT hnz).mono
    (Set.uIcc_subset_Icc hu hv)).intervalIntegrable

/-- **Base case.** If `Re ζ(σ+iT) ≠ 0` on `(u,v) ⊆ [1/2,2]` then `|Im ∫_u^v ζ'/ζ(σ+iT) dσ| ≤ 2π`. -/
lemma im_integral_le_two_pi (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    {u v : ℝ} (hu : 1/2 ≤ u) (huv : u < v) (hv : v ≤ 2)
    (hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0) :
    |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im| ≤ 2 * Real.pi := by
  set w : ℝ → ℂ := fun σ => riemannZeta (σ + T * I) with hwdef
  have hwc : Continuous w := continuous_riemannZeta_horizontal hT
  have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
  have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
  have hsub : Set.Icc u v ⊆ Set.Icc (1/2 : ℝ) 2 := Set.Icc_subset_Icc hu hv
  -- the sign ε ∈ {±1} of Re w at the midpoint
  set m : ℝ := (u + v) / 2 with hmdef
  have hm : m ∈ Set.Ioo u v := ⟨by rw [hmdef]; linarith, by rw [hmdef]; linarith⟩
  set ε : ℝ := if 0 < (w m).re then 1 else -1 with hεdef
  have hε : ε = 1 ∨ ε = -1 := by by_cases h : 0 < (w m).re <;> simp [hεdef, h]
  have hε0 : ε ≠ 0 := by rcases hε with h | h <;> simp [h]
  have hεm : 0 < ε * (w m).re := by
    by_cases h : 0 < (w m).re
    · simp [hεdef, h]
    · have h' : (w m).re < 0 := lt_of_le_of_ne (not_lt.mp h) (hno m hm)
      simp only [hεdef, if_neg h]; linarith
  -- g := ε · Re w is continuous and, by the IVT, positive on all of (u,v)
  set g : ℝ → ℝ := fun x => ε * (w x).re with hgdef
  have hg : Continuous g := continuous_const.mul (Complex.continuous_re.comp hwc)
  have hpos : ∀ σ ∈ Set.Ioo u v, 0 < g σ := by
    intro σ hσ
    by_contra hneg
    have hσne : g σ ≠ 0 := mul_ne_zero hε0 (hno σ hσ)
    have hσneg : g σ < 0 := lt_of_le_of_ne (not_lt.mp hneg) hσne
    have hIcc : Set.uIcc σ m ⊆ Set.Ioo u v := Set.ordConnected_Ioo.uIcc_subset hσ hm
    have h0 : (0 : ℝ) ∈ Set.uIcc (g σ) (g m) :=
      Set.mem_uIcc.mpr (Or.inl ⟨hσneg.le, hεm.le⟩)
    obtain ⟨x, hx, hx0⟩ := intermediate_value_uIcc hg.continuousOn h0
    exact mul_ne_zero hε0 (hno x (hIcc hx)) hx0
  -- by continuity, g ≥ 0 on the closed interval
  have hnonneg : ∀ σ ∈ Set.Icc u v, 0 ≤ g σ := by
    have hcl : IsClosed {x | 0 ≤ g x} := isClosed_le continuous_const hg
    have : Set.Icc u v ⊆ {x | 0 ≤ g x} := by
      rw [← closure_Ioo huv.ne]
      exact hcl.closure_subset_iff.mpr (fun x hx => (hpos x hx).le)
    exact fun σ hσ => this hσ
  -- hence ε·w stays in the slit plane on [u,v]
  have hslit : ∀ σ ∈ Set.Icc u v, (ε : ℂ) * w σ ∈ Complex.slitPlane := by
    intro σ hσ
    rw [Complex.mem_slitPlane_iff, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    rcases (hnonneg σ hσ).lt_or_eq with h | h
    · exact Or.inl h
    · right
      intro him
      have hre : (w σ).re = 0 := by
        rcases mul_eq_zero.mp h.symm with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      have him' : (w σ).im = 0 := by
        rcases mul_eq_zero.mp him with h1 | h1
        · exact absurd h1 hε0
        · exact h1
      exact hnz σ (hsub hσ) (Complex.ext hre him')
  -- Φ := log(ε·w) is a primitive of ζ'/ζ(σ+iT) on [u,v]
  have hderiv : ∀ σ ∈ Set.uIcc u v, HasDerivAt (fun x : ℝ => Complex.log ((ε : ℂ) * w x))
      (logDeriv riemannZeta (σ + T * I)) σ := by
    intro σ hσ
    rw [Set.uIcc_of_le huv.le] at hσ
    have hwσ : w σ ≠ 0 := hnz σ (hsub hσ)
    have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε0
    have h1 := (hasDerivAt_riemannZeta_horizontal hT σ).const_mul (ε : ℂ)
    have h2 := (Complex.hasDerivAt_log (hslit σ hσ)).comp σ h1
    have e : ((ε : ℂ) * w σ)⁻¹ * ((ε : ℂ) * deriv riemannZeta (σ + T * I))
        = logDeriv riemannZeta (σ + T * I) := by
      rw [logDeriv_apply, show riemannZeta ((σ : ℂ) + T * I) = w σ from rfl]
      field_simp
    rw [e] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_logDeriv_horizontal hT hnz huI hvI),
    Complex.sub_im, Complex.log_im, Complex.log_im]
  calc |((ε : ℂ) * w v).arg - ((ε : ℂ) * w u).arg|
      ≤ |((ε : ℂ) * w v).arg| + |((ε : ℂ) * w u).arg| := abs_sub _ _
    _ ≤ Real.pi + Real.pi := add_le_add (Complex.abs_arg_le_pi _) (Complex.abs_arg_le_pi _)
    _ = 2 * Real.pi := by ring

/-- **Induction.** With `P ⊇` the zeros of `Re ζ(σ+iT)` in `[1/2,2]`:
`|Im ∫_u^v ζ'/ζ(σ+iT) dσ| ≤ 2π (#(P ∩ (u,v)) + 1)` for `1/2 ≤ u < v ≤ 2`. -/
lemma im_integral_logDeriv_le_aux (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (P : Finset ℝ) (hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P) :
    ∀ n : ℕ, ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card ≤ n →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ 2 * Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
  -- the empty-interior case, used twice
  have base : ∀ u v : ℝ, 1/2 ≤ u → u < v → v ≤ 2 →
      (P.filter (fun x => u < x ∧ x < v)).card = 0 →
      |(∫ σ in u..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ 2 * Real.pi * ((P.filter (fun x => u < x ∧ x < v)).card + 1) := by
    intro u v hu huv hv hc
    have hno : ∀ σ ∈ Set.Ioo u v, (riemannZeta (σ + T * I)).re ≠ 0 := by
      intro σ hσ hre
      have hσP : σ ∈ P.filter (fun x => u < x ∧ x < v) :=
        Finset.mem_filter.mpr ⟨hP σ ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ hre, hσ.1, hσ.2⟩
      rw [Finset.card_eq_zero] at hc
      simp [hc] at hσP
    rw [hc]
    have := im_integral_le_two_pi hT hnz hu huv hv hno
    simpa using this
  intro n
  induction n with
  | zero =>
    intro u v hu huv hv hc
    exact base u v hu huv hv (Nat.le_zero.mp hc)
  | succ n ih =>
    intro u v hu huv hv hc
    by_cases hc0 : (P.filter (fun x => u < x ∧ x < v)).card = 0
    · exact base u v hu huv hv hc0
    obtain ⟨m, hm⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc0)
    obtain ⟨-, hum, hmv⟩ := Finset.mem_filter.mp hm
    -- the two halves carry fewer points: c₁ + c₂ + 1 ≤ c
    set S := P.filter (fun x => u < x ∧ x < v) with hSdef
    set S₁ := P.filter (fun x => u < x ∧ x < m) with hS₁def
    set S₂ := P.filter (fun x => m < x ∧ x < v) with hS₂def
    have hdisj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have := (Finset.mem_filter.mp hx1).2.2
      have := (Finset.mem_filter.mp hx2).2.1
      linarith
    have hsubS : S₁ ∪ S₂ ⊆ S.erase m := by
      intro x hx
      rw [Finset.mem_erase]
      rcases Finset.mem_union.mp hx with hx | hx
      · obtain ⟨hxP, hux, hxm⟩ := Finset.mem_filter.mp hx
        exact ⟨hxm.ne, Finset.mem_filter.mpr ⟨hxP, hux, by linarith⟩⟩
      · obtain ⟨hxP, hmx, hxv⟩ := Finset.mem_filter.mp hx
        exact ⟨hmx.ne', Finset.mem_filter.mpr ⟨hxP, by linarith, hxv⟩⟩
    have hcard : S₁.card + S₂.card + 1 ≤ S.card := by
      have h1 : S₁.card + S₂.card = (S₁ ∪ S₂).card := (Finset.card_union_of_disjoint hdisj).symm
      have h2 : (S₁ ∪ S₂).card ≤ (S.erase m).card := Finset.card_le_card hsubS
      have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hm
      have h4 : 1 ≤ S.card := Finset.card_pos.mpr ⟨m, hm⟩
      omega
    have hc1 : S₁.card ≤ n := by omega
    have hc2 : S₂.card ≤ n := by omega
    have e1 := ih u m hu hum (by linarith) hc1
    have e2 := ih m v (by linarith) hmv hv hc2
    -- split the integral at m
    have hmI : m ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, by linarith⟩
    have huI : u ∈ Set.Icc (1/2 : ℝ) 2 := ⟨hu, by linarith⟩
    have hvI : v ∈ Set.Icc (1/2 : ℝ) 2 := ⟨by linarith, hv⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_logDeriv_horizontal hT hnz huI hmI)
      (intervalIntegrable_logDeriv_horizontal hT hnz hmI hvI), Complex.add_im]
    have hcast : ((S₁.card : ℝ) + 1) + ((S₂.card : ℝ) + 1) ≤ (S.card : ℝ) + 1 := by
      have : ((S₁.card + S₂.card + 1 : ℕ) : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
      push_cast at this; linarith
    calc |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im
          + (∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im|
        ≤ |(∫ σ in u..m, logDeriv riemannZeta (σ + T * I)).im|
          + |(∫ σ in m..v, logDeriv riemannZeta (σ + T * I)).im| := abs_add_le _ _
      _ ≤ 2 * Real.pi * ((S₁.card : ℝ) + 1) + 2 * Real.pi * ((S₂.card : ℝ) + 1) := add_le_add e1 e2
      _ ≤ 2 * Real.pi * ((S.card : ℝ) + 1) := by nlinarith [Real.pi_pos]

/-- **(V) Variation of the argument along `[1/2,2] + iT`:** if `ζ ≠ 0` there and `Re ζ(σ+iT)` has
finitely many zeros, then `|Im ∫_{1/2}^{2} ζ'/ζ(σ+iT) dσ| ≤ 2π (#reZeroSet T + 1)`. -/
theorem im_integral_logDeriv_le (hT : T ≠ 0)
    (hnz : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0)
    (hfin : (reZeroSet T).Finite) :
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im|
      ≤ 2 * Real.pi * ((reZeroSet T).ncard + 1) := by
  set P := hfin.toFinset with hPdef
  have hP : ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, (riemannZeta (σ + T * I)).re = 0 → σ ∈ P :=
    fun σ hσ h => hfin.mem_toFinset.mpr ⟨hσ, h⟩
  have h := im_integral_logDeriv_le_aux hT hnz P hP P.card (1/2) 2 le_rfl (by norm_num) le_rfl
    (Finset.card_filter_le _ _)
  have hc : ((P.filter (fun x => (1/2 : ℝ) < x ∧ x < 2)).card : ℝ) ≤ (reZeroSet T).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast Finset.card_filter_le _ _
  refine h.trans ?_
  nlinarith [Real.pi_pos]

end Variation

/-! ## Assembly of Backlund's bound from (J) = `reZeroSet_card_le`  and (V) -/

/-- ζ has no zero on `[1/2,2] + iT` when `T` is not the ordinate of a nontrivial zero. -/
lemma riemannZeta_ne_zero_on_segment {T : ℝ} (hord : ∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) :
    ∀ σ ∈ Set.Icc (1/2 : ℝ) 2, riemannZeta (σ + T * I) ≠ 0 := by
  intro σ hσ hz
  rcases lt_or_ge σ 1 with h | h
  · refine hord (σ + T * I) ⟨hz, ?_, ?_⟩ (by simp)
    · simp; linarith [hσ.1]
    · simpa using h
  · exact riemannZeta_ne_zero_of_one_le_re (by simpa using h) hz

/-- **Backlund's bound from the zero count (J)**, parametric form: a count ncard ≤ C·log T for
T ≥ T₀ gives |Im ∫_{1/2}^{2} ζ'/ζ(σ+iT)dσ| ≤ 2π(C+1)·log T for T ≥ max T₀ 3. -/
theorem backlund_horizontal_of_count_at {C T₀ : ℝ}
    (hJ : ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∀ T : ℝ, max T₀ 3 ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im|
      ≤ 2 * Real.pi * (C + 1) * Real.log T := by
  intro T hT hord
  have hT₀ : T₀ ≤ T := (le_max_left _ _).trans hT
  have hT3 : (3 : ℝ) ≤ T := (le_max_right _ _).trans hT
  have hTne : T ≠ 0 := by linarith
  obtain ⟨hfin, hcount⟩ := hJ T hT₀
  have hlog : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)])
  have h := im_integral_logDeriv_le hTne (riemannZeta_ne_zero_on_segment hord) hfin
  refine h.trans ?_
  have hπ := Real.pi_pos
  nlinarith [hcount, hlog, mul_nonneg hπ.le (sub_nonneg.mpr hlog)]

/-- **Backlund's bound from the zero count (J).** -/
theorem backlund_horizontal_of_count
    (hJ : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      (reZeroSet T).Finite ∧ ((reZeroSet T).ncard : ℝ) ≤ C * Real.log T) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T := by
  obtain ⟨C, T₀, hJ⟩ := hJ
  exact ⟨_, _, backlund_horizontal_of_count_at hJ⟩

/-- **Backlund's bound**. For all large T that are not ordinates of nontrivial zeros,
|Im ∫_{1/2}^{2} ζ'/ζ(σ + iT) dσ| ≤ C·log T. -/
theorem backlund_horizontal : ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im| ≤ C * Real.log T :=
  backlund_horizontal_of_count reZeroSet_card_le

/-- **Backlund's bound, explicit**: for T ≥ 4 a zero-free height,
|Im ∫_{1/2}^{2} ζ'/ζ(σ+iT)dσ| ≤ 2π·(C_J + 1)·log T with C_J = (1/log(0.9/0.8))(|log 40| + 2) ≈ 48.3
(so the constant is ≈ 310). -/
theorem backlund_horizontal_at : ∀ T : ℝ, max 4 3 ≤ T →
    (∀ ρ, IsNontrivialZero ρ → ρ.im ≠ T) →
    |(∫ σ in (1 / 2 : ℝ)..2, logDeriv riemannZeta (σ + T * I)).im|
      ≤ 2 * Real.pi * ((1 / Real.log ((0.9 : ℝ) / 0.8)
          * (|Real.log (6 * (20 / 3 : ℝ))| + 2 * max (1 : ℝ) 0)) + 1) * Real.log T :=
  backlund_horizontal_of_count_at reZeroSet_card_le_at

/-! ## The vertical side σ = 2 -/

/-- `Re ζ(2+it) > 0` (indeed `≥ 2 − π²/6`), from `‖ζ(s) − 1‖ ≤ π²/6 − 1 < 1` on `Re s ≥ 2`. -/
lemma re_riemannZeta_two_pos (t : ℝ) : 0 < (riemannZeta (2 + t * I)).re := by
  have h := norm_riemannZeta_sub_one_le (s := 2 + t * I) (by simp)
  have h2 : |(riemannZeta (2 + t * I) - 1).re| ≤ ‖riemannZeta (2 + t * I) - 1‖ :=
    Complex.abs_re_le_norm _
  rw [Complex.sub_re, Complex.one_re] at h2
  have h3 := (abs_le.mp (h2.trans h)).1
  linarith [pi_sq_div_six_sub_one_lt_one]

lemma two_add_mul_I_ne_one (t : ℝ) : (2 : ℂ) + t * I ≠ 1 := by
  intro h
  have := congrArg Complex.re h
  simp at this

/-- `t ↦ log ζ(2+it)` is a primitive of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma hasDerivAt_log_riemannZeta_two (t : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.log (riemannZeta (2 + t * I)))
      (logDeriv riemannZeta (2 + t * I) * I) t := by
  have hs := two_add_mul_I_ne_one t
  have hζ : HasDerivAt riemannZeta (deriv riemannZeta (2 + t * I)) (2 + t * I) :=
    (differentiableAt_riemannZeta hs).hasDerivAt
  have hγ : HasDerivAt (fun t : ℝ => (2 : ℂ) + t * I) I t := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
    simpa using (h1.mul_const I).const_add (2 : ℂ)
  have hcomp : HasDerivAt (fun t : ℝ => riemannZeta (2 + t * I)) (deriv riemannZeta (2 + t * I) * I) t :=
    hζ.comp t hγ
  have hlog : HasDerivAt Complex.log (riemannZeta (2 + t * I))⁻¹ (riemannZeta (2 + t * I)) :=
    Complex.hasDerivAt_log (Or.inl (re_riemannZeta_two_pos t))
  have h := hlog.comp t hcomp
  have e : (riemannZeta (2 + t * I))⁻¹ * (deriv riemannZeta (2 + t * I) * I)
      = logDeriv riemannZeta (2 + t * I) * I := by
    rw [logDeriv_apply]; ring
  rw [e] at h
  exact h

/-- Continuity of `t ↦ ζ'/ζ(2+it)·i`. -/
lemma continuous_logDeriv_riemannZeta_two :
    Continuous (fun t : ℝ => logDeriv riemannZeta (2 + t * I) * I) := by
  have hγ : Continuous (fun t : ℝ => (2 : ℂ) + t * I) := by fun_prop
  have hA : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := analyticOnNhd_riemannZeta (by simp)
  have hd : Continuous (fun t : ℝ => deriv riemannZeta (2 + t * I)) :=
    hA.deriv.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hz : Continuous (fun t : ℝ => riemannZeta (2 + t * I)) :=
    hA.continuousOn.comp_continuous hγ (fun t => two_add_mul_I_ne_one t)
  have hne : ∀ t : ℝ, riemannZeta (2 + t * I) ≠ 0 := fun t h => by
    have := re_riemannZeta_two_pos t; rw [h] at this; simp at this
  simp only [logDeriv_apply]
  exact ((hd.div hz hne).mul continuous_const)

/-- **Vertical side σ = 2.** `|Im (∫_{T₁}^{T₂} ζ'/ζ(2+it)·i dt)| ≤ π` for all `T₁, T₂`:
`log ζ(2+it)` is a primitive, and `|arg ζ(2+it)| ≤ π/2` since `Re ζ(2+it) > 0`.
(The sharper constant `2 log 3` also holds — |arg| ≤ arcsin(π²/6−1) — but an absolute
constant suffices for the consumer.) -/
theorem vertical_two : ∀ T₁ T₂ : ℝ,
    |(∫ t in T₁..T₂, logDeriv riemannZeta (2 + t * I) * I).im| ≤ Real.pi := by
  intro T₁ T₂
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_log_riemannZeta_two t)
    (continuous_logDeriv_riemannZeta_two.intervalIntegrable _ _)]
  rw [Complex.sub_im, Complex.log_im, Complex.log_im]
  have h1 : |(riemannZeta (2 + T₂ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₂).le
  have h2 : |(riemannZeta (2 + T₁ * I)).arg| ≤ π / 2 :=
    Complex.abs_arg_le_pi_div_two_iff.mpr (re_riemannZeta_two_pos T₁).le
  calc |(riemannZeta (2 + T₂ * I)).arg - (riemannZeta (2 + T₁ * I)).arg|
      ≤ |(riemannZeta (2 + T₂ * I)).arg| + |(riemannZeta (2 + T₁ * I)).arg| := abs_sub _ _
    _ ≤ π / 2 + π / 2 := add_le_add h1 h2
    _ = π := by ring

end RvM
end Zeta23
