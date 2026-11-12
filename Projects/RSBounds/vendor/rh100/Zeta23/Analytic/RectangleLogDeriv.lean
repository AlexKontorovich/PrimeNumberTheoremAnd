module

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Residue calculus on rectangles beyond one simple pole.
Used for the weighted contour integral ∮ H·Λ'/Λ and for the Riemann–von Mangoldt count
N(T₁,T₂) = (1/2πi)∮ Λ'/Λ.

* `residueTheorem_finset`: f holomorphic on Rectangle z w minus a finite set S of interior points, with
  f − A p/(s − p) bounded near each p ∈ S  ⟹  RectangleIntegral' f z w = Σ_{p∈S} A p.
  (Induction on S: subtract one principal part, remove the singularity, recurse.)
* `rectangleIntegral'_mul_logDeriv` (the "argument principle with weight"): f, g analytic on a
  neighbourhood of each point of Rectangle z w, f ≠ 0 on the border, Z = the (finite) zero set of
  f in the rectangle  ⟹  RectangleIntegral' (g · f'/f) z w = Σ_{ρ∈Z} ord_ρ(f) · g(ρ).
* `finite_zeros_rectangle`, `rectangleIntegral'_mul_logDeriv'`: the zero set is finite; self-contained form.
-/
public import Zeta23.FromPNTPlus.ResidueCalcOnRectangles
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Calculus.LogDeriv

@[expose] public section

open Complex Set Topology Filter Asymptotics Real

noncomputable section

namespace Zeta23
namespace Analytic

/-- **Residue theorem on a rectangle for finitely many simple poles.** -/
theorem residueTheorem_finset {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty =>
    simp only [Finset.coe_empty, sdiff_empty] at fHolo
    rw [Finset.sum_empty]
    show (1 / (2 * π * I)) • RectangleIntegral f z w = 0
    rw [fHolo.vanishesOnRectangle subset_rfl, smul_zero]
  | @insert p S hpS ih =>
    have hp : Rectangle z w ∈ 𝓝 p := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ q ∈ S, Rectangle z w ∈ 𝓝 q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
    -- the principal part at p, the remainder f₁, and its extension f₂ across p
    set P : ℂ → ℂ := fun s => A p / (s - p) with hP
    set f₁ : ℂ → ℂ := f - P with hf₁
    set f₂ : ℂ → ℂ := Function.update f₁ p (limUnder (𝓝[≠] p) f₁) with hf₂
    have hPdiff : ∀ s, s ≠ p → DifferentiableAt ℂ P s := by
      intro s hs
      have : s - p ≠ 0 := sub_ne_zero.mpr hs
      simp only [hP]
      fun_prop (disch := assumption)
    have hf₁holo : HolomorphicOn f₁ (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) := by
      refine fHolo.sub ?_
      intro s hs
      apply (hPdiff s ?_).differentiableWithinAt
      intro h
      apply hs.2
      simp [h]
    have hSclosed : IsClosed (S : Set ℂ) := S.finite_toSet.isClosed
    have hRS : Rectangle z w \ (S : Set ℂ) ∈ 𝓝 p := by
      apply Filter.inter_mem hp
      exact hSclosed.isOpen_compl.mem_nhds (by simpa using hpS)
    obtain ⟨U, hU, hbdd⟩ := IsBigO_to_BddAbove (near p (Finset.mem_insert_self p S))
    have hV : U ∩ (Rectangle z w \ (S : Set ℂ)) ∈ 𝓝 p := Filter.inter_mem hU hRS
    have hf₁V : DifferentiableOn ℂ f₁ ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p}) := by
      apply hf₁holo.mono
      rintro s ⟨⟨_, hsR, hsS⟩, hsp⟩
      refine ⟨hsR, ?_⟩
      simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
      exact ⟨by simpa using hsp, by simpa using hsS⟩
    have hbddV : BddAbove (norm ∘ f₁ '' ((U ∩ (Rectangle z w \ (S : Set ℂ))) \ {p})) :=
      hbdd.mono (image_mono (Set.sdiff_subset_sdiff_left inter_subset_left))
    have hf₂V : DifferentiableOn ℂ f₂ (U ∩ (Rectangle z w \ (S : Set ℂ))) :=
      differentiableOn_update_limUnder_of_bddAbove hV hf₁V hbddV
    have hf₂eq : ∀ s, s ≠ p → f₂ s = f₁ s := fun s hs => Function.update_of_ne hs _ _
    -- f₂ is holomorphic on the rectangle minus the remaining poles
    have hf₂holo : HolomorphicOn f₂ (Rectangle z w \ (S : Set ℂ)) := by
      intro s hs
      by_cases hsp : s = p
      · rw [hsp]
        exact (hf₂V.differentiableAt hV).differentiableWithinAt
      · have h1 : DifferentiableWithinAt ℂ f₁
            (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ)) s :=
          hf₁holo s ⟨hs.1, by
            simp only [Finset.coe_insert, mem_insert_iff, Finset.mem_coe, not_or]
            exact ⟨hsp, by simpa using hs.2⟩⟩
        have hset : (Rectangle z w \ ((insert p S : Finset ℂ) : Set ℂ))
            = (Rectangle z w \ (S : Set ℂ)) ∩ {p}ᶜ := by
          ext x
          simp only [Finset.coe_insert, Set.mem_sdiff, mem_insert_iff, Finset.mem_coe, not_or,
            mem_inter_iff, mem_compl_iff, mem_singleton_iff]
          tauto
        rw [hset] at h1
        have hpc : {p}ᶜ ∈ 𝓝[Rectangle z w \ (S : Set ℂ)] s :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hsp)
        rw [differentiableWithinAt_inter' hpc] at h1
        refine h1.congr_of_eventuallyEq ?_ (hf₂eq s hsp)
        filter_upwards [hpc] with x hx
        exact hf₂eq x hx
    -- the principal parts at the other poles are unchanged
    have near₂ : ∀ q ∈ S, (f₂ - fun s => A q / (s - q)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
      intro q hq
      have hqp : q ≠ p := fun h => hpS (h ▸ hq)
      have hev : ((f - fun s => A q / (s - q)) - P)
          =ᶠ[𝓝[≠] q] (f₂ - fun s => A q / (s - q)) := by
        have : {p}ᶜ ∈ 𝓝[≠] q :=
          mem_nhdsWithin_of_mem_nhds (isOpen_compl_singleton.mem_nhds hqp)
        filter_upwards [this] with s hs
        simp only [Pi.sub_apply, hf₂eq s hs, hf₁]
        ring
      have hPO : P =O[𝓝[≠] q] (1 : ℂ → ℂ) := by
        have hc : ContinuousAt P q := (hPdiff q hqp).continuousAt
        exact (hc.tendsto.mono_left nhdsWithin_le_nhds).isBigO_one ℂ
      exact ((near q (Finset.mem_insert_of_mem hq)).sub hPO).congr' hev EventuallyEq.rfl
    have ih' := ih hS' hf₂holo near₂
    -- on the border, f = f₂ + P
    have hborder : EqOn f (f₂ + P) (RectangleBorder z w) := by
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      simp only [Pi.add_apply, hf₂eq s hsp, hf₁, Pi.sub_apply, sub_add_cancel]
    have hbS : ∀ s ∈ RectangleBorder z w, s ∈ Rectangle z w \ (S : Set ℂ) := fun s hs =>
      ⟨rectangleBorder_subset_rectangle z w hs,
        fun hsS => not_mem_rectangleBorder_of_rectangle_mem_nhds (hS' s hsS) hs⟩
    have hi₂ : RectangleBorderIntegrable f₂ z w :=
      ContinuousOn.rectangleBorder_integrable (hf₂holo.continuousOn.mono hbS)
    have hiP : RectangleBorderIntegrable P z w := by
      apply ContinuousOn.rectangleBorder_integrable
      intro s hs
      have hsp : s ≠ p := fun h => not_mem_rectangleBorder_of_rectangle_mem_nhds hp (h ▸ hs)
      exact (hPdiff s hsp).continuousAt.continuousWithinAt
    rw [RectangleIntegral'_congr hborder, Finset.sum_insert hpS]
    show (1 / (2 * π * I)) • RectangleIntegral (f₂ + P) z w = _
    rw [RectangleBorderIntegrable.add hi₂ hiP, smul_add]
    show RectangleIntegral' f₂ z w + RectangleIntegral' P z w = _
    rw [ih', ResidueTheoremInRectangle hre him hp, add_comm]

/-- The zero set of a function analytic on a neighbourhood of every point of a rectangle and
nonvanishing at one of its points is finite. -/
theorem finite_zeros_rectangle {f : ℂ → ℂ} {z w : ℂ} (hf : AnalyticOnNhd ℂ f (Rectangle z w))
    {x : ℂ} (hx : x ∈ Rectangle z w) (hfx : f x ≠ 0) :
    (Rectangle z w ∩ f ⁻¹' {0}).Finite := by
  have hconv : Convex ℝ (Rectangle z w) := by
    rw [rectangle_eq_convexHull]; exact convex_convexHull ℝ _
  have hcomp : IsCompact (Rectangle z w) := isCompact_uIcc.reProdIm isCompact_uIcc
  refine IsCompact.finite ?_ ?_
  · exact hcomp.of_isClosed_subset
      (hf.continuousOn.preimage_isClosed_of_isClosed hcomp.isClosed isClosed_singleton)
      inter_subset_left
  · rw [inter_comm]
    exact isDiscrete_of_codiscreteWithin
      (hf.preimage_zero_mem_codiscreteWithin hfx hx ⟨⟨x, hx⟩, hconv.isPreconnected⟩)

/-! ## Meromorphic version: finitely many zeros AND poles inside the rectangle

Intended for f = completedRiemannZeta (simple poles at 0 and 1, residues ∓1):
(1/2πi) ∮ g·(f'/f) = Σ_{zeros ρ} ord_ρ(f)·g(ρ) − Σ_{poles p} m_p·g(p).
A pole of order m at p is witnessed elementarily by  (s − p)^m · f(s) → c ≠ 0  (s → p, s ≠ p),
which is the shape of Mathlib's `completedRiemannZeta_residue_one` (m = 1). -/

/-- **Weighted argument principle with poles.** f analytic on a neighbourhood of every point of
the closed rectangle except at the finitely many interior points P, where (s − p)^{m p} f(s) → c_p ≠ 0;
g analytic on a neighbourhood of every point; f ≠ 0 on the border; Z = zero set of f in the
rectangle (off P). Then (1/2πi)∮ g·f'/f = Σ_{ρ∈Z} ord_ρ(f) g(ρ) − Σ_{p∈P} m_p g(p). -/
theorem rectangleIntegral'_mul_logDeriv_of_poles {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z P : Finset ℂ) (hZP : Disjoint Z P)
    (hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w \ (P : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w \ (P : Set ℂ), f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w)
    (m : ℂ → ℕ)
    (hpole : ∀ p ∈ P, ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun s => (s - p) ^ m p * f s) (𝓝[≠] p) (𝓝 c)) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ - ∑ p ∈ P, (m p : ℂ) * g p := by
  classical
  have hZnotP : ∀ ρ ∈ Z, ρ ∉ P := fun ρ hρ hρP => Finset.disjoint_left.mp hZP hρ hρP
  have hZmem : ∀ ρ ∈ Z, ρ ∈ Rectangle z w \ (P : Set ℂ) := fun ρ hρ =>
    ⟨hZsub hρ, by simpa using hZnotP ρ hρ⟩
  -- zeros are interior points
  have hZint : ∀ ρ ∈ Z, Rectangle z w ∈ 𝓝 ρ := by
    intro ρ hρ
    have hρR : ρ ∈ Rectangle z w := hZsub hρ
    have hρB : ρ ∉ RectangleBorder z w := fun h => hborder ρ h ((hZ ρ (hZmem ρ hρ)).mpr hρ)
    obtain ⟨h1, h2⟩ := hρR
    have h1' : z.re ≤ ρ.re ∧ ρ.re ≤ w.re := by simpa [uIcc_of_le hre] using h1
    have h2' : z.im ≤ ρ.im ∧ ρ.im ≤ w.im := by simpa [uIcc_of_le him] using h2
    simp only [RectangleBorder, mem_union, mem_reProdIm, mem_singleton_iff, not_or] at hρB
    obtain ⟨⟨⟨hb1, hb2⟩, hb3⟩, hb4⟩ := hρB
    rw [rectangle_mem_nhds_iff, mem_reProdIm, uIoo_of_le hre, uIoo_of_le him]
    refine ⟨⟨lt_of_le_of_ne h1'.1 (fun h => hb2 ⟨h.symm, h2⟩),
      lt_of_le_of_ne h1'.2 (fun h => hb4 ⟨h, h2⟩)⟩,
      ⟨lt_of_le_of_ne h2'.1 (fun h => hb1 ⟨h1, h.symm⟩),
      lt_of_le_of_ne h2'.2 (fun h => hb3 ⟨h1, h⟩)⟩⟩
  -- residues: +ord·g at zeros, −m·g at poles
  let A : ℂ → ℂ := fun q => if q ∈ P then -((m q : ℂ) * g q) else (analyticOrderNatAt f q : ℂ) * g q
  have hint : ∀ q ∈ Z ∪ P, Rectangle z w ∈ 𝓝 q := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    exacts [hZint q hq, hPint q hq]
  have key := residueTheorem_finset (f := fun s => g s * logDeriv f s) hre him (Z ∪ P) A hint
    ?holo ?near
  · rw [key, Finset.sum_union hZP]
    have hZsum : ∑ q ∈ Z, A q = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ :=
      Finset.sum_congr rfl (fun q hq => by simp [A, hZnotP q hq])
    have hPsum : ∑ q ∈ P, A q = -∑ p ∈ P, (m p : ℂ) * g p := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl (fun q hq => by simp [A, hq])
    rw [hZsum, hPsum, sub_eq_add_neg]
  case holo =>
    intro s hs
    have hsP : s ∉ P := fun h => hs.2 (by simp [h])
    have hsZ : s ∉ Z := fun h => hs.2 (by simp [h])
    have hsRP : s ∈ Rectangle z w \ (P : Set ℂ) := ⟨hs.1, by simpa using hsP⟩
    have hfs : f s ≠ 0 := fun h => hsZ ((hZ s hsRP).mp h)
    have hfa := hf s hsRP
    have hga := hg s hs.1
    apply DifferentiableAt.differentiableWithinAt
    show DifferentiableAt ℂ (fun s => g s * (deriv f s / f s)) s
    exact hga.differentiableAt.mul (hfa.deriv.differentiableAt.div hfa.differentiableAt hfs)
  case near =>
    intro q hq
    rcases Finset.mem_union.mp hq with hρ | hp
    · ---------------- a zero ρ := q
      have hρRP := hZmem q hρ
      have hga := hg q (hZsub hρ)
      have hA : A q = (analyticOrderNatAt f q : ℂ) * g q := by simp [A, hZnotP q hρ]
      by_cases htop : analyticOrderAt f q = ⊤
      · -- f vanishes identically near q: everything is 0
        have h0 : ∀ᶠ s in 𝓝 q, f s = 0 := analyticOrderAt_eq_top.mp htop
        have hO : (fun _ : ℂ => (0 : ℂ)) =O[𝓝[≠] q] (1 : ℂ → ℂ) := isBigO_zero _ _
        refine hO.congr' ?_ EventuallyEq.rfl
        filter_upwards [mem_nhdsWithin_of_mem_nhds (h0.eventually_nhds)] with s hs
        have hs' : f =ᶠ[𝓝 s] fun _ => (0 : ℂ) := hs
        have hds : deriv f s = 0 := by
          rw [hs'.deriv_eq]; simp
        simp [hA, logDeriv_apply, hds, analyticOrderNatAt, htop]
      obtain ⟨h, hh, hh0, hfh⟩ := (hf q hρRP).analyticOrderAt_ne_top.mp htop
      have hh_ne : ∀ᶠ s in 𝓝 q, h s ≠ 0 := hh.continuousAt.eventually_ne hh0
      have h2 : ∀ᶠ s in 𝓝 q, f =ᶠ[𝓝 s] (fun s => (s - q) ^ analyticOrderNatAt f q • h s) :=
        hfh.eventually_nhds
      have h3 : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ h s := hh.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q)) + g s * logDeriv h s
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds h2,
          mem_nhdsWithin_of_mem_nhds hh_ne, mem_nhdsWithin_of_mem_nhds h3]
          with s hs hfs hhs hhas
        have hsq : s - q ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
        have hld : logDeriv f s = (analyticOrderNatAt f q : ℂ) / (s - q) + logDeriv h s := by
          have e1 : logDeriv f s
              = logDeriv (fun s => (s - q) ^ analyticOrderNatAt f q * h s) s := by
            simp only [logDeriv_apply, hfs.deriv_eq, hfs.self_of_nhds, smul_eq_mul]
          rw [e1, logDeriv_fun_mul (f := fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) (g := h) s
            (pow_ne_zero _ hsq) hhs (by fun_prop) hhas.differentiableAt]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q) s
              = (analyticOrderNatAt f q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ analyticOrderNatAt f q)
                = (fun x : ℂ => x ^ analyticOrderNatAt f q) ∘ (fun s => s - q) from rfl,
              logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        simp only [Pi.sub_apply, hld, hA]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv h s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv h q)) := by
        have : ContinuousAt (fun s => g s * logDeriv h s) q := by
          show ContinuousAt (fun s => g s * (deriv h s / h s)) q
          exact hga.continuousAt.mul (hh.deriv.continuousAt.div hh.continuousAt hh0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => (analyticOrderNatAt f q : ℂ) * ((g s - g q) / (s - q))
          + g s * logDeriv h s) =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        ((hslope.const_mul (analyticOrderNatAt f q : ℂ)).add hcont).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl
    · ---------------- a pole p := q
      obtain ⟨c, hc, hT⟩ := hpole q hp
      have hqR : q ∈ Rectangle z w := mem_of_mem_nhds (hPint q hp)
      have hga := hg q hqR
      have hA : A q = -((m q : ℂ) * g q) := by simp [A, hp]
      -- the regularisation G := (s − q)^m · f, extended by c at q: analytic at q, G q ≠ 0
      set F : ℂ → ℂ := fun s => (s - q) ^ m q * f s with hF
      set G : ℂ → ℂ := Function.update F q c with hG
      have hGq : G q = c := Function.update_self _ _ _
      have hGF : ∀ s, s ≠ q → G s = F s := fun s hs => Function.update_of_ne hs _ _
      have hPc : ((P : Set ℂ) \ {q})ᶜ ∈ 𝓝 q :=
        (P.finite_toSet.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      have hnear : ∀ᶠ s in 𝓝[≠] q, s ≠ q ∧ s ∈ Rectangle z w \ (P : Set ℂ) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds (hPint q hp),
          mem_nhdsWithin_of_mem_nhds hPc, self_mem_nhdsWithin] with s h1 h2 h3
        have h3' : s ≠ q := by simpa using h3
        exact ⟨h3', h1, fun hsP => h2 ⟨hsP, by simpa using h3'⟩⟩
      have hGdiff : ∀ᶠ s in 𝓝[≠] q, DifferentiableAt ℂ G s := by
        filter_upwards [hnear] with s ⟨hsq, hsRP⟩
        have hFs : DifferentiableAt ℂ F s :=
          ((differentiableAt_id.sub_const q).pow _).mul (hf s hsRP).differentiableAt
        refine hFs.congr_of_eventuallyEq ?_
        filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
        exact hGF x hx
      have hGcont : ContinuousAt G q := by
        rw [hG, continuousAt_update_same]
        exact hT
      have hGan : AnalyticAt ℂ G q :=
        analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hGdiff hGcont
      have hG0 : G q ≠ 0 := by rwa [hGq]
      have hFne : ∀ᶠ s in 𝓝[≠] q, F s ≠ 0 := hT.eventually_ne hc
      have hGan' : ∀ᶠ s in 𝓝 q, AnalyticAt ℂ G s := hGan.eventually_analyticAt
      have hexp : ∀ᶠ s in 𝓝[≠] q,
          g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q))
            = ((fun s => g s * logDeriv f s) - fun s => A q / (s - q)) s := by
        filter_upwards [hnear, hFne, mem_nhdsWithin_of_mem_nhds hGan'] with s ⟨hsq, hsRP⟩ hFs hGs
        have hsq' : s - q ≠ 0 := sub_ne_zero.mpr hsq
        have hfs : f s ≠ 0 := fun h => hFs (by simp [hF, h])
        have hfd : DifferentiableAt ℂ f s := (hf s hsRP).differentiableAt
        have hldF : logDeriv F s = (m q : ℂ) / (s - q) + logDeriv f s := by
          rw [hF, logDeriv_fun_mul (f := fun s : ℂ => (s - q) ^ m q) (g := f) s
            (pow_ne_zero _ hsq') hfs (by fun_prop) hfd]
          have e2 : logDeriv (fun s : ℂ => (s - q) ^ m q) s = (m q : ℂ) / (s - q) := by
            rw [show (fun s : ℂ => (s - q) ^ m q) = (fun x : ℂ => x ^ m q) ∘ (fun s => s - q)
                from rfl, logDeriv_comp (by fun_prop) (by fun_prop), logDeriv_pow]
            simp
          rw [e2]
        have hGFs : G =ᶠ[𝓝 s] F := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hsq] with x hx
          exact hGF x hx
        have hldG : logDeriv G s = logDeriv F s := by
          simp only [logDeriv_apply, hGFs.deriv_eq, hGFs.self_of_nhds]
        simp only [Pi.sub_apply, hA, hldG, hldF]
        ring
      have hslope : Tendsto (fun s => (g s - g q) / (s - q)) (𝓝[≠] q) (𝓝 (deriv g q)) := by
        have := hasDerivAt_iff_tendsto_slope.mp hga.differentiableAt.hasDerivAt
        simpa only [slope_fun_def_field] using this
      have hcont : Tendsto (fun s => g s * logDeriv G s) (𝓝[≠] q)
          (𝓝 (g q * logDeriv G q)) := by
        have : ContinuousAt (fun s => g s * logDeriv G s) q := by
          show ContinuousAt (fun s => g s * (deriv G s / G s)) q
          exact hga.continuousAt.mul (hGan.deriv.continuousAt.div hGan.continuousAt hG0)
        exact this.tendsto.mono_left nhdsWithin_le_nhds
      have hO : (fun s => g s * logDeriv G s - (m q : ℂ) * ((g s - g q) / (s - q)))
          =O[𝓝[≠] q] (1 : ℂ → ℂ) :=
        (hcont.sub (hslope.const_mul (m q : ℂ))).isBigO_one ℂ
      exact hO.congr' hexp EventuallyEq.rfl

/-- **Weighted argument principle on a rectangle.** For f, g analytic on a neighbourhood of every
point of the closed rectangle, f nonvanishing on its border, and Z the zero set of f in the
rectangle (as a Finset):  (1/2πi) ∮ g·(f'/f) = Σ_{ρ ∈ Z} ord_ρ(f)·g(ρ). -/
theorem rectangleIntegral'_mul_logDeriv {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (Z : Finset ℂ) (hZ : ∀ s ∈ Rectangle z w, f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  have h := rectangleIntegral'_mul_logDeriv_of_poles hre him Z ∅ (Finset.disjoint_empty_right _)
    (by simp) (by simpa using hf) hg hborder (by simpa using hZ) hZsub (fun _ => 0) (by simp)
  simpa using h

/-- **Weighted argument principle, self-contained form**: as `rectangleIntegral'_mul_logDeriv`, with
the finite zero set produced rather than supplied. -/
theorem rectangleIntegral'_mul_logDeriv' {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w)) (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ (finite_zeros_rectangle hf (rectangleBorder_subset_rectangle z w
          (show z ∈ RectangleBorder z w from Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))
          (hborder z (Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))).toFinset,
        (analyticOrderNatAt f ρ : ℂ) * g ρ := by
  classical
  set hfin := finite_zeros_rectangle hf (rectangleBorder_subset_rectangle z w
    (show z ∈ RectangleBorder z w from Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))
    (hborder z (Or.inl (Or.inl (Or.inl ⟨left_mem_uIcc, rfl⟩))))
  refine rectangleIntegral'_mul_logDeriv hre him hf hg hborder hfin.toFinset ?_ ?_
  · intro s hs
    simp [Set.Finite.mem_toFinset, hs]
  · intro s hs
    exact ((Set.Finite.mem_toFinset _).mp hs).1


end Analytic
end Zeta23
