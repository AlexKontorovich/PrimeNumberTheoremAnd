import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Riemann.academic_framework.ZetaFunctionalEquation
import Riemann.academic_framework.Domain
import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
Completed Riemann ξ function (ext): we use mathlib's `completedRiemannZeta` and
expose minimal interface pieces needed by RS.
-/

noncomputable section

open Complex

namespace Complex

/-- Completed Riemann ξ (ext), defined as mathlib's completed zeta `Λ(s)`. -/
def riemannXi_ext (s : ℂ) : ℂ := completedRiemannZeta s

/-- Archimedean factor for the ext factorization `riemannXi_ext = G_ext · ζ`. -/
def G_ext (s : ℂ) : ℂ := Complex.Gammaℝ s

/-- Open right half-plane Ω = { s | Re s > 1/2 }. -/
private lemma isOpen_Ω : IsOpen RH.RS.Ω := by
  change IsOpen { s : ℂ | (1 / 2 : ℝ) < s.re }
  exact isOpen_lt continuous_const Complex.continuous_re

/-- Differentiability of `riemannXi_ext` away from `0` and `1`. -/
lemma differentiableAt_riemannXi_ext {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
  DifferentiableAt ℂ riemannXi_ext s := by
  simpa [riemannXi_ext] using differentiableAt_completedZeta (s := s) hs0 hs1

/-- Differentiability of `riemannXi_ext` on Ω \ {1}. -/
theorem riemannXi_ext_differentiable_on_RSΩ_minus_one :
  DifferentiableOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  intro z hz
  -- z ∈ Ω and z ≠ 1
  have hzΩ : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hz.1
  have hz0 : z ≠ 0 := by
    intro h0
    have : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hzΩ
    simp [h0, Complex.zero_re] at this
  have hz1 : z ≠ 1 := by simpa using hz.2
  exact (differentiableAt_riemannXi_ext (s := z) hz0 hz1).differentiableWithinAt

/-- Analyticity of `riemannXi_ext` on Ω \ {1}``, via open-set equivalence. -/
lemma riemannXi_ext_analytic_on_RSΩ_minus_one :
  AnalyticOn ℂ riemannXi_ext (RH.RS.Ω \ ({1} : Set ℂ)) := by
  have hOpen : IsOpen (RH.RS.Ω \ ({1} : Set ℂ)) :=
    (isOpen_Ω).sdiff isClosed_singleton
  -- use the equivalence on open sets
  have h :=
    (analyticOn_iff_differentiableOn (f := riemannXi_ext)
      (s := RH.RS.Ω \ ({1} : Set ℂ)) hOpen)
  exact h.mpr riemannXi_ext_differentiable_on_RSΩ_minus_one

-- symmetry lemmas are provided in CompletedXiSymmetry to avoid duplication

/-- On Ω, zeros of `riemannXi_ext` coincide with zeros of `riemannZeta`. -/
lemma xi_ext_zeros_eq_zeta_zeros_on_Ω :
  ∀ z ∈ RH.RS.Ω, riemannXi_ext z = 0 ↔ riemannZeta z = 0 := by
  intro z hzΩ
  -- From Ω: 1/2 < Re z
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hzΩ
  -- Hence Re z > 0 and Γℝ z ≠ 0
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  -- Also z ≠ 0, but only Γℝ z ≠ 0 is needed below
  have hζ : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z :=
    riemannZeta_def_of_ne_zero (s := z) (by
      intro h0
      have hnot : ¬ ((1 / 2 : ℝ) < 0) := by norm_num
      exact hnot (by simpa [h0, Complex.zero_re] using hhalf))
  constructor
  · intro hXi
    -- Λ z = 0 ⇒ ζ z = 0
    have hΛ0 : completedRiemannZeta z = 0 := by
      dsimp [riemannXi_ext] at hXi
      exact hXi
    -- Rewrite ζ and conclude explicitly
    calc
      riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z := hζ
      _ = completedRiemannZeta z * (Complex.Gammaℝ z)⁻¹ := by rw [div_eq_mul_inv]
      _ = 0 * (Complex.Gammaℝ z)⁻¹ := by rw [hΛ0]
      _ = 0 := by simp
  · intro hζ0
    -- ζ z = 0, and Γℝ z ≠ 0 ⇒ Λ z = 0
    have hdiv0 : completedRiemannZeta z / Complex.Gammaℝ z = 0 := by
      -- rewrite the ζ-definition into the equality
      have htmp := hζ0
      rw [hζ] at htmp
      exact htmp
    have hΛ0 : completedRiemannZeta z = 0 := by
      -- If Λ z ≠ 0 then division by nonzero Γ gives a nonzero value, contradiction
      by_contra hΛ
      have : completedRiemannZeta z / Complex.Gammaℝ z ≠ 0 :=
        div_ne_zero hΛ hΓnz
      exact this hdiv0
    -- Conclude ξ_ext z = 0
    dsimp [riemannXi_ext]
    exact hΛ0

/-- Nonvanishing of the Archimedean factor on Ω. -/
lemma G_ext_nonzero_on_Ω : ∀ z ∈ RH.RS.Ω, G_ext z ≠ 0 := by
  intro z hzΩ
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hzΩ
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  dsimp [G_ext]
  exact Complex.Gammaℝ_ne_zero_of_re_pos hpos

/-- Factorization of `riemannXi_ext` on Ω: `riemannXi_ext = G_ext · ζ`. -/
lemma xi_ext_factorization_on_Ω :
  ∀ z ∈ RH.RS.Ω, riemannXi_ext z = G_ext z * riemannZeta z := by
  intro z hzΩ
  have hhalf : (1 / 2 : ℝ) < z.re := by
    simpa [RH.RS.Ω, Set.mem_setOf_eq] using hzΩ
  have hpos : (0 : ℝ) < z.re := lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hhalf
  have hΓnz : Complex.Gammaℝ z ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hpos
  -- ζ definition away from 0 (which holds since Re z > 1/2 ⇒ z ≠ 0)
  have hζ : riemannZeta z = completedRiemannZeta z / Complex.Gammaℝ z := by
    -- supply `z ≠ 0` to the definition lemma
    refine riemannZeta_def_of_ne_zero (s := z) ?hne0
    intro h0
    have : (0 : ℝ) < z.re := hpos
    simp [h0, Complex.zero_re] at this
  -- Rearrange to the product form Λ = Γℝ · ζ
  have hprod : completedRiemannZeta z = Complex.Gammaℝ z * riemannZeta z := by
    -- from ζ = Λ / Γℝ, multiply both sides by Γℝ
    have : riemannZeta z * Complex.Gammaℝ z = completedRiemannZeta z := by
      calc
        riemannZeta z * Complex.Gammaℝ z
            = (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z := by
              simp [hζ]
        _ = completedRiemannZeta z := div_mul_cancel₀ _ hΓnz
    simpa [mul_comm] using this.symm
  -- Replace ξ with Λ and Γℝ with G_ext
  simpa [riemannXi_ext, G_ext] using hprod

/-- Measurability of the completed ξ extension on all of `ℂ`. -/
lemma measurable_riemannXi_ext : Measurable riemannXi_ext := by
  classical
  let S : Set ℂ := ({0, 1} : Set ℂ)
  let Scompl : Set ℂ := {z : ℂ | z ∉ S}
  have hFinite : S.Finite := by
    simp [S]
  have hRestr : Measurable (Scompl.restrict riemannXi_ext) := by
    have hCont : Continuous fun z : Scompl => riemannXi_ext z := by
      refine continuous_iff_continuousAt.mpr ?_
      intro z
      have hzNot : (z : ℂ) ∉ S := by
        have := z.property
        dsimp [Scompl] at this
        exact this
      have hzMem :
          (z : ℂ) ≠ 0 ∧ (z : ℂ) ≠ 1 := by
        simpa [S, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hzNot
      have hz0 : (z : ℂ) ≠ 0 := hzMem.1
      have hz1 : (z : ℂ) ≠ 1 := hzMem.2
      have hDiff : DifferentiableAt ℂ riemannXi_ext (z : ℂ) :=
        differentiableAt_riemannXi_ext (s := (z : ℂ)) hz0 hz1
      have hContAt : ContinuousAt riemannXi_ext (z : ℂ) := hDiff.continuousAt
      have hIncl :
          ContinuousAt (Subtype.val : Scompl → ℂ) z :=
        continuous_subtype_val.continuousAt
      exact hContAt.comp hIncl
    simpa using hCont.measurable
  have hCompl : Scompl = Sᶜ := by
    ext z; simp [Scompl, S]
  simpa [hCompl] using measurable_of_measurable_on_compl_finite S hFinite hRestr

lemma riemannXi_ext_continuous_on_compl01 :
  ContinuousOn riemannXi_ext (({0} : Set ℂ)ᶜ ∩ ({1} : Set ℂ)ᶜ) := by
  intro z hz
  have hz0 : z ≠ 0 := by
    have : z ∉ ({0} : Set ℂ) := hz.1
    simpa [Set.mem_singleton_iff] using this
  have hz1 : z ≠ 1 := by
    have : z ∉ ({1} : Set ℂ) := hz.2
    simpa [Set.mem_singleton_iff] using this
  exact ContinuousAt.continuousWithinAt
    (differentiableAt_riemannXi_ext (s := z) hz0 hz1).continuousAt

end Complex
