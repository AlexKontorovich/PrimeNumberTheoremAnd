/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in licenses/Gersh-LICENSE.

Adapted from gersh/ternary-goldbach-lean commit
27df23af6a712895f22204d0d81102baa74f0ebe:
BacklundEBound.lean, BacklundCompletedZetaConj.lean, and
ZetaInterlacingAssembly.lean. This selective port uses Mathlib's existing
completedRiemannZeta_conj and deriv_conj_conj, avoiding the external
count/convexity import closure. See docs/BacklundReflectionReuse.md.
-/
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

noncomputable section
open Complex Real
open scoped Topology

namespace TernaryGoldbach.RSBounds.BacklundReflection

theorem logDeriv_pi_cpow_neg_half (s : ℂ) :
    logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
    simpa using ((hasDerivAt_id s).neg.div_const 2)
  have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
    (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
  have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
    have := hg.comp s hf
    exact this
  have hval : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  rw [logDeriv_apply, hd.deriv, Complex.ofReal_log Real.pi_pos.le]
  field_simp

theorem im_logDeriv_pi_cpow_neg_half (s : ℂ) :
    (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s).im = 0 := by
  rw [logDeriv_pi_cpow_neg_half]
  simp

theorem logDeriv_completedZeta_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    logDeriv completedRiemannZeta (1 - s) = -logDeriv completedRiemannZeta s := by
  have hfe : completedRiemannZeta ∘ (fun z : ℂ => 1 - z) = completedRiemannZeta := by
    funext z; exact completedRiemannZeta_one_sub z
  have h1s0 : (1 : ℂ) - s ≠ 0 := fun h => hs1 (by linear_combination -h)
  have h1s1 : (1 : ℂ) - s ≠ 1 := fun h => hs0 (by linear_combination -h)
  have hf : DifferentiableAt ℂ completedRiemannZeta (1 - s) :=
    differentiableAt_completedZeta h1s0 h1s1
  have hg : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s := differentiableAt_id.const_sub 1
  have hderiv_g : deriv (fun z : ℂ => 1 - z) s = -1 :=
    ((hasDerivAt_id s).const_sub 1).deriv
  have hcomp := logDeriv_comp hf hg
  rw [hfe, hderiv_g] at hcomp
  -- hcomp : logDeriv Λ s = logDeriv Λ (1-s) * (-1)
  rw [hcomp]; ring

/-- Conjugation of the completed logarithmic derivative, reusing Mathlib's
completed-zeta conjugation theorem and derivative-of-conjugation rule. -/
theorem logDeriv_completedZeta_conj (s : ℂ) :
    logDeriv completedRiemannZeta (starRingEnd ℂ s)
      = starRingEnd ℂ (logDeriv completedRiemannZeta s) := by
  have hf : (starRingEnd ℂ ∘ completedRiemannZeta ∘ starRingEnd ℂ) =
      completedRiemannZeta := by
    funext w
    simp [Function.comp, completedRiemannZeta_conj]
  have hd := deriv_conj_conj (f := completedRiemannZeta)
  rw [hf] at hd
  have h2 : deriv completedRiemannZeta (starRingEnd ℂ s) =
      starRingEnd ℂ (deriv completedRiemannZeta s) := by
    rw [congrFun hd (starRingEnd ℂ s)]
    simp [Function.comp]
  rw [logDeriv_apply, logDeriv_apply, h2, completedRiemannZeta_conj, map_div₀]

theorem im_logDeriv_completedZeta_reflect (σ T : ℝ) (hT : T ≠ 0) :
    (logDeriv completedRiemannZeta ((1 - σ : ℝ) + T * Complex.I)).im
      = (logDeriv completedRiemannZeta ((σ : ℝ) + T * Complex.I)).im := by
  set s : ℂ := (σ : ℝ) + T * Complex.I with hs_def
  have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
  have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; rfl)
  have hs1 : s ≠ 1 := by
    intro h; apply hsim; rw [h]; simp
  -- (1−σ)+iT = 1 − conj s
  have hrewrite : ((1 - σ : ℝ) + T * Complex.I) = 1 - starRingEnd ℂ s := by
    rw [hs_def]; simp only [Complex.conj_ofReal, map_add, map_mul, Complex.conj_I]
    push_cast; ring
  rw [hrewrite]
  -- logDeriv Λ(1 − conj s) = −logDeriv Λ(conj s) = −conj(logDeriv Λ s)
  have hcs0 : starRingEnd ℂ s ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hs0
  have hcs1 : starRingEnd ℂ s ≠ 1 := by
    intro h; apply hs1
    have := congrArg (starRingEnd ℂ) h
    rwa [Complex.conj_conj, map_one] at this
  rw [logDeriv_completedZeta_one_sub hcs0 hcs1, logDeriv_completedZeta_conj s]
  -- Im(−conj z) = Im z
  simp [Complex.neg_im, Complex.conj_im]

theorem im_logDeriv_zeta_decomp {σ T : ℝ} (hT : T ≠ 0)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
      = (logDeriv completedRiemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            ((σ : ℂ) + T * Complex.I)).im := by
  set s : ℂ := (σ : ℂ) + T * Complex.I with hs_def
  have hsim : s.im ≠ 0 := by rw [hs_def]; simp [hT]
  have hs0 : s ≠ 0 := fun h => hsim (by rw [h]; exact Complex.zero_im)
  have hs1 : s ≠ 1 := fun h => hsim (by rw [h]; exact Complex.one_im)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  -- the half-point avoids the Γ-poles (its imaginary part is `T/2 ≠ 0`)
  have hhalf : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    apply hsim
    have him := congrArg Complex.im h
    simp only [Complex.div_ofNat_im, Complex.neg_im, Complex.natCast_im,
      neg_zero] at him
    linarith
  -- differentiability and nonvanishing of the three factors at `s`
  have hP_diff : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s := by
    have hf : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2 : ℂ) s := by
      simpa using ((hasDerivAt_id s).neg.div_const 2)
    have hg : HasDerivAt (fun y : ℂ => (Real.pi : ℂ) ^ y)
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ)) (-s / 2) :=
      (hasStrictDerivAt_const_cpow (Or.inl hπ)).hasDerivAt
    have hd : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2)) s := by
      have := hg.comp s hf
      exact this
    exact hd.differentiableAt
  have hG_diff : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have h1 : DifferentiableAt ℂ Complex.Gamma (s / 2) :=
      Complex.differentiableAt_Gamma _ hhalf
    have h2 : DifferentiableAt ℂ (fun z : ℂ => z / 2) s :=
      differentiableAt_id.div_const 2
    have := h1.comp s h2
    exact this
  have hP_ne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]
    exact Complex.exp_ne_zero _
  have hG_ne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hhalf
  have hΛ_ne : completedRiemannZeta s ≠ 0 := by
    intro h
    apply hζ
    rw [riemannZeta_def_of_ne_zero hs0, h, zero_div]
  have hΛ_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hPG_ne : (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) ≠ 0 :=
    mul_ne_zero hP_ne hG_ne
  have hPG_diff : DifferentiableAt ℂ
      (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) s :=
    hP_diff.mul hG_diff
  -- `ζ = Λ/(π^{−·/2}·Γ(·/2))` on the open set `{Im ≠ 0}` around `s`
  have hopen : IsOpen {z : ℂ | z.im ≠ 0} := isOpen_ne.preimage Complex.continuous_im
  have hEq : riemannZeta =ᶠ[nhds s]
      fun z => completedRiemannZeta z
        / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)) := by
    filter_upwards [hopen.mem_nhds hsim] with z hz
    have hz0 : z ≠ 0 := fun h => hz (by rw [h]; exact Complex.zero_im)
    rw [riemannZeta_def_of_ne_zero hz0, Complex.Gammaℝ_def]
  have hlog_eq : logDeriv riemannZeta s
      = logDeriv (fun z => completedRiemannZeta z
          / ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))) s := by
    rw [logDeriv_apply, logDeriv_apply, hEq.deriv_eq, hEq.self_of_nhds]
  have hdiv := logDeriv_div (f := completedRiemannZeta)
      (g := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))
      s hΛ_ne hPG_ne hΛ_diff hPG_diff
  have hmul := logDeriv_mul (f := fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      (g := fun z : ℂ => Complex.Gamma (z / 2))
      s hP_ne hG_ne hP_diff hG_diff
  change logDeriv (fun z => completedRiemannZeta z /
    ((Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2))) s = _ at hdiv
  change logDeriv (fun z => (Real.pi : ℂ) ^ (-z / 2) *
    Complex.Gamma (z / 2)) s = _ at hmul
  have hkey : logDeriv riemannZeta s
      = logDeriv completedRiemannZeta s
        - (logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s
            + logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s) := by
    rw [hlog_eq, hdiv, hmul]
  rw [hkey, Complex.sub_im, Complex.add_im, im_logDeriv_pi_cpow_neg_half s]
  ring

/-- The exact pointwise Backlund reflection identity. The completed-zeta
part cancels; only the difference of gamma logarithmic derivatives remains.
Nonvanishing is required only at the two evaluated points. -/
theorem im_logDeriv_zeta_reflect_diff {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
      = (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
        - (logDeriv (fun z : ℂ => Complex.Gamma (z / 2))
            ((σ : ℂ) + T * Complex.I)).im := by
  have h1 := im_logDeriv_zeta_decomp hT hζ
  have h2 := im_logDeriv_zeta_decomp hT hζ'
  have hrefl := im_logDeriv_completedZeta_reflect σ T hT
  linarith

/-- `logDeriv (fun s => Γ(s/2)) p = (1/2)·digamma(p/2)` for `Im p ≠ 0`. -/
lemma logDeriv_Gamma_half {p : ℂ} (hp : p.im ≠ 0) :
    logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) p
      = (1 / 2 : ℂ) * Complex.digamma (p / 2) := by
  have hp2ne : ∀ m : ℕ, (p / 2) ≠ -(m : ℂ) := by
    intro m heq
    apply hp
    have h2 : p = (2 : ℂ) * (p / 2) := by ring
    rw [heq] at h2
    rw [h2]; simp
  have hf : DifferentiableAt ℂ Complex.Gamma (p / 2) :=
    Complex.differentiableAt_Gamma _ hp2ne
  have hg : DifferentiableAt ℂ (fun s : ℂ => s / 2) p := by fun_prop
  have hcomp :
      logDeriv (Complex.Gamma ∘ (fun s : ℂ => s / 2)) p
        = logDeriv Complex.Gamma (p / 2) * deriv (fun s : ℂ => s / 2) p :=
    logDeriv_comp hf hg
  have hderiv2 : deriv (fun s : ℂ => s / 2) p = 1 / 2 := by
    rw [deriv_div_const]; simp
  have hcompeq : (Complex.Gamma ∘ (fun s : ℂ => s / 2)) = (fun s => Complex.Gamma (s / 2)) :=
    rfl
  rw [← hcompeq, hcomp, hderiv2, ← Complex.digamma_def]
  ring

/-- Pointwise reflection, expressed in the digamma function for quantitative
estimation of the remaining gamma-factor difference. -/
theorem im_logDeriv_zeta_reflect_digamma {T : ℝ} (hT : T ≠ 0) (σ : ℝ)
    (hζ : riemannZeta ((σ : ℂ) + T * Complex.I) ≠ 0)
    (hζ' : riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I) ≠ 0) :
    (logDeriv riemannZeta ((σ : ℂ) + T * Complex.I)).im
        - (logDeriv riemannZeta (((1 - σ : ℝ) : ℂ) + T * Complex.I)).im
      = (1 / 2 : ℝ) *
        (Complex.digamma ((((1 - σ : ℝ) : ℂ) + T * Complex.I) / 2)
          - Complex.digamma (((σ : ℂ) + T * Complex.I) / 2)).im := by
  rw [im_logDeriv_zeta_reflect_diff hT σ hζ hζ',
    logDeriv_Gamma_half (by simpa using hT),
    logDeriv_Gamma_half (by simpa using hT)]
  simp only [Complex.mul_im, Complex.div_ofNat_re, Complex.one_re,
    Complex.div_ofNat_im, Complex.one_im, Complex.sub_im]
  ring

end TernaryGoldbach.RSBounds.BacklundReflection
