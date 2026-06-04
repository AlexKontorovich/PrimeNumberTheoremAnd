import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hadamard Log-Derivative Bridges for Kadiri

This file contains zeta-specific algebraic bridges from the completed zeta
factor to the logarithmic derivative `-ζ'/ζ` used in Kadiri's zero-free-region
argument.
-/

namespace Kadiri

open Complex

/-- The genus-one elementary factor used in Hadamard products. -/
noncomputable def genusOneFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- Pairing the genus-one factors at opposite zeros cancels the exponential corrections. -/
theorem genusOne_pair_cancellation (α w : ℂ) (hα : α ≠ 0) :
    genusOneFactor (w / α) * genusOneFactor (w / (-α)) = 1 - w ^ 2 / α ^ 2 := by
  unfold genusOneFactor
  have hsum : w / α + w / (-α) = 0 := by
    field_simp [hα]
    ring
  have hexp : Complex.exp (w / α) * Complex.exp (w / (-α)) = 1 := by
    rw [← Complex.exp_add, hsum, Complex.exp_zero]
  calc
    (1 - w / α) * Complex.exp (w / α) *
        ((1 - w / (-α)) * Complex.exp (w / (-α)))
        = ((1 - w / α) * (1 - w / (-α))) *
            (Complex.exp (w / α) * Complex.exp (w / (-α))) := by
          ring
    _ = 1 - w ^ 2 / α ^ 2 := by
      rw [hexp]
      field_simp [hα]
      ring

/-- The quadratic zero-orbit block normalized at a basepoint `w₀`. -/
noncomputable def centeredOrbitBlock (w₀ α w : ℂ) : ℂ :=
  (α ^ 2 - w ^ 2) / (α ^ 2 - w₀ ^ 2)

theorem centeredOrbitBlock_base {w₀ α : ℂ} (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    centeredOrbitBlock w₀ α w₀ = 1 := by
  unfold centeredOrbitBlock
  field_simp [hden]

theorem centeredOrbitBlock_zero_pos {w₀ α : ℂ} :
    centeredOrbitBlock w₀ α α = 0 := by
  unfold centeredOrbitBlock
  simp

theorem centeredOrbitBlock_zero_neg {w₀ α : ℂ} :
    centeredOrbitBlock w₀ α (-α) = 0 := by
  unfold centeredOrbitBlock
  simp

/-- The normalized paired genus-one factors are exactly the centered quadratic orbit block. -/
theorem normalized_genusOne_pair_cancellation (α w₀ w : ℂ)
    (hα : α ≠ 0) (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    (genusOneFactor (w / α) * genusOneFactor (w / (-α))) /
        (genusOneFactor (w₀ / α) * genusOneFactor (w₀ / (-α))) =
      centeredOrbitBlock w₀ α w := by
  rw [genusOne_pair_cancellation α w hα, genusOne_pair_cancellation α w₀ hα]
  unfold centeredOrbitBlock
  field_simp [hα, hden]

theorem logDeriv_centeredOrbitBlock (w₀ α w : ℂ)
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => centeredOrbitBlock w₀ α z) w =
      2 * w / (w ^ 2 - α ^ 2) := by
  unfold centeredOrbitBlock
  rw [logDeriv_apply]
  have hderiv :
      deriv (fun z : ℂ => (α ^ 2 - z ^ 2) / (α ^ 2 - w₀ ^ 2)) w =
        (-2 * w) / (α ^ 2 - w₀ ^ 2) := by
    simp
  rw [hderiv]
  have hden' : w ^ 2 - α ^ 2 ≠ 0 := sub_ne_zero.mpr hw
  have hden'' : α ^ 2 - w ^ 2 ≠ 0 := sub_ne_zero.mpr hw.symm
  field_simp [hden, hden', hden'']
  ring

/-- The pole factor in the completed zeta function. -/
noncomputable def zetaPoleFactor (s : ℂ) : ℂ :=
  s - 1

/-- The archimedean exponential factor `π^{-s/2}`, written as an exponential
to expose its logarithmic derivative directly. -/
noncomputable def zetaPiFactor (s : ℂ) : ℂ :=
  Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))

/-- The gamma factor in the Kadiri normalization of the completed zeta function. -/
noncomputable def zetaGammaFactor (s : ℂ) : ℂ :=
  Gamma (s / 2 + 1)

/-- The Kadiri normalization of the completed zeta factor:
`(s - 1) π^{-s/2} Γ(s/2+1) ζ(s)`. -/
noncomputable def completedZetaFactor (s : ℂ) : ℂ :=
  zetaPoleFactor s * zetaPiFactor s * zetaGammaFactor s * riemannZeta s

theorem logDeriv_zetaPoleFactor (s : ℂ) :
    logDeriv zetaPoleFactor s = 1 / (s - 1) := by
  unfold zetaPoleFactor
  rw [logDeriv_apply]
  simp

theorem logDeriv_zetaPiFactor (s : ℂ) :
    logDeriv zetaPiFactor s = -(1 / 2 : ℂ) * Real.log Real.pi := by
  unfold zetaPiFactor
  rw [show (fun s : ℂ => Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) =
      Complex.exp ∘ (fun s : ℂ => -(s / 2) * (Real.log Real.pi : ℂ)) by rfl]
  rw [logDeriv_comp]
  · simp
  · fun_prop
  · fun_prop

theorem logDeriv_zetaGammaFactor (s : ℂ)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    logDeriv zetaGammaFactor s = (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  unfold zetaGammaFactor
  rw [show (fun s : ℂ => Gamma (s / 2 + 1)) =
      Gamma ∘ (fun s : ℂ => s / 2 + 1) by rfl]
  rw [logDeriv_comp]
  · simp [digamma_def]
    ring
  · exact differentiableAt_Gamma _ hΓdiff
  · fun_prop

theorem logDeriv_completedZetaFactor (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    logDeriv completedZetaFactor s =
      1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1)
      + deriv riemannZeta s / riemannZeta s := by
  have hpole : zetaPoleFactor s ≠ 0 := by
    simp [zetaPoleFactor, sub_ne_zero, hs1]
  have hpi : zetaPiFactor s ≠ 0 := by
    simp [zetaPiFactor]
  have hpole_diff : DifferentiableAt ℂ zetaPoleFactor s := by
    unfold zetaPoleFactor
    fun_prop
  have hpi_diff : DifferentiableAt ℂ zetaPiFactor s := by
    unfold zetaPiFactor
    fun_prop
  have hgamma_diff : DifferentiableAt ℂ zetaGammaFactor s := by
    unfold zetaGammaFactor
    exact (differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop)
  have hzeta_diff : DifferentiableAt ℂ riemannZeta s :=
    differentiableAt_riemannZeta hs1
  unfold completedZetaFactor
  rw [logDeriv_mul]
  · rw [logDeriv_mul]
    · rw [logDeriv_mul]
      · rw [logDeriv_zetaPoleFactor, logDeriv_zetaPiFactor,
          logDeriv_zetaGammaFactor s hΓdiff, logDeriv_apply]
        ring
      · exact hpole
      · exact hpi
      · exact hpole_diff
      · exact hpi_diff
    · exact mul_ne_zero hpole hpi
    · exact hΓ
    · exact hpole_diff.mul hpi_diff
    · exact hgamma_diff
  · exact mul_ne_zero (mul_ne_zero hpole hpi) hΓ
  · exact hζ
  · exact (hpole_diff.mul hpi_diff).mul hgamma_diff
  · exact hzeta_diff

/-- Kadiri-facing algebraic bridge from the completed zeta factor to `-ζ'/ζ`. -/
theorem neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv
    (s : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0) :
    -deriv riemannZeta s / riemannZeta s =
      -logDeriv completedZetaFactor s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  rw [logDeriv_completedZetaFactor s hs1 hΓdiff hΓ hζ]
  ring

end Kadiri
