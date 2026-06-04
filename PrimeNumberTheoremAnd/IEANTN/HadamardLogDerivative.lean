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

theorem centeredOrbitBlock_ne_zero {w₀ α w : ℂ}
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    centeredOrbitBlock w₀ α w ≠ 0 := by
  unfold centeredOrbitBlock
  have hnum : α ^ 2 - w ^ 2 ≠ 0 := by
    intro h
    exact hw (sub_eq_zero.mp h).symm
  exact div_ne_zero hnum hden

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

/-- Finite product of centered zero-orbit blocks. -/
noncomputable def finiteCenteredOrbitProduct (w₀ : ℂ) (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∏ α ∈ A, centeredOrbitBlock w₀ α w

/-- Finite logarithmic-derivative contribution of centered zero-orbit blocks. -/
noncomputable def finiteCenteredOrbitLogDerivSum (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∑ α ∈ A, 2 * w / (w ^ 2 - α ^ 2)

/-- The standard genus-one zero contribution in the Hadamard logarithmic derivative. -/
noncomputable def genusOneZeroLogTerm (ρ s : ℂ) : ℂ :=
  1 / ρ + 1 / (s - ρ)

/-- A standard Hadamard zero sum, indexed by a supplied zero enumeration. -/
noncomputable def genusOneZeroLogSum {ι : Type*} (zero : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, genusOneZeroLogTerm (zero i) s

/-- The centered zero-orbit contribution after writing `w = s - 1/2`. -/
noncomputable def centeredOrbitLogTerm (α s : ℂ) : ℂ :=
  let w := s - (1 / 2 : ℂ)
  2 * w / (w ^ 2 - α ^ 2)

/-- A centered zero-orbit Hadamard sum, indexed by a supplied orbit representative map. -/
noncomputable def centeredOrbitLogSum {ι : Type*} (orbit : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, centeredOrbitLogTerm (orbit i) s

/-- Finite Hadamard-orbit calculation before any infinite product limit is needed. -/
theorem logDeriv_finiteCenteredOrbitProduct (w₀ w : ℂ) (A : Finset ℂ)
    (hden : ∀ α ∈ A, α ^ 2 - w₀ ^ 2 ≠ 0)
    (hw : ∀ α ∈ A, w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => finiteCenteredOrbitProduct w₀ A z) w =
      finiteCenteredOrbitLogDerivSum A w := by
  classical
  unfold finiteCenteredOrbitProduct finiteCenteredOrbitLogDerivSum
  rw [logDeriv_prod]
  · exact Finset.sum_congr rfl fun α hα =>
      logDeriv_centeredOrbitBlock w₀ α w (hden α hα) (hw α hα)
  · exact fun α hα => centeredOrbitBlock_ne_zero (hden α hα) (hw α hα)
  · intro α hα
    unfold centeredOrbitBlock
    fun_prop

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

/-- Kadiri-facing bridge after a Hadamard log-derivative formula has been supplied. -/
theorem neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv
    (s B Z : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + Z) :
    -deriv riemannZeta s / riemannZeta s =
      -B - Z
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  rw [neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv s hs1 hΓdiff hΓ hζ, hHad]
  ring

/--
Assuming a Hadamard logarithmic-derivative formula for the completed zeta factor,
recover the classical explicit expression for `-ζ'/ζ` in terms of the Hadamard
zero sum.
-/
theorem neg_zeta_logDeriv_eq_of_genusOne_hadamard
    {ι : Type*} (zero : ι → ℂ) (s B : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + genusOneZeroLogSum zero s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - genusOneZeroLogSum zero s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s B (genusOneZeroLogSum zero s)
    hs1 hΓdiff hΓ hζ hHad

/--
Assuming a centered zero-orbit Hadamard logarithmic-derivative formula for the
completed zeta factor, recover the corresponding explicit expression for
`-ζ'/ζ`.
-/
theorem neg_zeta_logDeriv_eq_of_centered_orbit_hadamard
    {ι : Type*} (orbit : ι → ℂ) (s B : ℂ)
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hζ : riemannZeta s ≠ 0)
    (hHad : logDeriv completedZetaFactor s = B + centeredOrbitLogSum orbit s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - centeredOrbitLogSum orbit s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s B (centeredOrbitLogSum orbit s)
    hs1 hΓdiff hΓ hζ hHad

end Kadiri
