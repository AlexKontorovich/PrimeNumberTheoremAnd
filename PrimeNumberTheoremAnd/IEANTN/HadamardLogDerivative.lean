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
noncomputable def hadamardGenusOneFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- Pairing the genus-one factors at opposite zeros cancels the exponential corrections. -/
theorem hadamardGenusOneFactor_pair_cancellation (α w : ℂ) (hα : α ≠ 0) :
    hadamardGenusOneFactor (w / α) * hadamardGenusOneFactor (w / (-α)) = 1 - w ^ 2 / α ^ 2 := by
  unfold hadamardGenusOneFactor
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
noncomputable def centeredHadamardOrbitBlock (w₀ α w : ℂ) : ℂ :=
  (α ^ 2 - w ^ 2) / (α ^ 2 - w₀ ^ 2)

theorem centeredHadamardOrbitBlock_base {w₀ α : ℂ} (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    centeredHadamardOrbitBlock w₀ α w₀ = 1 := by
  unfold centeredHadamardOrbitBlock
  field_simp [hden]

theorem centeredHadamardOrbitBlock_zero_pos {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α α = 0 := by
  unfold centeredHadamardOrbitBlock
  simp

theorem centeredHadamardOrbitBlock_zero_neg {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α (-α) = 0 := by
  unfold centeredHadamardOrbitBlock
  simp

theorem centeredHadamardOrbitBlock_ne_zero {w₀ α w : ℂ}
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    centeredHadamardOrbitBlock w₀ α w ≠ 0 := by
  unfold centeredHadamardOrbitBlock
  have hnum : α ^ 2 - w ^ 2 ≠ 0 := by
    intro h
    exact hw (sub_eq_zero.mp h).symm
  exact div_ne_zero hnum hden

/-- The normalized paired genus-one factors are exactly the centered quadratic orbit block. -/
theorem normalized_hadamardGenusOneFactor_pair_cancellation (α w₀ w : ℂ)
    (hα : α ≠ 0) (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    (hadamardGenusOneFactor (w / α) * hadamardGenusOneFactor (w / (-α))) /
        (hadamardGenusOneFactor (w₀ / α) * hadamardGenusOneFactor (w₀ / (-α))) =
      centeredHadamardOrbitBlock w₀ α w := by
  rw [hadamardGenusOneFactor_pair_cancellation α w hα, hadamardGenusOneFactor_pair_cancellation α w₀ hα]
  unfold centeredHadamardOrbitBlock
  field_simp [hα, hden]

theorem logDeriv_centeredHadamardOrbitBlock (w₀ α w : ℂ)
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => centeredHadamardOrbitBlock w₀ α z) w =
      2 * w / (w ^ 2 - α ^ 2) := by
  unfold centeredHadamardOrbitBlock
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
noncomputable def finiteCenteredHadamardOrbitProduct (w₀ : ℂ) (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∏ α ∈ A, centeredHadamardOrbitBlock w₀ α w

/-- Finite logarithmic-derivative contribution of centered zero-orbit blocks. -/
noncomputable def finiteCenteredHadamardOrbitLogDerivSum (A : Finset ℂ) (w : ℂ) : ℂ :=
  ∑ α ∈ A, 2 * w / (w ^ 2 - α ^ 2)

/-- The standard genus-one zero contribution in the Hadamard logarithmic derivative. -/
noncomputable def genusOneZeroLogTerm (ρ s : ℂ) : ℂ :=
  1 / ρ + 1 / (s - ρ)

/-- A standard Hadamard zero sum, indexed by a supplied zero enumeration. -/
noncomputable def genusOneZeroLogSum {ι : Type*} (zero : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, genusOneZeroLogTerm (zero i) s

/-- The centered zero-orbit contribution after writing `w = s - 1/2`. -/
noncomputable def centeredHadamardOrbitLogTerm (α s : ℂ) : ℂ :=
  let w := s - (1 / 2 : ℂ)
  2 * w / (w ^ 2 - α ^ 2)

/-- A centered zero-orbit Hadamard sum, indexed by a supplied orbit representative map. -/
noncomputable def centeredHadamardOrbitLogSum {ι : Type*} (orbit : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, centeredHadamardOrbitLogTerm (orbit i) s

/-- Finite Hadamard-orbit calculation before any infinite product limit is needed. -/
theorem logDeriv_finiteCenteredHadamardOrbitProduct (w₀ w : ℂ) (A : Finset ℂ)
    (hden : ∀ α ∈ A, α ^ 2 - w₀ ^ 2 ≠ 0)
    (hw : ∀ α ∈ A, w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => finiteCenteredHadamardOrbitProduct w₀ A z) w =
      finiteCenteredHadamardOrbitLogDerivSum A w := by
  classical
  unfold finiteCenteredHadamardOrbitProduct finiteCenteredHadamardOrbitLogDerivSum
  rw [logDeriv_prod]
  · exact Finset.sum_congr rfl fun α hα =>
      logDeriv_centeredHadamardOrbitBlock w₀ α w (hden α hα) (hw α hα)
  · exact fun α hα => centeredHadamardOrbitBlock_ne_zero (hden α hα) (hw α hα)
  · intro α hα
    unfold centeredHadamardOrbitBlock
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
    (hHad : logDeriv completedZetaFactor s = B + centeredHadamardOrbitLogSum orbit s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - centeredHadamardOrbitLogSum orbit s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_completed_hadamard_logDeriv s B (centeredHadamardOrbitLogSum orbit s)
    hs1 hΓdiff hΓ hζ hHad

end Kadiri
