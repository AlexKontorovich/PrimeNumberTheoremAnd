import PrimeNumberTheoremAnd.IEANTN.ZetaDefinitions
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaHadamard
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Hadamard logarithmic derivatives for Kadiri

This file records the algebraic identities relating the completed zeta factor and Riemann's
entire `ξ` to the logarithmic derivative `-ζ'/ζ` used in Kadiri's zero-free-region argument.
-/

namespace Kadiri

open scoped Topology

open Complex

/-- The genus-one elementary factor used in Hadamard products. -/
noncomputable def hadamardGenusOneFactor (z : ℂ) : ℂ :=
  (1 - z) * Complex.exp z

/-- Kadiri's genus-one factor is Mathlib's genus-one Weierstrass factor. -/
theorem hadamardGenusOneFactor_eq_weierstrassFactor_one (z : ℂ) :
    hadamardGenusOneFactor z = Complex.weierstrassFactor 1 z := by
  dsimp only [hadamardGenusOneFactor, Complex.weierstrassFactor]
  rw [Complex.partialLogSum_eq_sum]
  simp

/-- Pairing the genus-one factors at opposite zeros cancels the exponential corrections. -/
theorem hadamardGenusOneFactor_pair_cancellation (α w : ℂ) (hα : α ≠ 0) :
    hadamardGenusOneFactor (w / α) * hadamardGenusOneFactor (w / (-α)) = 1 - w ^ 2 / α ^ 2 := by
  dsimp only [hadamardGenusOneFactor]
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
  dsimp only [centeredHadamardOrbitBlock]
  field_simp [hden]

theorem centeredHadamardOrbitBlock_zero_pos {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α α = 0 := by
  dsimp only [centeredHadamardOrbitBlock]
  simp

theorem centeredHadamardOrbitBlock_zero_neg {w₀ α : ℂ} :
    centeredHadamardOrbitBlock w₀ α (-α) = 0 := by
  dsimp only [centeredHadamardOrbitBlock]
  simp

theorem centeredHadamardOrbitBlock_ne_zero {w₀ α w : ℂ}
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    centeredHadamardOrbitBlock w₀ α w ≠ 0 := by
  dsimp only [centeredHadamardOrbitBlock]
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
  dsimp only [centeredHadamardOrbitBlock]
  field_simp [hα, hden]

/-- The centered orbit block is the normalized pair of Mathlib genus-one Weierstrass factors. -/
theorem centeredHadamardOrbitBlock_eq_normalized_weierstrassFactor_pair
    (α w₀ w : ℂ) (hα : α ≠ 0) (hden : α ^ 2 - w₀ ^ 2 ≠ 0) :
    (Complex.weierstrassFactor 1 (w / α) * Complex.weierstrassFactor 1 (w / (-α))) /
        (Complex.weierstrassFactor 1 (w₀ / α) * Complex.weierstrassFactor 1 (w₀ / (-α))) =
      centeredHadamardOrbitBlock w₀ α w := by
  simpa [← hadamardGenusOneFactor_eq_weierstrassFactor_one] using
    normalized_hadamardGenusOneFactor_pair_cancellation α w₀ w hα hden

theorem logDeriv_centeredHadamardOrbitBlock (w₀ α w : ℂ)
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0) (hw : w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => centeredHadamardOrbitBlock w₀ α z) w =
      2 * w / (w ^ 2 - α ^ 2) := by
  dsimp only [centeredHadamardOrbitBlock]
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

/-- The genus-one zero term is the logarithmic derivative of the corresponding
Mathlib genus-one Weierstrass factor. -/
theorem logDeriv_hadamardGenusOneFactor_div (ρ s : ℂ) (hρ : ρ ≠ 0) (hs : s ≠ ρ) :
    logDeriv (fun w : ℂ => hadamardGenusOneFactor (w / ρ)) s =
      genusOneZeroLogTerm ρ s := by
  simpa [← hadamardGenusOneFactor_eq_weierstrassFactor_one, genusOneZeroLogTerm, add_comm]
    using Complex.logDeriv_weierstrassFactor_one_div (a := ρ) (z := s) hρ hs

/-- A standard Hadamard zero sum, indexed by a supplied zero enumeration. -/
noncomputable def genusOneZeroLogSum {ι : Type*} (zero : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, genusOneZeroLogTerm (zero i) s

/-- The centered zero-orbit contribution after writing `w = s - 1/2`. -/
noncomputable def centeredHadamardOrbitLogTerm (α s : ℂ) : ℂ :=
  let w := s - (1 / 2 : ℂ)
  2 * w / (w ^ 2 - α ^ 2)

/-- The centered orbit term is the logarithmic derivative of the shifted centered
quadratic block. -/
theorem logDeriv_shifted_centeredHadamardOrbitBlock (w₀ α s : ℂ)
    (hden : α ^ 2 - w₀ ^ 2 ≠ 0)
    (hs : (s - (1 / 2 : ℂ)) ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => centeredHadamardOrbitBlock w₀ α (z - (1 / 2 : ℂ))) s =
      centeredHadamardOrbitLogTerm α s := by
  let f : ℂ → ℂ := fun w => centeredHadamardOrbitBlock w₀ α w
  let g : ℂ → ℂ := fun z => z - (1 / 2 : ℂ)
  have hf : DifferentiableAt ℂ f (g s) := by
    dsimp only [f, centeredHadamardOrbitBlock]
    fun_prop
  have hg : DifferentiableAt ℂ g s := by
    dsimp only [g]
    fun_prop
  change logDeriv (f ∘ g) s = centeredHadamardOrbitLogTerm α s
  rw [logDeriv_comp hf hg]
  rw [logDeriv_centeredHadamardOrbitBlock w₀ α (g s) hden]
  · dsimp only [g, centeredHadamardOrbitLogTerm]
    simp
  · simpa [g] using hs

/-- A centered zero-orbit Hadamard sum, indexed by a supplied orbit representative map. -/
noncomputable def centeredHadamardOrbitLogSum {ι : Type*} (orbit : ι → ℂ) (s : ℂ) : ℂ :=
  ∑' i : ι, centeredHadamardOrbitLogTerm (orbit i) s

/-- Finite Hadamard-orbit calculation before any infinite product limit is needed. -/
theorem logDeriv_finiteCenteredHadamardOrbitProduct (w₀ w : ℂ) (A : Finset ℂ)
    (hden : ∀ α ∈ A, α ^ 2 - w₀ ^ 2 ≠ 0)
    (hw : ∀ α ∈ A, w ^ 2 ≠ α ^ 2) :
    logDeriv (fun z : ℂ => finiteCenteredHadamardOrbitProduct w₀ A z) w =
      finiteCenteredHadamardOrbitLogDerivSum A w := by
  dsimp only [finiteCenteredHadamardOrbitProduct, finiteCenteredHadamardOrbitLogDerivSum]
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

/-- The exponential form of Kadiri's archimedean factor is the usual complex power `π^{-s/2}`. -/
theorem zetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-s / 2) := by
  dsimp only [zetaPiFactor]
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos))]
  rw [Complex.ofReal_log Real.pi_pos.le]
  ring_nf

/-- The gamma factor in the Kadiri normalization of the completed zeta function. -/
noncomputable def zetaGammaFactor (s : ℂ) : ℂ :=
  Gamma (s / 2 + 1)

/-- Kadiri's gamma factor is `(s / 2) Γ(s / 2)` away from `s = 0`. -/
theorem zetaGammaFactor_eq_mul_Gamma_half {s : ℂ} (hs0 : s ≠ 0) :
    zetaGammaFactor s = (s / 2) * Gamma (s / 2) := by
  unfold zetaGammaFactor
  have h := Complex.Gamma_add_one (s / 2) (div_ne_zero hs0 (by norm_num : (2 : ℂ) ≠ 0))
  simpa [add_comm] using h

/-- The Kadiri normalization of the completed zeta factor:
`(s - 1) π^{-s/2} Γ(s/2+1) ζ(s)`. -/
noncomputable def completedZetaFactor (s : ℂ) : ℂ :=
  zetaPoleFactor s * zetaPiFactor s * zetaGammaFactor s * riemannZeta s

/-- Kadiri's completed zeta factor is `(s - 1) * (s / 2)` times Mathlib's completed zeta.

The factor `s / 2` appears because Kadiri uses `Γ(s / 2 + 1)` rather than `Γ(s / 2)`. -/
theorem completedZetaFactor_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedZetaFactor s = (s - 1) * (s / 2) * completedRiemannZeta s := by
  have hζΛ : riemannZeta s * Gammaℝ s = completedRiemannZeta s := by
    have hζ := riemannZeta_def_of_ne_zero (s := s) hs0
    have hζ_mul := congrArg (fun x => x * Gammaℝ s) hζ
    simpa [div_eq_mul_inv, mul_assoc, hΓ] using hζ_mul
  dsimp only [completedZetaFactor, zetaPoleFactor]
  rw [zetaPiFactor_eq_cpow, zetaGammaFactor_eq_mul_Gamma_half hs0]
  rw [Complex.Gammaℝ_def] at hζΛ
  rw [← hζΛ]
  ring

/-- Away from the poles of the raw factors, Kadiri's completed zeta factor is Riemann's entire
`ξ` function. The half-plane version below packages the hypotheses normally used in Kadiri's
argument. -/
theorem completedZetaFactor_eq_riemannXi {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΓ : Gammaℝ s ≠ 0) :
    completedZetaFactor s = riemannXi s := by
  rw [completedZetaFactor_eq_mul_completedRiemannZeta hs0 hΓ,
    riemannXi_eq_mul_completedRiemannZeta hs0 hs1]
  ring

/-- On the Kadiri half-plane `1 < re s`, the raw completed factor agrees with `riemannXi`. -/
theorem completedZetaFactor_eq_riemannXi_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedZetaFactor s = riemannXi s := by
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  have hs1 : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (zero_lt_one.trans hs)
  exact completedZetaFactor_eq_riemannXi hs0 hs1 hΓ

/-- On `1 < re s`, the logarithmic derivative of Kadiri's raw completed factor is the
logarithmic derivative of Riemann's entire `ξ` function. -/
theorem logDeriv_completedZetaFactor_eq_logDeriv_riemannXi_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv completedZetaFactor s = logDeriv riemannXi s := by
  have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : ∀ᶠ z in 𝓝 s, z ∈ {z : ℂ | 1 < z.re} := hopen.mem_nhds hs
  have heq : completedZetaFactor =ᶠ[𝓝 s] riemannXi :=
    hev.mono fun z hz => completedZetaFactor_eq_riemannXi_of_one_lt_re hz
  have hderiv : deriv completedZetaFactor s = deriv riemannXi s :=
    Filter.EventuallyEq.deriv_eq heq
  rw [logDeriv_apply, logDeriv_apply, hderiv, completedZetaFactor_eq_riemannXi_of_one_lt_re hs]

theorem logDeriv_zetaPoleFactor (s : ℂ) :
    logDeriv zetaPoleFactor s = 1 / (s - 1) := by
  unfold zetaPoleFactor
  rw [logDeriv_apply]
  simp [div_eq_mul_inv]

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

/-- Algebraic identity relating the completed zeta factor to `-ζ'/ζ`. -/
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

/-- Consequence of a Hadamard logarithmic-derivative formula for the completed zeta factor. -/
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

/-- Version using a Hadamard logarithmic-derivative formula for Riemann's entire `ξ`, whose
constant term is the derivative of the degree-one Hadamard polynomial. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_hadamard_logDeriv
    (s B Z : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hHad : logDeriv riemannXi s = B + Z) :
    -deriv riemannZeta s / riemannZeta s =
      -B - Z
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have hs1 : s ≠ 1 := by
    intro h
    norm_num [h] at hs
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv s hs1 hΓdiff hΓ hζ,
    logDeriv_completedZetaFactor_eq_logDeriv_riemannXi_of_one_lt_re hs, hHad]
  ring

/-- Version with the constant term expressed as the derivative of the degree-one Hadamard
polynomial for Riemann's entire `ξ`. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_polynomial_hadamard
    {P : Polynomial ℂ} (s : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hfac : ∀ w : ℂ, riemannXi w =
      Complex.exp (Polynomial.eval w P) *
        Complex.Hadamard.divisorCanonicalProduct 1 riemannXi (Set.univ : Set ℂ) w)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    -deriv riemannZeta s / riemannZeta s =
      -Polynomial.eval s P.derivative
      - ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
          (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
            1 / Complex.Hadamard.divisorZeroIndex₀_val p)
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  have hHad :=
    logDeriv_riemannXi_eq_polynomial_derivative_add_tsum
      (P := P) (z := s) hfac hz
  exact neg_zeta_logDeriv_eq_of_riemannXi_hadamard_logDeriv s
    (Polynomial.eval s P.derivative)
    (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    hs hΓdiff hΓ hHad

/-- Existential version of the xi-polynomial logarithmic-derivative identity. The constant in the
explicit formula is `Polynomial.eval s P.derivative` for a degree-one Hadamard polynomial of
`riemannXi`. -/
theorem exists_neg_zeta_logDeriv_eq_of_riemannXi_polynomial_hadamard
    (s : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hz : ∀ p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      s ≠ Complex.Hadamard.divisorZeroIndex₀_val p) :
    ∃ (P : Polynomial ℂ), P.degree ≤ 1 ∧
      -deriv riemannZeta s / riemannZeta s =
        -Polynomial.eval s P.derivative
        - ∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
            (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
              1 / Complex.Hadamard.divisorZeroIndex₀_val p)
        + 1 / (s - 1)
        - (1 / 2 : ℂ) * Real.log Real.pi
        + (1 / 2 : ℂ) * digamma (s / 2 + 1) := by
  rcases exists_riemannXi_logDeriv_eq_polynomial_derivative_add_tsum
    (z := s) hz with ⟨P, hdeg, hHad⟩
  refine ⟨P, hdeg, ?_⟩
  exact neg_zeta_logDeriv_eq_of_riemannXi_hadamard_logDeriv s
    (Polynomial.eval s P.derivative)
    (∑' p : Complex.Hadamard.divisorZeroIndex₀ riemannXi (Set.univ : Set ℂ),
      (1 / (s - Complex.Hadamard.divisorZeroIndex₀_val p) +
        1 / Complex.Hadamard.divisorZeroIndex₀_val p))
    hs hΓdiff hΓ hHad

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

/-- Genus-one form with the Hadamard formula stated for Riemann's entire `ξ`. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_genusOne_hadamard
    {ι : Type*} (zero : ι → ℂ) (s B : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hHad : logDeriv riemannXi s = B + genusOneZeroLogSum zero s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - genusOneZeroLogSum zero s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_riemannXi_hadamard_logDeriv s B (genusOneZeroLogSum zero s)
    hs hΓdiff hΓ hHad

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

/-- Centered-orbit form with the Hadamard formula stated for Riemann's entire `ξ`. -/
theorem neg_zeta_logDeriv_eq_of_riemannXi_centered_orbit_hadamard
    {ι : Type*} (orbit : ι → ℂ) (s B : ℂ)
    (hs : 1 < s.re)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓ : zetaGammaFactor s ≠ 0)
    (hHad : logDeriv riemannXi s = B + centeredHadamardOrbitLogSum orbit s) :
    -deriv riemannZeta s / riemannZeta s =
      -B - centeredHadamardOrbitLogSum orbit s
      + 1 / (s - 1)
      - (1 / 2 : ℂ) * Real.log Real.pi
      + (1 / 2 : ℂ) * digamma (s / 2 + 1) :=
  neg_zeta_logDeriv_eq_of_riemannXi_hadamard_logDeriv s B (centeredHadamardOrbitLogSum orbit s)
    hs hΓdiff hΓ hHad

end Kadiri
