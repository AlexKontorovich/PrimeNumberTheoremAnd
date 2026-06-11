import PrimeNumberTheoremAnd.IEANTN.KadiriContourShift
import PrimeNumberTheoremAnd.IEANTN.KadiriFunctionalEquation
import PrimeNumberTheoremAnd.IEANTN.KadiriGoodHeights

/-!
# Kadiri equation (16)-(18) assembly skeleton

This file records the local assembly shape for the repaired
`kadiri_thm_3_1_q1` statement.  The contour-pull theorem lives on the
separate lane at commit `56e3a7d` (`KadiriContourPull.lean:372-394`), while
the theorem statement receipt is commit `23a1510` (`Kadiri.lean:160-181`).

The proved endpoints below keep the algebra and real Kadiri pole-split
inversion local.  The line-to-series and functional-equation contour
identifications are named hypotheses until those lane files are merged.
-/

namespace Kadiri

open Complex MeasureTheory Filter Set Asymptotics
open ArithmeticFunction hiding log
open scoped Topology BigOperators

noncomputable section

/-- The Laplace transform notation used in the repaired Kadiri statement. -/
def u8Phi (φ : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ y in Set.Ioi (0 : ℝ), φ y * exp (-z * (y : ℂ)) ∂volume

/-- The von Mangoldt side of the repaired Kadiri statement. -/
def u8FormulaLHS (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)

/-- The zero sum appearing in the repaired Kadiri statement. -/
def u8ZeroesTerm (φ : ℝ → ℂ) : ℂ :=
  riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.univ : Set ℝ)
    fun ρ => u8Phi φ (-ρ)

/-- The `-φ(0) log π` contribution from the functional equation. -/
def u8PiLogTerm (φ : ℝ → ℂ) : ℂ :=
  -φ 0 * ((Real.log Real.pi : ℝ) : ℂ)

/-- The reflected von Mangoldt series from the functional equation. -/
def u8ReflectedVonMangoldtTerm (φ : ℝ → ℂ) : ℂ :=
  ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)

/-- The gamma-factor contour term, including the real-line `dt` Jacobian. -/
def u8GammaContourTerm (φ : ℝ → ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t : ℝ,
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
        u8Phi φ (-((1 / 2 : ℂ) + (t : ℂ) * I))

/-- The full right side of the repaired Kadiri statement. -/
def u8FormulaRHS (φ : ℝ → ℂ) : ℂ :=
  u8Phi φ (-1) + u8Phi φ 0 - u8ZeroesTerm φ + u8PiLogTerm φ +
    u8ReflectedVonMangoldtTerm φ + u8GammaContourTerm φ

/-- The contour integrand used by the residue theorem and contour pull. -/
def u8ContourIntegrand (Φ : ℂ → ℂ) (s : ℂ) : ℂ :=
  -logDeriv riemannZeta s * (-(Φ (-s)))

/-- Normalized vertical-line integral with the `1/(2πi)` factor. -/
def u8NormalizedVertical (Φ : ℂ → ℂ) (σ : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) • VerticalIntegral (u8ContourIntegrand Φ) σ

/-- The literal target shape of
`56e3a7d:KadiriContourPull.lean:391-394`. -/
def u8ContourPullSourceTarget (Φ : ℂ → ℂ) (σL σR : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ) * I)) •
    (VerticalIntegral (u8ContourIntegrand Φ) σR -
      VerticalIntegral (u8ContourIntegrand Φ) σL) +
    Φ (-1)

/-- The finite-window zero sum used before passing to full height. -/
def u8ZeroWindow (Φ : ℂ → ℂ) (σL σR : ℝ) (T : ℕ → ℝ) (k : ℕ) : ℂ :=
  riemannZeta.zeroes_sum (Set.uIcc σL σR) (Set.uIcc (-(T k)) (T k))
    fun ρ => Φ (-ρ)

/-- The contour-pull identity from the good-height lane, restated in local
notation.  Source shape: `56e3a7d:KadiriContourPull.lean:372-394`. -/
def U8ContourPullIdentity (Φ : ℂ → ℂ) (σL σR : ℝ) (T : ℕ → ℝ) : Prop :=
  Tendsto (u8ZeroWindow Φ σL σR T) atTop
    (𝓝 (u8ContourPullSourceTarget Φ σL σR))

/-- The full-height identification needed after the good-height contour pull. -/
def U8ZeroWindowLimit (Φ : ℂ → ℂ) (σL σR : ℝ) (T : ℕ → ℝ) : Prop :=
  Tendsto (u8ZeroWindow Φ σL σR T) atTop
    (𝓝 (riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.univ : Set ℝ)
      fun ρ => Φ (-ρ)))

/-- Right-line inversion target.  The real Kadiri pole-split wrapper below is
the local discharge for the corresponding Mellin inversion layer. -/
def U8RightLineInversionHypothesis (φ : ℝ → ℂ) (Φ : ℂ → ℂ) (σR : ℝ) : Prop :=
  u8NormalizedVertical Φ σR = u8Phi φ 0 - u8FormulaLHS φ

/-- Left-line functional-equation split target.  The sign convention is the
one needed after moving the left vertical integral across the contour identity. -/
def U8LeftLineFunctionalEquationSplitHypothesis
    (φ : ℝ → ℂ) (Φ : ℂ → ℂ) (σL : ℝ) : Prop :=
  u8NormalizedVertical Φ σL =
    -(u8PiLogTerm φ + u8ReflectedVonMangoldtTerm φ + u8GammaContourTerm φ)

/-- The literal contour-pull target is the vertical-line split used by the
equation (16)-(18) algebra. -/
theorem u8ContourPullSourceTarget_eq_vertical_split (Φ : ℂ → ℂ) (σL σR : ℝ) :
    u8ContourPullSourceTarget Φ σL σR =
      u8NormalizedVertical Φ σR - u8NormalizedVertical Φ σL + Φ (-1) := by
  unfold u8ContourPullSourceTarget u8NormalizedVertical
  ring

/-- The contour pull and zero-window limit identify the full zero sum with the
two vertical lines plus the pole at `1`. -/
theorem u8_zeroes_sum_eq_vertical_split_of_contour_pull {Φ : ℂ → ℂ}
    {σL σR : ℝ} {T : ℕ → ℝ}
    (hContour : U8ContourPullIdentity Φ σL σR T)
    (hZeroLimit : U8ZeroWindowLimit Φ σL σR T) :
    riemannZeta.zeroes_sum (Set.Ioo (0 : ℝ) 1) (Set.univ : Set ℝ)
        (fun ρ => Φ (-ρ)) =
      u8NormalizedVertical Φ σR - u8NormalizedVertical Φ σL + Φ (-1) :=
  (tendsto_nhds_unique hZeroLimit hContour).trans
    (u8ContourPullSourceTarget_eq_vertical_split Φ σL σR)

/-- The local real-Kadiri pole-split wrapper specialized to von Mangoldt
weights. -/
theorem u8_vonMangoldt_inversion_wrapper_available {d σ : ℝ}
    (hd : 0 < d) (hσ : 0 < σ) {f : ℝ → ℝ}
    (hf_C2 : ContDiffOn ℝ 2 f (Set.Icc 0 d))
    (hf_supp : tsupport f ⊆ Set.Ico 0 d)
    (hf_d : f d = 0)
    (hf_deriv_0 : derivWithin f (Set.Icc 0 d) 0 = 0)
    (hf_deriv_d : derivWithin f (Set.Icc 0 d) d = 0) :
    (∑' n : ℕ, (Λ n : ℂ) * kadiriPoleSplitMellinInv σ f n) =
      ∑' n : ℕ, (Λ n : ℂ) * (f (Real.log n) : ℂ) := by
  exact kadiriPoleSplit_mellinInv_weighted_log_sum_eq_of_laplaceDecay
    (d := d) (σ := σ) hd hσ (fun n : ℕ => (Λ n : ℂ)) (by simp) (by simp)
    hf_C2 hf_supp hf_d hf_deriv_0 hf_deriv_d

/-- Algebraic assembly from the contour pull, right-line inversion, and
left-line functional-equation split. -/
theorem u8_formula_assembly_of_named_hypotheses {φ : ℝ → ℂ} {σL σR : ℝ}
    {T : ℕ → ℝ}
    (hContour : U8ContourPullIdentity (u8Phi φ) σL σR T)
    (hZeroLimit : U8ZeroWindowLimit (u8Phi φ) σL σR T)
    (hRight : U8RightLineInversionHypothesis φ (u8Phi φ) σR)
    (hLeft : U8LeftLineFunctionalEquationSplitHypothesis φ (u8Phi φ) σL) :
    u8FormulaLHS φ = u8FormulaRHS φ := by
  have hZero :=
    u8_zeroes_sum_eq_vertical_split_of_contour_pull
      (Φ := u8Phi φ) hContour hZeroLimit
  dsimp [U8RightLineInversionHypothesis] at hRight
  dsimp [U8LeftLineFunctionalEquationSplitHypothesis] at hLeft
  rw [u8FormulaRHS, u8ZeroesTerm, hZero, hRight, hLeft]
  ring

/-- Statement-shape endpoint for the repaired Kadiri theorem.  The original
Kadiri analytic hypotheses are kept in the same surface as the repaired lane;
the three named U8 hypotheses mark the contour-pull and line-split inputs that
do not live on this branch yet. -/
theorem u8_kadiri_thm_3_1_q1_exact_statement_skeleton {φ : ℝ → ℂ}
    (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
      =O[cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1 / 2 + b) * |x|))
    (_hΦ_sum : Summable (fun ρ :
      riemannZeta.zeroes_rect (.Ioo 0 1) (.univ : Set ℝ) =>
        (∫ y in (.Ioi (0 : ℝ)), φ y * exp (ρ.val * (y : ℂ)) ∂volume) *
          (riemannZeta.order ρ.val : ℂ)))
    (_hΓ_int : Integrable (fun t : ℝ =>
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
        ∫ y in (.Ioi (0 : ℝ)),
          φ y * exp (((1 / 2 : ℂ) + (t : ℂ) * I) * (y : ℂ)) ∂volume))
    {σL σR : ℝ} {T : ℕ → ℝ}
    (hContour : U8ContourPullIdentity (u8Phi φ) σL σR T)
    (hZeroLimit : U8ZeroWindowLimit (u8Phi φ) σL σR T)
    (hRight : U8RightLineInversionHypothesis φ (u8Phi φ) σR)
    (hLeft : U8LeftLineFunctionalEquationSplitHypothesis φ (u8Phi φ) σL) :
    let Φ : ℂ → ℂ := fun z ↦ ∫ y in (.Ioi (0 : ℝ)), φ y * exp (-z * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      Φ (-1) + Φ 0
        - riemannZeta.zeroes_sum (.Ioo 0 1) (.univ : Set ℝ) (fun ρ ↦ Φ (-ρ))
        - φ 0 * ((Real.log Real.pi : ℝ) : ℂ)
        + ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)
        + (1 / (2 * (Real.pi : ℂ))) *
            ∫ t : ℝ,
              ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
                Φ (-((1 / 2 : ℂ) + (t : ℂ) * I)) := by
  have h := u8_formula_assembly_of_named_hypotheses hContour hZeroLimit hRight hLeft
  dsimp [u8FormulaLHS, u8FormulaRHS, u8Phi, u8ZeroesTerm, u8PiLogTerm,
    u8ReflectedVonMangoldtTerm, u8GammaContourTerm] at h ⊢
  rw [h]
  ring

end

end Kadiri
