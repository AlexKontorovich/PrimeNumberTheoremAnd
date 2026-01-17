import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.Hadamard
import PrimeNumberTheoremAnd.Mathlib.Analysis.Complex.ZetaFiniteOrder
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Irrational

/-!
## Intrinsic Hadamard factorization for the completed Riemann zeta function

This is the zeta-facing theorem that lives on the `Riemann/Mathlib` side: it uses the intrinsic
divisor-indexed canonical product and the intrinsic Hadamard factorization theorem from
`Riemann/Mathlib/Analysis/Complex/Hadamard.lean`.

It is parameterized by an explicit growth bound, so analytic estimates (Stirling/convexity) can be
ported independently without pulling in the legacy `ZeroData` pipeline.
-/

noncomputable section

open Complex Set

namespace Riemann

open scoped BigOperators

theorem completedRiemannZeta₀_hadamard_factorization_intrinsic_of_growth
    (hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖completedRiemannZeta₀ z‖) ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ)) :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ 1 ∧
      ∀ z : ℂ,
        completedRiemannZeta₀ z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
            Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  have hρ : (0 : ℝ) ≤ (3 / 2 : ℝ) := by norm_num
  have hentire : Differentiable ℂ completedRiemannZeta₀ := differentiable_completedZeta₀
  have hfloor : (Nat.floor (3 / 2 : ℝ)) = 1 := by
    have h1 : (1 : ℝ) ≤ (3 / 2 : ℝ) := by norm_num
    have h2 : (3 / 2 : ℝ) < (1 : ℝ) + 1 := by norm_num
    exact (Nat.floor_eq_iff (a := (3 / 2 : ℝ)) (n := 1) hρ).2 ⟨by simpa using h1, by simpa using h2⟩

  -- Nontriviality witness: `Λ₀(2) = (π - 3) / 6`, and `π ≠ 3` by irrationality.
  have hnot : ∃ z : ℂ, completedRiemannZeta₀ z ≠ 0 := by
    refine ⟨(2 : ℂ), ?_⟩
    have hs : (1 : ℝ) < Complex.re (2 : ℂ) := by norm_num
    have hΛ2 : completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ) / 6 := by
      have hpi0 : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have htsum :
          completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * (∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹) := by
        simpa [Complex.cpow_neg_one] using
          (completedZeta_eq_tsum_of_one_lt_re (s := (2 : ℂ)) hs)
      have hzeta : riemannZeta (2 : ℂ) = ∑' n : ℕ, ((n : ℂ) ^ 2)⁻¹ := by
        simpa using (zeta_eq_tsum_one_div_nat_cpow (s := (2 : ℂ)) hs)
      have hζ2 : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6 := by
        simpa using (riemannZeta_two : riemannZeta (2 : ℂ) = (Real.pi : ℂ) ^ 2 / 6)
      have hΛ2' : completedRiemannZeta (2 : ℂ) = (Real.pi : ℂ)⁻¹ * riemannZeta (2 : ℂ) := by
        simpa [hzeta] using htsum
      calc
        completedRiemannZeta (2 : ℂ)
            = (Real.pi : ℂ)⁻¹ * ((Real.pi : ℂ) ^ 2 / 6) := by
                simpa [hζ2] using hΛ2'
        _ = (Real.pi : ℂ) / 6 := by
                field_simp [hpi0]
    have hΛ₀2 : completedRiemannZeta₀ (2 : ℂ) = ((Real.pi : ℂ) - 3) / 6 := by
      have h := completedRiemannZeta_eq (2 : ℂ)
      have h' :
          completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) =
            completedRiemannZeta₀ (2 : ℂ) := by
        have := congrArg (fun x => x + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ))) h
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using this
      have h'' :
          completedRiemannZeta₀ (2 : ℂ) =
            completedRiemannZeta (2 : ℂ) + (1 : ℂ) / 2 + (1 : ℂ) / (1 - (2 : ℂ)) := by
        simpa [add_assoc, add_left_comm, add_comm] using h'.symm
      have hden : (1 : ℂ) / (1 - (2 : ℂ)) = (-1 : ℂ) := by norm_num
      simpa [h'', hΛ2, hden] using (by ring :
        (Real.pi : ℂ) / 6 + (1 : ℂ) / 2 + (-1 : ℂ) = ((Real.pi : ℂ) - 3) / 6)
    have hpi_ne3 : (Real.pi : ℂ) ≠ (3 : ℂ) := by
      intro h'
      have hpi' : (Real.pi : ℝ) = (3 : ℝ) := by
        simpa using congrArg Complex.re h'
      have hirr : Irrational Real.pi := by simp
      exact (hirr.ne_nat 3) (by simp at hpi')
    have hnum : ((Real.pi : ℂ) - 3) ≠ 0 := sub_ne_zero.2 hpi_ne3
    have hden : (6 : ℂ) ≠ 0 := by norm_num
    have : ((Real.pi : ℂ) - 3) / 6 ≠ 0 := div_ne_zero hnum hden
    simpa [hΛ₀2] using this

  -- Invoke intrinsic Hadamard factorization with `ρ = 3/2`.
  rcases
      (Complex.Hadamard.hadamard_factorization_of_growth
        (f := completedRiemannZeta₀) (ρ := (3 / 2 : ℝ))
        hρ hentire hnot hgrowth) with
    ⟨P, hdeg, hfac⟩
  refine ⟨P, ?_, ?_⟩
  · simpa [hfloor] using hdeg
  · intro z
    simpa [hfloor] using hfac z

/-!
## Zeta specialization: intrinsic Hadamard factorization for `completedRiemannZeta₀`

The core theorem above is parameterized by a growth hypothesis.  The analytic work proving such
a bound lives in `ZetaFiniteOrder.lean`, and we instantiate it here to provide a ready-to-use
statement for the completed zeta function.
-/

theorem completedRiemannZeta₀_hadamard_factorization_intrinsic :
    ∃ (P : Polynomial ℂ),
      P.degree ≤ 1 ∧
      ∀ z : ℂ,
        completedRiemannZeta₀ z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
            Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  have hgrowth :
      ∃ C > 0, ∀ z : ℂ,
        Real.log (1 + ‖completedRiemannZeta₀ z‖) ≤ C * (1 + ‖z‖) ^ (3 / 2 : ℝ) := by
    simpa using Complex.completedRiemannZeta₀_growth
  simpa using completedRiemannZeta₀_hadamard_factorization_intrinsic_of_growth hgrowth

theorem completedRiemannZeta₀_hadamard_factorization_intrinsic_natDegree :
    ∃ (P : Polynomial ℂ),
      P.natDegree ≤ 1 ∧
      ∀ z : ℂ,
        completedRiemannZeta₀ z =
          Complex.exp (Polynomial.eval z P) *
            z ^ (analyticOrderNatAt completedRiemannZeta₀ 0) *
            Complex.Hadamard.divisorCanonicalProduct 1 completedRiemannZeta₀ (Set.univ : Set ℂ) z := by
  rcases completedRiemannZeta₀_hadamard_factorization_intrinsic with ⟨P, hdeg, hfac⟩
  exact ⟨P, Polynomial.natDegree_le_of_degree_le hdeg, hfac⟩

end Riemann
