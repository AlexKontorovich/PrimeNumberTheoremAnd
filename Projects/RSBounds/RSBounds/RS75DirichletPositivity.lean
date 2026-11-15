import TernaryGoldbach.Explicit.ZeroFreeRegion
import RSBounds.RS75Polynomial

/-!
# Positivity for the RS75 difference of Dirichlet series

This uses the actual von Mangoldt Dirichlet series and the exact RS75
degree-four cosine polynomial. The difference of the two Dirichlet
weights is nonnegative when `σ ≤ σ₀` and `κ ≤ 1`. Absolute convergence
in both half-planes permits subtraction and the finite polynomial sum.

The series representation is reused from the pinned
`TernaryGoldbach.Explicit.hasSum_re_vM`; no RH or zero-count input is used.
Source for the polynomial method: Rosser--Schoenfeld (1975), pp. 249--250,
https://doi.org/10.1090/S0025-5718-1975-0457373-7.
-/

open Complex
open scoped ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.RS75DirichletPositivity

open TernaryGoldbach.Explicit RS75Polynomial

/-- The actual difference of the real von Mangoldt Dirichlet series. -/
noncomputable def D (σ σ₀ κ τ : ℝ) : ℝ :=
  (LSeries (fun n => (Λ n : ℂ)) ((σ : ℂ) + τ * I)).re -
    κ * (LSeries (fun n => (Λ n : ℂ)) ((σ₀ : ℂ) + τ * I)).re

/-- Common coefficient of the cosine in the difference of the two series. -/
noncomputable def differenceWeight (σ σ₀ κ : ℝ) (n : ℕ) : ℝ :=
  Λ n * (Real.exp (-σ * Real.log n) - κ * Real.exp (-σ₀ * Real.log n))

theorem differenceWeight_nonneg {σ σ₀ κ : ℝ} (hσσ₀ : σ ≤ σ₀) (hκ : κ ≤ 1)
    (n : ℕ) : 0 ≤ differenceWeight σ σ₀ κ n := by
  have hl := Real.log_natCast_nonneg n
  have he : Real.exp (-σ₀ * Real.log n) ≤ Real.exp (-σ * Real.log n) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hσσ₀) hl)
  have hk : κ * Real.exp (-σ₀ * Real.log n) ≤ Real.exp (-σ₀ * Real.log n) := by
    exact mul_le_of_le_one_left (Real.exp_pos _).le hκ
  exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (sub_nonneg.mpr (hk.trans he))

/-- Subtraction is performed on two convergent actual Dirichlet series. -/
theorem hasSum_difference {σ σ₀ : ℝ} (hσ : 1 < σ) (hσ₀ : 1 < σ₀)
    (κ τ : ℝ) :
    HasSum (fun n : ℕ => if n = 0 then 0 else
      differenceWeight σ σ₀ κ n * Real.cos (τ * Real.log n)) (D σ σ₀ κ τ) := by
  unfold D
  refine ((hasSum_re_vM hσ τ).sub ((hasSum_re_vM hσ₀ τ).mul_left κ)).congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, differenceWeight]
    ring

/-- The finite polynomial sum is the sum of the nonnegative weighted terms. -/
theorem hasSum_weighted_polynomial {σ σ₀ : ℝ} (hσ : 1 < σ) (hσ₀ : 1 < σ₀)
    (κ t : ℝ) :
    HasSum (fun n : ℕ => if n = 0 then 0 else
      differenceWeight σ σ₀ κ n * P (t * Real.log n))
      (∑ k ∈ Finset.range 5, coeff k * D σ σ₀ κ ((k : ℝ) * t)) := by
  have h : HasSum
      (fun n : ℕ => ∑ k ∈ Finset.range 5, coeff k *
        (if n = 0 then 0 else
          differenceWeight σ σ₀ κ n * Real.cos (((k : ℝ) * t) * Real.log n)))
      (∑ k ∈ Finset.range 5, coeff k * D σ σ₀ κ ((k : ℝ) * t)) :=
    hasSum_sum fun k _ => (hasSum_difference hσ hσ₀ κ ((k : ℝ) * t)).mul_left (coeff k)
  refine h.congr_fun ?_
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn, P_eq_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_assoc (k : ℝ) t (Real.log n)]
    ring

/-- RS75 positivity, with its exact coefficients and the Stechkin difference. -/
theorem weighted_D_nonneg {σ σ₀ κ : ℝ} (hσ : 1 < σ) (hσσ₀ : σ ≤ σ₀)
    (hκ : κ ∈ Set.Icc (0 : ℝ) 1) (t : ℝ) :
    0 ≤ ∑ k ∈ Finset.range 5, coeff k * D σ σ₀ κ ((k : ℝ) * t) := by
  refine (hasSum_weighted_polynomial hσ (hσ.trans_le hσσ₀) κ t).nonneg ?_
  intro n
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (differenceWeight_nonneg hσσ₀ hκ.2 n) (P_nonneg _)

/-- Identification with the usual real logarithmic-derivative difference. -/
theorem D_eq_logDeriv {σ σ₀ : ℝ} (hσ : 1 < σ) (hσ₀ : 1 < σ₀) (κ τ : ℝ) :
    D σ σ₀ κ τ =
      -(logDeriv riemannZeta ((σ : ℂ) + τ * I)).re +
        κ * (logDeriv riemannZeta ((σ₀ : ℂ) + τ * I)).re := by
  have hs : 1 < ((σ : ℂ) + τ * I).re := by simpa using hσ
  have hs₀ : 1 < ((σ₀ : ℂ) + τ * I).re := by simpa using hσ₀
  unfold D
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs₀]
  simp only [logDeriv_apply, neg_div, Complex.neg_re]
  ring

end TernaryGoldbach.RSBounds.RS75DirichletPositivity
