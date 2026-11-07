import RSBounds.MertensSignedLimit
import RSBounds.MertensDFinite
import RSBounds.MertensCenteredNormalization
import RSBounds.MertensSecondSigned
import RSBounds.Targets

/-!
# The normalized first Mertens error

The difference `D(x)=E₁Λ(x)-ψ(x)/x` is exactly the finite centered psi integral
from one to x. Its limit therefore follows from the degree-two zero potential,
without inserting a pointwise PNT hypothesis. The separate Abel/Laurent
argument identifies the constant, and the final theorem has no normalization
or RH hypothesis.
-/

open Real Filter MeasureTheory
open scoped Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensDLimit

open TernaryGoldbach.PNTMertens MertensPsiAbel MertensSignedLimit

/-- The required limit exists unconditionally; its value is not assumed here. -/
theorem tendsto_D : Tendsto D atTop (𝓝 (signedLimit 1).re) := by
  apply (tendsto_signed_integral (a := 1) le_rfl).congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (D_eq_integral hx).symm

/-- A separate Abel/Laurent identification of the limit immediately yields the
exact all-x first-Mertens error formula. The displayed premise is not an axiom. -/
theorem first_error_eq_of_normalization
    (hC : (signedLimit 1).re = -Real.eulerMascheroniConstant - 1)
    {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x = (Chebyshev.psi x - x) / x - Real.eulerMascheroniConstant -
      (signedLimit x).re := by
  have hlim := (tendsto_signed_integral hx).const_add (D x)
  have hlimD : Tendsto D atTop (𝓝 (D x + (signedLimit x).re)) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop x] with b hb
    have h := D_sub_eq_integral hx hb
    linarith
  have h := tendsto_nhds_unique tendsto_D hlimD
  rw [hC, D] at h
  rw [sub_div, div_self (by linarith : x ≠ 0)]
  linarith

/-- Euler normalization is proved from the actual Abel transform, not assumed. -/
theorem signedLimit_one_re :
    (signedLimit 1).re = -Real.eulerMascheroniConstant - 1 :=
  MertensCenteredNormalization.centered_limit_eq tendsto_D

/-- The exact all-x formula, with the classical Euler normalization discharged. -/
theorem first_error_eq {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x = (Chebyshev.psi x - x) / x - Real.eulerMascheroniConstant -
      (signedLimit x).re :=
  first_error_eq_of_normalization signedLimit_one_re hx

/-- Identifies the elementary centered function used by the second-Mertens
identity with the actual improper signed tail. -/
theorem signedLimit_re_eq_centered {x : ℝ} (hx : 1 ≤ x) :
    (signedLimit x).re = -D x - Real.eulerMascheroniConstant - 1 := by
  have h := first_error_eq hx
  rw [sub_div, div_self (by linarith : x ≠ 0)] at h
  unfold D
  linarith

/-- The signed function in the checked second-Mertens identity is the
actual improper psi tail. -/
theorem J_eq_signedLimit {x : ℝ} (hx : 1 ≤ x) :
    MertensSecondSigned.J x = (signedLimit x).re := by
  simpa only [MertensSecondSigned.J] using (signedLimit_re_eq_centered hx).symm

theorem E1p_eq_primeWeightedSum (x : ℝ) :
    E₁p x = primeWeightedSum x - Real.log x := by
  have hs : (Finset.Icc 0 ⌊x⌋₊).filter Nat.Prime =
      (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨⟨hprime.pos, hp⟩, hprime⟩
    · rintro ⟨⟨_, hp⟩, hprime⟩
      exact ⟨⟨Nat.zero_le _, hp⟩, hprime⟩
  unfold primeWeightedSum
  rw [hs]

/-- Higher prime powers can only improve the prime-sum lower bound. This reuses
the existing unconditional comparison with the full convergent prime-power sum. -/
theorem primeWeightedSum_lower_signed {x : ℝ} (hx : 1 ≤ x) :
    Real.log x + Goals.mertensE + (Chebyshev.psi x - x) / x -
      (signedLimit x).re ≤ primeWeightedSum x := by
  have h := E₁Λ.le_E₁p_add_E₁ hx
  rw [first_error_eq hx, E1p_eq_primeWeightedSum] at h
  change Real.log x + (-Real.eulerMascheroniConstant - E₁) +
    (Chebyshev.psi x - x) / x - (signedLimit x).re ≤ primeWeightedSum x
  linarith

/-- Numerical endpoint and signed-tail estimates suffice directly for the
original RS62 prime-weighted lower bound. No theta/PNT proxy is required. -/
theorem mertens_lower_of_errors {x e j : ℝ} (hx : 1 < x)
    (hpsi : |Chebyshev.psi x - x| ≤ e * x)
    (hI : ‖signedLimit x‖ ≤ j) (hbudget : e + j < 1 / (2 * Real.log x)) :
    Real.log x + Goals.mertensE - 1 / (2 * Real.log x) < primeWeightedSum x := by
  have hx0 : 0 < x := by linarith
  have he : -e ≤ (Chebyshev.psi x - x) / x := by
    apply (le_div_iff₀ hx0).mpr
    linarith [(abs_le.mp hpsi).1]
  have hRe : (signedLimit x).re ≤ j := (Complex.re_le_norm _).trans hI
  have hl := primeWeightedSum_lower_signed hx.le
  linarith

end TernaryGoldbach.RSBounds.MertensDLimit
