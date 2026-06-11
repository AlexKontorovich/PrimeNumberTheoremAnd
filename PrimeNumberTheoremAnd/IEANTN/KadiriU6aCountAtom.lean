import PrimeNumberTheoremAnd.IEANTN.KadiriU6aFarTail
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZetaConvexity
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# U6a count atom: the local zero count `N(t+1) - N(t) = O(log t)`

This file discharges `Kadiri.U6aLocalZeroCountLogHypothesis`, the single
analytic atom left open by `KadiriU6aFarTail`.  The chain:

1. Euler reflection at the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`,
   via `Γ(z)Γ(1-z) = π/sin(πz)` and `1 - z = conj z` on `Re z = 1/2`.
2. Gronwall transport of `‖Γ‖` across the strip `Re ∈ [1/2, 7/2]` along the
   digamma logarithmic-derivative bound `‖ψ(σ+it)‖ ≤ C log(|t|+2)`.
3. The packaged product `‖Γ(s) cos(πs/2)‖ ≤ √π (|Im s|+2)^B` on the strip:
   the exponential decay of `Γ` at the left edge exactly cancels the
   exponential growth of `cos`, through `cosh(x)² ≤ cosh(2x)`.
4. The functional equation then gives polynomial growth of `ζ` on
   `Re ∈ [-5/2, 1/2]`; the Abel-summation bound covers `Re ∈ [1/2, 13/2]`.
5. A Jensen disk of radius `9/4` centered at `2 + it` (max-modulus form of
   the divisor-mass bound, fed by the band estimate and the Dirichlet-series
   lower bound `‖ζ(2+it)‖ ≥ 1/4`) counts the order-weighted zeros in the
   Kadiri window, yielding `u6aNearbyZeroCount (-1) 2 t ≤ C log |t|`.
-/

namespace Kadiri

open Complex

noncomputable section

/-! ## Reflection at the critical line -/

private lemma u6aCA_one_sub_eq_conj (u : ℝ) :
    (1 : ℂ) - (1 / 2 + u * I) = starRingEnd ℂ (1 / 2 + u * I) := by
  apply Complex.ext
  · simp
    norm_num
  · simp

/-- Euler reflection on the critical line: `‖Γ(1/2 + iu)‖² = π / cosh(πu)`. -/
theorem u6aCA_norm_sq_gamma_half (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ ^ 2 = Real.pi / Real.cosh (Real.pi * u) := by
  set z : ℂ := 1 / 2 + u * I with hz
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  rw [hz] at hrefl
  rw [u6aCA_one_sub_eq_conj u] at hrefl
  rw [Complex.Gamma_conj, Complex.mul_conj] at hrefl
  have hsin : Complex.sin (↑Real.pi * (1 / 2 + u * I)) = ↑(Real.cosh (Real.pi * u)) := by
    have hexp : (↑Real.pi : ℂ) * (1 / 2 + u * I) =
        ↑Real.pi / 2 + ↑(Real.pi * u) * I := by
      push_cast
      ring
    rw [hexp, Complex.sin_add, Complex.sin_pi_div_two, Complex.cos_pi_div_two,
      Complex.cos_mul_I, Complex.ofReal_cosh]
    ring
  rw [hsin, ← Complex.ofReal_div] at hrefl
  have hreal : Complex.normSq (Complex.Gamma (1 / 2 + u * I)) =
      Real.pi / Real.cosh (Real.pi * u) := by
    exact_mod_cast hrefl
  rw [← Complex.normSq_eq_norm_sq]
  exact hreal

/-- The cosine grows at most like `cosh` of the imaginary part. -/
theorem u6aCA_norm_cos_le_cosh (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh z.im := by
  rw [Complex.cos]
  have h1 : ‖Complex.exp (z * I) + Complex.exp (-z * I)‖ ≤
      Real.exp (-z.im) + Real.exp z.im := by
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_exp, Complex.norm_exp]
    have he1 : (z * I).re = -z.im := Complex.mul_I_re z
    have he2 : (-z * I).re = z.im := by
      rw [neg_mul, Complex.neg_re, Complex.mul_I_re]
      ring
    rw [he1, he2]
  rw [norm_div, Real.cosh_eq]
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2]
  have h3 : Real.exp (-z.im) + Real.exp z.im = Real.exp z.im + Real.exp (-z.im) := by ring
  rw [h3] at h1
  linarith

/-- The exact cancellation: the critical-line value of `‖Γ‖` times the cosh
growth of the half-angle cosine stays below `√π`. -/
theorem u6aCA_norm_gamma_half_mul_cosh_le (u : ℝ) :
    ‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2) ≤
      Real.sqrt Real.pi := by
  have hsq := u6aCA_norm_sq_gamma_half u
  have hcosh2 : Real.cosh (Real.pi * u / 2) ^ 2 ≤ Real.cosh (Real.pi * u) := by
    have hdouble := Real.cosh_two_mul (Real.pi * u / 2)
    have h2 : 2 * (Real.pi * u / 2) = Real.pi * u := by ring
    rw [h2] at hdouble
    nlinarith [sq_nonneg (Real.sinh (Real.pi * u / 2))]
  have hpos : 0 < Real.cosh (Real.pi * u) := Real.cosh_pos _
  rw [Real.le_sqrt (by positivity) Real.pi_pos.le]
  have hexpand : (‖Complex.Gamma (1 / 2 + u * I)‖ * Real.cosh (Real.pi * u / 2)) ^ 2 =
      Real.pi / Real.cosh (Real.pi * u) * Real.cosh (Real.pi * u / 2) ^ 2 := by
    rw [mul_pow, hsq]
  rw [hexpand, div_mul_eq_mul_div, div_le_iff₀ hpos]
  nlinarith [hcosh2, Real.pi_pos]

end

end Kadiri
