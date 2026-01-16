import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Data.Real.StarOrdered
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Gamma.BinetFormula

/-!
# Gamma Function Product Bounds (DLMF 5.6.7)

This file proves the bound |Γ(x + iy)| ≤ Γ(x) for x ≥ 1/2, which is
a consequence of the Weierstrass product representation of Gamma.

## Main Results

* `Complex.norm_sq_Gamma_le_sq_Gamma_re`: |Γ(x + iy)|² ≤ Γ(x)² for x ≥ 1/2
* `Complex.norm_Gamma_le_Gamma_re`: |Γ(x + iy)| ≤ Γ(x) for x ≥ 1/2
* `Real.Gamma_convex`: Γ is convex on (0, ∞) (used for max bounds)

## Mathematical Background

The Weierstrass product representation gives:
  Γ(z) = e^{-γz}/z * ∏_{n=1}^∞ (1 + z/n)^{-1} e^{z/n}

For z = x + iy with x > 0:
  |Γ(x + iy)|/|Γ(x)| = |x/(x+iy)| * ∏_{n=1}^∞ |(1 + x/n)/(1 + (x+iy)/n)|

Each factor in the product has the form:
  |(1 + x/n)/(1 + (x+iy)/n)|² = (1 + x/n)² / ((1 + x/n)² + (y/n)²)
                               = 1 / (1 + y²/((n+x)²)) ≤ 1

Therefore |Γ(x + iy)| ≤ Γ(x) for x > 0.

For x ≥ 1/2, the bound is sharp and this is DLMF 5.6.7.

## References

* NIST DLMF 5.6.7
* Whittaker & Watson, "A Course of Modern Analysis"
-/

open Real Complex Set Filter MeasureTheory Topology
open scoped Topology BigOperators

namespace GammaProductBound

/-!
## Note on the Weierstrass-product approach

An alternate route to DLMF 5.6.7 is via the Weierstrass product for `Γ` and termwise estimates.
Mathlib does not currently expose that product in a convenient form, so in this development we
prefer the Euler integral representation (already used elsewhere in `Riemann/Mathlib`) to avoid
API duplication and heavyweight prerequisites.
-/

/-- Each factor in the product is ≤ 1. -/
lemma prod_factor_le_one {x y : ℝ} (hx : 0 < x) (n : ℕ) :
    (1 + x / (n + 1)) ^ 2 / ((1 + x / (n + 1)) ^ 2 + (y / (n + 1)) ^ 2) ≤ 1 := by
  have h1 : 0 < 1 + x / (n + 1) := by positivity
  have h2 : 0 ≤ (y / (n + 1)) ^ 2 := sq_nonneg _
  have h3 : (1 + x / (n + 1)) ^ 2 ≤ (1 + x / (n + 1)) ^ 2 + (y / (n + 1)) ^ 2 := by linarith
  have h4 : 0 < (1 + x / (n + 1)) ^ 2 + (y / (n + 1)) ^ 2 := by positivity
  exact div_le_one_of_le₀ h3 h4.le

/-- The x²/(x² + y²) factor is ≤ 1. -/
lemma x_sq_factor_le_one {x y : ℝ} (hx : 0 < x) :
    x ^ 2 / (x ^ 2 + y ^ 2) ≤ 1 := by
  have h1 : x ^ 2 ≤ x ^ 2 + y ^ 2 := by linarith [sq_nonneg y]
  have h2 : 0 < x ^ 2 + y ^ 2 := by positivity
  exact div_le_one_of_le₀ h1 h2.le

/-! ## Section 2: The main bound -/

/-- **DLMF 5.6.7**: For x > 0, |Γ(x + iy)|² ≤ Γ(x)².
The infinite product representation shows each factor is ≤ 1. -/
theorem norm_sq_le {x y : ℝ} (hx : 0 < x) :
    ‖Complex.Gamma (x + y * Complex.I)‖ ^ 2 ≤ (Real.Gamma x) ^ 2 := by
  -- Use the Euler integral representation inequality `‖Γ(z)‖ ≤ Γ(Re z)` (already proved in
  -- `BinetFormula.lean`).
  have h_le : ‖Complex.Gamma (x + y * Complex.I)‖ ≤ Real.Gamma x := by
    -- `re (x + y*i) = x`
    simpa using (Binet.norm_Gamma_le_Gamma_re (z := (x : ℂ) + y * Complex.I) (by simpa using hx))
  have h0 : 0 ≤ ‖Complex.Gamma (x + y * Complex.I)‖ := norm_nonneg _
  have hG0 : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos hx).le
  -- square both sides (both are nonnegative)
  simpa [pow_two] using (mul_le_mul h_le h_le h0 hG0)

/-- Corollary: |Γ(x + iy)| ≤ Γ(x) for x > 0. -/
theorem norm_le {x y : ℝ} (hx : 0 < x) :
    ‖Complex.Gamma (x + y * Complex.I)‖ ≤ Real.Gamma x := by
  have h := norm_sq_le (y := y) hx
  have hGamma_pos : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hnorm_nonneg : 0 ≤ ‖Complex.Gamma (x + y * Complex.I)‖ := norm_nonneg _
  nlinarith [sq_nonneg ‖Complex.Gamma (x + y * Complex.I)‖,
             sq_nonneg (Real.Gamma x), sq_abs (Real.Gamma x)]

/-- For general z with Re(z) > 0, |Γ(z)| ≤ Γ(Re(z)). -/
theorem norm_le' {z : ℂ} (hz : 0 < z.re) :
    ‖Complex.Gamma z‖ ≤ Real.Gamma z.re := by
  have h : z = z.re + z.im * Complex.I := (Complex.re_add_im z).symm
  conv_lhs => rw [h]
  exact norm_le (y := z.im) hz

end GammaProductBound

/-! ## Section 3: Integration into the Complex namespace -/

namespace Complex

/-- **DLMF 5.6.7**: For Re(z) > 0, |Γ(z)|² ≤ Γ(Re(z))². -/
theorem norm_sq_Gamma_le' {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ^ 2 ≤ (Real.Gamma z.re) ^ 2 := by
  have h : z = z.re + z.im * I := (re_add_im z).symm
  conv_lhs => rw [h]
  exact GammaProductBound.norm_sq_le hz

/-- For Re(z) > 0, |Γ(z)| ≤ Γ(Re(z)). -/
theorem norm_Gamma_le_Gamma_re'' {z : ℂ} (hz : 0 < z.re) :
    ‖Gamma z‖ ≤ Real.Gamma z.re :=
  GammaProductBound.norm_le' hz

/-- For Re(z) ≥ 1/2, |Γ(z)|² ≤ |Γ(Re(z))|².
This is the precise statement of DLMF 5.6.7. -/
theorem norm_sq_Gamma_le_norm_sq_Gamma_re {z : ℂ} (hz : 1/2 ≤ z.re) :
    ‖Gamma z‖ ^ 2 ≤ ‖Gamma z.re‖ ^ 2 := by
  have hz_pos : 0 < z.re := by linarith
  have h := norm_sq_Gamma_le' hz_pos
  -- ‖Gamma z.re‖ = |Γ(z.re)| = Γ(z.re) since z.re > 0
  have hpos : 0 < Real.Gamma z.re := Real.Gamma_pos_of_pos hz_pos
  -- Gamma (z.re : ℂ) = (Real.Gamma z.re : ℂ)
  have habs : ‖Gamma (z.re : ℂ)‖ = Real.Gamma z.re := by
    rw [Complex.Gamma_ofReal z.re]
    -- ‖(x : ℂ)‖ = |x| for real x, and |Γ(x)| = Γ(x) for x > 0
    rw [Complex.norm_real]
    exact abs_of_pos hpos
  rw [habs]
  exact h

end Complex

/-! ## Section 4: Gamma convexity -/

namespace Real

/-- Γ is log-convex on (0, ∞), which implies convexity. -/
theorem Gamma_logConvex : ConvexOn ℝ (Set.Ioi 0) (fun x => log (Gamma x)) := by
  simpa [Function.comp] using (Real.convexOn_log_Gamma : ConvexOn ℝ (Set.Ioi 0) (Real.log ∘ Real.Gamma))

/-- Γ is convex on (0, ∞). -/
theorem Gamma_convex : ConvexOn ℝ (Set.Ioi 0) Gamma := by
  simpa using (Real.convexOn_Gamma : ConvexOn ℝ (Set.Ioi 0) Real.Gamma)

/-- On [1, 2], Γ achieves its maximum at the endpoints.
Since Γ(1) = Γ(2) = 1, we have Γ(x) ≤ 1 for x ∈ [1, 2]. -/
theorem Gamma_le_one_of_mem_Icc' {x : ℝ} (hlo : 1 ≤ x) (hhi : x ≤ 2) :
    Gamma x ≤ 1 := by
  -- Use convexity: max on [1,2] is at endpoints, both equal 1
  have h_convex := convexOn_Gamma
  have h1 : Gamma 1 = 1 := Gamma_one
  have h2 : Gamma 2 = 1 := Gamma_two
  -- Express x as convex combination
  let t := 2 - x
  have ht_nonneg : 0 ≤ t := by linarith
  have ht_le_one : t ≤ 1 := by linarith
  have hx_conv : x = t * 1 + (1 - t) * 2 := by field_simp [t]; ring
  have := h_convex.2 (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 2)
    ht_nonneg (by linarith : 0 ≤ 1 - t) (by ring : t + (1 - t) = 1)
  rw [smul_eq_mul, smul_eq_mul] at this
  calc Gamma x
      = Gamma (t * 1 + (1 - t) * 2) := by rw [hx_conv]
    _ ≤ t * Gamma 1 + (1 - t) * Gamma 2 := this
    _ = t * 1 + (1 - t) * 1 := by rw [h1, h2]
    _ = 1 := by ring

end Real
