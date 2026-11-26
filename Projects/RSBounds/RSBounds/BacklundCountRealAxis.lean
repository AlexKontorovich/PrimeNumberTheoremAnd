import RSBounds.BacklundCountDefinitions

/-!
# Xi is nonzero on the real axis

This generalizes calr's proof of nonvanishing at `1/2` using its checked
Euler--Maclaurin integral for `(s-1)ζ(s)`. No zero table is required.
-/

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.BacklundCountIdentity
open TernaryGoldbach.Explicit

theorem re_zetaF_real_ge {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ≤ (zetaF (x : ℂ)).re := by
  have hs : 0 < (x : ℂ).re := hx0
  rw [zetaF_eq hs]
  have hI : (Izeta (x : ℂ)).re ≤ 0 := by
    unfold Izeta
    have hint := integrableOn_saw_integrand hs
    rw [show (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re =
        RCLike.re (∫ t in Ioi (1 : ℝ), saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) from rfl,
      ← integral_re hint]
    refine setIntegral_nonpos measurableSet_Ioi fun t (ht : 1 < t) => ?_
    have he : (t : ℂ) ^ (-((x : ℂ) + 1)) = ((t ^ (-(x + 1)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (by linarith)]
      push_cast
      rfl
    rw [show RCLike.re (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))) =
        (saw t * (t : ℂ) ^ (-((x : ℂ) + 1))).re from rfl,
      he, saw, Complex.re_mul_ofReal]
    simp only [Complex.sub_re, Complex.ofReal_re]
    have hfloor : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (by linarith)
    have hp : 0 < t ^ (-(x + 1)) := Real.rpow_pos_of_pos (by linarith) _
    nlinarith
  simp only [add_re, mul_re, mul_im, ofReal_re, ofReal_im, sub_re, sub_im, one_re, one_im,
    sub_zero, sub_self, mul_zero, zero_mul, sub_zero, add_zero]
  have hc : x * (x - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hc hI]

theorem xiF_ne_zero_real (x : ℝ) : xiF (x : ℂ) ≠ 0 := by
  by_cases hx0 : x ≤ 0
  · exact xiF_ne_zero_of_re_nonpos hx0
  by_cases hx1 : 1 ≤ x
  · exact xiF_ne_zero_of_one_le_re hx1
  have hx0' : 0 < x := lt_of_not_ge hx0
  have hx1' : x < 1 := lt_of_not_ge hx1
  have hxne1 : (x : ℂ) ≠ 1 := by exact_mod_cast (ne_of_lt hx1')
  rw [xiF_eq hx0' hxne1]
  apply mul_ne_zero (mul_ne_zero (by exact_mod_cast hx0'.ne')
    (Gammaℝ_ne_zero_of_re_pos hx0'))
  intro hz
  have hh := re_zetaF_real_ge hx0' hx1'
  rw [hz] at hh
  simp only [zero_re] at hh
  linarith

theorem xiF_zero_re_strip {ρ : ℂ} (hρ : xiF ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  constructor
  · by_contra h
    exact xiF_ne_zero_of_re_nonpos (not_lt.mp h) hρ
  · by_contra h
    exact xiF_ne_zero_of_one_le_re (not_lt.mp h) hρ

theorem xiF_zero_im_ne_zero {ρ : ℂ} (hρ : xiF ρ = 0) : ρ.im ≠ 0 := by
  intro him
  have he : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [him]
  exact xiF_ne_zero_real ρ.re (he ▸ hρ)

theorem xiF_ne_zero_of_goodHeight {T : ℝ} (hg : zetaGoodHeight T)
    {s : ℂ} (hs : s.im = T) : xiF s ≠ 0 := by
  intro hz
  have hstrip := xiF_zero_re_strip hz
  exact hg s ((xiF_eq_zero_iff hstrip.1 hstrip.2).mp hz) hs

end TernaryGoldbach.RSBounds.BacklundCountIdentity
