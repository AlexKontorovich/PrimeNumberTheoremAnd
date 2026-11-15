import RSBounds.IEANTNDigamma
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# IEANTN input for the Zeta23 quantitative digamma estimate

These two identities adapt the already proved IEANTN Gauss series to the
indexing used by the independently developed Zeta23 estimate. No Zeta23
analytic hypothesis or theorem is assumed.
-/

open Complex

namespace TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries

lemma harmonic_cast_eq (N : ℕ) :
    ((harmonic N : ℚ) : ℝ) = ∑ m ∈ Finset.range N, (1 : ℝ) / ((m : ℝ) + 1) := by
  rw [harmonic]
  push_cast
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [one_div]

theorem hasSum_digamma_series {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (z + n + 1))
      (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) := by
  have hz' : 0 < (z + 1).re := by simp; linarith
  have hne := GammaSolution.ne_neg_natCast_of_mem hz
  have hne' := GammaSolution.ne_neg_natCast_of_mem hz'
  have hs := (GammaSolution.summable_gaussTerm hne').hasSum
  have he : (∑' k, GammaSolution.gaussTerm (z + 1) k) =
      Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z := by
    have h := GammaSolution.digamma_eq_gaussSum hz'
    rw [Complex.digamma_apply_add_one z hne, GammaSolution.gaussSum] at h
    simp only [one_div]
    linear_combination -h
  rw [he] at hs
  change HasSum (fun n : ℕ => ((n : ℂ) + 1)⁻¹ - ((n : ℂ) + (z + 1))⁻¹)
    (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z) at hs
  simpa only [GammaSolution.gaussTerm, one_div, add_assoc, add_comm,
    add_left_comm] using hs

end TernaryGoldbach.RSBounds.BacklundZeta23.DigammaSeries
