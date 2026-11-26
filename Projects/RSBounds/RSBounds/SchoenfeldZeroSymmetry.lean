import RSBounds.PolynomialZeroPairing
import RSBounds.RS75ZeroPowerDecay

/-!
# The half-count improvement in Schoenfeld's Theorem 11

Reflection in the critical line is averaged before converting ordinate-only
sums to positive ordinates. This preserves the coefficient of the high-zero
term: no extra factor two is introduced by conjugation.
-/

open Complex Finset Real
open scoped ComplexConjugate

namespace TernaryGoldbach.RSBounds.SchoenfeldZeroSymmetry

open TernaryGoldbach.Explicit BacklundCountIdentity PolynomialZeroCountBridge
open PolynomialZeroPairing RS75ZeroFree1975

/-- Reindexing by reflection, preserving the entire actual finite zero set. -/
theorem sum_reflect {T : ℝ} (hT : 0 < T) (f : ℂ → ℝ) :
    (∑ ρ ∈ zerosRectD zetaF T, f (1 - conj ρ)) =
      ∑ ρ ∈ zerosRectD zetaF T, f ρ := by
  classical
  apply Finset.sum_bij (fun ρ _ => 1 - conj ρ)
  · exact fun ρ hρ => reflect_mem_zerosRectD hT hρ
  · intro ρ _ σ _ he
    simpa using congrArg (fun z : ℂ => 1 - conj z) he
  · intro ρ hρ
    exact ⟨1 - conj ρ, reflect_mem_zerosRectD hT hρ, by simp⟩
  · intro ρ _
    rfl

/-- Pair bounds turn into a full low allowance and only one positive-count high allowance. -/
theorem sum_le_low_and_high {T : ℝ} (hT : 0 < T) (f : ℂ → ℝ) (L H : ℝ → ℝ)
    (hpair : ∀ ρ ∈ zerosRectD zetaF T,
      f ρ + f (1 - conj ρ) ≤
        2 * (multRectD zetaF T ρ : ℝ) * L |ρ.im| +
          (multRectD zetaF T ρ : ℝ) * H |ρ.im|) :
    (∑ ρ ∈ zerosRectD zetaF T, f ρ) ≤
      (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * L |ρ.im|) +
        ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * H ρ.im := by
  have hh := Finset.sum_le_sum hpair
  rw [Finset.sum_add_distrib, sum_reflect hT] at hh
  have hr : (∑ ρ ∈ zerosRectD zetaF T,
      (2 * (multRectD zetaF T ρ : ℝ) * L |ρ.im| +
        (multRectD zetaF T ρ : ℝ) * H |ρ.im|)) =
      2 * (∑ ρ ∈ zerosRectD zetaF T, (multRectD zetaF T ρ : ℝ) * L |ρ.im|) +
        2 * ∑ ρ ∈ positiveZeros T, (multRectD zetaF T ρ : ℝ) * H ρ.im := by
    rw [Finset.sum_add_distrib]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, sum_ordinate_weight_eq_two hT H]
  rw [hr] at hh
  linarith

/-- In each reflected pair, one exponent is at most one half. -/
theorem rpow_pair_le_sqrt_add {x β α : ℝ} (hx : 1 ≤ x)
    (hβ : β ≤ α) (hβ' : 1 - β ≤ α) :
    x ^ β + x ^ (1 - β) ≤ Real.sqrt x + x ^ α := by
  by_cases hh : β ≤ 1 / 2
  · have h1 := Real.rpow_le_rpow_of_exponent_le hx hh
    have h2 := Real.rpow_le_rpow_of_exponent_le hx hβ'
    rw [← Real.sqrt_eq_rpow] at h1
    exact add_le_add h1 h2
  · have h1 := Real.rpow_le_rpow_of_exponent_le hx hβ
    have h2 := Real.rpow_le_rpow_of_exponent_le hx (show 1 - β ≤ 1 / 2 by linarith)
    rw [← Real.sqrt_eq_rpow] at h2
    linarith

/-- The RS75 boundary, converted exactly to the exponential height weight. -/
theorem rpow_boundary_eq {x γ : ℝ} (hx : 0 < x) (hγ : 1894439 ≤ γ) :
    x ^ (1 - 1 / (9.645908801 * Real.log (γ / 17))) =
      x * Real.exp (-(Real.log x / 9.645908801) / Real.log (γ / 17)) := by
  have hu := RS75ZeroPowerDecay.log_height_pos hγ
  rw [Real.rpow_def_of_pos hx]
  calc
    _ = Real.exp (Real.log x + (-(Real.log x / 9.645908801) / Real.log (γ / 17))) := by
      congr 1
      field_simp [hu.ne']
      <;> ring
    _ = _ := by rw [Real.exp_add, Real.exp_log hx]

/-- Exact high-zero reflection estimate; no RH premise occurs. -/
theorem zero_pair_power_le {T x : ℝ} (hT : 0 < T) (hx : 1 ≤ x)
    {ρ : ℂ} (hρ : ρ ∈ zerosRectD zetaF T) (hA : 1894439 ≤ |ρ.im|) :
    x ^ ρ.re + x ^ (1 - ρ.re) ≤ Real.sqrt x +
      x * Real.exp (-(Real.log x / 9.645908801) / Real.log (|ρ.im| / 17)) := by
  have hz := (mem_zerosRectD_zetaF_iff_xi hT).mp hρ
  have hb := (xi_zero_re_lt hz.1 hA).le
  have hρ' := reflect_mem_zerosRectD hT hρ
  have hz' := (mem_zerosRectD_zetaF_iff_xi hT).mp hρ'
  have hb' := (xi_zero_re_lt hz'.1 (by simpa using hA)).le
  have hb'' : 1 - ρ.re ≤ 1 - 1 / (9.645908801 * Real.log (|ρ.im| / 17)) := by
    simpa using hb'
  have hp := rpow_pair_le_sqrt_add hx hb hb''
  rw [rpow_boundary_eq (by linarith : 0 < x) hA] at hp
  exact hp

end TernaryGoldbach.RSBounds.SchoenfeldZeroSymmetry
