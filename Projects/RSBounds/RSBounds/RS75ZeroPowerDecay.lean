import RSBounds.RS75ZeroFree1975
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Decay of an individual high-zero contribution

The proved RS75 zero-free region is used only above height 1894439, where
it is unconditional. Its constant is weakened to 10. Combining the loss
in `x^(beta-1)` with two powers of the ordinate leaves a reciprocal cube
and the decaying factor `exp(-(8/9)*sqrt(log x))`.

The elementary square identity in `amgm_log_exponent` supplies the entire
optimization; no zero-density or PNT estimate is assumed.
-/

namespace TernaryGoldbach.RSBounds.RS75ZeroPowerDecay

open TernaryGoldbach.Explicit

noncomputable def decay (x : ℝ) : ℝ :=
  Real.exp (-(8 / 9 : ℝ) * Real.sqrt (Real.log x))

theorem decay_pos (x : ℝ) : 0 < decay x := Real.exp_pos _

theorem log_height_pos {γ : ℝ} (hγ : 1894439 ≤ γ) : 0 < Real.log (γ / 17) := by
  apply Real.log_pos
  apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 17)).mpr
  linarith

/-- A rational AM--GM bound, proved directly by a nonnegative square. -/
theorem amgm_log_exponent {L u : ℝ} (hL : 0 ≤ L) (hu : 0 < u) :
    (8 / 9 : ℝ) * Real.sqrt L ≤ L / (10 * u) + 2 * u := by
  have hsq := Real.sq_sqrt hL
  have hsquare := sq_nonneg (9 * Real.sqrt L - 40 * u)
  have hu2 := sq_nonneg u
  have he : L / (10 * u) + 2 * u = (L + 20 * u ^ 2) / (10 * u) := by
    field_simp [hu.ne']
    <;> ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 10 * u)).mpr
  nlinarith

/-- The actual unconditional RS75 region implies the weaker constant 10. -/
theorem zero_re_le_ten {ρ : ℂ} (hρ : xiF ρ = 0) (hA : 1894439 ≤ |ρ.im|) :
    ρ.re ≤ 1 - 1 / (10 * Real.log (|ρ.im| / 17)) := by
  have hz := RS75ZeroFree1975.xi_zero_re_lt hρ hA
  have hu := log_height_pos hA
  have hden : (0 : ℝ) < 9.645908801 * Real.log (|ρ.im| / 17) := by positivity
  have hm : 9.645908801 * Real.log (|ρ.im| / 17) ≤
      10 * Real.log (|ρ.im| / 17) :=
    mul_le_mul_of_nonneg_right (by norm_num) hu.le
  have hd := one_div_le_one_div_of_le hden hm
  linarith

/-- Two powers of the ordinate absorb the exponential loss from the region. -/
theorem exp_over_fifth_le {L γ : ℝ} (hL : 0 ≤ L) (hγ : 1894439 ≤ γ) :
    Real.exp (-L / (10 * Real.log (γ / 17))) / γ ^ 5 ≤
      Real.exp (-(8 / 9 : ℝ) * Real.sqrt L) / (289 * γ ^ 3) := by
  have hγ0 : 0 < γ := by linarith
  have hu := log_height_pos hγ
  have ha := amgm_log_exponent hL hu
  have he := Real.exp_le_exp.mpr (show
      -L / (10 * Real.log (γ / 17)) - 2 * Real.log (γ / 17) ≤
        -(8 / 9 : ℝ) * Real.sqrt L by
      rw [neg_div]
      linarith)
  have hden : Real.exp (2 * Real.log (γ / 17)) = γ ^ 2 / 289 := by
    rw [show 2 * Real.log (γ / 17) = Real.log (γ / 17) + Real.log (γ / 17) by ring,
      Real.exp_add, Real.exp_log (by positivity : 0 < γ / 17)]
    ring
  rw [Real.exp_sub, hden] at he
  have hb := (div_le_iff₀ (by positivity : 0 < γ ^ 2 / (289 : ℝ))).mp he
  calc
    _ ≤ (Real.exp (-(8 / 9 : ℝ) * Real.sqrt L) * (γ ^ 2 / 289)) / γ ^ 5 :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = _ := by field_simp [hγ0.ne'] <;> ring

/-- A generic real-power version, independent of the zero-set representation. -/
theorem rpow_over_fifth_le {x γ β : ℝ} (hx : 1 ≤ x) (hγ : 1894439 ≤ γ)
    (hβ : β ≤ 1 - 1 / (10 * Real.log (γ / 17))) :
    x ^ β / γ ^ 5 ≤ x * decay x / (289 * γ ^ 3) := by
  have hx0 : 0 < x := by linarith
  have hL := Real.log_nonneg hx
  have hβL : Real.log x * β ≤ Real.log x - Real.log x / (10 * Real.log (γ / 17)) := by
    have h := mul_le_mul_of_nonneg_left hβ hL
    convert h using 1 <;> ring
  have hp : x ^ β ≤ x * Real.exp (-Real.log x / (10 * Real.log (γ / 17))) := by
    rw [Real.rpow_def_of_pos hx0]
    calc
      _ ≤ Real.exp (Real.log x - Real.log x / (10 * Real.log (γ / 17))) :=
        Real.exp_le_exp.mpr hβL
      _ = _ := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hx0]
        congr 1
        ring
  have hdec := exp_over_fifth_le hL hγ
  calc
    _ ≤ (x * Real.exp (-Real.log x / (10 * Real.log (γ / 17)))) / γ ^ 5 :=
      div_le_div_of_nonneg_right hp (pow_nonneg (by linarith : 0 ≤ γ) 5)
    _ = x * (Real.exp (-Real.log x / (10 * Real.log (γ / 17))) / γ ^ 5) := by ring
    _ ≤ x * (Real.exp (-(8 / 9 : ℝ) * Real.sqrt (Real.log x)) / (289 * γ ^ 3)) :=
      mul_le_mul_of_nonneg_left hdec hx0.le
    _ = _ := by unfold decay; ring

/-- Each actual high xi zero satisfies the decaying reciprocal-cube bound. -/
theorem zero_power_weight_le {x : ℝ} (hx : 1 ≤ x) {ρ : ℂ}
    (hρ : xiF ρ = 0) (hA : 1894439 ≤ |ρ.im|) :
    x ^ ρ.re / |ρ.im| ^ 5 ≤ x * decay x / (289 * |ρ.im| ^ 3) :=
  rpow_over_fifth_le hx hA (zero_re_le_ten hρ hA)

end TernaryGoldbach.RSBounds.RS75ZeroPowerDecay
