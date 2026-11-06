import RSBounds.PolynomialExplicitFormula
import RSBounds.QuarticMellin

/-!
# The quartic kernel in the fixed-strip explicit formula

This specializes the polynomial contour bridge to the rational continuation
of the Mellin transform of `(1-u)_+^4/24`. The left vertical integral is kept
explicit; this file does not assert its evaluation by the trivial zeros.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology

namespace TernaryGoldbach.RSBounds.PolynomialQuartic

open TernaryGoldbach.Explicit PolynomialExplicit QuarticMellin

noncomputable def numerator (s : ℂ) : ℂ :=
  1 / ((s + 1) * (s + 2) * (s + 3) * (s + 4))

theorem kernel_eq_numerator_div (s : ℂ) : kernel s = numerator s / s := by
  simp only [kernel, numerator, div_div]
  congr 1
  ring

theorem numerator_zero : numerator 0 = 1 / 24 := by
  norm_num [numerator]

theorem differentiableAt_numerator {s : ℂ} (hs : -1 < s.re) :
    DifferentiableAt ℂ numerator s := by
  have hn (n : ℕ) (hn : 1 ≤ n) : s + n ≠ 0 := by
    intro hz
    have he := congrArg Complex.re hz
    simp only [add_re, natCast_re, zero_re] at he
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : s + 1 ≠ 0 := by simpa using hn 1 le_rfl
  have h2 : s + 2 ≠ 0 := by simpa using hn 2 (by omega)
  have h3 : s + 3 ≠ 0 := by simpa using hn 3 (by omega)
  have h4 : s + 4 ≠ 0 := by simpa using hn 4 (by omega)
  unfold numerator
  exact (differentiableAt_const _).div
    ((((differentiableAt_id.add_const 1).mul (differentiableAt_id.add_const 2)).mul
      (differentiableAt_id.add_const 3)).mul (differentiableAt_id.add_const 4))
    (mul_ne_zero (mul_ne_zero (mul_ne_zero h1 h2) h3) h4)

private theorem norm_kernel_le {s : ℂ} {d : ℝ} (hd : 0 < d)
    (h0 : d ≤ ‖s‖) (h1 : d ≤ ‖s + 1‖) (h2 : d ≤ ‖s + 2‖)
    (h3 : d ≤ ‖s + 3‖) (h4 : d ≤ ‖s + 4‖) :
    ‖kernel s‖ ≤ 1 / d ^ 5 := by
  have hp : d ^ 5 ≤ ‖s‖ * ‖s + 1‖ * ‖s + 2‖ * ‖s + 3‖ * ‖s + 4‖ := by
    calc
      d ^ 5 = d * d * d * d * d := by ring
      _ ≤ _ := by gcongr
  simpa only [kernel, norm_div, norm_one, norm_mul] using
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 1) (pow_pos hd 5) hp

private theorem factor_lower (σ t : ℝ) (hσ : σ = -1 / 2 ∨ σ = 3 / 2)
    (n : ℕ) (hn : n ≤ 4) :
    (1 + |t|) / 3 ≤ ‖((σ : ℂ) + t * I) + n‖ := by
  have hreal : (1 / 2 : ℝ) ≤ |σ + n| := by
    rcases hσ with rfl | rfl <;> interval_cases n <;> norm_num
  have hr := Complex.abs_re_le_norm (((σ : ℂ) + t * I) + n)
  have hi := Complex.abs_im_le_norm (((σ : ℂ) + t * I) + n)
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
    I_im, mul_one, sub_self, add_zero, natCast_re] at hr
  simp only [add_im, ofReal_im, ofReal_re, mul_im, I_im, mul_one, I_re, mul_zero,
    add_zero, zero_add, natCast_im] at hi
  linarith

/-- A uniform fifth-power bound on the two vertical lines and the strip's
horizontal sides. The constant is deliberately coarse; it is used here only
to justify convergence. -/
theorem decayFive_kernel : DecayFive kernel 243 := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · intro σ hσ
    have hn (n : ℕ) (hn : n ≤ 4) (t : ℝ) :
        ((σ : ℂ) + t * I) + n ≠ 0 := by
      apply norm_pos_iff.mp
      exact lt_of_lt_of_le (by positivity) (factor_lower σ t hσ n hn)
    unfold kernel
    refine continuous_const.div (by fun_prop) (fun t => ?_)
    have h0 : ((σ : ℂ) + t * I) ≠ 0 := by simpa using hn 0 (by omega) t
    have h1 : ((σ : ℂ) + t * I) + 1 ≠ 0 := by simpa using hn 1 (by omega) t
    have h2 : ((σ : ℂ) + t * I) + 2 ≠ 0 := by simpa using hn 2 (by omega) t
    have h3 : ((σ : ℂ) + t * I) + 3 ≠ 0 := by simpa using hn 3 (by omega) t
    have h4 : ((σ : ℂ) + t * I) + 4 ≠ 0 := by simpa using hn 4 (by omega) t
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h0 h1) h2) h3) h4
  · intro σ hσ t
    have hn (n : ℕ) (hn : n ≤ 4) := factor_lower σ t hσ n hn
    have h := norm_kernel_le (s := (σ : ℂ) + t * I)
      (d := (1 + |t|) / 3) (by positivity)
      (by simpa using hn 0 (by omega))
      (by simpa using hn 1 (by omega))
      (by simpa using hn 2 (by omega))
      (by simpa using hn 3 (by omega))
      (by simpa using hn 4 (by omega))
    refine h.trans_eq ?_
    have hp : 1 + |t| ≠ 0 := by positivity
    field_simp [hp]
    <;> ring
  · intro s _ _ ht
    have hn (n : ℕ) : |s.im| ≤ ‖s + n‖ := by
      simpa using Complex.abs_im_le_norm (s + n)
    have h := norm_kernel_le (s := s) (d := |s.im|) (by linarith)
      (by simpa using hn 0) (by simpa using hn 1) (by simpa using hn 2)
      (by simpa using hn 3) (by simpa using hn 4)
    exact h.trans (by gcongr; norm_num)

/-- The fourfold kernel's explicit formula, retaining its left remainder.
On the right line this rational kernel is the actual Mellin transform,
by `QuarticMellin.mellin_weight`. -/
theorem explicit_formula_quartic_at_heights {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0) {x : ℝ} (hx : 0 < x)
    {T : ℕ → ℝ} (hT : GoodHeights f B T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
      (kernel u * (x : ℂ) ^ u)) atTop
      (𝓝 ((1 / (2 * π) : ℂ) *
        ((∫ y : ℝ, contourIntegrand f kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
          ∫ y : ℝ, contourIntegrand f kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
        logDeriv f 0 / 24)) := by
  have hM : DecayFive (fun s => numerator s / s) 243 := by
    simpa only [← kernel_eq_numerator_div] using decayFive_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    explicit_formula_pole_zero_at_heights hd hf0
      (fun _ hs => differentiableAt_numerator hs) hM hx hT

/-- Existential version of the quartic formula. -/
theorem explicit_formula_quartic {f : ℂ → ℂ} {B : ℝ → ℝ} {D CR : ℝ}
    (hd : LDatum f B D CR) (hf0 : f 0 ≠ 0) {x : ℝ} (hx : 0 < x) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD f (T k), (multRectD f (T k) u : ℂ) *
        (kernel u * (x : ℂ) ^ u)) atTop
        (𝓝 ((1 / (2 * π) : ℂ) *
          ((∫ y : ℝ, contourIntegrand f kernel x (((3 / 2 : ℝ) : ℂ) + y * I)) -
            ∫ y : ℝ, contourIntegrand f kernel x (((-1 / 2 : ℝ) : ℂ) + y * I)) -
          logDeriv f 0 / 24)) := by
  have hM : DecayFive (fun s => numerator s / s) 243 := by
    simpa only [← kernel_eq_numerator_div] using decayFive_kernel
  simpa only [← kernel_eq_numerator_div, numerator_zero, mul_one_div] using
    explicit_formula_pole_zero hd hf0 (fun _ hs => differentiableAt_numerator hs) hM hx

end TernaryGoldbach.RSBounds.PolynomialQuartic
