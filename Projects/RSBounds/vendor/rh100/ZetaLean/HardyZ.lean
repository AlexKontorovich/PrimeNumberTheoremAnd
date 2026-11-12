module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

@[expose] public section

namespace RH100HardyZ

open Complex
open scoped ComplexConjugate

/--
Hardy's Z function.

Defined using the completed Riemann zeta function `Λ(s)` to avoid
needing a continuous branch of `log Γ` along the critical line.
Since `Λ(1/2 + it)` is real, we divide by the positive real factor
`π^(-1/4) * ‖Γ(1/4 + I*t/2)‖` to obtain `Z(t)`.

Note: The goal is to eventually type this as `ℝ → ℝ` if preferred by Mathlib,
but here we start with the definition over `ℂ` or returning `ℂ` for easier
algebra before extracting the real part or proving it's real.
-/
noncomputable def hardyZ (t : ℝ) : ℂ :=
  completedRiemannZeta (1/2 + t * I) /
    ( (Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * ‖Gamma (1/4 + t / 2 * I)‖ )

lemma Gammaℝ_conj (s : ℂ) : conj (Gammaℝ s) = Gammaℝ (conj s) := by
  rw [Gammaℝ_def, Gammaℝ_def, map_mul, ← Gamma_conj]
  have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
    rw [arg_ofReal_of_nonneg Real.pi_pos.le]
    exact Real.pi_pos.ne
  have h1 := (cpow_conj (↑Real.pi) (-s/2) hpi).symm
  rw [conj_ofReal] at h1
  rw [h1]
  congr 1
  · congr 1
    rw [map_div₀, map_neg]
    congr 2
    exact map_ofNat (starRingEnd ℂ) 2
  · congr 1
    rw [map_div₀]
    congr 1
    exact map_ofNat (starRingEnd ℂ) 2

lemma completedRiemannZeta_conj_half (t : ℝ) :
    conj (completedRiemannZeta (1/2 + t * I)) = completedRiemannZeta (1/2 - t * I) := by
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]; simp
  have hcs_re : 0 < (conj s).re := by
    rw [conj_re]; exact hs_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h_s_ne_zero : s ≠ 0 := by
      intro h
      have : s.re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  have H2 : completedRiemannZeta (conj s) = riemannZeta (conj s) * Gammaℝ (conj s) := by
    have h_s_ne_zero : conj s ≠ 0 := by
      intro h
      have : (conj s).re = 0 := by rw [h, zero_re]
      linarith
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hcs_re)).symm
  have h_conj_s : conj (1/2 + (t:ℂ) * I) = 1/2 - t * I := by
    apply Complex.ext <;> simp
  rw [← h_conj_s]
  change conj (completedRiemannZeta s) = completedRiemannZeta (conj s)
  rw [H1, H2, map_mul, ← riemannZeta_conj, RH100HardyZ.Gammaℝ_conj]

/-- `Z t` is strictly real. -/
lemma hardyZ_is_real (t : ℝ) : ∃ (r : ℝ), hardyZ t = r := by
  use (hardyZ t).re
  symm
  apply conj_eq_iff_re.mp
  dsimp [hardyZ]
  rw [map_div₀, completedRiemannZeta_conj_half]
  congr 1
  · have h_symm : 1/2 - (t:ℂ) * I = 1 - (1/2 + (t:ℂ) * I) := by ring
    rw [h_symm, completedRiemannZeta_one_sub]
  · rw [map_mul]
    congr 1
    · have hpi : (↑Real.pi : ℂ).arg ≠ Real.pi := by
        rw [arg_ofReal_of_nonneg Real.pi_pos.le]; exact Real.pi_pos.ne
      have h1 := (cpow_conj (↑Real.pi) (-(1/4:ℝ)) hpi).symm
      rw [conj_ofReal, map_neg, conj_ofReal] at h1
      exact h1
    · exact conj_ofReal _

/-- The absolute value of `Z t` is exactly the absolute value of `ζ(1/2 + it)`. -/
lemma abs_hardyZ_eq_abs_zeta (t : ℝ) : ‖hardyZ t‖ = ‖riemannZeta (1/2 + t * I)‖ := by
  dsimp [hardyZ]
  rw [norm_div]
  let s : ℂ := 1/2 + t * I
  have hs_re : 0 < s.re := by
    dsimp [s]
    norm_num
  have h_s_ne_zero : s ≠ 0 := by
    intro h
    have h_re : s.re = 0 := by rw [h, zero_re]
    dsimp [s] at h_re
    norm_num at h_re
  have H1 : completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    rw [riemannZeta_def_of_ne_zero h_s_ne_zero]
    exact (div_mul_cancel₀ _ (Gammaℝ_ne_zero_of_re_pos hs_re)).symm
  rw [H1, norm_mul]
  have H3 : ‖(↑Real.pi : ℂ) ^ (-(1/4 : ℝ) : ℂ) * (‖Gamma (1/4 + ↑t / 2 * I)‖ : ℂ)‖ = ‖Gammaℝ s‖ := by
    rw [Gammaℝ_def, norm_mul, norm_mul]
    congr 1
    · rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
      congr 1
      have H_re : (-(1/4 : ℝ) : ℂ).re = (-s/2).re := by
        dsimp [s]; simp; norm_num
      exact H_re
    · rw [Complex.norm_of_nonneg (norm_nonneg _)]
      congr 1
      have H_eq : 1/4 + (t:ℂ) / 2 * I = s / 2 := by
        dsimp [s]; apply Complex.ext <;> simp <;> ring
      rw [H_eq]
  rw [H3, mul_div_cancel_right₀]
  rw [norm_ne_zero_iff]
  exact Gammaℝ_ne_zero_of_re_pos hs_re

/-- `Z t` is an even function. -/
lemma hardyZ_even (t : ℝ) : hardyZ (-t) = hardyZ t := by
  unfold hardyZ
  push_cast
  have H_num : completedRiemannZeta (1/2 + -(t:ℂ) * I) = completedRiemannZeta (1/2 + t * I) := by
    have H : 1/2 + -(t:ℂ) * I = 1 - (1/2 + (t:ℂ) * I) := by ring
    rw [H, completedRiemannZeta_one_sub]
  rw [H_num]
  congr 1
  congr 1
  have H_den : 1/4 + -(t:ℂ) / 2 * I = conj (1/4 + (t:ℂ) / 2 * I) := by
    apply Complex.ext_iff.mpr
    constructor
    · rw [Complex.conj_re]
      simp
    · rw [Complex.conj_im]
      simp; ring
  rw [H_den, Gamma_conj, Complex.norm_conj]

/-- `Z t` is zero if and only if `ζ(1/2 + it)` is zero. -/
lemma hardyZ_zero_iff (t : ℝ) : hardyZ t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  have h1 : hardyZ t = 0 ↔ ‖hardyZ t‖ = 0 := norm_eq_zero.symm
  have h2 : riemannZeta (1/2 + (t:ℂ) * I) = 0 ↔ ‖riemannZeta (1/2 + (t:ℂ) * I)‖ = 0 := norm_eq_zero.symm
  rw [h1, h2, abs_hardyZ_eq_abs_zeta]

/-- `Z t` is continuous. -/
lemma continuous_hardyZ : Continuous hardyZ := by
  apply continuous_iff_continuousAt.mpr
  intro x
  unfold hardyZ
  apply ContinuousAt.div
  · let f (t : ℝ) : ℂ := 1/2 + (t : ℂ) * I
    have h1 : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul continuous_ofReal continuous_const
      exact h_cont.continuousAt
    have hs0 : f x ≠ 0 := by
      intro h; have h_re : (f x).re = 0 := by rw [h, zero_re]
      dsimp [f] at h_re; norm_num at h_re
    have hs1 : f x ≠ 1 := by
      intro h; have h_re : (f x).re = 1 := by rw [h, one_re]
      dsimp [f] at h_re; norm_num at h_re
    exact (differentiableAt_completedZeta hs0 hs1).continuousAt.comp h1
  · have H_const : ContinuousAt (fun (t : ℝ) => (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)) x := continuousAt_const
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have H_arg : ContinuousAt f x := by
      have h_cont : Continuous f := by
        refine continuous_const.add ?_
        refine Continuous.mul ?_ continuous_const
        refine Continuous.div continuous_ofReal continuous_const ?_
        intro _; exact two_ne_zero
      exact h_cont.continuousAt
    have H_gamma : ContinuousAt (fun (t : ℝ) => (‖Gamma (f t)‖ : ℂ)) x := by
      have hc1 : ContinuousAt Gamma (f x) := by
        apply continuousAt_Gamma
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact continuous_ofReal.continuousAt.comp (continuous_norm.continuousAt.comp (hc1.comp H_arg))
    exact H_const.mul H_gamma
  · intro h
    let f (t : ℝ) : ℂ := 1 / 4 + (t : ℂ) / 2 * I
    have h_mul : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) * (‖Gamma (f x)‖ : ℂ) = 0 := h
    rw [mul_eq_zero] at h_mul
    cases h_mul with
    | inl h_pi =>
      have H_pi_ne : (↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ) ≠ 0 := by
        intro h_eq
        have h_norm : ‖(↑Real.pi : ℂ) ^ (-(1 / 4 : ℝ) : ℂ)‖ = 0 := by rw [h_eq, norm_zero]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at h_norm
        have h_re : (-(1 / 4 : ℝ) : ℂ).re = -1 / 4 := by norm_num
        rw [h_re] at h_norm
        have h_pos : (Real.pi : ℝ) ^ (-1/4 : ℝ) > 0 := Real.rpow_pos_of_pos Real.pi_pos _
        linarith
      exact H_pi_ne h_pi
    | inr h_gamma =>
      have H_g_norm_zero : ‖Gamma (f x)‖ = 0 := by
        exact (Complex.ofReal_eq_zero).mp h_gamma
      rw [norm_eq_zero] at H_g_norm_zero
      have H_g_ne_zero : Gamma (f x) ≠ 0 := by
        apply Gamma_ne_zero
        intro m h_eq
        have h_re : (f x).re = (-m : ℂ).re := by rw [h_eq]
        dsimp [f] at h_re; simp at h_re
        have hm : (m : ℝ) ≥ 0 := Nat.cast_nonneg m
        linarith
      exact H_g_ne_zero H_g_norm_zero

/-!
### The real-valued Z

`hardyZ_is_real` proves every value of `hardyZ` equals some real number, but
`hardyZ` itself is still typed `ℝ → ℂ`: the docstring at the top of this file
flagged that as provisional ("the goal is to eventually type this as
`ℝ → ℝ`"). This section meets that goal, purely additively: `hardyZReal` and
everything below are *derived* from the five lemmas above via the coercion
`ℝ → ℂ`, without editing a single one of them, so nothing already
kernel-checked is put at risk by this section existing.
-/

/-- Hardy's Z, retyped `ℝ → ℝ` now that `hardyZ_is_real` is proved. -/
noncomputable def hardyZReal (t : ℝ) : ℝ := (hardyZ t).re

/-- `hardyZReal` and `hardyZ` agree under the standard `ℝ → ℂ` coercion. -/
lemma hardyZReal_eq_hardyZ (t : ℝ) : (hardyZReal t : ℂ) = hardyZ t := by
  obtain ⟨r, hr⟩ := hardyZ_is_real t
  unfold hardyZReal
  rw [hr, Complex.ofReal_re]

/-- The real-valued Z has the same magnitude as `ζ(1/2 + it)`. -/
lemma abs_hardyZReal_eq_abs_zeta (t : ℝ) :
    |hardyZReal t| = ‖riemannZeta (1/2 + t * I)‖ := by
  rw [← abs_hardyZ_eq_abs_zeta t, ← hardyZReal_eq_hardyZ t, Complex.norm_real,
    Real.norm_eq_abs]

/-- `hardyZReal` is even. -/
lemma hardyZReal_even (t : ℝ) : hardyZReal (-t) = hardyZReal t := by
  have h : (hardyZReal (-t) : ℂ) = (hardyZReal t : ℂ) := by
    rw [hardyZReal_eq_hardyZ, hardyZReal_eq_hardyZ, hardyZ_even]
  exact_mod_cast h

/-- `hardyZReal t = 0` iff `ζ(1/2 + it) = 0`. -/
lemma hardyZReal_zero_iff (t : ℝ) :
    hardyZReal t = 0 ↔ riemannZeta (1/2 + t * I) = 0 := by
  rw [← hardyZ_zero_iff t, ← hardyZReal_eq_hardyZ t, Complex.ofReal_eq_zero]

/-- `hardyZReal` is continuous. -/
lemma continuous_hardyZReal : Continuous hardyZReal :=
  Complex.continuous_re.comp continuous_hardyZ

end RH100HardyZ
