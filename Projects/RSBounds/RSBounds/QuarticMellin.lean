import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic

/-!
# Mellin transform of the truncated quartic

The weight `(max (1-u) 0)^4 / 24` has Mellin transform
`1 / (s(s+1)(s+2)(s+3)(s+4))` on `Re s > 0`.

The rational `kernel` is defined separately: outside that half-plane it is
the meromorphic continuation, not the value of a convergent Mellin integral.
The proof uses Mathlib's Mellin transform of a power on `(0,1]` and the
binomial expansion. There is no prime-number or zero-location hypothesis.
-/

open Complex Set MeasureTheory

namespace TernaryGoldbach.RSBounds.QuarticMellin

/-- The compactly supported quartic weight on the positive half-line. -/
noncomputable def weight (u : ℝ) : ℂ :=
  (((max (1 - u) 0) ^ 4 / 24 : ℝ) : ℂ)

/-- The rational continuation of the quartic weight's Mellin transform. -/
noncomputable def kernel (s : ℂ) : ℂ :=
  1 / (s * (s + 1) * (s + 2) * (s + 3) * (s + 4))

theorem continuous_weight : Continuous weight := by
  unfold weight
  fun_prop

theorem weight_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) : weight u = 0 := by
  simp [weight, max_eq_right (sub_nonpos.mpr hu)]

private theorem hasMellin_congr_pos {f g : ℝ → ℂ} {s a : ℂ}
    (hfg : ∀ u : ℝ, 0 < u → f u = g u) (hf : HasMellin f s a) :
    HasMellin g s a := by
  constructor
  · exact (integrableOn_congr_fun
      (fun (u : ℝ) hu => congrArg (fun z : ℂ => (u : ℂ) ^ (s - 1) • z) (hfg u hu))
      measurableSet_Ioi).mp hf.1
  · calc
      mellin g s = mellin f s := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        change (u : ℂ) ^ (s - 1) • g u = (u : ℂ) ^ (s - 1) • f u
        rw [hfg u hu]
      _ = a := hf.2

private theorem hasMellin_add_values {f g : ℝ → ℂ} {s a b : ℂ}
    (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (fun u => f u + g u) s (a + b) := by
  simpa only [hf.2, hg.2] using hasMellin_add hf.1 hg.1

private theorem hasMellin_sub_values {f g : ℝ → ℂ} {s a b : ℂ}
    (hf : HasMellin f s a) (hg : HasMellin g s b) :
    HasMellin (fun u => f u - g u) s (a - b) := by
  simpa only [hf.2, hg.2] using hasMellin_sub hf.1 hg.1

private theorem hasMellin_mul_value {f : ℝ → ℂ} {s a : ℂ}
    (hf : HasMellin f s a) (c : ℂ) :
    HasMellin (fun u => c * f u) s (c * a) := by
  simpa only [smul_eq_mul, hf.2] using hasMellin_const_smul hf.1 c

private theorem hasMellin_div_value {f : ℝ → ℂ} {s a : ℂ}
    (hf : HasMellin f s a) (c : ℂ) :
    HasMellin (fun u => f u / c) s (a / c) :=
  ⟨hf.1.div_const c, by rw [mellin_div_const, hf.2]⟩

private theorem shifted_ne_zero {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    s + n ≠ 0 := by
  have hpos : 0 < (s + n).re := by
    simp only [add_re, natCast_re]
    positivity
  intro h
  exact (ne_of_gt hpos) (congrArg Complex.re h)

/-- Convergence and exact evaluation of the Mellin integral in its half-plane
of convergence. -/
theorem hasMellin_weight {s : ℂ} (hs : 0 < s.re) :
    HasMellin weight s (kernel s) := by
  let p : ℕ → ℝ → ℂ := fun n => indicator (Ioc 0 1) (fun u => (u : ℂ) ^ n)
  have hp (n : ℕ) : HasMellin (p n) s (1 / (s + n)) := by
    have hpos : 0 < s.re + (n : ℂ).re := by
      simp only [natCast_re]
      positivity
    simpa only [p, cpow_natCast] using hasMellin_cpow_Ioc (n : ℂ) hpos
  have hq := hasMellin_div_value
    (hasMellin_add_values
      (hasMellin_sub_values
        (hasMellin_add_values
          (hasMellin_sub_values (hp 0) (hasMellin_mul_value (hp 1) 4))
          (hasMellin_mul_value (hp 2) 6))
        (hasMellin_mul_value (hp 3) 4))
      (hp 4)) 24
  norm_num only [Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, add_zero] at hq
  have hweight : HasMellin weight s
      ((1 / s - 4 * (1 / (s + 1)) + 6 * (1 / (s + 2)) -
        4 * (1 / (s + 3)) + 1 / (s + 4)) / 24) := by
    refine hasMellin_congr_pos (fun u hu => ?_) hq
    by_cases hu1 : u ≤ 1
    · have hmem : u ∈ Ioc (0 : ℝ) 1 := ⟨hu, hu1⟩
      simp only [p, indicator_of_mem hmem, weight,
        max_eq_left (sub_nonneg.mpr hu1)]
      push_cast
      ring
    · have hnmem : u ∉ Ioc (0 : ℝ) 1 := fun h => hu1 h.2
      have hle : 1 ≤ u := (lt_of_not_ge hu1).le
      simp [p, hnmem, weight_eq_zero_of_one_le hle]
  have h0 : s ≠ 0 := by simpa using shifted_ne_zero hs 0
  have h1 : s + 1 ≠ 0 := by simpa using shifted_ne_zero hs 1
  have h2 : s + 2 ≠ 0 := by simpa using shifted_ne_zero hs 2
  have h3 : s + 3 ≠ 0 := by simpa using shifted_ne_zero hs 3
  have h4 : s + 4 ≠ 0 := by simpa using shifted_ne_zero hs 4
  have heval :
      (1 / s - 4 * (1 / (s + 1)) + 6 * (1 / (s + 2)) -
        4 * (1 / (s + 3)) + 1 / (s + 4)) / 24 = kernel s := by
    unfold kernel
    field_simp [h0, h1, h2, h3, h4]
    ring
  exact heval ▸ hweight

theorem mellinConvergent_weight {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent weight s :=
  (hasMellin_weight hs).1

theorem mellin_weight {s : ℂ} (hs : 0 < s.re) :
    mellin weight s = kernel s :=
  (hasMellin_weight hs).2

end TernaryGoldbach.RSBounds.QuarticMellin
