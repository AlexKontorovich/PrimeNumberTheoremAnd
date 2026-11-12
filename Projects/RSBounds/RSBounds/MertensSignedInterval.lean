import RSBounds.MertensIntervalMellin
import RSBounds.MertensIntervalDecay
import RSBounds.QuadraticSubOne
import RSBounds.PolynomialZetaFormula

/-!
# A degree-two integrated explicit formula on a finite interval

For `1 ≤ a ≤ b`, the actual multiplicity zero sum with kernel
`(b^(s-1)-a^(s-1))/(s*(s-1))` converges along the existing good-height sequence.
The formula contains the finite signed psi integral, the evaluated residue at
zero, and an explicit left vertical remainder. No RH, prime-number theorem,
limiting Mertens normalization, or assumed zero-sum formula is used.

The passage to an infinite interval, a bound or evaluation for the left
remainder, and identification of the limiting Euler normalization are separate
subsequent obligations. This theorem alone is not RS62 Lemma 7 or 8.
-/

open Complex Set Filter MeasureTheory
open scoped Real Topology ArithmeticFunction.vonMangoldt

namespace TernaryGoldbach.RSBounds.MertensSignedInterval

open TernaryGoldbach.Explicit PolynomialExplicit MertensIntervalKernel
  MertensIntervalMellin QuadraticContourLimit QuadraticSubOne

/-- The left vertical contribution, retained as an actual convergent integral. -/
noncomputable def leftRemainder (a b : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ y : ℝ,
    contourIntegrand riemannZeta (kernel a b) 1 (((-1 / 2 : ℝ) : ℂ) + y * I)

private theorem contourIntegrand_zetaF_eq (a b : ℝ) {s : ℂ}
    (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    contourIntegrand zetaF (kernel a b) 1 s =
      contourIntegrand (fun z : ℂ => z - 1) (kernel a b) 1 s +
        contourIntegrand riemannZeta (kernel a b) 1 s := by
  rw [contourIntegrand, contourIntegrand, contourIntegrand,
    logDeriv_zetaF_eq hs hz, logDeriv_sub_one]
  ring

theorem integrable_leftRemainder {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun y : ℝ =>
      contourIntegrand riemannZeta (kernel a b) 1
        (((-1 / 2 : ℝ) : ℂ) + y * I)) := by
  have hM := decayTwo_kernel ha hb
  have hL1 (y : ℝ) : ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hLz (y : ℝ) : riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 :=
    zeta_ne_zero_of_zetaF (hL1 y)
      (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have h := (integrable_zetaF_contour_left hM (by norm_num : (0 : ℝ) < 1)).sub
    (integrable_sub_one_contour_left hM (by norm_num : (0 : ℝ) < 1))
  convert h using 1
  ext y
  dsimp only [Pi.sub_apply]
  rw [contourIntegrand_zetaF_eq a b (hL1 y) (hLz y)]
  ring

/-- The finite-interval explicit formula, retaining the entire divided-difference
kernel. The height hypothesis is provided unconditionally by `exists_goodHeights`. -/
theorem kernel_formula_at_heights {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {T : ℕ → ℝ} (hT : GoodHeights zetaF BPz2 T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) u : ℂ) * kernel a b u) atTop
      (𝓝 (-((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) -
        leftRemainder a b - Complex.log (2 * π) * (1 / a - 1 / b : ℝ))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hM := decayTwo_kernel ha0 hb0
  have hH : ∀ s : ℂ, -1 < s.re → DifferentiableAt ℂ (H a b) s :=
    fun s _ => (differentiable_H ha0 hb0) s
  have hlim := QuadraticContourLimit.explicit_formula_pole_zero_at_heights hH hM
    (by norm_num : (0 : ℝ) < 1) hT
  have hmain := sub_one_contour_difference hH hM (by norm_num : (0 : ℝ) < 1)
  change Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k),
      (multRectD zetaF (T k) u : ℂ) * (kernel a b u * (1 : ℂ) ^ u)) atTop
    (𝓝 ((1 / (2 * π) : ℂ) *
      ((∫ y : ℝ, contourIntegrand zetaF (kernel a b) 1
        (((3 / 2 : ℝ) : ℂ) + y * I)) -
       ∫ y : ℝ, contourIntegrand zetaF (kernel a b) 1
        (((-1 / 2 : ℝ) : ℂ) + y * I)) - logDeriv zetaF 0 * H a b 0)) at hlim
  simp only [Complex.one_cpow, mul_one] at hlim
  have hR1 : ∀ y : ℝ, ((3 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    norm_num at this
  have hL1 : ∀ y : ℝ, ((-1 / 2 : ℝ) : ℂ) + y * I ≠ 1 := fun y h => by
    have := congrArg Complex.re h
    norm_num at this
  have hRz : ∀ y : ℝ, riemannZeta (((3 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    riemannZeta_ne_zero_of_one_lt_re (by simp; norm_num)
  have hLz : ∀ y : ℝ, riemannZeta (((-1 / 2 : ℝ) : ℂ) + y * I) ≠ 0 := fun y =>
    zeta_ne_zero_of_zetaF (hL1 y)
      (zetaF_ne_zero_strip (by simp; norm_num) (by simp; norm_num))
  have iR := QuadraticContourLimit.integrable_contour_right ldatum_zeta2 hM
    (by norm_num : (0 : ℝ) < 1)
  have iL := integrable_zetaF_contour_left hM (by norm_num : (0 : ℝ) < 1)
  have iR1 := QuadraticContourLimit.integrable_contour_right ldatum_sub_one hM
    (by norm_num : (0 : ℝ) < 1)
  have iL1 := integrable_sub_one_contour_left hM (by norm_num : (0 : ℝ) < 1)
  set A := ∫ y : ℝ, contourIntegrand zetaF (kernel a b) 1
    (((3 / 2 : ℝ) : ℂ) + y * I) with hA
  set A1 := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (kernel a b) 1
    (((3 / 2 : ℝ) : ℂ) + y * I) with hA1
  set Bv := ∫ y : ℝ, contourIntegrand zetaF (kernel a b) 1
    (((-1 / 2 : ℝ) : ℂ) + y * I) with hBv
  set B1v := ∫ y : ℝ, contourIntegrand (fun s : ℂ => s - 1) (kernel a b) 1
    (((-1 / 2 : ℝ) : ℂ) + y * I) with hB1v
  have IR : ∫ y : ℝ, contourIntegrand riemannZeta (kernel a b) 1
      (((3 / 2 : ℝ) : ℂ) + y * I) = A - A1 := by
    rw [hA, hA1, ← integral_sub iR iR1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq a b (hR1 y) (hRz y)]
    ring
  have IL : ∫ y : ℝ, contourIntegrand riemannZeta (kernel a b) 1
      (((-1 / 2 : ℝ) : ℂ) + y * I) = Bv - B1v := by
    rw [hBv, hB1v, ← integral_sub iL iL1]
    congr 1
    ext y
    rw [contourIntegrand_zetaF_eq a b (hL1 y) (hLz y)]
    ring
  have hS := prime_sum_eq_right_line ha0 hb0 hM
  rw [IR] at hS
  have hzero : logDeriv zetaF 0 = logDeriv (fun s : ℂ => s - 1) 0 +
      Complex.log (2 * π) := by
    rw [logDeriv_zetaF_eq (by norm_num)
      (by rw [riemannZeta_zero]; norm_num), logDeriv_sub_one,
      PolynomialZeta.logDeriv_riemannZeta_zero]
  have hcenter := SsumG_sub_log_eq_signed_integral ha hab
  change H a b 1 * (1 : ℂ) = (1 / (2 * π) : ℂ) * (A1 - B1v) -
    logDeriv (fun s : ℂ => s - 1) 0 * H a b 0 at hmain
  rw [mul_one, H_one ha0 hb0, H_zero] at hmain
  change Tendsto _ _ (𝓝 ((1 / (2 * π) : ℂ) * (A - Bv) -
    logDeriv zetaF 0 * H a b 0)) at hlim
  convert hlim using 2
  rw [leftRemainder, IL, ← hcenter, hS, hmain, hzero, H_zero]
  ring

/-- The literal degree-two rational kernel at every zero, including actual
analytic multiplicity. No enumeration or simple-zero premise is introduced. -/
theorem explicit_formula_at_heights {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b)
    {T : ℕ → ℝ} (hT : GoodHeights zetaF BPz2 T) :
    Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k),
        (multRectD zetaF (T k) u : ℂ) *
          (((b : ℂ) ^ (u - 1) - (a : ℂ) ^ (u - 1)) / (u * (u - 1)))) atTop
      (𝓝 (-((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) -
        leftRemainder a b - Complex.log (2 * π) * (1 / a - 1 / b : ℝ))) := by
  have heq (k : ℕ) :
      (∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) * kernel a b u) =
      ∑ u ∈ zerosRectD zetaF (T k), (multRectD zetaF (T k) u : ℂ) *
        (((b : ℂ) ^ (u - 1) - (a : ℂ) ^ (u - 1)) / (u * (u - 1))) := by
    apply Finset.sum_congr rfl
    intro u hu
    have h1 : u ≠ 1 := by
      intro h
      have hc := (zerosRectD_zetaF_cases hu).2
      simp [h] at hc
    rw [kernel_eq h1, numerator]
  simpa only [heq] using kernel_formula_at_heights ha hab hT

/-- Unconditional existential good-height version of the finite-interval formula. -/
theorem explicit_formula {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∃ T : ℕ → ℝ, (∀ k : ℕ, T k ∈ Icc ((k : ℝ) + 1) ((k : ℝ) + 2)) ∧
      Tendsto (fun k => ∑ u ∈ zerosRectD zetaF (T k),
          (multRectD zetaF (T k) u : ℂ) *
            (((b : ℂ) ^ (u - 1) - (a : ℂ) ^ (u - 1)) / (u * (u - 1)))) atTop
        (𝓝 (-((∫ t in a..b, (Chebyshev.psi t - t) / t ^ 2 : ℝ) : ℂ) -
          leftRemainder a b - Complex.log (2 * π) * (1 / a - 1 / b : ℝ))) := by
  obtain ⟨T, hT⟩ := exists_goodHeights ldatum_zeta2
  exact ⟨T, hT.mem, explicit_formula_at_heights ha hab hT⟩

end TernaryGoldbach.RSBounds.MertensSignedInterval
