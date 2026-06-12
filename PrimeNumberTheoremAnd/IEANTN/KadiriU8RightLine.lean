import PrimeNumberTheoremAnd.IEANTN.KadiriLaplaceInversion
import PrimeNumberTheoremAnd.IEANTN.KadiriEq1618Assembly

/-!
# The right-line inversion identity (sprint U8, gap 2)

This file discharges `U8RightLineInversionHypothesis`: on the line `Re = σR > 1`
the normalized vertical integral of the contour integrand equals minus the von
Mangoldt series `∑' n, Λ n * φ (log n)`.

The proof has three layers:
1. a logarithmic change of variables identifying the one-sided transform
   `u8Phi φ (-z)` with `mellin (φ ∘ log) z` (the complex-valued version of
   `kadiriMellin_log_eq_laplaceTransform`);
2. the Dirichlet-series expansion of `logDeriv riemannZeta` on the line and the
   interchange of `∑'` and `∫`, dominated by `Λ n * n ^ (-σR) * ‖mellin (φ ∘ log)‖`
   with summability witnessed by the von Mangoldt `L`-series at `σR`;
3. the per-`n` Mellin inversion `kadiriVerticalIntegral_mellin_log_eq` at `x = n`.

Nothing here requires `φ` to be real-valued or compactly supported: the inputs
are one-sidedness, Mellin convergence, line integrability of the transform, and
continuity of `φ` at the points `log n`, all of which the Kadiri test-function
class supplies.
-/

namespace Kadiri

open Complex MeasureTheory
open ArithmeticFunction hiding log
open Filter Set Asymptotics
open scoped Topology NNReal ENNReal

noncomputable section

/-! ## The logarithmic change of variables, complex-valued -/

private theorem u8_rexpNegDeriv :
    ∀ x ∈ Set.univ, HasDerivWithinAt (Real.exp ∘ Neg.neg) (-Real.exp (-x)) Set.univ x :=
  fun x _ => mul_neg_one (Real.exp (-x)) ▸
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).hasDerivWithinAt

private theorem u8_rexpNeg_image_univ : Real.exp ∘ Neg.neg '' Set.univ = Set.Ioi 0 := by
  rw [Set.image_comp, Set.image_univ_of_surjective neg_surjective, Set.image_univ, Real.range_exp]

private theorem u8_rexpNeg_injOn_univ : Set.univ.InjOn (Real.exp ∘ Neg.neg) :=
  Real.exp_injective.injOn.comp neg_injective.injOn (Set.univ.mapsTo_univ _)

private theorem u8_rexp_smul_cpow (x : ℝ) (s : ℂ) (z : ℂ) :
    Real.exp (-x) • Complex.exp (-(x : ℂ)) ^ (s - 1) • z =
      Complex.exp (-s * (x : ℂ)) • z := by
  change (Real.exp (-x) : ℂ) * (Complex.exp (-(x : ℂ)) ^ (s - 1) * z) =
    Complex.exp (-s * (x : ℂ)) * z
  rw [Complex.ofReal_exp]
  push_cast
  rw [← mul_assoc]
  nth_rewrite 1 [← cpow_one (Complex.exp (-(x : ℂ)))]
  rw [← cpow_add _ _ (Complex.exp_ne_zero _), cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simpa using Real.pi_nonneg)]
  ring_nf

private theorem u8_integral_comp_neg_univ (F : ℝ → ℂ) :
    (∫ x : ℝ, F (-x)) = ∫ x : ℝ, F x := by
  have A : MeasurableEmbedding fun x : ℝ => -x :=
    (Homeomorph.neg ℝ).isClosedEmbedding.measurableEmbedding
  have h := A.integral_map (μ := volume) F
  rw [Measure.map_neg_eq_self (volume : Measure ℝ)] at h
  simpa using h.symm

/-- Logarithmic change of variables for a complex-valued test function: the
Mellin transform of `t ↦ φ (log t)` is the two-sided exponential integral. -/
theorem u8_mellin_log_eq_integral (φ : ℝ → ℂ) (s : ℂ) :
    mellin (fun t : ℝ => φ (Real.log t)) s =
      ∫ y : ℝ, Complex.exp (s * (y : ℂ)) * φ y := by
  calc
    mellin (fun t : ℝ => φ (Real.log t)) s
        = ∫ u : ℝ, Complex.exp (-s * (u : ℂ)) * φ (-u) := by
          rw [mellin, ← u8_rexpNeg_image_univ, integral_image_eq_integral_abs_deriv_smul
            MeasurableSet.univ u8_rexpNegDeriv u8_rexpNeg_injOn_univ]
          rw [setIntegral_univ]
          congr with x
          simpa [Function.comp_def, Real.log_exp, abs_of_pos (Real.exp_pos (-x)), smul_eq_mul,
            mul_assoc] using u8_rexp_smul_cpow x s (φ (-x))
    _ = ∫ y : ℝ, Complex.exp (s * (y : ℂ)) * φ y := by
          rw [← u8_integral_comp_neg_univ (fun y : ℝ => Complex.exp (s * (y : ℂ)) * φ y)]
          congr
          ext u
          simp

/-- For `φ` vanishing on the negative axis the one-sided transform `u8Phi`
agrees with the Mellin transform of `t ↦ φ (log t)`. -/
theorem u8Phi_neg_eq_mellin_log {φ : ℝ → ℂ} (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0) (s : ℂ) :
    u8Phi φ (-s) = mellin (fun t : ℝ => φ (Real.log t)) s := by
  rw [u8_mellin_log_eq_integral]
  have h1 : (∫ y : ℝ, Complex.exp (s * (y : ℂ)) * φ y)
      = ∫ y in Set.Ici (0 : ℝ), Complex.exp (s * (y : ℂ)) * φ y := by
    rw [← setIntegral_univ]
    exact setIntegral_eq_of_subset_of_forall_diff_eq_zero MeasurableSet.univ
      (Set.subset_univ _) fun x hx => by
        have hxneg : x < 0 := lt_of_not_ge hx.2
        simp [hφ_neg x hxneg]
  rw [h1, integral_Ici_eq_integral_Ioi]
  unfold u8Phi
  refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
  rw [neg_neg, mul_comm]

/-! ## The Dirichlet-series expansion of the integrand on the right line -/

/-- On `Re = σR > 1` the contour integrand is minus the von Mangoldt Dirichlet
series weighted by the Mellin data of `φ`. -/
lemma u8ContourIntegrand_eq_neg_tsum_right {φ : ℝ → ℂ} {σR : ℝ} (hσR : 1 < σR)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0) (t : ℝ) :
    u8ContourIntegrand (u8Phi φ) ((σR : ℂ) + (t : ℂ) * I) =
      -∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I) := by
  have hre : ((σR : ℂ) + (t : ℂ) * I).re = σR := by simp
  have hser := tsum_vonMangoldt_eq (s := (σR : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hσR)
  unfold u8ContourIntegrand
  rw [neg_mul_neg, logDeriv_apply, u8Phi_neg_eq_mellin_log hφ_neg, tsum_mul_right, hser]
  ring

/-! ## The dominated interchange of sum and line integral -/

/-- Fubini swap on the right line: the dominating function is
`Λ n * n ^ (-σR) * ‖mellin (φ ∘ log)‖`, with summability supplied by the von
Mangoldt `L`-series at real argument `σR > 1` and the line mass of the
transform. -/
lemma u8_rightline_integral_tsum_swap {φ : ℝ → ℂ} {σR : ℝ} (hσR : 1 < σR)
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σR) :
    (∫ t : ℝ, ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)) =
      ∑' n : ℕ, ∫ t : ℝ, (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I) := by
  have hre : ∀ t : ℝ, ((σR : ℂ) + (t : ℂ) * I).re = σR := fun t => by simp
  have hσR0 : σR ≠ 0 := (zero_lt_one.trans hσR).ne'
  rw [MeasureTheory.integral_tsum]
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using aestronglyMeasurable_const
    · have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hexp : Continuous fun t : ℝ => (σR : ℂ) + (t : ℂ) * I := by fun_prop
      have hcont : Continuous fun t : ℝ =>
          (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) := by
        refine continuous_const.div (hexp.const_cpow (Or.inl hbase)) fun t => ?_
        rw [Complex.cpow_def_of_ne_zero hbase]
        exact Complex.exp_ne_zero _
      exact hcont.aestronglyMeasurable.mul hVertical.1
  · rw [← lt_top_iff_ne_top]
    have habs : ∀ t : ℝ, ∀ n : ℕ,
        ‖(n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I)‖₊ = (n : ℝ≥0) ^ σR := by
      intro t n
      simp_rw [← norm_toNNReal]
      rw [norm_natCast_cpow_of_re_ne_zero _ (by rw [hre]; exact hσR0), hre]
      simp only [Real.toNNReal_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σR)]
      norm_cast
    have hpoint : ∀ n : ℕ, ∀ t : ℝ,
        ‖(Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)‖ₑ =
          ((‖Λ n‖₊ / (n : ℝ≥0) ^ σR : ℝ≥0) : ℝ≥0∞) *
            ‖mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)‖ₑ := by
      intro n t
      rw [enorm_mul]
      congr 1
      rw [enorm_eq_nnnorm, nnnorm_div, nnnorm_real, habs t n]
    calc
      ∑' n : ℕ, ∫⁻ t : ℝ, ‖(Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
          mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)‖ₑ
          = ∑' n : ℕ, ((‖Λ n‖₊ / (n : ℝ≥0) ^ σR : ℝ≥0) : ℝ≥0∞) *
              ∫⁻ t : ℝ, ‖mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)‖ₑ := by
            refine tsum_congr fun n => ?_
            simp_rw [hpoint n]
            exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (∑' n : ℕ, ((‖Λ n‖₊ / (n : ℝ≥0) ^ σR : ℝ≥0) : ℝ≥0∞)) *
              ∫⁻ t : ℝ, ‖mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)‖ₑ :=
            ENNReal.tsum_mul_right
      _ < ⊤ := by
            refine ENNReal.mul_lt_top ?_ ?_
            · rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
              push_cast
              refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (σR : ℂ))
                (by simp only [Complex.ofReal_re]; exact hσR)).norm).congr fun n => ?_
              rcases eq_or_ne n 0 with rfl | hn
              · simp
              · rw [LSeries.term_of_ne_zero hn, norm_div,
                  norm_natCast_cpow_of_re_ne_zero n
                    (by simp only [Complex.ofReal_re]; exact hσR0),
                  Complex.ofReal_re]
                norm_num [Complex.norm_real]
            · rw [← hasFiniteIntegral_iff_enorm]
              exact hVertical.2

/-! ## The per-term inversion and the endpoint -/

/-- Per-`n` evaluation: each Dirichlet-series term integrates to the inverted
value `Λ n * φ (log n)`, with the `n = 0, 1` terms vanishing since `Λ` does. -/
lemma u8_rightline_term_eq {φ : ℝ → ℂ} {σR : ℝ}
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σR : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σR)
    (hφ_cont : ∀ n : ℕ, 2 ≤ n → ContinuousAt φ (Real.log n)) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) * ∫ t : ℝ, (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I) =
      (Λ n : ℂ) * φ (Real.log n) := by
  by_cases hn : 2 ≤ n
  · have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    have hinv := kadiriVerticalIntegral_mellin_log_eq (φ := φ) (σ := σR)
      (x := ((n : ℕ) : ℝ)) hx hMellin hVertical (hφ_cont n hn)
    simp only [Complex.real_smul, smul_eq_mul] at hinv
    push_cast at hinv
    have hker : (fun t : ℝ => (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ => (Λ n : ℂ) •
          ((n : ℂ) ^ (-((σR : ℂ) + (t : ℂ) * I)) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I)) := by
      funext t
      simp only [smul_eq_mul]
      rw [Complex.cpow_neg, div_eq_mul_inv, mul_assoc]
    rw [hker, integral_smul, smul_eq_mul]
    linear_combination (Λ n : ℂ) * hinv
  · have h2 : n < 2 := by omega
    interval_cases n
    · simp
    · simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- Discharge of the right-line inversion hypothesis: on `Re = σR > 1` the
normalized vertical integral of the contour integrand is exactly minus the von
Mangoldt series of `φ`.  The inputs are one-sidedness of `φ`, Mellin
convergence and line integrability of its transform, and continuity at the
points `log n`; the Kadiri test-function class supplies all four. -/
theorem u8RightLineInversionHypothesis_of_mellin_data {φ : ℝ → ℂ} {σR : ℝ}
    (hσR : 1 < σR)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0)
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σR : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σR)
    (hφ_cont : ∀ n : ℕ, 2 ≤ n → ContinuousAt φ (Real.log n)) :
    U8RightLineInversionHypothesis φ (u8Phi φ) σR := by
  unfold U8RightLineInversionHypothesis u8NormalizedVertical VerticalIntegral
  rw [smul_smul]
  have hpre : 1 / (2 * (Real.pi : ℂ) * I) * I = 1 / (2 * (Real.pi : ℂ)) := by
    rw [div_mul_eq_mul_div, one_mul, mul_comm (2 * (Real.pi : ℂ)) I, ← div_div,
      div_self Complex.I_ne_zero]
  rw [hpre]
  have hint : (fun t : ℝ => u8ContourIntegrand (u8Phi φ) ((σR : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ => -∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ ((σR : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σR : ℂ) + (t : ℂ) * I) :=
    funext fun t => u8ContourIntegrand_eq_neg_tsum_right hσR hφ_neg t
  rw [hint, integral_neg, u8_rightline_integral_tsum_swap hσR hVertical, smul_eq_mul, mul_neg,
    ← tsum_mul_left, tsum_congr fun n => u8_rightline_term_eq hMellin hVertical hφ_cont n]
  rfl

end

end Kadiri
