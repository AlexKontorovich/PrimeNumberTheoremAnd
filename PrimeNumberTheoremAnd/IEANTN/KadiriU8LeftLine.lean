import PrimeNumberTheoremAnd.IEANTN.KadiriU8RightLine
import PrimeNumberTheoremAnd.IEANTN.KadiriContourPull
import Mathlib.Analysis.Calculus.DSlope

/-!
# The left-line functional-equation split (sprint U8, gap 3)

This file works toward `U8LeftLineFunctionalEquationSplitHypothesis`: on the
line `Re = σL ∈ (-2, 0)` the normalized vertical integral of the contour
integrand splits, via the symmetric functional-equation identity
`neg_logDeriv_zeta_left_eq_reflected`, into
* a reflected von Mangoldt piece (vanishing for one-sided `φ`),
* the `-φ(0) log π` constant (Mellin inversion at `x = 1`, a continuity point,
  so the value is unhalved),
* the digamma-plus-rational kernel, which after a rightward shift to the
  critical line contributes the transform value `Φ 0` (the `z = 0` residue of
  the `-1/z` rational term) plus the `Re digamma` contour term.

This chunk holds the pointwise layer: analyticity and conjugation symmetry of
the digamma function, the collapse of the shifted kernel to the symmetric pair
`(1/2)(ψ(z/2) + ψ((1-z)/2))` (the rational terms are exactly the recurrence
corrections), its realification on the critical line, the functional-equation
split of the contour integrand on the left line, and the vanishing of the
reflected von Mangoldt term for one-sided `φ`.
-/

namespace Kadiri

open Complex MeasureTheory
open ArithmeticFunction hiding log
open Filter Set Asymptotics
open scoped Topology NNReal ENNReal

noncomputable section

/-! ## Digamma helpers -/

private lemma ne_neg_natCast_of_re_pos {w : ℂ} (hw : 0 < w.re) (m : ℕ) : w ≠ -m := by
  intro h
  rw [h] at hw
  simp only [Complex.neg_re, Complex.natCast_re] at hw
  have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- `Γ` is analytic on the right half-plane. -/
private lemma analyticAt_Gamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ Complex.Gamma w := by
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ Complex.Gamma {z : ℂ | 0 < z.re} := fun z hz =>
    (Complex.differentiableAt_Gamma z fun m =>
      ne_neg_natCast_of_re_pos hz m).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hw)

/-- The digamma function is analytic on the right half-plane. -/
lemma analyticAt_digamma_of_re_pos {w : ℂ} (hw : 0 < w.re) :
    AnalyticAt ℂ digamma w := by
  have hΓ := analyticAt_Gamma_of_re_pos hw
  have hne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero fun m => ne_neg_natCast_of_re_pos hw m
  have h : AnalyticAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) w :=
    hΓ.deriv.div hΓ hne
  have hfun : digamma = fun z => deriv Complex.Gamma z / Complex.Gamma z := by
    funext z
    rw [digamma_def, logDeriv_apply]
  rw [hfun]
  exact h

/-- Conjugation symmetry of the digamma function away from its poles. -/
lemma digamma_conj {z : ℂ} (hz : ∀ n : ℕ, z ≠ -n) :
    digamma ((starRingEnd ℂ) z) = (starRingEnd ℂ) (digamma z) := by
  have hzc : ∀ n : ℕ, (starRingEnd ℂ) z ≠ -n := by
    intro n h
    apply hz n
    have h2 := congrArg (starRingEnd ℂ) h
    simpa using h2
  have h1 := (hasSum_digamma hz).star
  have h2 := hasSum_digamma hzc
  have hfun : (fun n : ℕ => star ((1 : ℂ) / ((n : ℂ) + 1) - 1 / ((n : ℂ) + z))) =
      fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / ((n : ℂ) + (starRingEnd ℂ) z) := by
    funext n
    simp [star_sub, star_add]
  rw [hfun] at h1
  have hkey := h2.unique h1
  have hγ : (starRingEnd ℂ) ((Real.eulerMascheroniConstant : ℝ) : ℂ) =
      ((Real.eulerMascheroniConstant : ℝ) : ℂ) := Complex.conj_ofReal _
  rw [show star (digamma z + ((Real.eulerMascheroniConstant : ℝ) : ℂ)) =
      (starRingEnd ℂ) (digamma z) + (starRingEnd ℂ) ((Real.eulerMascheroniConstant : ℝ) : ℂ)
    from by simp, hγ] at hkey
  exact add_right_cancel hkey

/-! ## The kernel of the functional-equation split -/

/-- The digamma-plus-rational kernel produced by
`neg_logDeriv_zeta_left_eq_reflected`, grouped for the contour shift. -/
def u8LeftKernel (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * digamma (z / 2 + 1) + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)
    + 1 / (z - 1) + 1 / ((1 - z) - 1)

/-- The shifted kernel collapses to the symmetric digamma pair: the rational
terms are exactly the recurrence corrections `digamma (s+1) = digamma s + 1/s`. -/
lemma u8LeftKernel_eq_symm_pair {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hz : ∀ m : ℕ, z / 2 ≠ -m) (hz' : ∀ m : ℕ, (1 - z) / 2 ≠ -m) :
    u8LeftKernel z = (1 / 2 : ℂ) * digamma (z / 2) + (1 / 2 : ℂ) * digamma ((1 - z) / 2) := by
  unfold u8LeftKernel
  rw [digamma_apply_add_one _ hz, digamma_apply_add_one _ hz']
  have h2 : z / 2 ≠ 0 := by simpa using hz 0
  have h2' : (1 - z) / 2 ≠ 0 := by simpa using hz' 0
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    apply hz1
    linear_combination -h
  have hz0' : (1 - z) - 1 ≠ 0 := by
    intro h
    apply hz0
    linear_combination -h
  field_simp
  ring

/-- On the critical line the kernel is the real part of `digamma (z/2)`:
the two digamma arguments are conjugate there. -/
lemma u8LeftKernel_critical_line (t : ℝ) :
    u8LeftKernel ((1 / 2 : ℂ) + (t : ℂ) * I) =
      ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) := by
  set z : ℂ := (1 / 2 : ℂ) + (t : ℂ) * I with hzdef
  have hzre : z.re = 1 / 2 := by simp [hzdef]
  have hhalf : z / 2 = (1 / 4 : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by
    rw [hzdef]; push_cast; ring
  have hhalf' : (1 - z) / 2 = (1 / 4 : ℂ) + ((-(t / 2) : ℝ) : ℂ) * I := by
    rw [hzdef]; push_cast; ring
  have hre_form : ∀ s : ℝ, ((1 / 4 : ℂ) + ((s : ℝ) : ℂ) * I).re = 1 / 4 := by
    intro s
    simp
  have hz2re : (0 : ℝ) < (z / 2).re := by
    rw [hhalf, hre_form]; norm_num
  have hz2re' : (0 : ℝ) < ((1 - z) / 2).re := by
    rw [hhalf', hre_form]; norm_num
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzre
    norm_num at hzre
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hzre
    norm_num at hzre
  rw [u8LeftKernel_eq_symm_pair hz0 hz1 (ne_neg_natCast_of_re_pos hz2re)
    (ne_neg_natCast_of_re_pos hz2re')]
  have hconj : (1 - z) / 2 = (starRingEnd ℂ) (z / 2) := by
    rw [hhalf, hhalf', map_add, map_mul, Complex.conj_I]
    have h14 : (starRingEnd ℂ) (1 / 4 : ℂ) = (1 / 4 : ℂ) := by
      have h := Complex.conj_ofReal (1 / 4 : ℝ)
      push_cast at h
      exact h
    rw [h14, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj, digamma_conj (ne_neg_natCast_of_re_pos hz2re)]
  have hac := Complex.add_conj (digamma (z / 2))
  push_cast at hac ⊢
  linear_combination hac / 2

/-! ## The functional-equation split of the integrand on the left line -/

/-- On `Re = σL ∈ (-2, 0)` the contour integrand splits into the reflected
log-derivative, the kernel, and the `log π` constant, each against the Mellin
data of `φ`. -/
lemma u8ContourIntegrand_eq_split_left {φ : ℝ → ℂ} {σL : ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0) (t : ℝ) :
    u8ContourIntegrand (u8Phi φ) ((σL : ℂ) + (t : ℂ) * I) =
      -(deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
          mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)
        + u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)
        - (Real.log Real.pi : ℂ) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) := by
  set z : ℂ := (σL : ℂ) + (t : ℂ) * I with hzdef
  have hzre : z.re = σL := by simp [hzdef]
  have hz0 : z ≠ 0 := by
    intro h
    rw [h] at hzre
    simp only [Complex.zero_re] at hzre
    exact hσL0.ne' hzre
  have hz1 : z ≠ 1 := by
    intro h
    rw [h] at hzre
    simp only [Complex.one_re] at hzre
    linarith
  have hζz : riemannZeta z ≠ 0 :=
    riemannZeta_ne_zero_of_re_mem_Ioo_neg (by rw [hzre]; exact hσL2) (by rw [hzre]; exact hσL0)
  have hζref : riemannZeta (1 - z) ≠ 0 := by
    refine riemannZeta_ne_zero_of_one_le_re ?_
    rw [Complex.sub_re, Complex.one_re, hzre]
    linarith
  have hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -m := by
    refine ne_neg_natCast_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp only [hzdef]
    simp
    nlinarith [sq_nonneg (2 : ℝ)]
  have hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m := by
    refine ne_neg_natCast_of_re_pos ?_
    rw [Complex.add_re, Complex.one_re, Complex.div_re]
    simp only [Complex.sub_re, Complex.one_re, hzre, Complex.normSq_apply]
    simp
    nlinarith [sq_nonneg (2 : ℝ)]
  have hΓz : zetaGammaFactor z ≠ 0 := by
    unfold zetaGammaFactor
    exact Complex.Gamma_ne_zero (hΓz_diff)
  have hΓref : zetaGammaFactor (1 - z) ≠ 0 := by
    unfold zetaGammaFactor
    exact Complex.Gamma_ne_zero (hΓref_diff)
  have hFE := neg_logDeriv_zeta_left_eq_reflected hz0 hz1 hζz hζref hΓz_diff hΓref_diff hΓz hΓref
  unfold u8ContourIntegrand
  rw [neg_mul_neg, logDeriv_apply, u8Phi_neg_eq_mellin_log hφ_neg]
  unfold u8LeftKernel
  linear_combination (-(mellin (fun u : ℝ => φ (Real.log u)) z)) * hFE

/-! ## The reflected von Mangoldt term vanishes for one-sided test functions -/

lemma u8ReflectedVonMangoldtTerm_eq_zero {φ : ℝ → ℂ}
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0) :
    u8ReflectedVonMangoldtTerm φ = 0 := by
  unfold u8ReflectedVonMangoldtTerm
  have hterm : ∀ n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n) = 0 := by
    intro n
    by_cases hn : 2 ≤ n
    · have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
      rw [hφ_neg (-Real.log n) (by linarith), mul_zero]
    · have h2 : n < 2 := by omega
      interval_cases n
      · simp
      · simp [ArithmeticFunction.vonMangoldt_apply_one]
  simp only [hterm]
  exact tsum_zero

/-! ## The dominated swap for a general constant-real-part exponent -/

/-- Dominated interchange of the von Mangoldt Dirichlet series and a line
integral, for any continuous exponent family of constant real part `c > 1`
against an integrable line factor.  This generalizes the right-line swap to
the reflected series on the left line. -/
lemma u8_dirichlet_integral_tsum_swap {g : ℝ → ℂ} (hg : Integrable g)
    {e : ℝ → ℂ} (he : Continuous e) {c : ℝ} (hc : 1 < c) (hre : ∀ t, (e t).re = c) :
    (∫ t : ℝ, ∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ (e t) * g t) =
      ∑' n : ℕ, ∫ t : ℝ, (Λ n : ℂ) / (n : ℂ) ^ (e t) * g t := by
  have hc0 : c ≠ 0 := (zero_lt_one.trans hc).ne'
  rw [MeasureTheory.integral_tsum]
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using aestronglyMeasurable_const
    · have hbase : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
      have hcont : Continuous fun t : ℝ => (Λ n : ℂ) / (n : ℂ) ^ (e t) := by
        refine continuous_const.div (he.const_cpow (Or.inl hbase)) fun t => ?_
        rw [Complex.cpow_def_of_ne_zero hbase]
        exact Complex.exp_ne_zero _
      exact hcont.aestronglyMeasurable.mul hg.1
  · rw [← lt_top_iff_ne_top]
    have habs : ∀ t : ℝ, ∀ n : ℕ, ‖(n : ℂ) ^ (e t)‖₊ = (n : ℝ≥0) ^ c := by
      intro t n
      simp_rw [← norm_toNNReal]
      rw [norm_natCast_cpow_of_re_ne_zero _ (by rw [hre]; exact hc0), hre]
      simp only [Real.toNNReal_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) c)]
      norm_cast
    have hpoint : ∀ n : ℕ, ∀ t : ℝ,
        ‖(Λ n : ℂ) / (n : ℂ) ^ (e t) * g t‖ₑ =
          ((‖Λ n‖₊ / (n : ℝ≥0) ^ c : ℝ≥0) : ℝ≥0∞) * ‖g t‖ₑ := by
      intro n t
      rw [enorm_mul]
      congr 1
      rw [enorm_eq_nnnorm, nnnorm_div, nnnorm_real, habs t n]
    calc
      ∑' n : ℕ, ∫⁻ t : ℝ, ‖(Λ n : ℂ) / (n : ℂ) ^ (e t) * g t‖ₑ
          = ∑' n : ℕ, ((‖Λ n‖₊ / (n : ℝ≥0) ^ c : ℝ≥0) : ℝ≥0∞) * ∫⁻ t : ℝ, ‖g t‖ₑ := by
            refine tsum_congr fun n => ?_
            simp_rw [hpoint n]
            exact lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (∑' n : ℕ, ((‖Λ n‖₊ / (n : ℝ≥0) ^ c : ℝ≥0) : ℝ≥0∞)) * ∫⁻ t : ℝ, ‖g t‖ₑ :=
            ENNReal.tsum_mul_right
      _ < ⊤ := by
            refine ENNReal.mul_lt_top ?_ ?_
            · rw [lt_top_iff_ne_top, ENNReal.tsum_coe_ne_top_iff_summable_coe]
              push_cast
              refine ((ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (c : ℂ))
                (by simp only [Complex.ofReal_re]; exact hc)).norm).congr fun n => ?_
              rcases eq_or_ne n 0 with rfl | hn
              · simp
              · rw [LSeries.term_of_ne_zero hn, norm_div,
                  norm_natCast_cpow_of_re_ne_zero n
                    (by simp only [Complex.ofReal_re]; exact hc0),
                  Complex.ofReal_re]
                norm_num [Complex.norm_real]
            · rw [← hasFiniteIntegral_iff_enorm]
              exact hg.2

/-! ## The reflected piece integrates to zero -/

/-- Per-`n` value of the reflected series: the inversion lands at `x = 1/n < 1`,
where the multiplicative test function of a one-sided `φ` vanishes. -/
lemma u8_leftline_reflected_term_eq_zero {φ : ℝ → ℂ} {σL : ℝ}
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0)
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σL : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σL) (n : ℕ) :
    (∫ t : ℝ, (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I)) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) = 0 := by
  by_cases hn : 2 ≤ n
  · have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hxpos : (0 : ℝ) < 1 / (n : ℝ) := by
      have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      positivity
    have hlogneg : Real.log (1 / (n : ℝ)) < 0 := by
      rw [one_div, Real.log_inv]
      have : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast hn)
      linarith
    have hcont : ContinuousAt φ (Real.log (1 / (n : ℝ))) := by
      have hev : φ =ᶠ[nhds (Real.log (1 / (n : ℝ)))] fun _ => (0 : ℂ) := by
        filter_upwards [Iio_mem_nhds hlogneg] with y hy
        exact hφ_neg y hy
      exact hev.continuousAt
    have hinv := kadiriVerticalIntegral_mellin_log_eq (φ := φ) (σ := σL)
      (x := 1 / (n : ℝ)) hxpos hMellin hVertical hcont
    rw [hφ_neg _ hlogneg] at hinv
    have hzero : (∫ y : ℝ, ((1 / (n : ℝ) : ℝ) : ℂ) ^ (-((σL : ℂ) + (y : ℂ) * I)) •
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (y : ℂ) * I)) = 0 := by
      have h2π : (1 / (2 * Real.pi) : ℝ) ≠ 0 := by positivity
      exact (smul_eq_zero.mp hinv).resolve_left h2π
    have harg : ((n : ℕ) : ℂ).arg ≠ Real.pi := by
      rw [show ((n : ℕ) : ℂ) = (((n : ℝ) : ℝ) : ℂ) from by push_cast; rfl,
        Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact Ne.symm Real.pi_ne_zero
    have hker : (fun t : ℝ => (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I)) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ => ((Λ n : ℂ) / (n : ℂ)) •
          (((1 / (n : ℝ) : ℝ) : ℂ) ^ (-((σL : ℂ) + (t : ℂ) * I)) •
            mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) := by
      funext t
      have h1n : ((1 / (n : ℝ) : ℝ) : ℂ) = ((n : ℕ) : ℂ)⁻¹ := by
        push_cast
        rw [one_div]
      have hsplit : (1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I) =
          1 + -((σL : ℂ) + (t : ℂ) * I) := by ring
      rw [h1n, inv_cpow _ _ harg, Complex.cpow_neg, inv_inv, hsplit,
        Complex.cpow_add _ _ hn0, Complex.cpow_one, Complex.cpow_neg]
      simp only [smul_eq_mul, div_eq_mul_inv, mul_inv, inv_inv]
      ring
    rw [hker, integral_smul, hzero, smul_zero]
  · have h2 : n < 2 := by omega
    interval_cases n
    · simp
    · simp [ArithmeticFunction.vonMangoldt_apply_one]

/-- The reflected log-derivative piece on the left line integrates to zero for
one-sided `φ`. -/
lemma u8_leftline_reflected_integral_eq_zero {φ : ℝ → ℂ} {σL : ℝ} (hσL0 : σL < 0)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0)
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σL : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σL) :
    (∫ t : ℝ, deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) = 0 := by
  have hre : ∀ t : ℝ, ((1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I)).re = 1 - σL := fun t => by simp
  have hc : 1 < 1 - σL := by linarith
  have hint : (fun t : ℝ => deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
      riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
      mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ => -∑' n : ℕ, (Λ n : ℂ) / (n : ℂ) ^ ((1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I)) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I) := by
    funext t
    have hser := tsum_vonMangoldt_eq (s := (1 : ℂ) - ((σL : ℂ) + (t : ℂ) * I))
      (by rw [hre]; exact hc)
    rw [tsum_mul_right, hser]
    ring
  rw [hint, integral_neg, u8_dirichlet_integral_tsum_swap hVertical
    (by fun_prop) hc hre]
  rw [tsum_congr fun n =>
    u8_leftline_reflected_term_eq_zero hφ_neg hMellin hVertical n]
  simp

/-! ## The constant piece: inversion at `x = 1`, unhalved -/

/-- The bare transform line integral inverts at `x = 1`: since `φ` is required
to be continuous at `0` (forcing `φ 0 = 0` for one-sided `φ`, the only
dischargeable case), the value is the full `φ 0` with no endpoint halving;
the symmetric-convention fork never enters at Lebesgue grade. -/
lemma u8_leftline_const_integral {φ : ℝ → ℂ} {σL : ℝ}
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σL : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σL)
    (hφ0 : ContinuousAt φ 0) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ, mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) = φ 0 := by
  have hinv := kadiriVerticalIntegral_mellin_log_eq (φ := φ) (σ := σL)
    (x := (1 : ℝ)) one_pos hMellin hVertical (by simpa [Real.log_one] using hφ0)
  simp only [Complex.real_smul, smul_eq_mul, Complex.ofReal_one, Real.log_one, one_cpow,
    one_mul] at hinv
  push_cast at hinv
  exact hinv

/-! ## The kernel piece: the strip shift to the critical line -/

private lemma re_div_two (z : ℂ) : (z / 2).re = z.re / 2 := by
  rw [Complex.div_re]
  norm_num [Complex.normSq_apply]
  ring

private lemma im_div_two (z : ℂ) : (z / 2).im = z.im / 2 := by
  rw [Complex.div_im]
  norm_num [Complex.normSq_apply]
  ring

/-- Log growth of the kernel on a substrip of `(-2, 1]`, away from the real
axis: both digamma arguments stay in right half-planes and the rational terms
are bounded. -/
private lemma u8LeftKernel_strip_log_bound {σ₁ σ₂ : ℝ} (h1 : -2 < σ₁) (h2 : σ₂ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, σ₁ ≤ z.re → z.re ≤ σ₂ → 1 ≤ |z.im| →
      ‖u8LeftKernel z‖ ≤ C * Real.log (|z.im| + 2) := by
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_norm_digamma_le_log (a := 1 + σ₁ / 2) (b := 1 + σ₂ / 2)
    (by linarith)
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_norm_digamma_le_log (a := (1 - σ₂) / 2 + 1)
    (b := (1 - σ₁) / 2 + 1) (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨C₁ / 2 + C₂ / 2 + 2 / Real.log 2,
    by have := hC₁; have := hC₂; positivity, fun z hre1 hre2 him => ?_⟩
  have him0 : (0 : ℝ) < |z.im| := lt_of_lt_of_le one_pos him
  have hL2 : Real.log 2 ≤ Real.log (|z.im| + 2) :=
    Real.log_le_log two_pos (by linarith)
  have hL0 : (0 : ℝ) < Real.log (|z.im| + 2) := lt_of_lt_of_le hlog2 hL2
  have harg1 : ‖digamma (z / 2 + 1)‖ ≤ C₁ * Real.log (|z.im| + 2) := by
    have hre : (z / 2 + 1).re = z.re / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re, re_div_two]
    have him' : |(z / 2 + 1).im| ≤ |z.im| := by
      rw [Complex.add_im, Complex.one_im, add_zero, im_div_two, abs_div]
      simp only [abs_two]
      linarith [abs_nonneg z.im]
    refine (hb₁ _ (by rw [hre]; linarith) (by rw [hre]; linarith)).trans ?_
    have := Real.log_le_log (by positivity) (show |(z / 2 + 1).im| + 2 ≤ |z.im| + 2 by linarith)
    nlinarith
  have harg2 : ‖digamma ((1 - z) / 2 + 1)‖ ≤ C₂ * Real.log (|z.im| + 2) := by
    have hre : ((1 - z) / 2 + 1).re = (1 - z.re) / 2 + 1 := by
      rw [Complex.add_re, Complex.one_re, re_div_two, Complex.sub_re, Complex.one_re]
    have him' : |((1 - z) / 2 + 1).im| ≤ |z.im| := by
      rw [Complex.add_im, Complex.one_im, add_zero, im_div_two, Complex.sub_im,
        Complex.one_im, abs_div]
      simp only [abs_two, zero_sub, abs_neg]
      linarith [abs_nonneg z.im]
    refine (hb₂ _ (by rw [hre]; linarith) (by rw [hre]; linarith)).trans ?_
    have := Real.log_le_log (by positivity)
      (show |((1 - z) / 2 + 1).im| + 2 ≤ |z.im| + 2 by linarith)
    nlinarith
  have hrat1 : ‖(1 : ℂ) / (z - 1)‖ ≤ (1 / Real.log 2) * Real.log (|z.im| + 2) := by
    have hzim : |(z - 1).im| = |z.im| := by rw [Complex.sub_im, Complex.one_im, sub_zero]
    have hge : |z.im| ≤ ‖z - 1‖ := hzim ▸ Complex.abs_im_le_norm (z - 1)
    rw [norm_div, norm_one]
    have h1 : 1 / ‖z - 1‖ ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le him0 hge)]
      linarith
    calc 1 / ‖z - 1‖ ≤ 1 := h1
      _ ≤ (1 / Real.log 2) * Real.log (|z.im| + 2) := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2, one_mul]
          exact hL2
  have hrat2 : ‖(1 : ℂ) / ((1 - z) - 1)‖ ≤ (1 / Real.log 2) * Real.log (|z.im| + 2) := by
    have heq : (1 : ℂ) - z - 1 = -z := by ring
    have hzim : |((1 : ℂ) - z - 1).im| = |z.im| := by rw [heq, Complex.neg_im, abs_neg]
    have hge : |z.im| ≤ ‖(1 : ℂ) - z - 1‖ := hzim ▸ Complex.abs_im_le_norm _
    rw [norm_div, norm_one]
    have h1 : 1 / ‖(1 : ℂ) - z - 1‖ ≤ 1 := by
      rw [div_le_one (lt_of_lt_of_le him0 hge)]
      linarith
    calc 1 / ‖(1 : ℂ) - z - 1‖ ≤ 1 := h1
      _ ≤ (1 / Real.log 2) * Real.log (|z.im| + 2) := by
          rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hlog2, one_mul]
          exact hL2
  unfold u8LeftKernel
  calc ‖(1 / 2 : ℂ) * digamma (z / 2 + 1) + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)
        + 1 / (z - 1) + 1 / ((1 - z) - 1)‖
      ≤ ‖(1 / 2 : ℂ) * digamma (z / 2 + 1) + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)
        + 1 / (z - 1)‖ + ‖(1 : ℂ) / ((1 - z) - 1)‖ := norm_add_le _ _
    _ ≤ ‖(1 / 2 : ℂ) * digamma (z / 2 + 1) + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖
        + ‖(1 : ℂ) / (z - 1)‖ + ‖(1 : ℂ) / ((1 - z) - 1)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ ‖(1 / 2 : ℂ) * digamma (z / 2 + 1)‖ + ‖(1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖
        + ‖(1 : ℂ) / (z - 1)‖ + ‖(1 : ℂ) / ((1 - z) - 1)‖ := by
          gcongr
          exact norm_add_le _ _
    _ ≤ (C₁ / 2 + C₂ / 2 + 2 / Real.log 2) * Real.log (|z.im| + 2) := by
          rw [norm_mul, norm_mul]
          have h12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
          rw [h12]
          have hexp : (C₁ / 2 + C₂ / 2 + 2 / Real.log 2) * Real.log (|z.im| + 2) =
              (1 / 2) * (C₁ * Real.log (|z.im| + 2)) +
                (1 / 2) * (C₂ * Real.log (|z.im| + 2)) +
                ((1 / Real.log 2) * Real.log (|z.im| + 2) +
                  (1 / Real.log 2) * Real.log (|z.im| + 2)) := by ring
          rw [hexp]
          linarith [harg1, harg2, hrat1, hrat2]

/-- Continuity of the kernel along a vertical line avoiding `0` and `1`. -/
private lemma continuous_u8LeftKernel_line {σ : ℝ} (hσ2 : -2 < σ) (hσ0 : σ ≠ 0)
    (hσ1 : σ < 1) :
    Continuous fun t : ℝ => u8LeftKernel ((σ : ℂ) + (t : ℂ) * I) := by
  rw [continuous_iff_continuousAt]
  intro t₀
  have hline : Continuous fun t : ℝ => (σ : ℂ) + (t : ℂ) * I := by fun_prop
  have hre : ((σ : ℂ) + (t₀ : ℂ) * I).re = σ := by simp
  have hd1 : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) *
      digamma (((σ : ℂ) + (t : ℂ) * I) / 2 + 1)) t₀ := by
    refine continuousAt_const.mul (ContinuousAt.comp ?_ (by fun_prop))
    refine (analyticAt_digamma_of_re_pos ?_).continuousAt
    rw [Complex.add_re, Complex.one_re, re_div_two, hre]
    linarith
  have hd2 : ContinuousAt (fun t : ℝ => (1 / 2 : ℂ) *
      digamma ((1 - ((σ : ℂ) + (t : ℂ) * I)) / 2 + 1)) t₀ := by
    refine continuousAt_const.mul (ContinuousAt.comp ?_ (by fun_prop))
    refine (analyticAt_digamma_of_re_pos ?_).continuousAt
    rw [Complex.add_re, Complex.one_re, re_div_two, Complex.sub_re, Complex.one_re, hre]
    linarith
  have hd3 : ContinuousAt (fun t : ℝ => (1 : ℂ) / (((σ : ℂ) + (t : ℂ) * I) - 1)) t₀ := by
    refine continuousAt_const.div (by fun_prop) ?_
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.zero_re,
      mul_zero, mul_one, sub_self, add_zero] at h2
    linarith
  have hd4 : ContinuousAt (fun t : ℝ => (1 : ℂ) / ((1 - ((σ : ℂ) + (t : ℂ) * I)) - 1)) t₀ := by
    refine continuousAt_const.div (by fun_prop) ?_
    intro h
    have h2 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.one_re, Complex.zero_re,
      mul_zero, mul_one, sub_self, add_zero] at h2
    apply hσ0
    linarith
  exact ((hd1.add hd2).add hd3).add hd4

/-- Integrability of the kernel against the Mellin data along a vertical line
in the band. -/
private lemma integrable_u8LeftKernel_mul_line {φ : ℝ → ℂ} {σL σ : ℝ}
    (hσL2 : -2 < σL) (hσL : σL ≤ σ) (hσhalf : σ ≤ 1 / 2) (hσ0 : σ ≠ 0)
    (hM_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ 1 / 2 →
      AnalyticAt ℂ (mellin fun u : ℝ => φ (Real.log u)) s)
    {CΦ : ℝ} (hMdec : ∀ x ∈ Set.uIcc σL (1 / 2 : ℝ), ∀ t : ℝ, 1 ≤ |t| →
      ‖mellin (fun u : ℝ => φ (Real.log u)) ((x : ℂ) + (t : ℂ) * I)‖ ≤ CΦ / t ^ 2) :
    Integrable fun t : ℝ => u8LeftKernel ((σ : ℂ) + (t : ℂ) * I) *
      mellin (fun u : ℝ => φ (Real.log u)) ((σ : ℂ) + (t : ℂ) * I) := by
  obtain ⟨C₁, hC₁, hker⟩ := u8LeftKernel_strip_log_bound (σ₁ := σL) (σ₂ := 1 / 2) hσL2
    (by norm_num)
  have hσmem : σ ∈ Set.uIcc σL (1 / 2 : ℝ) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact ⟨hσL, hσhalf⟩
  have hMcont : Continuous fun t : ℝ =>
      mellin (fun u : ℝ => φ (Real.log u)) ((σ : ℂ) + (t : ℂ) * I) := by
    rw [continuous_iff_continuousAt]
    intro t₀
    have houter : ContinuousAt (mellin fun u : ℝ => φ (Real.log u))
        ((σ : ℂ) + (t₀ : ℂ) * I) := by
      refine (hM_an _ ?_ ?_).continuousAt <;> simp <;> linarith
    exact ContinuousAt.comp (g := mellin fun u : ℝ => φ (Real.log u))
      (f := fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) houter (by fun_prop)
  refine integrable_of_norm_le_log_div_sq (C := C₁ * CΦ)
    ((continuous_u8LeftKernel_line (lt_of_lt_of_le hσL2 hσL) hσ0 (by linarith)).mul hMcont)
    fun t ht => ?_
  have hre : ((σ : ℂ) + (t : ℂ) * I).re = σ := by simp
  have him : ((σ : ℂ) + (t : ℂ) * I).im = t := by simp
  have h1 := hker ((σ : ℂ) + (t : ℂ) * I) (by rw [hre]; exact hσL) (by rw [hre]; exact hσhalf)
    (by rw [him]; exact ht)
  rw [him] at h1
  have h2 := hMdec σ hσmem t ht
  rw [norm_mul]
  have hlogpos : (0 : ℝ) < Real.log (|t| + 2) :=
    Real.log_pos (by have := abs_nonneg t; linarith)
  calc ‖u8LeftKernel ((σ : ℂ) + (t : ℂ) * I)‖ *
        ‖mellin (fun u : ℝ => φ (Real.log u)) ((σ : ℂ) + (t : ℂ) * I)‖
      ≤ (C₁ * Real.log (|t| + 2)) * (CΦ / t ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _)
          (mul_nonneg hC₁.le (Real.log_nonneg (by linarith [abs_nonneg t])))
    _ = C₁ * CΦ * Real.log (|t| + 2) / t ^ 2 := by ring

/-- The kernel piece on the left line: the shift to the critical line crosses
the single strip pole at `z = 0` (from the `-1/z` rational term) with residue
`-M 0`, yielding the transform value at `0` plus the real-digamma contour
term. -/
lemma u8_leftline_kernel_integral {φ : ℝ → ℂ} {σL : ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0)
    (hM_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ 1 / 2 →
      AnalyticAt ℂ (mellin fun u : ℝ => φ (Real.log u)) s)
    {CΦ : ℝ} (hMdec : ∀ x ∈ Set.uIcc σL (1 / 2 : ℝ), ∀ t : ℝ, 1 ≤ |t| →
      ‖mellin (fun u : ℝ => φ (Real.log u)) ((x : ℂ) + (t : ℂ) * I)‖ ≤ CΦ / t ^ 2) :
    (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ, u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
          mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) =
      u8Phi φ 0 + u8GammaContourTerm φ := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  -- corner data for the rectangles of height k+1
  have hcre : ∀ k : ℕ, ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ)).re = σL := fun k => by simp
  have hcre' : ∀ k : ℕ, (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)).re = 1 / 2 :=
    fun k => by simp
  have hcim : ∀ k : ℕ, ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ)).im = -((k : ℝ) + 1) :=
    fun k => by simp
  have hcim' : ∀ k : ℕ, (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)).im = (k : ℝ) + 1 :=
    fun k => by simp
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  have hmem0 : ∀ k : ℕ, Rectangle ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)) ∈ nhds (0 : ℂ) := by
    intro k
    rw [rectangle_mem_nhds_iff, Complex.mem_reProdIm, hcre k, hcre' k, hcim k, hcim' k,
      Set.uIoo_of_le (by linarith : σL ≤ (1 / 2 : ℝ)),
      Set.uIoo_of_le (by linarith [hk1 k] : -((k : ℝ) + 1) ≤ (k : ℝ) + 1)]
    refine ⟨⟨by simpa using hσL0, by norm_num⟩, ?_, ?_⟩
    · simp only [Complex.zero_im]
      linarith [hk1 k]
    · simp only [Complex.zero_im]
      exact hk1 k
  -- membership in the rectangle pins the real part to the band
  have hband : ∀ k : ℕ, ∀ s ∈ Rectangle ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)), σL ≤ s.re ∧ s.re ≤ 1 / 2 := by
    intro k s hs
    have h := (Complex.mem_reProdIm.mp hs).1
    rw [hcre k, hcre' k, Set.uIcc_of_le (by linarith : σL ≤ (1 / 2 : ℝ))] at h
    exact ⟨h.1, h.2⟩
  -- the rectangle identity at each height
  have hrect' : ∀ k : ℕ,
      (1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral
          (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
          ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
          (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)) =
        -(mellin (fun u : ℝ => φ (Real.log u)) 0) := by
    intro k
    have hMrect : DifferentiableOn ℂ (mellin fun u : ℝ => φ (Real.log u))
        (Rectangle ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
          (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ))) := fun s hs =>
      ((hM_an s (hband k s hs).1 (hband k s hs).2).differentiableAt).differentiableWithinAt
    refine ResidueTheoremOnRectangleWithSimplePole (p := (0 : ℂ))
      (g := fun s => ((1 / 2 : ℂ) * digamma (s / 2 + 1) +
        (1 / 2 : ℂ) * digamma ((1 - s) / 2 + 1) + 1 / (s - 1)) *
          mellin (fun u : ℝ => φ (Real.log u)) s -
        dslope (mellin fun u : ℝ => φ (Real.log u)) 0 s)
      (by rw [hcre k, hcre' k]; linarith) (by rw [hcim k, hcim' k]; linarith [hk1 k])
      (hmem0 k) ?_ ?_
    · -- holomorphy of the companion
      refine DifferentiableOn.sub ?_ ((differentiableOn_dslope (hmem0 k)).mpr hMrect)
      refine DifferentiableOn.mul (fun s hs => ?_) hMrect
      obtain ⟨hs1, hs2⟩ := hband k s hs
      have hψ1 : DifferentiableAt ℂ (fun u : ℂ => (1 / 2 : ℂ) * digamma (u / 2 + 1)) s := by
        refine (differentiableAt_const _).mul ?_
        refine DifferentiableAt.comp s ((analyticAt_digamma_of_re_pos ?_).differentiableAt)
          (by fun_prop)
        rw [Complex.add_re, Complex.one_re, re_div_two]
        linarith
      have hψ2 : DifferentiableAt ℂ
          (fun u : ℂ => (1 / 2 : ℂ) * digamma ((1 - u) / 2 + 1)) s := by
        refine (differentiableAt_const _).mul ?_
        refine DifferentiableAt.comp s ((analyticAt_digamma_of_re_pos ?_).differentiableAt)
          (by fun_prop)
        rw [Complex.add_re, Complex.one_re, re_div_two, Complex.sub_re, Complex.one_re]
        linarith
      have hrat : DifferentiableAt ℂ (fun u : ℂ => 1 / (u - 1)) s := by
        refine (differentiableAt_const _).div (by fun_prop) ?_
        intro h
        have := congrArg Complex.re h
        simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
        linarith
      exact ((hψ1.add hψ2).add hrat).differentiableWithinAt
    · -- the principal part at 0
      intro s hs
      obtain ⟨hsR, hs0set⟩ := hs
      have hs0 : s ≠ 0 := by
        intro h
        exact hs0set (by rw [h]; rfl)
      simp only [Pi.sub_apply]
      rw [dslope_of_ne _ hs0, slope_def_field]
      have hrat0 : (1 : ℂ) / ((1 - s) - 1) = -(1 / s) := by
        rw [show (1 : ℂ) - s - 1 = -s from by ring, div_neg]
      unfold u8LeftKernel
      rw [hrat0, sub_zero]
      ring
  -- the plain rectangle integrals are constant in the height
  have hrectI : ∀ k : ℕ, RectangleIntegral
      (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
      ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ)) =
      (2 * (Real.pi : ℂ) * I) • (-(mellin (fun u : ℝ => φ (Real.log u)) 0)) := by
    intro k
    have hne : (2 * (Real.pi : ℂ) * I) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero two_ne_zero hπ) hI
    calc RectangleIntegral _ _ _
        = (2 * (Real.pi : ℂ) * I) • ((1 / (2 * (Real.pi : ℂ) * I)) • RectangleIntegral
            (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
            ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
            (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ))) := by
          rw [smul_smul, mul_one_div, div_self hne, one_smul]
      _ = (2 * (Real.pi : ℂ) * I) • (-(mellin (fun u : ℝ => φ (Real.log u)) 0)) := by
          rw [hrect' k]
  -- the contour-pull limit
  have hT : Filter.Tendsto (fun k : ℕ => (k : ℝ) + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hleft : Integrable fun t : ℝ =>
      (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
        ((σL : ℝ) + (t : ℝ) * I) :=
    integrable_u8LeftKernel_mul_line hσL2 le_rfl (by linarith) hσL0.ne hM_an hMdec
  have hright : Integrable fun t : ℝ =>
      (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
        ((1 / 2 : ℝ) + (t : ℝ) * I) :=
    integrable_u8LeftKernel_mul_line hσL2 (by linarith) le_rfl (by norm_num) hM_an hMdec
  -- the edge decay
  obtain ⟨C₁, hC₁, hker⟩ := u8LeftKernel_strip_log_bound (σ₁ := σL) (σ₂ := 1 / 2) hσL2
    (by norm_num)
  have hedge : ∀ y : ℝ, 1 ≤ |y| → ∀ x ∈ Set.uIcc σL (1 / 2 : ℝ),
      ‖(fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
        ((x : ℂ) + (y : ℝ) * I)‖ ≤ 2 * C₁ * CΦ / |y| := by
    intro y hy x hx
    have hre : ((x : ℂ) + (y : ℝ) * I).re = x := by simp
    have him : ((x : ℂ) + (y : ℝ) * I).im = y := by simp
    have hxmem := hx
    rw [Set.uIcc_of_le (by linarith : σL ≤ (1 / 2 : ℝ))] at hxmem
    have h1 := hker ((x : ℂ) + (y : ℝ) * I) (by rw [hre]; exact hxmem.1)
      (by rw [hre]; exact hxmem.2) (by rw [him]; exact hy)
    rw [him] at h1
    have h2 := hMdec x hx y hy
    have hy0 : (0 : ℝ) < |y| := lt_of_lt_of_le one_pos hy
    have hlog_le : Real.log (|y| + 2) ≤ 2 * |y| := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < |y| + 2 by linarith)
      linarith
    simp only [norm_mul]
    calc ‖u8LeftKernel ((x : ℂ) + (y : ℝ) * I)‖ *
          ‖mellin (fun u : ℝ => φ (Real.log u)) ((x : ℂ) + (y : ℝ) * I)‖
        ≤ (C₁ * Real.log (|y| + 2)) * (CΦ / y ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg hC₁.le (Real.log_nonneg (by linarith [abs_nonneg y])))
      _ ≤ (C₁ * (2 * |y|)) * (CΦ / y ^ 2) := by
          have hMnn : (0 : ℝ) ≤ CΦ / y ^ 2 := le_trans (norm_nonneg _) h2
          have : C₁ * Real.log (|y| + 2) ≤ C₁ * (2 * |y|) := by nlinarith
          exact mul_le_mul_of_nonneg_right this hMnn
      _ = 2 * C₁ * CΦ * (|y| / y ^ 2) := by ring
      _ = 2 * C₁ * CΦ / |y| := by
          rw [show |y| / y ^ 2 = 1 / |y| from by
            rw [← sq_abs, sq, div_mul_eq_div_div, div_self hy0.ne']]
          ring
  have hTneg : Filter.Tendsto (fun k : ℕ => -((k : ℝ) + 1)) Filter.atTop Filter.atBot :=
    tendsto_neg_atTop_atBot.comp hT
  have hEdgeBot := tendsto_horizontal_integral_zero_atBot_of_decay
    (F := fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
    (a := σL) (b := (1 / 2 : ℝ)) (C := 2 * C₁ * CΦ) (R := 1)
    (fun y hy x hx => hedge y hy x hx)
  have hEdgeTop := tendsto_horizontal_integral_zero_atTop_of_decay
    (F := fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
    (a := σL) (b := (1 / 2 : ℝ)) (C := 2 * C₁ * CΦ) (R := 1)
    (fun y hy x hx => hedge y hy x hx)
  have hbot := hEdgeBot.comp hTneg
  have htop := hEdgeTop.comp hT
  rw [Function.comp_def] at hbot htop
  simp only [Complex.ofReal_neg] at hbot
  have hseq := rectangleIntegral_tendsto_verticalIntegral_of_seq
    (F := fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
    (σL := σL) (σR := (1 / 2 : ℝ)) (T := fun k : ℕ => (k : ℝ) + 1)
    hT hleft hright hbot htop
  have hconstseq : (fun k : ℕ => RectangleIntegral
      (fun s => u8LeftKernel s * mellin (fun u : ℝ => φ (Real.log u)) s)
      ((σL : ℂ) - I * (((k : ℝ) + 1 : ℝ) : ℂ))
      (((1 / 2 : ℝ) : ℂ) + I * (((k : ℝ) + 1 : ℝ) : ℂ))) =
      fun _ : ℕ => (2 * (Real.pi : ℂ) * I) •
        (-(mellin (fun u : ℝ => φ (Real.log u)) 0)) := funext hrectI
  rw [hconstseq] at hseq
  have hkey := tendsto_nhds_unique hseq tendsto_const_nhds
  -- unfold the two vertical integrals and cancel I, then 2π
  rw [VerticalIntegral, VerticalIntegral] at hkey
  simp only [smul_eq_mul] at hkey
  have hkey2 : (∫ t : ℝ, u8LeftKernel (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ, u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) =
      2 * (Real.pi : ℂ) * (-(mellin (fun u : ℝ => φ (Real.log u)) 0)) := by
    apply mul_left_cancel₀ hI
    linear_combination hkey
  -- evaluate the half-line integral as the Gamma contour term
  have hhalfpt : ∀ t : ℝ, (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) =
      ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    intro t
    norm_num
  have hA : (1 / (2 * (Real.pi : ℂ))) *
      (∫ t : ℝ, u8LeftKernel (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
      u8GammaContourTerm φ := by
    have hcongr : (fun t : ℝ => u8LeftKernel (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) =
        fun t : ℝ => ((digamma (((1 / 2 : ℂ) + (t : ℂ) * I) / 2)).re : ℂ) *
          u8Phi φ (-((1 / 2 : ℂ) + (t : ℂ) * I)) := by
      funext t
      rw [hhalfpt t, u8LeftKernel_critical_line t,
        u8Phi_neg_eq_mellin_log hφ_neg ((1 / 2 : ℂ) + (t : ℂ) * I)]
    rw [hcongr]
    rfl
  have hM0 : mellin (fun u : ℝ => φ (Real.log u)) 0 = u8Phi φ 0 := by
    have h := u8Phi_neg_eq_mellin_log hφ_neg 0
    rw [neg_zero] at h
    exact h.symm
  rw [hM0] at hkey2
  have hkey3 : (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ, u8LeftKernel (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I) *
          mellin (fun u : ℝ => φ (Real.log u)) (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)) -
      (1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ, u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
          mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) =
      -(u8Phi φ 0) := by
    have h := congrArg (fun w => (1 / (2 * (Real.pi : ℂ))) * w) hkey2
    simp only [mul_sub] at h
    rw [show (1 / (2 * (Real.pi : ℂ))) * (2 * (Real.pi : ℂ) * -(u8Phi φ 0)) =
      -(u8Phi φ 0) from by field_simp] at h
    exact h
  linear_combination -hkey3 + hA

/-! ## The endpoint: discharging the left-line split hypothesis -/

/-- Discharge of the left-line functional-equation split hypothesis from Mellin
data: the reflected piece vanishes (one-sidedness), the constant piece inverts
at `x = 1` to the unhalved `-φ(0) log π`, and the kernel piece shifts to the
critical line picking up the `z = 0` kernel value `Φ 0` plus the real-digamma
contour term. -/
theorem u8LeftLineFunctionalEquationSplitHypothesis_of_mellin_data {φ : ℝ → ℂ} {σL : ℝ}
    (hσL2 : -2 < σL) (hσL0 : σL < 0)
    (hφ_neg : ∀ y : ℝ, y < 0 → φ y = 0)
    (hφ0 : ContinuousAt φ 0)
    (hMellin : MellinConvergent (fun u : ℝ => φ (Real.log u)) (σL : ℂ))
    (hVertical : VerticalIntegrable (mellin fun u : ℝ => φ (Real.log u)) σL)
    (hM_an : ∀ s : ℂ, σL ≤ s.re → s.re ≤ 1 / 2 →
      AnalyticAt ℂ (mellin fun u : ℝ => φ (Real.log u)) s)
    {CΦ : ℝ} (hMdec : ∀ x ∈ Set.uIcc σL (1 / 2 : ℝ), ∀ t : ℝ, 1 ≤ |t| →
      ‖mellin (fun u : ℝ => φ (Real.log u)) ((x : ℂ) + (t : ℂ) * I)‖ ≤ CΦ / t ^ 2) :
    U8LeftLineFunctionalEquationSplitHypothesis φ (u8Phi φ) σL := by
  unfold U8LeftLineFunctionalEquationSplitHypothesis u8NormalizedVertical VerticalIntegral
  rw [smul_smul]
  have hpre : 1 / (2 * (Real.pi : ℂ) * I) * I = 1 / (2 * (Real.pi : ℂ)) := by
    rw [div_mul_eq_mul_div, one_mul, mul_comm (2 * (Real.pi : ℂ)) I, ← div_div,
      div_self Complex.I_ne_zero]
  rw [hpre]
  -- split the integrand via the functional equation
  have hsplit : (fun t : ℝ => u8ContourIntegrand (u8Phi φ) ((σL : ℂ) + (t : ℂ) * I)) =
      fun t : ℝ =>
        -(deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)
          + u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
              mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)
          - (Real.log Real.pi : ℂ) *
              mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)) :=
    funext (u8ContourIntegrand_eq_split_left hσL2 hσL0 hφ_neg)
  rw [hsplit]
  -- integrability of the three pieces on the line
  have hrefl_int : Integrable fun t : ℝ =>
      deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I) := by
    have hζan : ∀ t₀ : ℝ, AnalyticAt ℂ riemannZeta (1 - ((σL : ℂ) + (t₀ : ℂ) * I)) := by
      intro t₀
      have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      have hdiff : DifferentiableOn ℂ riemannZeta {s : ℂ | 1 < s.re} := fun s hs =>
        (differentiableAt_riemannZeta (fun h => by
          rw [h] at hs
          simp only [Set.mem_setOf_eq, Complex.one_re, lt_self_iff_false] at hs
          )).differentiableWithinAt
      refine hdiff.analyticAt (hopen.mem_nhds ?_)
      simp only [Set.mem_setOf_eq, Complex.sub_re, Complex.one_re, Complex.add_re,
        Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
        mul_zero, mul_one, sub_self, add_zero]
      linarith
    have hζne : ∀ t₀ : ℝ, riemannZeta (1 - ((σL : ℂ) + (t₀ : ℂ) * I)) ≠ 0 := by
      intro t₀
      refine riemannZeta_ne_zero_of_one_le_re ?_
      simp only [Complex.sub_re, Complex.one_re, Complex.add_re, Complex.ofReal_re,
        Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero, mul_one,
        sub_self, add_zero]
      linarith
    have hcont : Continuous fun t : ℝ =>
        deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) := by
      rw [continuous_iff_continuousAt]
      intro t₀
      have hline : ContinuousAt (fun t : ℝ => 1 - ((σL : ℂ) + (t : ℂ) * I)) t₀ := by fun_prop
      have houter : ContinuousAt (fun z : ℂ => deriv riemannZeta z / riemannZeta z)
          (1 - ((σL : ℂ) + (t₀ : ℂ) * I)) :=
        ((hζan t₀).deriv.div (hζan t₀) (hζne t₀)).continuousAt
      exact ContinuousAt.comp (g := fun z : ℂ => deriv riemannZeta z / riemannZeta z)
        (f := fun t : ℝ => 1 - ((σL : ℂ) + (t : ℂ) * I)) houter hline
    have hbdd : ∀ t : ℝ, ‖deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I))‖ ≤
        ‖deriv riemannZeta ((1 - σL : ℝ) : ℂ) / riemannZeta ((1 - σL : ℝ) : ℂ)‖ := by
      intro t
      have h := dlog_riemannZeta_bdd_on_vertical_lines_generalized (1 - σL) (1 - σL) (-t)
        (by linarith) le_rfl
      have hpt : ((1 - σL : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I = 1 - ((σL : ℂ) + (t : ℂ) * I) := by
        push_cast
        ring
      rw [hpt] at h
      calc ‖deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I))‖
          = ‖-deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I))‖ := by
            rw [neg_div, norm_neg]
        _ ≤ ‖deriv riemannZeta ((1 - σL : ℝ) : ℂ) / riemannZeta ((1 - σL : ℝ) : ℂ)‖ := h
    exact hVertical.bdd_mul hcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  have hkern_int : Integrable fun t : ℝ =>
      u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I) :=
    integrable_u8LeftKernel_mul_line hσL2 le_rfl (by linarith) hσL0.ne hM_an hMdec
  have hconst_int : Integrable fun t : ℝ =>
      (Real.log Real.pi : ℂ) *
        mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I) :=
    hVertical.const_mul _
  -- split the integral
  have hsum_int : Integrable fun t : ℝ =>
      deriv riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - ((σL : ℂ) + (t : ℂ) * I)) *
          mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)
        + u8LeftKernel ((σL : ℂ) + (t : ℂ) * I) *
            mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I) :=
    hrefl_int.add hkern_int
  rw [integral_neg, integral_sub hsum_int hconst_int, integral_add hrefl_int hkern_int]
  -- evaluate the three pieces
  have hA0 := u8_leftline_reflected_integral_eq_zero hσL0 hφ_neg hMellin hVertical
  have hB := u8_leftline_kernel_integral hσL2 hσL0 hφ_neg hM_an hMdec
  have hC := u8_leftline_const_integral hMellin hVertical hφ0
  have hCmul : (1 / (2 * (Real.pi : ℂ))) * ((Real.log Real.pi : ℂ) *
      (∫ t : ℝ, mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I))) =
      (Real.log Real.pi : ℂ) * φ 0 := by
    rw [show (1 / (2 * (Real.pi : ℂ))) * ((Real.log Real.pi : ℂ) *
        (∫ t : ℝ, mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I))) =
      (Real.log Real.pi : ℂ) * ((1 / (2 * (Real.pi : ℂ))) *
        (∫ t : ℝ, mellin (fun u : ℝ => φ (Real.log u)) ((σL : ℂ) + (t : ℂ) * I)))
      from by ring, hC]
  rw [integral_const_mul]
  unfold u8PiLogTerm
  rw [u8ReflectedVonMangoldtTerm_eq_zero hφ_neg]
  simp only [smul_eq_mul]
  linear_combination -hB + hCmul - (1 / (2 * (Real.pi : ℂ))) * hA0

end

end Kadiri
