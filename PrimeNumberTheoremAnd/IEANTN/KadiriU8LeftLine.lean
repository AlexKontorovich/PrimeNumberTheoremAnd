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

end

end Kadiri
