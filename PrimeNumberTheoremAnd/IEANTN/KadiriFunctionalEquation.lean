import PrimeNumberTheoremAnd.IEANTN.HadamardLogDerivative
import PrimeNumberTheoremAnd.ZetaBounds
import PrimeNumberTheoremAnd.IEANTN.KadiriLaplaceInversion
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.RiemannZeta
import PrimeNumberTheoremAnd.Mathlib.NumberTheory.LSeries.ZetaFunctionalEquation
import PrimeNumberTheoremAnd.Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Functional-equation transport for Kadiri's left vertical line

This file isolates the functional-equation ladder used to move the left
vertical side of Kadiri's contour to right-half-plane zeta data plus elementary
archimedean factors.
-/

namespace Kadiri

open Complex MeasureTheory Filter Asymptotics
open scoped Topology

noncomputable section

private lemma zetaPiFactor_eq_cpow (s : ℂ) :
    zetaPiFactor s = (Real.pi : ℂ) ^ (-(s / 2)) := by
  unfold zetaPiFactor
  rw [Complex.cpow_def_of_ne_zero, Complex.ofReal_log Real.pi_pos.le]
  · ring_nf
  · exact_mod_cast Real.pi_ne_zero

private lemma completedZetaFactor_eq_mul_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hΓhalf : Gamma (s / 2) ≠ 0) :
    completedZetaFactor s = (s * (s - 1) / 2) * completedRiemannZeta s := by
  have hGamma :
      Gamma (s / 2 + 1) = (s / 2) * Gamma (s / 2) := by
    exact Gamma_add_one (s / 2) (div_ne_zero hs0 two_ne_zero)
  rw [completedZetaFactor, zetaPoleFactor, zetaGammaFactor, zetaPiFactor_eq_cpow,
    hGamma, riemannZeta_def_of_ne_zero hs0, Gammaℝ_def]
  field_simp [hs0, hΓhalf]

private lemma gamma_half_avoid_neg_nat_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    ∀ m : ℕ, s / 2 ≠ -m := by
  intro m hm
  cases m with
  | zero =>
      apply hs0
      rw [show s = 2 * (s / 2) by ring, hm]
      ring
  | succ m =>
      have hbad : s / 2 + 1 = -(m : ℂ) := by
        rw [hm]
        norm_num
      exact hΓdiff m hbad

private lemma gamma_half_ne_zero_of_shift {s : ℂ} (hs0 : s ≠ 0)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    Gamma (s / 2) ≠ 0 :=
  Gamma_ne_zero (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff)

/-- The Kadiri completed zeta factor is symmetric under `s ↦ 1 - s`, away
from the endpoints where the reduction to Mathlib's completed zeta has a
removable singularity. -/
theorem completedZetaFactor_one_sub {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓhalf : Gamma (s / 2) ≠ 0) (hΓhalf_ref : Gamma ((1 - s) / 2) ≠ 0) :
    completedZetaFactor (1 - s) = completedZetaFactor s := by
  have h1s0 : 1 - s ≠ 0 := by
    intro h
    apply hs1
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 := by rw [h]; ring
  rw [completedZetaFactor_eq_mul_completedRiemannZeta h1s0 hΓhalf_ref,
    completedZetaFactor_eq_mul_completedRiemannZeta hs0 hΓhalf, completedRiemannZeta_one_sub]
  ring

private lemma differentiableAt_completedZetaFactor {s : ℂ}
    (hs1 : s ≠ 1)
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    DifferentiableAt ℂ completedZetaFactor s := by
  unfold completedZetaFactor zetaPoleFactor zetaPiFactor zetaGammaFactor
  exact (((by fun_prop : DifferentiableAt ℂ (fun s : ℂ => s - 1) s).mul
      (by
        rw [show (fun s : ℂ => Complex.exp (-(s / 2) * (Real.log Real.pi : ℂ))) =
          Complex.exp ∘ (fun s : ℂ => -(s / 2) * (Real.log Real.pi : ℂ)) by rfl]
        exact Complex.differentiableAt_exp.comp s (by fun_prop))).mul
      ((differentiableAt_Gamma _ hΓdiff).comp s (by fun_prop))).mul
    (differentiableAt_riemannZeta hs1)

/-- Logarithmic-derivative transport across the completed-factor symmetry. -/
theorem logDeriv_completedZetaFactor_one_sub {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΓdiff_s : ∀ m : ℕ, s / 2 + 1 ≠ -m)
    (hΓdiff_ref : ∀ m : ℕ, (1 - s) / 2 + 1 ≠ -m) :
    logDeriv completedZetaFactor (1 - s) = -logDeriv completedZetaFactor s := by
  let R : ℂ → ℂ := fun z => 1 - z
  have hΓhalf_s : Gamma (s / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift hs0 hΓdiff_s
  have hΓhalf_ref_s : Gamma ((1 - s) / 2) ≠ 0 :=
    gamma_half_ne_zero_of_shift (by
      intro h
      apply hs1
      calc
        s = 1 - (1 - s) := by ring
        _ = 1 := by rw [h]; ring) hΓdiff_ref
  have hΓhalf_near : ∀ᶠ z in 𝓝 s, Gamma (z / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma (z / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift hs0 hΓdiff_s)).comp
        s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma (z / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_s
  have hΓhalf_ref_near : ∀ᶠ z in 𝓝 s, Gamma ((1 - z) / 2) ≠ 0 := by
    have hdiff : DifferentiableAt ℂ (fun z : ℂ => Gamma ((1 - z) / 2)) s :=
      (differentiableAt_Gamma _ (gamma_half_avoid_neg_nat_of_shift (by
        intro h
        apply hs1
        calc
          s = 1 - (1 - s) := by ring
          _ = 1 := by rw [h]; ring) hΓdiff_ref)).comp s (by fun_prop)
    have hcont : ContinuousAt (fun z : ℂ => Gamma ((1 - z) / 2)) s := hdiff.continuousAt
    exact (hcont.ne_iff_eventually_ne continuousAt_const).mp hΓhalf_ref_s
  have hsym_near :
      (completedZetaFactor ∘ R) =ᶠ[𝓝 s] completedZetaFactor := by
    filter_upwards [isOpen_ne.mem_nhds hs0, isOpen_ne.mem_nhds hs1, hΓhalf_near,
      hΓhalf_ref_near] with z hz0 hz1 hΓz hΓrefz
    exact completedZetaFactor_one_sub hz0 hz1 hΓz hΓrefz
  have hcomp :
      logDeriv (completedZetaFactor ∘ R) s =
        logDeriv completedZetaFactor (R s) * deriv R s := by
    rw [logDeriv_comp]
    · exact differentiableAt_completedZetaFactor
        (by simpa [R] using sub_ne_zero.mpr hs0.symm) hΓdiff_ref
    · dsimp [R]
      fun_prop
  have hderivR : deriv R s = -1 := by
    dsimp [R]
    simp
  have hlog_eq :
      logDeriv (completedZetaFactor ∘ R) s = logDeriv completedZetaFactor s := by
    rw [logDeriv_apply, logDeriv_apply]
    rw [Filter.EventuallyEq.deriv_eq hsym_near]
    exact congrArg (fun z => deriv completedZetaFactor s / z) hsym_near.eq_of_nhds
  rw [hcomp, hderivR] at hlog_eq
  calc
    logDeriv completedZetaFactor (1 - s)
        = -(logDeriv completedZetaFactor (R s) * -1) := by simp [R]
    _ = -logDeriv completedZetaFactor s := by rw [hlog_eq]

/-- Functional-equation transport for `-ζ'/ζ` from the left half-plane to
the reflected right half-plane, with the sign inherited from the derivative of
`s ↦ 1 - s`. -/
theorem neg_logDeriv_zeta_left_eq_reflected {z : ℂ}
    (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hζz : riemannZeta z ≠ 0)
    (hζref : riemannZeta (1 - z) ≠ 0)
    (hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -m)
    (hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m)
    (hΓz : zetaGammaFactor z ≠ 0)
    (hΓref : zetaGammaFactor (1 - z) ≠ 0) :
    -deriv riemannZeta z / riemannZeta z =
      deriv riemannZeta (1 - z) / riemannZeta (1 - z)
        + 1 / (z - 1) + 1 / ((1 - z) - 1)
        - (Real.log Real.pi : ℂ)
        + (1 / 2 : ℂ) * digamma (z / 2 + 1)
        + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
  have href1 : 1 - z ≠ 1 := by
    intro h
    apply hz0
    calc
      z = 1 - (1 - z) := by ring
      _ = 0 := by rw [h]; ring
  have hleft := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv z hz1 hΓz_diff hΓz hζz
  have hright := neg_zeta_logDeriv_eq_neg_completedZeta_logDeriv (1 - z) href1
    hΓref_diff hΓref hζref
  have htransport := logDeriv_completedZetaFactor_one_sub hz0 hz1 hΓz_diff hΓref_diff
  have hnegLD :
      -logDeriv completedZetaFactor z =
        deriv riemannZeta (1 - z) / riemannZeta (1 - z)
          + 1 / ((1 - z) - 1)
          - (1 / 2 : ℂ) * Real.log Real.pi
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1) := by
    rw [htransport] at hright
    have hright' := congrArg Neg.neg hright
    ring_nf at hright' ⊢
    rw [hright']
    ring
  rw [hleft, hnegLD]
  ring

private lemma one_sub_left_verticalLine_eq_reflected (a t : ℝ) :
    1 - verticalLine (-(1 + a)) t = verticalLine (2 + a) (-t) := by
  apply Complex.ext
  · simp [verticalLine]
    ring
  · simp [verticalLine]

/-- The existing right-half-plane bound transported to Kadiri's reflected
left vertical line. -/
theorem reflected_right_logDeriv_bdd_on_left_line {a : ℝ} (ha : 0 < a) :
    ∀ t : ℝ,
      ‖deriv riemannZeta (1 - verticalLine (-(1 + a)) t) /
          riemannZeta (1 - verticalLine (-(1 + a)) t)‖
        ≤ ‖deriv riemannZeta ((2 + a : ℝ) : ℂ) /
            riemannZeta ((2 + a : ℝ) : ℂ)‖ := by
  intro t
  have hσ : 1 < 2 + a := by linarith
  have hbound := dlog_riemannZeta_bdd_on_vertical_lines_generalized
    (2 + a) (2 + a) (-t) hσ (le_refl _)
  rw [one_sub_left_verticalLine_eq_reflected]
  simpa [verticalLine, norm_neg] using hbound

private lemma zetaGammaFactor_ne_zero_of_no_neg_nat {s : ℂ}
    (hΓdiff : ∀ m : ℕ, s / 2 + 1 ≠ -m) :
    zetaGammaFactor s ≠ 0 := by
  unfold zetaGammaFactor
  exact Gamma_ne_zero hΓdiff

private lemma left_verticalLine_ne_zero {a t : ℝ} (ha : 0 < a) :
    verticalLine (-(1 + a)) t ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  simp [verticalLine] at hre
  linarith

private lemma left_verticalLine_ne_one {a t : ℝ} (ha : 0 < a) :
    verticalLine (-(1 + a)) t ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  simp [verticalLine] at hre
  linarith

private lemma left_gamma_arg_ne_neg_nat {a t : ℝ} (ha1 : a < 1) :
    ∀ m : ℕ, verticalLine (-(1 + a)) t / 2 + 1 ≠ -m := by
  intro m hm
  have hpos : 0 < (verticalLine (-(1 + a)) t / 2 + 1).re := by
    simp [verticalLine]
    linarith
  have hre : (verticalLine (-(1 + a)) t / 2 + 1).re = -(m : ℝ) := by
    simpa using congrArg Complex.re hm
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  linarith

private lemma reflected_left_gamma_arg_ne_neg_nat {a t : ℝ} (ha : 0 < a) :
    ∀ m : ℕ, (1 - verticalLine (-(1 + a)) t) / 2 + 1 ≠ -m := by
  intro m hm
  have hpos : 0 < ((1 - verticalLine (-(1 + a)) t) / 2 + 1).re := by
    simp [verticalLine]
    linarith
  have hre : ((1 - verticalLine (-(1 + a)) t) / 2 + 1).re = -(m : ℝ) := by
    simpa using congrArg Complex.re hm
  have hm_nonneg : 0 ≤ (m : ℝ) := by positivity
  linarith

private lemma const_le_log_abs_add_two_mul {K t : ℝ} (hK : 0 ≤ K)
    (ht : 1 ≤ |t|) :
    K ≤ (K / Real.log 3) * Real.log (|t| + 2) := by
  have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have harg_pos : 0 < (3 : ℝ) := by norm_num
  have harg_le : (3 : ℝ) ≤ |t| + 2 := by linarith
  have hlog_le : Real.log 3 ≤ Real.log (|t| + 2) :=
    Real.log_le_log harg_pos harg_le
  calc
    K = (K / Real.log 3) * Real.log 3 := by
      field_simp [hlog3_pos.ne']
    _ ≤ (K / Real.log 3) * Real.log (|t| + 2) := by
      exact mul_le_mul_of_nonneg_left hlog_le (div_nonneg hK hlog3_pos.le)

private lemma one_le_norm_sub_one_of_left_verticalLine {a t : ℝ}
    (ht : 1 ≤ |t|) :
    1 ≤ ‖verticalLine (-(1 + a)) t - 1‖ := by
  have him_le := Complex.abs_im_le_norm (verticalLine (-(1 + a)) t - 1)
  have him_eq : (verticalLine (-(1 + a)) t - 1).im = t := by
    simp [verticalLine]
  rw [him_eq] at him_le
  exact le_trans ht him_le

private lemma one_le_norm_reflected_sub_one_of_left_verticalLine {a t : ℝ}
    (ht : 1 ≤ |t|) :
    1 ≤ ‖(1 - verticalLine (-(1 + a)) t) - 1‖ := by
  have him_le := Complex.abs_im_le_norm ((1 - verticalLine (-(1 + a)) t) - 1)
  have him_eq : ((1 - verticalLine (-(1 + a)) t) - 1).im = -t := by
    simp [verticalLine]
  rw [him_eq, abs_neg] at him_le
  exact le_trans ht him_le

private lemma norm_add_six_le (u v w x y z : ℂ) :
    ‖u + v + w + x + y + z‖ ≤ ‖u‖ + ‖v‖ + ‖w‖ + ‖x‖ + ‖y‖ + ‖z‖ := by
  have h1 : ‖u + v + w + x + y + z‖ ≤ ‖u + v + w + x + y‖ + ‖z‖ :=
    norm_add_le _ _
  have h2 : ‖u + v + w + x + y‖ ≤ ‖u + v + w + x‖ + ‖y‖ :=
    norm_add_le _ _
  have h3 : ‖u + v + w + x‖ ≤ ‖u + v + w‖ + ‖x‖ :=
    norm_add_le _ _
  have h4 : ‖u + v + w‖ ≤ ‖u + v‖ + ‖w‖ :=
    norm_add_le _ _
  have h5 : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
    norm_add_le _ _
  linarith

/-- Functional-equation transport plus the right-half-plane bound gives
logarithmic control of `-ζ'/ζ` on Kadiri's left vertical line.  The digamma
strip estimate is supplied with the sibling-branch theorem's statement shape. -/
theorem left_logDeriv_le_log_of_functional_equation {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1)
    (hdigamma : ∀ {α β : ℝ}, 0 < α →
      ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ w : ℂ, α ≤ w.re → w.re ≤ β →
        ‖digamma (w / 2)‖ ≤ Cψ * Real.log (|w.im| + 2)) :
    ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖-deriv riemannZeta (verticalLine (-(1 + a)) t) /
          riemannZeta (verticalLine (-(1 + a)) t)‖
        ≤ Cζ * Real.log (|t| + 2) := by
  obtain ⟨CψL, hCψLpos, hψL⟩ := hdigamma (α := 1 - a) (β := 1 - a) (by linarith)
  obtain ⟨CψR, hCψRpos, hψR⟩ := hdigamma (α := 4 + a) (β := 4 + a) (by linarith)
  let Cright : ℝ :=
    ‖deriv riemannZeta ((2 + a : ℝ) : ℂ) /
        riemannZeta ((2 + a : ℝ) : ℂ)‖
  let Cζ : ℝ :=
    Cright / Real.log 3 + 1 / Real.log 3 + 1 / Real.log 3
      + ‖-((Real.log Real.pi : ℂ))‖ / Real.log 3
      + (1 / 2 : ℝ) * CψL + (1 / 2 : ℝ) * CψR
  refine ⟨Cζ, ?_, fun t ht => ?_⟩
  · have hlog3_pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
    have hCright_nonneg : 0 ≤ Cright := norm_nonneg _
    have hpi_nonneg : 0 ≤ ‖-((Real.log Real.pi : ℂ))‖ := norm_nonneg _
    positivity
  · set z : ℂ := verticalLine (-(1 + a)) t
    have ht0 : t ≠ 0 := by
      intro h
      rw [h] at ht
      norm_num at ht
    have hz0 : z ≠ 0 := by
      simpa [z] using left_verticalLine_ne_zero (a := a) (t := t) ha
    have hz1 : z ≠ 1 := by
      simpa [z] using left_verticalLine_ne_one (a := a) (t := t) ha
    have hζz : riemannZeta z ≠ 0 := by
      apply riemannZeta_ne_zero_of_re_nonpos_im_ne_zero
      · simp [z, verticalLine]
        linarith
      · simpa [z, verticalLine] using ht0
    have hζref : riemannZeta (1 - z) ≠ 0 := by
      apply riemannZeta_ne_zero_of_one_le_re
      have href : 1 - z = verticalLine (2 + a) (-t) := by
        simpa [z] using one_sub_left_verticalLine_eq_reflected a t
      rw [href]
      simp [verticalLine]
      linarith
    have hΓz_diff : ∀ m : ℕ, z / 2 + 1 ≠ -m := by
      simpa [z] using left_gamma_arg_ne_neg_nat (a := a) (t := t) ha1
    have hΓref_diff : ∀ m : ℕ, (1 - z) / 2 + 1 ≠ -m := by
      simpa [z] using reflected_left_gamma_arg_ne_neg_nat (a := a) (t := t) ha
    have hΓz : zetaGammaFactor z ≠ 0 :=
      zetaGammaFactor_ne_zero_of_no_neg_nat hΓz_diff
    have hΓref : zetaGammaFactor (1 - z) ≠ 0 :=
      zetaGammaFactor_ne_zero_of_no_neg_nat hΓref_diff
    have hFE := neg_logDeriv_zeta_left_eq_reflected hz0 hz1 hζz hζref
      hΓz_diff hΓref_diff hΓz hΓref
    have hright :=
      reflected_right_logDeriv_bdd_on_left_line (a := a) ha t
    have hright_log :
        ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖
          ≤ (Cright / Real.log 3) * Real.log (|t| + 2) := by
      have hright' :
          ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖ ≤ Cright := by
        simpa [z, Cright] using hright
      exact hright'.trans (const_le_log_abs_add_two_mul (norm_nonneg _) ht)
    have hrat1 :
        ‖1 / (z - 1)‖ ≤ (1 / Real.log 3) * Real.log (|t| + 2) := by
      have hden : 1 ≤ ‖z - 1‖ := by
        simpa [z] using one_le_norm_sub_one_of_left_verticalLine (a := a) (t := t) ht
      have hraw : ‖1 / (z - 1)‖ ≤ (1 : ℝ) := by
        rw [norm_div, norm_one]
        simpa [one_div] using inv_le_one_of_one_le₀ hden
      exact hraw.trans (const_le_log_abs_add_two_mul zero_le_one ht)
    have hrat2 :
        ‖1 / ((1 - z) - 1)‖ ≤ (1 / Real.log 3) * Real.log (|t| + 2) := by
      have hden : 1 ≤ ‖(1 - z) - 1‖ := by
        simpa [z] using one_le_norm_reflected_sub_one_of_left_verticalLine
          (a := a) (t := t) ht
      have hraw : ‖1 / ((1 - z) - 1)‖ ≤ (1 : ℝ) := by
        rw [norm_div, norm_one]
        simpa [one_div] using inv_le_one_of_one_le₀ hden
      exact hraw.trans (const_le_log_abs_add_two_mul zero_le_one ht)
    have hpi :
        ‖-((Real.log Real.pi : ℂ))‖
          ≤ (‖-((Real.log Real.pi : ℂ))‖ / Real.log 3)
            * Real.log (|t| + 2) :=
      const_le_log_abs_add_two_mul (norm_nonneg _) ht
    have hψL_raw := hψL (z + 2)
      (by simp [z, verticalLine]; linarith)
      (by simp [z, verticalLine]; linarith)
    have hψL_bound :
        ‖digamma (z / 2 + 1)‖ ≤ CψL * Real.log (|t| + 2) := by
      have harg : (z + 2) / 2 = z / 2 + 1 := by ring
      rw [harg] at hψL_raw
      simpa [harg, z, verticalLine] using hψL_raw
    have hψR_raw := hψR (3 - z)
      (by simp [z, verticalLine]; linarith)
      (by simp [z, verticalLine]; linarith)
    have hψR_bound :
        ‖digamma ((1 - z) / 2 + 1)‖ ≤ CψR * Real.log (|t| + 2) := by
      have harg : (3 - z) / 2 = (1 - z) / 2 + 1 := by ring
      rw [harg] at hψR_raw
      simpa [harg, z, verticalLine, abs_neg] using hψR_raw
    have hψL_term :
        ‖(1 / 2 : ℂ) * digamma (z / 2 + 1)‖
          ≤ ((1 / 2 : ℝ) * CψL) * Real.log (|t| + 2) := by
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [norm_mul, hhalf]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hψL_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have hψR_term :
        ‖(1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖
          ≤ ((1 / 2 : ℝ) * CψR) * Real.log (|t| + 2) := by
      have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
      rw [norm_mul, hhalf]
      simpa [mul_assoc] using
        mul_le_mul_of_nonneg_left hψR_bound (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [hFE]
    calc
      ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z) + 1 / (z - 1)
          + 1 / ((1 - z) - 1) - ↑(Real.log Real.pi)
          + (1 / 2 : ℂ) * digamma (z / 2 + 1)
          + (1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖
        ≤ ‖deriv riemannZeta (1 - z) / riemannZeta (1 - z)‖
            + ‖1 / (z - 1)‖ + ‖1 / ((1 - z) - 1)‖
          + ‖-((Real.log Real.pi : ℂ))‖
          + ‖(1 / 2 : ℂ) * digamma (z / 2 + 1)‖
          + ‖(1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1)‖ := by
          simpa [sub_eq_add_neg, add_assoc] using
            norm_add_six_le
              (deriv riemannZeta (1 - z) / riemannZeta (1 - z))
              (1 / (z - 1))
              (1 / ((1 - z) - 1))
              (-((Real.log Real.pi : ℂ)))
              ((1 / 2 : ℂ) * digamma (z / 2 + 1))
              ((1 / 2 : ℂ) * digamma ((1 - z) / 2 + 1))
      _ ≤ Cζ * Real.log (|t| + 2) := by
          dsimp [Cζ]
          nlinarith [hright_log, hrat1, hrat2, hpi, hψL_term, hψR_term]

private theorem left_vertical_integrable_of_logDeriv_bound {Φ : ℂ → ℂ} {a b : ℝ}
    (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (hlogDeriv : ∃ Cζ : ℝ, 0 ≤ Cζ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖-deriv riemannZeta (verticalLine (-(1 + a)) t) /
          riemannZeta (verticalLine (-(1 + a)) t)‖
        ≤ Cζ * Real.log (|t| + 2))
    (hΦ : ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Φ (-(verticalLine (-(1 + a)) t))‖ ≤ CΦ / t ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖(-deriv riemannZeta (verticalLine (-(1 + a)) t) /
            riemannZeta (verticalLine (-(1 + a)) t)) *
          Φ (-(verticalLine (-(1 + a)) t))‖
        ≤ C * Real.log (|t| + 2) / t ^ 2 := by
  obtain ⟨Cζ, hCζ0, hζbound⟩ := hlogDeriv
  obtain ⟨CΦ, hCΦ0, hΦbound⟩ := hΦ
  refine ⟨Cζ * CΦ, mul_nonneg hCζ0 hCΦ0, fun t ht => ?_⟩
  have ht0 : t ≠ 0 := by
    intro h
    rw [h] at ht
    norm_num at ht
  have ht2_nonneg : 0 ≤ t ^ 2 := sq_nonneg t
  rw [norm_mul]
  calc
    ‖-deriv riemannZeta (verticalLine (-(1 + a)) t) /
          riemannZeta (verticalLine (-(1 + a)) t)‖ *
        ‖Φ (-(verticalLine (-(1 + a)) t))‖
      ≤ (Cζ * Real.log (|t| + 2)) * (CΦ / t ^ 2) := by
        exact mul_le_mul (hζbound t ht) (hΦbound t ht) (norm_nonneg _)
          (mul_nonneg hCζ0 (Real.log_nonneg (by linarith [abs_nonneg t])))
    _ = Cζ * CΦ * Real.log (|t| + 2) / t ^ 2 := by
        field_simp [pow_ne_zero 2 ht0]

/-- Product-tail bound on Kadiri's left vertical line once the functional
equation has supplied logarithmic growth for `-ζ'/ζ`.  This is the integration
surface for the later contour side: the sibling-branch digamma theorem is
passed in by name-shaped hypothesis to produce the logarithmic term, and the
Kadiri test-function decay supplies the `1/t^2` factor. -/
theorem left_vertical_integrable_of_functional_equation {Φ : ℂ → ℂ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hΦ : ∃ CΦ : ℝ, 0 ≤ CΦ ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖Φ (-(verticalLine (-(1 + a)) t))‖ ≤ CΦ / t ^ 2)
    (hdigamma : ∀ {α β : ℝ}, 0 < α →
      ∃ Cψ : ℝ, 0 < Cψ ∧ ∀ w : ℂ, α ≤ w.re → w.re ≤ β →
        ‖digamma (w / 2)‖ ≤ Cψ * Real.log (|w.im| + 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ |t| →
      ‖(-deriv riemannZeta (verticalLine (-(1 + a)) t) /
            riemannZeta (verticalLine (-(1 + a)) t)) *
          Φ (-(verticalLine (-(1 + a)) t))‖
        ≤ C * Real.log (|t| + 2) / t ^ 2 := by
  exact left_vertical_integrable_of_logDeriv_bound ha hab ha1
    (left_logDeriv_le_log_of_functional_equation ha ha1 hdigamma) hΦ

end

end Kadiri
