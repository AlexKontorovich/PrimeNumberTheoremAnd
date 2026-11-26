import TernaryGoldbach.Prelim.PNTMertens
import RSBounds.BacklundCenterNumericsBase
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.TrapezoidalRule
import Mathlib.Tactic

/-!
# Convexity and quadrature for Backlund's right semicircle

Backlund (1918), p. 373, uses the convexity of
`θ ↦ log ζ(5/4 + 1.32 cos θ)` to bound its integral by trapezoids.
The logarithmic Dirichlet series is reused from the existing Mertens module;
all coefficients are nonnegative. The quadrature theorem below only requires
convexity and continuity, not numerical differentiation or a remainder bound.
-/

open Real Complex Set Filter MeasureTheory Finset ArithmeticFunction
open scoped Topology BigOperators

namespace TernaryGoldbach.RSBounds.BacklundRightArc

noncomputable def logZeta (σ : ℝ) : ℝ := Real.log ‖riemannZeta (σ : ℂ)‖
noncomputable def logCoeff (n : ℕ) : ℝ := Λ n / Real.log n

lemma logCoeff_nonneg (n : ℕ) : 0 ≤ logCoeff n :=
  div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

lemma logCoeff_le_one (n : ℕ) : logCoeff n ≤ 1 := by
  by_cases hn : n ≤ 1
  · interval_cases n <;> norm_num [logCoeff]
  have hl : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  exact (div_le_one hl).mpr vonMangoldt_le_log

lemma summable_logCoeff {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => logCoeff n * (n : ℝ) ^ (-σ)) := by
  apply Summable.of_nonneg_of_le (fun n => mul_nonneg (logCoeff_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    (fun n => ?_) (Real.summable_nat_rpow.mpr (show -σ < -1 by linarith))
  exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) (logCoeff_le_one n)

lemma logZeta_eq_tsum {σ : ℝ} (hσ : 1 < σ) :
    logZeta σ = ∑' n : ℕ, logCoeff n * (n : ℝ) ^ (-σ) := by
  have he : riemannZeta (σ : ℂ) = ((riemannZeta (σ : ℂ)).re : ℂ) := by
    apply Complex.ext <;> simp [riemannZeta_im_eq_zero_of_one_lt hσ]
  unfold logZeta
  rw [he, Complex.norm_of_nonneg (riemannZeta_re_pos_of_one_lt hσ).le,
    TernaryGoldbach.PNTMertens.log_zeta_eq_sum σ hσ]
  apply tsum_congr
  intro n
  rw [logCoeff, Real.rpow_neg (Nat.cast_nonneg n)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma logZeta_nonneg {σ : ℝ} (hσ : 1 < σ) : 0 ≤ logZeta σ := by
  rw [logZeta_eq_tsum hσ]
  exact tsum_nonneg (fun n => mul_nonneg (logCoeff_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))

lemma convexOn_logZeta : ConvexOn ℝ (Ioi 1) logZeta := by
  refine ⟨convex_Ioi 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : 1 < a • x + b • y := (convex_Ioi 1) hx hy ha hb hab
  rw [logZeta_eq_tsum hx, logZeta_eq_tsum hy, logZeta_eq_tsum hz]
  simp only [smul_eq_mul]
  rw [← tsum_mul_left, ← tsum_mul_left,
    ← Summable.tsum_add ((summable_logCoeff hx).mul_left a) ((summable_logCoeff hy).mul_left b)]
  apply (summable_logCoeff hz).tsum_le_tsum _
    (((summable_logCoeff hx).mul_left a).add ((summable_logCoeff hy).mul_left b))
  intro n
  by_cases hn : n = 0
  · simp [hn, logCoeff]
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := convexOn_exp.2 (mem_univ (-x * Real.log n))
    (mem_univ (-y * Real.log n)) ha hb hab
  simp only [smul_eq_mul] at hh ⊢
  rw [Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0, Real.rpow_def_of_pos hn0]
  have he : Real.log (n : ℝ) * -(a * x + b * y) =
      a * (-x * Real.log n) + b * (-y * Real.log n) := by ring
  rw [he, show Real.log (n : ℝ) * -x = -x * Real.log n by ring,
    show Real.log (n : ℝ) * -y = -y * Real.log n by ring]
  have hm := mul_le_mul_of_nonneg_left hh (logCoeff_nonneg n)
  nlinarith [hm]

lemma antitoneOn_logZeta : AntitoneOn logZeta (Ioi 1) := by
  intro x hx y hy hxy
  rw [logZeta_eq_tsum hx, logZeta_eq_tsum hy]
  apply (summable_logCoeff hy).tsum_le_tsum _ (summable_logCoeff hx)
  intro n
  by_cases hn : n = 0
  · simp [hn, logCoeff]
  apply mul_le_mul_of_nonneg_left _ (logCoeff_nonneg n)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)) (by linarith)

lemma continuousOn_logZeta : ContinuousOn logZeta (Ioi 1) := by
  intro σ hσ
  change 1 < σ at hσ
  unfold logZeta
  apply ContinuousWithinAt.log
  · apply ContinuousWithinAt.norm
    exact ((differentiableAt_riemannZeta (by
      intro he
      have hh := congrArg Complex.re he
      simp only [Complex.ofReal_re, Complex.one_re] at hh
      linarith [hσ])).continuousAt.comp Complex.continuous_ofReal.continuousAt).continuousWithinAt
  · exact norm_ne_zero_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ))

noncomputable def arcFunction (θ : ℝ) : ℝ := logZeta (5 / 4 + (33 / 25) * Real.cos θ)

lemma arc_sigma_gt_one {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) :
    1 < 5 / 4 + (33 / 25) * Real.cos θ := by
  have hc := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hθ.1], hθ.2⟩
  linarith

lemma arcFunction_nonneg {θ : ℝ} (hθ : θ ∈ Icc 0 (Real.pi / 2)) : 0 ≤ arcFunction θ :=
  logZeta_nonneg (arc_sigma_gt_one hθ)

lemma convexOn_arcFunction : ConvexOn ℝ (Icc 0 (Real.pi / 2)) arcFunction := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy a b ha hb hab
  have hz : a • x + b • y ∈ Icc 0 (Real.pi / 2) := (convex_Icc _ _) hx hy ha hb hab
  have hc := strictConcaveOn_cos_Icc.concaveOn.2
    (show x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hx.1, hx.2, Real.pi_pos])
    (show y ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) by constructor <;> linarith [hy.1, hy.2, Real.pi_pos])
    ha hb hab
  have hsx := arc_sigma_gt_one hx
  have hsy := arc_sigma_gt_one hy
  have hsz := arc_sigma_gt_one hz
  have hsmix : 1 < a * (5 / 4 + (33 / 25) * Real.cos x) +
      b * (5 / 4 + (33 / 25) * Real.cos y) := by
    have hh := (convex_Ioi (1 : ℝ)) hsx hsy ha hb hab
    simpa only [smul_eq_mul, Set.mem_Ioi] using hh
  have hsm : a * (5 / 4 + (33 / 25) * Real.cos x) +
      b * (5 / 4 + (33 / 25) * Real.cos y) ≤
      5 / 4 + (33 / 25) * Real.cos (a • x + b • y) := by
    simp only [smul_eq_mul] at hc ⊢
    nlinarith
  have ha1 := antitoneOn_logZeta hsmix hsz hsm
  have ha2 := convexOn_logZeta.2 hsx hsy ha hb hab
  simpa only [arcFunction, smul_eq_mul] using ha1.trans ha2

lemma continuousOn_arcFunction : ContinuousOn arcFunction (Icc 0 (Real.pi / 2)) :=
  continuousOn_logZeta.comp (by fun_prop) (fun _ hx => arc_sigma_gt_one hx)

/-- The convex trapezoid bound on a single unit interval. -/
lemma integral_unit_le_trapezoid {f : ℝ → ℝ} {a : ℝ}
    (hf : ConvexOn ℝ (Icc a (a + 1)) f) (hc : ContinuousOn f (Icc a (a + 1))) :
    (∫ x in a..a + 1, f x) ≤ (f a + f (a + 1)) / 2 := by
  let L : ℝ → ℝ := fun x => (a + 1 - x) * f a + (x - a) * f (a + 1)
  have hL : Continuous L := by dsimp [L]; fun_prop
  have hpoint : ∀ x ∈ Icc a (a + 1), f x ≤ L x := by
    intro x hx
    have hh := hf.2 (show a ∈ Icc a (a + 1) by constructor <;> linarith)
      (show a + 1 ∈ Icc a (a + 1) by constructor <;> linarith)
      (show 0 ≤ a + 1 - x by linarith [hx.2]) (show 0 ≤ x - a by linarith [hx.1])
      (show (a + 1 - x) + (x - a) = 1 by ring)
    simpa only [smul_eq_mul, show (a + 1 - x) * a + (x - a) * (a + 1) = x by ring] using hh
  have hi := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a ≤ a + 1)
    (hc.intervalIntegrable_of_Icc (by linarith)) (hL.intervalIntegrable a (a + 1)) hpoint
  have he : (∫ x in a..a + 1, L x) = (f a + f (a + 1)) / 2 := by
    dsimp [L]
    rw [intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop) (by apply Continuous.intervalIntegrable; fun_prop),
      intervalIntegral.integral_const, intervalIntegral.integral_const,
      integral_id]
    simp only [smul_eq_mul]
    ring
  exact hi.trans_eq he

/-- Uniform trapezoids bound the integral of any continuous convex function. -/
lemma integral_nat_le_trapezoids {f : ℝ → ℝ} {N : ℕ}
    (hf : ConvexOn ℝ (Icc 0 (N : ℝ)) f) (hc : ContinuousOn f (Icc 0 (N : ℝ))) :
    (∫ x in (0 : ℝ)..N, f x) ≤
      ∑ i ∈ Finset.range N, (f i + f ((i : ℝ) + 1)) / 2 := by
  have hi (i : ℕ) (hi : i < N) : Icc (i : ℝ) (i + 1) ⊆ Icc 0 (N : ℝ) := by
    apply Set.Icc_subset_Icc (Nat.cast_nonneg i)
    exact_mod_cast (show i + 1 ≤ N by omega)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
    (a := fun i : ℕ => (i : ℝ)) (n := N) (fun i hi' =>
      (hc.mono (by simpa only [Nat.cast_add, Nat.cast_one] using hi i hi')).intervalIntegrable_of_Icc
        (by exact_mod_cast Nat.le_succ i))
  simp only [Nat.cast_zero] at hsum
  rw [← hsum]
  apply Finset.sum_le_sum
  intro i hi'
  simpa only [Nat.cast_add, Nat.cast_one] using integral_unit_le_trapezoid
    (hf.subset (hi i (Finset.mem_range.mp hi')) (convex_Icc _ _))
    (hc.mono (hi i (Finset.mem_range.mp hi')))

/-- The sixteen-panel trapezoidal upper bound, normalized as in Backlund. -/
lemma right_arc_le_samples :
    (∫ θ in (0 : ℝ)..Real.pi / 2, arcFunction θ) / (2 * Real.pi) ≤
      (∑ i ∈ Finset.range 16,
        (arcFunction (Real.pi / 32 * i) + arcFunction (Real.pi / 32 * ((i : ℝ) + 1))) / 2) / 64 := by
  let F : ℝ → ℝ := fun x => arcFunction (Real.pi / 32 * x)
  have hmem {x : ℝ} (hx : x ∈ Icc 0 (16 : ℝ)) : Real.pi / 32 * x ∈ Icc 0 (Real.pi / 2) := by
    rcases hx with ⟨hx0, hx16⟩
    constructor
    · exact mul_nonneg (by positivity) hx0
    · nlinarith [mul_le_mul_of_nonneg_left hx16 Real.pi_pos.le]
  have hF : ConvexOn ℝ (Icc 0 (16 : ℝ)) F := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := convexOn_arcFunction.2 (hmem hx) (hmem hy) ha hb hab
    simpa only [F, smul_eq_mul, mul_add, mul_assoc, mul_left_comm] using hh
  have hc : ContinuousOn F (Icc 0 (16 : ℝ)) :=
    continuousOn_arcFunction.comp (by fun_prop) (fun _ hx => hmem hx)
  have hi := integral_nat_le_trapezoids (N := 16) hF hc
  have he := intervalIntegral.smul_integral_comp_mul_left (a := 0) (b := 16) arcFunction (Real.pi / 32)
  norm_num only [smul_eq_mul, mul_zero, show Real.pi / 32 * 16 = Real.pi / 2 by ring] at he
  rw [← he]
  have hh := div_le_div_of_nonneg_right hi (show (0 : ℝ) ≤ 64 by norm_num)
  convert hh using 1 <;> dsimp [F] <;> field_simp [Real.pi_ne_zero] <;> ring

end TernaryGoldbach.RSBounds.BacklundRightArc
