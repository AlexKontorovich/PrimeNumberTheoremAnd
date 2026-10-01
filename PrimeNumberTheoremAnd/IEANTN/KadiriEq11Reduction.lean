import Mathlib.Analysis.Normed.Group.Tannery
import PrimeNumberTheoremAnd.LaplaceInversion
import PrimeNumberTheoremAnd.IEANTN.KadiriEq11Base
import PrimeNumberTheoremAnd.IEANTN.KadiriSupport

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology

noncomputable section

private lemma kadiri_laplace_source_integrable_of_decay {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Integrable
      (fun y : ℝ =>
        exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) :=
  kadiri_laplace_neg_line_weight_integrable_of_continuous hφ.continuous
    (by linarith) (by linarith) hφ_decay

private lemma kadiri_weighted_source_bounded_of_decay {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ)
    {b : ℝ} (_hb : 0 < b)
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ y : ℝ, ‖exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * ψ y‖ ≤ B :=
  kadiri_laplace_neg_line_weight_bounded_of_continuous hψ_cont
    (by linarith) (by linarith) hψ_decay

private lemma kadiri_weighted_source_differentiable {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {a : ℝ} :
    Differentiable ℝ
      (fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y) :=
  ((laplaceKernel_contDiff_paren (((-(1 + a) : ℝ) : ℂ))).differentiable (by norm_num)).mul
    (hφ.differentiable (by norm_num))

private lemma kadiri_weighted_source_deriv {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {a y : ℝ} :
    deriv (fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))) * φ x) y =
      exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) *
        (((1 + a : ℝ) : ℂ) * φ y + deriv φ y) := by
  rw [kadiri_laplace_neg_line_weight_deriv hφ (-(1 + a)) y]
  push_cast
  ring

private lemma kadiri_weighted_source_deriv_bound_of_decay {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ y : ℝ,
        ‖deriv (fun x : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (x : ℂ))) * φ x) y‖ ≤ D :=
  kadiri_laplace_neg_line_weight_deriv_bounded hφ (by linarith) (by linarith)
    hφ_decay hφ'_decay

private def kadiriNegLine (a : ℝ) (t : ℝ) : ℂ :=
  ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)

private lemma kadiriNegLine_re (a t : ℝ) :
    (kadiriNegLine a t).re = -(1 + a) := by
  simp [kadiriNegLine]

private def kadiriPhiNegLine (φ : ℝ → ℂ) (a : ℝ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, φ y * exp (-(kadiriNegLine a t * (y : ℂ)))

private lemma kadiri_phi_neg_line_continuous {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    Continuous (kadiriPhiNegLine φ a) := by
  have hsource := kadiri_laplace_source_integrable_of_decay
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  convert
    continuous_laplaceIntegral_verticalLine_add_of_integrable
      (φ := φ) (σ := (-(1 + a) : ℝ)) hφ.continuous hsource
    using 2
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  simp only [kadiriNegLine, ofReal_add, ofReal_neg, ofReal_one]

/-- Collapse the von Mangoldt Dirichlet series on the negative Mellin line. -/
lemma tsum_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    (∑' n : ℕ,
        (Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
      -deriv riemannZeta (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) /
        riemannZeta (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
  have hs : 1 < (((1 + a : ℝ) : ℂ) - (t : ℂ) * I).re := by
    simp
    linarith
  rw [← tsum_vonMangoldt_eq hs]
  refine tsum_congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hline :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
      ring
    rw [hline, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Summable fun n : ℕ =>
      (Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
  have hs : 1 < (((1 + a : ℝ) : ℂ) - (t : ℂ) * I).re := by
    simp
    linarith
  refine (summable_vonMangoldt_cpow hs).congr fun n ↦ ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hline :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) - (t : ℂ) * I) := by
      ring
    rw [hline, Complex.cpow_neg, div_eq_mul_inv]

private lemma summable_norm_vonMangoldt_neg_mellin_line {a : ℝ} (ha : 0 < a) (t : ℝ) :
    Summable fun n : ℕ =>
      ‖(Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
  (summable_vonMangoldt_neg_mellin_line ha t).norm

private lemma norm_vonMangoldt_neg_mellin_line_eq_real (a t : ℝ) (n : ℕ) :
    ‖(Λ n : ℂ) * (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)‖ =
      ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    rw [norm_mul, norm_div]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    rw [Complex.norm_natCast_cpow_of_pos hn]
    have hleft :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I).re = -(1 + a) := by
      simp
    have hright : (((1 + a : ℝ) : ℂ)).re = 1 + a := by simp
    rw [hleft, hright, Real.rpow_neg hnpos.le, div_eq_mul_inv]

private lemma summable_norm_vonMangoldt_real_line {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ =>
      ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  have hs : 1 < (((1 + a : ℝ) : ℂ)).re := by
    simp
    linarith
  exact summable_norm_vonMangoldt_cpow hs

private lemma kadiri_eq11_truncated_mellin_swap_core {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (T : ℝ) :
    HasSum
      (fun n : ℕ =>
        ∫ t in (-T)..T,
          ((Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            kadiriPhiNegLine φ a t)
      (∫ t in (-T)..T,
        (∑' n : ℕ,
            (Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
          kadiriPhiNegLine φ a t) := by
  have hPhi_cont := kadiri_phi_neg_line_continuous
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hPhi_cont_on : ContinuousOn (kadiriPhiNegLine φ a) (Set.uIcc (-T) T) :=
    hPhi_cont.continuousOn
  obtain ⟨C0, hC0⟩ := isCompact_uIcc.exists_bound_of_continuousOn hPhi_cont_on
  let C : ℝ := max C0 0
  have hC_nonneg : 0 ≤ C := le_max_right _ _
  have hC : ∀ y ∈ Set.uIcc (-T) T, ‖kadiriPhiNegLine φ a y‖ ≤ C := by
    intro y hy
    exact (hC0 y hy).trans (le_max_left _ _)
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume)
    (F := fun n t =>
      ((Λ n : ℂ) *
          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        kadiriPhiNegLine φ a t)
    (f := fun t =>
      (∑' n : ℕ,
          (Λ n : ℂ) *
            (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        kadiriPhiNegLine φ a t)
    (bound := fun n _t =>
      C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖) ?_ ?_ ?_ ?_ ?_
  · intro n
    by_cases hn : n = 0
    · simpa [hn] using
        (aestronglyMeasurable_const :
          AEStronglyMeasurable (fun _ : ℝ => (0 : ℂ))
            (volume.restrict (Set.uIoc (-T) T)))
    · have hpow : Continuous fun t : ℝ =>
          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
        refine Continuous.const_cpow (by fun_prop) ?_
        exact Or.inl (Nat.cast_ne_zero.mpr hn)
      exact ((continuous_const.mul hpow).mul hPhi_cont).aestronglyMeasurable
  · intro n
    filter_upwards with y hy
    calc
      ‖((Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (y : ℂ) * I)) *
            kadiriPhiNegLine φ a y‖
          = ‖(Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (y : ℂ) * I)‖ *
            ‖kadiriPhiNegLine φ a y‖ := norm_mul _ _
      _ = ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ *
            ‖kadiriPhiNegLine φ a y‖ := by
          rw [norm_vonMangoldt_neg_mellin_line_eq_real]
      _ ≤ ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ * C := by
          exact mul_le_mul_of_nonneg_left
            (hC y (Set.uIoc_subset_uIcc hy)) (norm_nonneg _)
      _ = C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
          ring
  · filter_upwards with y hy
    exact (summable_norm_vonMangoldt_real_line ha).mul_left C
  · exact intervalIntegrable_const
  · filter_upwards with y hy
    exact (summable_vonMangoldt_neg_mellin_line ha y).hasSum.mul_right
      (kadiriPhiNegLine φ a y)

private lemma kadiri_eq11_truncated_mellin_swap {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (T : ℝ) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (∑' n : ℕ,
        (Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
  intro Φ
  have hcore := kadiri_eq11_truncated_mellin_swap_core
    (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab T
  have hscaled :=
    congrArg (fun z : ℂ => (1 / (2 * (Real.pi : ℂ))) * z) hcore.tsum_eq
  calc
    (∑' n : ℕ,
        (Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
        = (1 / (2 * (Real.pi : ℂ))) *
            (∑' n : ℕ,
              ∫ t in (-T)..T,
                ((Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                  kadiriPhiNegLine φ a t) := by
          rw [← tsum_mul_left]
          refine tsum_congr fun n ↦ ?_
          calc
            (Λ n : ℂ) *
                ((1 / (2 * (Real.pi : ℂ))) *
                  ∫ t in (-T)..T,
                    Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
                = (1 / (2 * (Real.pi : ℂ))) *
                    ((Λ n : ℂ) *
                      ∫ t in (-T)..T,
                        Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                          (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
                  ring
            _ = (1 / (2 * (Real.pi : ℂ))) *
                ∫ t in (-T)..T,
                  (Λ n : ℂ) *
                    (Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
                  rw [intervalIntegral.integral_const_mul]
            _ = (1 / (2 * (Real.pi : ℂ))) *
                ∫ t in (-T)..T,
                  ((Λ n : ℂ) *
                      (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                    kadiriPhiNegLine φ a t := by
                  congr 1
                  apply intervalIntegral.integral_congr
                  intro t ht
                  simp [Φ, kadiriPhiNegLine, kadiriNegLine]
                  ring
    _ = (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            kadiriPhiNegLine φ a t := hscaled
    _ = (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) := by
          congr 1
          apply intervalIntegral.integral_congr
          intro t ht
          simp [Φ, kadiriPhiNegLine, kadiriNegLine]

private lemma fourierInvTrunc_uniform_bound_of_deriv_bound
    {g : ℝ → ℂ} {B D : ℝ}
    (hg_int : Integrable g) (hgdiff : Differentiable ℝ g)
    (hg_bound : ∀ x : ℝ, ‖g x‖ ≤ B)
    (hD : 0 ≤ D) (hg_deriv : ∀ x : ℝ, ‖deriv g x‖ ≤ D) :
    ∀ᶠ T in atTop, ∀ x : ℝ,
      ‖fourierInvTrunc (FourierTransform.fourier g) x T‖ ≤
        2 * B + (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) +
          (1 / Real.pi) * ∫ u : ℝ, ‖g u‖ := by
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ),
    eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two (R := (1 : ℝ)) zero_lt_one]
    with T hT hmass x
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (g (x - u) - g x))
      volume (-(1 : ℝ)) (1 : ℝ) := by
    exact intervalIntegrable_local_quotient_of_differentiableAt
      (E := ℂ) (f := g) (x := x) (R := (1 : ℝ)) zero_lt_one
      (hgdiff.continuous.continuousOn) (hgdiff.differentiableAt)
  have herr := intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
    (E := ℂ) (f := g) (x := x) (R := (1 : ℝ)) hq T
  have hlocal := sin_div_error_interval_bound (g := g) (D := D) (x := x) (T := T)
    hD hgdiff hg_deriv
  have hcore := norm_fourierInvTrunc_le_of_windowed_sin_div_bounds
    (E := ℂ) (f := g) hg_int (x := x) (T := T) (R := (1 : ℝ))
    (B := B) (L := (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))))
    (M := (2 : ℝ)) hT zero_lt_one (hg_bound x) hmass herr hlocal
  simpa [mul_assoc] using hcore

private lemma laplaceIntegralCpowTrunc_norm_bound_of_fourier
    {φ : ℝ → ℂ} {sigma x T C : ℝ} (hx : 0 < x)
    (hC : ‖fourierInvTrunc
      (FourierTransform.fourier
        (fun y : ℝ => Complex.exp (-((sigma : ℂ) * (y : ℂ))) * φ y))
      (Real.log x) T‖ ≤ C) :
    ‖laplaceIntegralCpowTrunc φ sigma x T‖ ≤ Real.exp (sigma * Real.log x) * C := by
  rw [laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc sigma φ hx T]
  rw [laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc]
  rw [norm_smul, norm_exp]
  have hre : ((sigma : ℂ) * (Real.log x : ℂ)).re = sigma * Real.log x := by
    norm_num [Complex.mul_re]
  rw [hre]
  simpa [smul_eq_mul] using mul_le_mul_of_nonneg_left hC (Real.exp_nonneg _)

private lemma norm_exp_neg_log_eq_norm_nat_cpow {a : ℝ} {n : ℕ} (hn : 0 < n) :
    Real.exp ((-(1 + a)) * Real.log n) =
      ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
  rw [Complex.norm_natCast_cpow_of_pos hn]
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
  congr 1
  simp
  ring

private lemma kadiri_eq11_tannery_bound {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ C : ℝ,
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤
          C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
  let g : ℝ → ℂ := fun y : ℝ =>
    exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y
  obtain ⟨B, _hB_nonneg, hB⟩ :=
    kadiri_weighted_source_bounded_of_decay
      (ψ := φ) hφ.continuous (b := b) hb hφ_decay (a := a) ha hab
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_weighted_source_deriv_bound_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab
  let C : ℝ :=
    2 * B + (D / Real.pi) * (volume.real (Set.Ioc (-(1 : ℝ)) (1 : ℝ))) +
      (1 / Real.pi) * ∫ u : ℝ, ‖g u‖
  refine ⟨C, ?_⟩
  have hg_int : Integrable g := by
    exact kadiri_laplace_source_integrable_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hgdiff : Differentiable ℝ g := by
    simpa [g] using kadiri_weighted_source_differentiable (φ := φ) hφ (a := a)
  have hg_deriv : ∀ x : ℝ, ‖deriv g x‖ ≤ D := by
    intro x
    simpa [g] using hD x
  have hfourier :=
    fourierInvTrunc_uniform_bound_of_deriv_bound
      (g := g) (B := B) (D := D) hg_int hgdiff hB hD_nonneg hg_deriv
  filter_upwards [hfourier] with T hT n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hx : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hlaplace :
        ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖ ≤
          C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
      have hTlog :
          ‖fourierInvTrunc
              (FourierTransform.fourier
                (fun y : ℝ => Complex.exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y))
              (Real.log (n : ℝ)) T‖ ≤ C := by
        simpa [C, g, norm_mul] using hT (Real.log (n : ℝ))
      have hcore := laplaceIntegralCpowTrunc_norm_bound_of_fourier
        (φ := φ) (sigma := -(1 + a)) (x := (n : ℝ)) (T := T) (C := C) hx
        hTlog
      have hpow := norm_exp_neg_log_eq_norm_nat_cpow (a := a) (n := n) hn
      calc
        ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖
            ≤ Real.exp (-(1 + a) * Real.log ↑n) * C := hcore
        _ = C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
            rw [hpow]
            ring
    have hpv_eq :
        ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
          laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T := by
      simp [laplaceIntegralCpowTrunc, laplaceIntegral]
    rw [hpv_eq]
    calc
      ‖(Λ n : ℂ) * laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖
          = ‖(Λ n : ℂ)‖ *
              ‖laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T‖ := by
            rw [norm_mul]
      _ ≤ ‖(Λ n : ℂ)‖ * (C * ‖(n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖) := by
            exact mul_le_mul_of_nonneg_left hlaplace (norm_nonneg _)
      _ = C * ‖(Λ n : ℂ) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ))‖ := by
            rw [norm_mul]
            ring
      _ = C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖ := by
            rw [← norm_vonMangoldt_neg_mellin_line_eq_real (a := a) (t := 0) (n := n)]
            simp

/-- Tannery exchange for the principal-value inversion terms.  This converts
pointwise PV inversion at each integer into the summed PV limit, using an
explicit summable domination bound over `n`. -/
lemma kadiri_thm_3_1_q1_eq_11_summed_pv_of_pointwise_inversion_bound
    {φ : ℝ → ℂ} {a : ℝ}
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {bound : ℕ → ℝ} (hbound_sum : Summable bound)
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤ bound n) :
    Tendsto
      (fun T : ℝ =>
        ∑' n : ℕ,
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t in (-T)..T,
                (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
                 Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  refine tendsto_tsum_of_dominated_convergence
    (𝓕 := atTop)
    (f := fun T n =>
      (Λ n : ℂ) *
        ((1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
             Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))))
    (g := fun n => (Λ n : ℂ) * φ (Real.log n))
    hbound_sum ?_ hbound
  intro n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · simpa using (hinv n hn).const_mul (Λ n : ℂ)

/-- Positive-line reflection of the already-summed negative-line principal value.
The public reduction below proves this summed PV from pointwise inversion and a
Tannery domination bound before using this helper. -/
private lemma kadiri_eq11_pv_positive_line_of_negative_line_pv
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (hinv :
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (∑' n : ℕ,
                  (Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop
        (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  intro Φ
  dsimp only at hinv
  refine hinv.congr' ?_
  filter_upwards with T
  congr 1
  let F : ℝ → ℂ := fun t ↦
    (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
        riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
      Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))
  have hneg : (∫ t in (-T)..T, F (-t)) = ∫ t in (-T)..T, F t := by
    simp [intervalIntegral.integral_comp_neg]
  rw [← hneg]
  refine intervalIntegral.integral_congr fun t _ ↦ ?_
  dsimp [F]
  rw [tsum_vonMangoldt_neg_mellin_line ha t]
  have hzeta_arg :
      (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) =
        (((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    simp only [ofReal_neg]
    ring
  have hPhi_arg :
      ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
        -(((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
    simp only [ofReal_neg]
    ring
  rw [hzeta_arg, hPhi_arg]

/-- Principal-value reduction of Kadiri equation (11) from pointwise PV
inversion and an explicit Tannery domination bound.  The finite-window
sum/integral exchange is proved in this file, and the final vertical-line
reflection is the Dirichlet-series identity followed by `t ↦ -t`. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {bound : ℕ → ℝ} (hbound_sum : Summable bound)
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤ bound n) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  intro Φ
  have hsummed :=
    kadiri_thm_3_1_q1_eq_11_summed_pv_of_pointwise_inversion_bound
      (φ := φ) (a := a) hinv hbound_sum hbound
  have hneg :
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (∑' n : ℕ,
                  (Λ n : ℂ) *
                    (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop
        (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
    dsimp only at hsummed
    refine hsummed.congr' ?_
    filter_upwards with T
    exact kadiri_eq11_truncated_mellin_swap
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab T
  exact kadiri_eq11_pv_positive_line_of_negative_line_pv
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1 hneg

/-- Principal-value reduction with the explicit Tannery majorant expected from
the finite-height inversion bound.  The only domination input is the eventual
uniform estimate by a constant multiple of the absolutely summable von Mangoldt
line `Λ n / n^(1+a)`. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_tannery_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))))
    {C : ℝ}
    (hbound :
      ∀ᶠ T in atTop, ∀ n : ℕ,
        ‖(Λ n : ℂ) *
          ((1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              (let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
               Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)))‖ ≤
          C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  exact kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_bound
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
    (a := a) ha hab ha1 hinv
    (bound := fun n : ℕ => C * ‖(Λ n : ℂ) / (n : ℂ) ^ ((1 + a : ℝ) : ℂ)‖)
    ((summable_norm_vonMangoldt_real_line ha).mul_left C)
    hbound

/-- Principal-value reduction of Kadiri equation (11) from pointwise PV inversion.
The Tannery domination bound is discharged from the Kadiri decay hypotheses via
the finite-window Fourier/Laplace estimate. -/
theorem kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n)))) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    Tendsto
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
                riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)))
      atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  obtain ⟨C, hC⟩ :=
    kadiri_eq11_tannery_bound
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab
  exact kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion_tannery_bound
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay
    (a := a) ha hab ha1 hinv (C := C) hC

/-- Reduction of Kadiri equation (11) from the pointwise inversion identity.

The analytic exchange of the von Mangoldt sum with the Mellin integral is kept as an
explicit hypothesis. This isolates the part blocked by the concrete Fubini/Tonelli
side-condition proof while avoiding any dependency on the sorried inversion theorem in
`Kadiri.lean`. -/
theorem kadiri_thm_3_1_q1_eq_11_of_inversion {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (_hab : a < b) (_ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      (φ (Real.log n) : ℂ) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ,
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
    (hMellinSwap :
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      (∑' n : ℕ,
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))) =
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t : ℝ,
            (∑' n : ℕ,
                (Λ n : ℂ) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) :
    let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
    (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n)) =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t : ℝ,
          (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  intro Φ
  dsimp only at hMellinSwap
  have hterm :
      ∀ n : ℕ,
        (Λ n : ℂ) * φ (Real.log n) =
          (Λ n : ℂ) *
            ((1 / (2 * (Real.pi : ℂ))) *
              ∫ t : ℝ,
                Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                  (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rw [hinv n hn]
  rw [tsum_congr hterm]
  rw [hMellinSwap]
  have hcollapse :
      (∫ t : ℝ,
          (∑' n : ℕ,
              (Λ n : ℂ) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t : ℝ,
          (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
              riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
            Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    let F : ℝ → ℂ := fun t ↦
      (-deriv riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I) /
          riemannZeta (((1 + a : ℝ) : ℂ) + (t : ℂ) * I)) *
        Φ (-(((1 + a : ℝ) : ℂ) + (t : ℂ) * I))
    have hneg : (∫ t : ℝ, F (-t)) = ∫ t : ℝ, F t := by
      simpa using
        (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
          (Homeomorph.neg ℝ).measurableEmbedding F
    rw [← hneg]
    refine integral_congr_ae ?_
    filter_upwards with t
    dsimp [F]
    rw [tsum_vonMangoldt_neg_mellin_line ha t]
    have hzeta_arg :
        (((1 + a : ℝ) : ℂ) - (t : ℂ) * I) =
          (((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      simp only [ofReal_neg]
      ring
    have hPhi_arg :
        ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) =
          -(((1 + a : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) := by
      simp only [ofReal_neg]
      ring
    rw [hzeta_arg, hPhi_arg]
  rw [hcollapse]

/-- The single-point truncated-limit inverse Laplace identity at `y = log n`
(\cite{Kadiri2005}, the displayed equation just before eq.~(11)): for `φ` of class `C¹`
with the strip decay of (B), and any `0 < a < b` with `n ≥ 1`,
$$\varphi(\log n)
   = \lim_{T \to \infty} \frac{1}{2\pi i} \int_{-(1+a)-iT}^{-(1+a)+iT}
       \Phi(s)\, n^{s}\, ds,$$
with `Φ(s) = ∫ y, φ y e^{-s y}`. This is the truncated-window Fourier/Laplace inversion
theorem from `PrimeNumberTheoremAnd.LaplaceInversion`, specialized to the contour
`σ = -(1+a)` and the point `x = n` (so `n^s = exp (s log n)`). It discharges the `hinv`
hypothesis carried by the eq.~(11) reduction lemmas above. -/
theorem kadiri_thm_3_1_q1_pointwise_inversion {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n))) := by
  intro n hn Φ
  -- Reduce to the multiplication-form truncated inverse Laplace integral.
  have hx : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  -- The exponentially weighted source `g y = exp (-(σ y)) φ y` with `σ = -(1+a)`.
  set g : ℝ → ℂ :=
    fun y : ℝ => exp (-(((-(1 + a) : ℝ) : ℂ) * (y : ℂ))) * φ y with hg_def
  have hg_int : Integrable g :=
    kadiri_laplace_source_integrable_of_decay
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab
  have hgdiff : Differentiable ℝ g :=
    kadiri_weighted_source_differentiable (φ := φ) hφ (a := a)
  -- Interval integrability of the local difference quotient of `g` at `x = log n`.
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else
          (1 / (Real.pi * u) : ℂ) • (g (Real.log (n : ℝ) - u) - g (Real.log (n : ℝ))))
      volume (-(1 : ℝ)) (1 : ℝ) :=
    intervalIntegrable_local_quotient_of_differentiableAt
      (E := ℂ) (f := g) (x := Real.log (n : ℝ)) (R := (1 : ℝ)) zero_lt_one
      hgdiff.continuous.continuousOn hgdiff.differentiableAt
  -- The master truncated-limit inverse Laplace theorem applied with `σ = -(1+a)`,
  -- source `φ`, point `x = n`, window radius `R = 1`.
  have hmaster :=
    laplaceIntegralCpowTrunc_tendsto_of_integrable_local_quotient
      (sigma := (-(1 + a) : ℝ)) (f := φ) (x := (n : ℝ)) (R := (1 : ℝ))
      hx zero_lt_one hg_int hq
  -- The truncated integral defining `hinv` is exactly `laplaceIntegralCpowTrunc`.
  have hreindex :
      (fun T : ℝ =>
        (1 / (2 * (Real.pi : ℂ))) *
          ∫ t in (-T)..T,
            Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
              (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I)) =
        fun T : ℝ => laplaceIntegralCpowTrunc φ (-(1 + a)) (n : ℝ) T := by
    funext T
    simp only [Φ, laplaceIntegralCpowTrunc, laplaceIntegral]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _ht
    push_cast
    ring_nf
  -- The target value `φ (log n)` matches the master theorem's `φ (log x)` at `x = n`.
  rw [hreindex]
  simpa using hmaster

/-- The faithful truncated-limit form of Kadiri equation (11) (\cite{Kadiri2005},
Théorème 3.1, eq.~(11), arXiv math/0401238): the von Mangoldt sum is the `T → ∞`
limit of the truncated contour integral `kadiri_thm_3_1_q1_I φ a T` over the compact
segment `[1+a-iT, 1+a+iT]`.  Under the same `C¹` hypotheses as the stub
`kadiri_thm_3_1_q1_eq_11`, the only remaining analytic input is the single-point
truncated-limit Laplace inversion `hinv` (the displayed identity just before
\cite[(11)]{Kadiri2005}); the sum/integral exchange over the compact window and the
Tannery domination are discharged by this file, so no full-line `L¹` integrability is
needed.  This replaces the (mis-stated) absolute Bochner form `∫ t : ℝ` of the stub. -/
theorem kadiri_thm_3_1_q1_eq_11_truncated_limit_of_pointwise_inversion
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hinv : ∀ n : Nat, 1 ≤ n →
      let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
      Tendsto
        (fun T : ℝ =>
          (1 / (2 * (Real.pi : ℂ))) *
            ∫ t in (-T)..T,
              Φ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I) *
                (n : ℂ) ^ ((-(1 + a : ℝ) : ℂ) + (t : ℂ) * I))
        atTop (𝓝 (φ (Real.log n)))) :
    Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I φ a T) atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) := by
  -- The bank reduction gives the limit for the interval-integral form `∫ t in (-T)..T`.
  have hbank :=
    kadiri_thm_3_1_q1_eq_11_pv_of_pointwise_inversion
      (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1 hinv
  dsimp only at hbank
  -- `kadiri_thm_3_1_q1_I` uses `∫ t in Set.Ioo (-T) T`; the bank uses `∫ t in (-T)..T`.
  -- For `T ≥ 0` these set integrals agree (`(-T)..T = Ioc (-T) T`, and `Ioo`/`Ioc`
  -- differ only on the null set `{T}`), so the two limits coincide eventually.
  refine hbank.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  have hTle : (-T) ≤ T := by linarith
  unfold kadiri_thm_3_1_q1_I
  dsimp only
  congr 1
  rw [intervalIntegral.integral_of_le hTle,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- The unconditional faithful truncated-limit form of Kadiri equation (11)
(\cite{Kadiri2005}, Théorème 3.1, eq.~(11)): the von Mangoldt sum is the `T → ∞` limit
of the truncated contour integral `kadiri_thm_3_1_q1_I φ a T`.  The single-point Laplace
inversion input is now supplied internally by `kadiri_thm_3_1_q1_pointwise_inversion`, so
this carries no analytic hypotheses beyond the `C¹` regularity and strip decay of `φ`. -/
theorem kadiri_thm_3_1_q1_eq_11_truncated_limit
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    Tendsto (fun T : ℝ => kadiri_thm_3_1_q1_I φ a T) atTop
      (𝓝 (∑' n : ℕ, (Λ n : ℂ) * φ (Real.log n))) :=
  kadiri_thm_3_1_q1_eq_11_truncated_limit_of_pointwise_inversion
    (φ := φ) hφ (b := b) hb hφ_decay hφ'_decay (a := a) ha hab ha1
    (kadiri_thm_3_1_q1_pointwise_inversion
      (φ := φ) hφ (b := b) hb hφ_decay (a := a) ha hab)

end

end Kadiri
