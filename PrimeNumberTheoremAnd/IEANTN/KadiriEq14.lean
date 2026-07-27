import Architect
import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.LaplaceInversion
import PrimeNumberTheoremAnd.IEANTN.KadiriEq13
import PrimeNumberTheoremAnd.IEANTN.KadiriSupport
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Kadiri

open MeasureTheory Complex
open ArithmeticFunction hiding log
open Filter
open scoped Topology
open scoped FourierTransform

@[blueprint
  "kadiri-thm-3-1-q1-I-2"
  (title := "Kadiri's $I_2(T)$: the reflected Dirichlet-series piece")
  (statement := /-- Kadiri's $I_2(T)$ from \cite[p.~12]{Kadiri2005}: the reflected
  Dirichlet-series piece of the functional-equation rewrite of the $\sigma = -a$
  integral,
  $$ I_2(T) \;:=\; \frac{1}{2\pi i} \int_{-a - iT}^{-a + iT}
                  \frac{\zeta'}{\zeta}(1-s)\, \Phi(-s)\, ds. $$

  \emph{Sign:} the $+\zeta'/\zeta(1-s)$ integrand comes from substituting the
  (corrected) functional equation
  $-\zeta'/\zeta(s) = -\log\pi + \zeta'/\zeta(1-s) + \tfrac{1}{2}\{\Gamma'/\Gamma(s/2)
  + \Gamma'/\Gamma((1-s)/2)\}$ (see \ref{kadiri-thm-3-1-q1-functional-eq}) into the
  integrand of the $\sigma = -a$ integral and reading off the middle term. The paper
  states the integrand with a leading minus, which is a typo (matching the sign typo
  in the functional equation on \cite[p.~12]{Kadiri2005}). Its $T \to \infty$ limit
  is given by \ref{kadiri-thm-3-1-q1-eq-14}. -/)
  (latexEnv := "definition")]
noncomputable def kadiri_thm_3_1_q1_I_2 (φ : ℝ → ℂ) (a T : ℝ) : ℂ :=
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ t in Set.Ioo (-T) T,
      (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
        Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I))


private lemma kadiri_laplace_positive_line_weight_isBigO_atBot {φ : ℝ → ℂ} {b a : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|)) :
    (fun x : ℝ => exp (-((a : ℂ) * (x : ℂ))) • φ x)
      =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
  simpa [smul_eq_mul] using
    kadiri_laplace_neg_line_weight_isBigO_atBot (ψ := φ) (b := b) a
      (hφ_decay.mono atBot_le_cocompact)

private lemma kadiri_laplace_positive_line_nat_inv_bounded {φ : ℝ → ℂ} {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (hab : a < b) :
    ∃ B : ℝ, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  have hO : F =O[Filter.atBot] fun x : ℝ => Real.exp ((b - a) * x) := by
    simpa [F] using
      kadiri_laplace_positive_line_weight_isBigO_atBot (φ := φ) (a := a) (b := b)
        hφ_decay
  have hcomp_zero :
      Filter.Tendsto (fun x : ℝ => Real.exp ((b - a) * x)) Filter.atBot (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp
      ((tendsto_const_mul_atBot_of_pos (sub_pos.mpr hab)).2 tendsto_id)
  have hF_zero : Filter.Tendsto F Filter.atBot (nhds 0) := hO.trans_tendsto hcomp_zero
  have hlogseq :
      Filter.Tendsto (fun n : ℕ => -Real.log ((n + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atBot := by
    have hnat : Filter.Tendsto (fun n : ℕ => ((n + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
    exact tendsto_neg_atTop_atBot.comp (Real.tendsto_log_atTop.comp hnat)
  have hseq : Filter.Tendsto
      (fun n : ℕ => ‖F (-Real.log ((n + 2 : ℕ) : ℝ))‖) Filter.atTop (nhds 0) := by
    simpa using (hF_zero.comp hlogseq).norm
  obtain ⟨B, hB⟩ := hseq.bddAbove_range
  refine ⟨B, ?_⟩
  intro n hn0 hn1
  have hn2 : 2 ≤ n := (Nat.two_le_iff n).mpr ⟨hn0, hn1⟩
  have hrepr : n - 2 + 2 = n := Nat.sub_add_cancel hn2
  have hmem : ‖F (-Real.log n)‖ ∈
      Set.range (fun k : ℕ => ‖F (-Real.log ((k + 2 : ℕ) : ℝ))‖) := by
    refine ⟨n - 2, ?_⟩
    change ‖F (-Real.log (((n - 2 + 2 : ℕ) : ℝ)))‖ = ‖F (-Real.log (n : ℝ))‖
    rw [hrepr]
  exact hB hmem

private lemma kadiri_laplace_positive_line_weight_boundedOn_Iic_of_continuous {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) {b : ℝ}
    (hψ_decay : (fun x : ℝ ↦ ψ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (C : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, x ≤ C →
      ‖exp (-((a : ℂ) * (x : ℂ))) • ψ x‖ ≤ B := by
  obtain ⟨B, hB_nonneg, hB⟩ :=
    kadiri_laplace_neg_line_weight_bounded_of_continuous hψ
      (show -(1 + b) < a by linarith) hab hψ_decay
  exact ⟨B, hB_nonneg, fun x _hx => by simpa [smul_eq_mul] using hB x⟩

/-- Continuity of the bilateral Laplace integral on the positive vertical line
`re s = a`, obtained by reflecting the shifted contour statement. -/
lemma kadiri_laplace_positive_vertical_segment_continuousOn
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) :
    ContinuousOn (fun t : ℝ => laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))
      (Set.Icc (-T) T) := by
  have hminus := kadiri_laplace_shifted_vertical_segment_continuousOn
    (φ := φ) hφ hb hφ_decay (a := a) (T := T) ha hab ha1
  have hcomp : ContinuousOn
      (fun t : ℝ =>
        (fun u : ℝ =>
          let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
          let s : ℂ := ((-a : ℝ) : ℂ) + (u : ℂ) * I
          Φ (-s)) (-t))
      (Set.Icc (-T) T) := by
    refine hminus.comp (continuous_neg.continuousOn) ?_
    intro t ht
    exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
  refine hcomp.congr ?_
  intro t _ht
  dsimp [laplaceIntegral]
  apply integral_congr_ae
  filter_upwards with y
  apply congrArg (fun z : ℂ => φ y * exp (-z * (y : ℂ)))
  norm_num
  ring_nf

private lemma kadiri_laplace_positive_line_weight_deriv_boundedOn_Iic
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (C : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, x ≤ C →
      ‖deriv (fun z : ℝ => exp (-((a : ℂ) * (z : ℂ))) * φ z) x‖ ≤ D := by
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_laplace_neg_line_weight_deriv_bounded hφ
      (show -(1 + b) < a by linarith) hab hφ_decay hφ'_decay
  exact ⟨D, hD_nonneg, fun x _hx => hD x⟩

lemma kadiri_laplace_positive_line_pv_nat_inv {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) {n : ℕ} (hn : n ≠ 0) :
    Filter.Tendsto (fun T : ℝ => laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop (nhds (φ (-Real.log n))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hx : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr hnpos
  have h := kadiri_laplace_positive_line_pv
    (φ := φ) hφ hb hφ_decay ha hab hx
  simpa [Real.log_inv] using h

private lemma kadiri_vonMangoldt_nat_inv_cpow {n : ℕ} (hn : n ≠ 0) (a t : ℝ) :
    ((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
      (Λ n : ℂ) /
        (((n : ℝ) : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnC : (((n : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast hnpos.ne'
  have harg : (((n : ℝ) : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hnpos.le]
    exact Real.pi_ne_zero.symm
  change ((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        ((((n : ℝ) : ℂ))⁻¹ ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
      (Λ n : ℂ) /
        (((n : ℝ) : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)))
  rw [Complex.inv_cpow _ _ harg]
  rw [Complex.cpow_add (x := (((n : ℝ) : ℂ))) (y := (1 : ℂ))
    (z := (((a : ℝ) : ℂ) + (t : ℂ) * I))] <;> try exact hnC
  rw [Complex.cpow_add (x := (((n : ℝ) : ℂ))) (y := ((a : ℂ)))
    (z := ((t : ℂ) * I))] <;> try exact hnC
  norm_num
  field_simp [hnC]

private lemma kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq
    {a : ℝ} (ha : 0 < a) (n : ℕ) :
    ‖(Λ n : ℂ) / (((n : ℝ) : ℂ))‖ * ((n : ℝ)⁻¹) ^ a =
      ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ := by
  by_cases hn : n = 0
  · subst n
    simp [ha.ne']
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [norm_div, norm_div]
    norm_num
    have hpowcast : (n : ℂ) ^ (1 + (a : ℂ)) =
        (((n : ℝ) : ℂ)) ^ (1 + (a : ℂ)) := by
      norm_num
    rw [hpowcast]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
    simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
    rw [Real.inv_rpow hnpos.le, Real.rpow_add hnpos, Real.rpow_one]
    field_simp [hnpos.ne', (Real.rpow_pos_of_pos hnpos a).ne']

private lemma kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum
    (φ : ℝ → ℂ) {a t : ℝ} (ha : 0 < a) :
    (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
    ∑' n : ℕ,
      -(((Λ n : ℂ) /
          (n : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  have hs : 1 < (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)).re := by
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have hsum := tsum_vonMangoldt_eq hs
  have hder :
      deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
          riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
        -∑' n : ℕ, (Λ n : ℂ) /
          (n : ℂ) ^ (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [hsum]
    ring
  rw [hder, neg_mul]
  rw [← tsum_mul_right, ← tsum_neg]

private lemma kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum_nat_inv
    (φ : ℝ → ℂ) {a t : ℝ} (ha : 0 < a) :
    (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
        riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
    ∑' n : ℕ,
      -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
        (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
  rw [kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum (φ := φ) ha]
  refine tsum_congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp
  · rw [kadiri_vonMangoldt_nat_inv_cpow hn a t]
    norm_num

private lemma kadiri_I2_tsum_integral_term_eq_laplace_trunc
    (φ : ℝ → ℂ) (a T : ℝ) (n : ℕ) :
    (1 / (2 * (Real.pi : ℂ))) *
      ∫ t in (-T)..T,
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) =
    -(((Λ n : ℂ) / (n : ℂ)) * laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T) := by
  let c : ℂ := (Λ n : ℂ) / (n : ℂ)
  have hint :
      (∫ t in (-T)..T,
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))) =
      (-c) * ∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    norm_num [c]
    ring_nf
  rw [hint, laplaceIntegralCpowTrunc]
  have hcommInt :
      (∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I))) =
      ∫ t in (-T)..T,
        laplaceIntegral φ (((a : ℝ) : ℂ) + I * (t : ℂ)) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + I * (t : ℂ))) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    simp [mul_comm]
  rw [hcommInt]
  norm_num [c]
  ring_nf

lemma kadiri_thm_3_1_q1_I_2_eq_reflected_interval
    (φ : ℝ → ℂ) (a : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      (1 / (2 * (Real.pi : ℂ))) *
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
  let Φ : ℂ → ℂ := fun s ↦ ∫ y, φ y * exp (-s * (y : ℂ)) ∂volume
  have hle : -T ≤ T := by linarith
  have hset_to_interval :
      ∫ t in Set.Ioo (-T) T,
        (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    rw [intervalIntegral.integral_of_le hle,
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
  have hflip :
      ∫ t in (-T)..T,
        (deriv riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I)) /
            riemannZeta (1 - (((-a : ℝ) : ℂ) + (t : ℂ) * I))) *
          Φ (-(((-a : ℝ) : ℂ) + (t : ℂ) * I)) =
        ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
    simpa [sub_eq_add_neg, neg_mul, add_comm, add_left_comm, add_assoc] using
      (intervalIntegral.integral_comp_neg
        (fun t : ℝ =>
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            Φ (((a : ℝ) : ℂ) + (t : ℂ) * I))
        (a := -T) (b := T))
  rw [kadiri_thm_3_1_q1_I_2]
  dsimp only
  rw [hset_to_interval, hflip]
  congr 1

private lemma kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc_of_integral_tsum
    (φ : ℝ → ℂ) {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T)
    (hF_int : ∀ n : ℕ,
      Integrable
        (fun t : ℝ =>
          -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
            (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (volume.restrict (Set.Ioc (-T) T)))
    (hF_sum : Summable fun n : ℕ =>
      ∫ t in Set.Ioc (-T) T,
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T := by
  rw [kadiri_thm_3_1_q1_I_2_eq_reflected_interval φ a hT]
  have hle : -T ≤ T := by linarith
  have hrewrite :
      ∫ t in (-T)..T,
          (deriv riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I)) /
              riemannZeta (1 + (((a : ℝ) : ℂ) + (t : ℂ) * I))) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I) =
        ∫ t in (-T)..T,
          ∑' n : ℕ,
            -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
              (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
              laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact kadiri_reflected_zeta_logDeriv_mul_laplace_eq_tsum_nat_inv (φ := φ) ha
  rw [hrewrite, intervalIntegral.integral_of_le hle]
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Set.Ioc (-T) T)) hF_int hF_sum
  rw [← hswap, ← tsum_mul_left]
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  rw [← intervalIntegral.integral_of_le hle]
  simpa using (kadiri_I2_tsum_integral_term_eq_laplace_trunc φ a T n)

private lemma kadiri_I2_tsum_summand_integrable
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (n : ℕ) :
    Integrable
      (fun t : ℝ =>
        -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
      (volume.restrict (Set.Ioc (-T) T)) := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hbase : (((n : ℝ)⁻¹ : ℂ)) ∈ slitPlane := by
      rw [Complex.mem_slitPlane_iff]
      left
      simp [inv_pos.mpr hnpos]
    have hexp : Continuous fun t : ℝ => (((a : ℝ) : ℂ) + (t : ℂ) * I) := by
      fun_prop
    have hpow : ContinuousOn
        (fun t : ℝ => (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (Set.Icc (-T) T) := by
      exact (continuous_const.cpow hexp (fun _ => hbase)).continuousOn
    have hlap := kadiri_laplace_positive_vertical_segment_continuousOn
      (φ := φ) hφ hb hφ_decay (a := a) (T := T) ha hab ha1
    have hcont : ContinuousOn
        (fun t : ℝ =>
          -(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
            (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
            laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)))
        (Set.Icc (-T) T) := by
      exact ((continuousOn_const.mul hpow).mul hlap).neg
    exact (hcont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self

private lemma kadiri_I2_tsum_summand_norm_eq
    (φ : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (n : ℕ) (t : ℝ) :
    ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
      (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
      laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ =
    ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ *
      ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    rw [norm_neg, norm_mul, norm_mul]
    have hpow :
        ‖(((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ =
          ((n : ℝ)⁻¹) ^ a := by
      rw [← Complex.ofReal_inv]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos (inv_pos.mpr hnpos)]
      simp [Complex.add_re, Complex.mul_re]
    rw [hpow, kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq ha n]

private lemma kadiri_I2_tsum_summable_integral_norm
    (φ : ℝ → ℂ) {a T : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ =>
      ∫ t in Set.Ioc (-T) T,
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖ := by
  let C : ℝ :=
    ∫ t in Set.Ioc (-T) T,
      ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖
  have hcoeff : Summable fun n : ℕ =>
      ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ := by
    apply summable_norm_vonMangoldt_cpow
    simp [Complex.add_re]
    linarith
  refine (hcoeff.mul_right C).congr fun n => ?_
  have hnorm :
      (fun t : ℝ =>
        ‖-(((Λ n : ℂ) / (((n : ℝ) : ℂ))) *
          (((n : ℝ)⁻¹ : ℂ) ^ (((a : ℝ) : ℂ) + (t : ℂ) * I)) *
          laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I))‖)
        =
      (fun t : ℝ =>
        ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖ *
          ‖laplaceIntegral φ (((a : ℝ) : ℂ) + (t : ℂ) * I)‖) := by
    funext t
    exact kadiri_I2_tsum_summand_norm_eq φ ha n t
  rw [hnorm, MeasureTheory.integral_const_mul]

private lemma kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a T : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hT : 0 ≤ T) :
    kadiri_thm_3_1_q1_I_2 φ a T =
      -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T := by
  exact kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc_of_integral_tsum
    φ ha hT
    (fun n => kadiri_I2_tsum_summand_integrable hφ hb hφ_decay ha hab ha1 n)
    (kadiri_I2_tsum_summable_integral_norm φ ha)

private lemma kadiri_I2_weighted_laplace_trunc_tendsto_of_dominated_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b)
    (bound : ℕ → ℝ) (hbound_sum : Summable bound)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n) :
    Filter.Tendsto
      (fun T : ℝ =>
        ∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
          laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop
      (nhds (∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  apply tendsto_tsum_of_dominated_convergence (bound := bound)
  · exact hbound_sum
  · intro n
    by_cases hn : n = 0
    · subst n
      simp
    · exact (kadiri_laplace_positive_line_pv_nat_inv
        (φ := φ) hφ hb hφ_decay ha hab hn).const_mul ((Λ n : ℂ) / (n : ℂ))
  · exact hbound

lemma kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_tendsto
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (hlim : Filter.Tendsto
      (fun T : ℝ =>
        -∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) *
          laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n)))) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  refine hlim.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with T hT
  exact (kadiri_thm_3_1_q1_I_2_eq_neg_tsum_laplace_trunc
    hφ hb hφ_decay ha hab ha1 hT).symm

lemma kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_dominated_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (bound : ℕ → ℝ) (hbound_sum : Summable bound)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  have hseries := kadiri_I2_weighted_laplace_trunc_tendsto_of_dominated_bound
    hφ hb hφ_decay ha hab bound hbound_sum hbound
  exact kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_tendsto
    hφ hb hφ_decay ha hab ha1 hseries.neg

lemma kadiri_thm_3_1_q1_eq_14_of_uniform_laplace_trunc_cpow_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (C : ℝ)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ C * ((n : ℝ)⁻¹) ^ a) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  let bound : ℕ → ℝ :=
    fun n => C * ‖(Λ n : ℂ) / (n : ℂ) ^ (((1 + a : ℝ) : ℂ))‖
  have hbound_sum : Summable bound := by
    have hs : 1 < (((1 + a : ℝ) : ℂ)).re := by
      simp
      linarith
    exact (summable_norm_vonMangoldt_cpow hs).mul_left C
  have hweighted : ∀ᶠ T in Filter.atTop, ∀ n : ℕ,
      ‖((Λ n : ℂ) / (n : ℂ)) *
        laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖ ≤ bound n := by
    filter_upwards [hbound] with T hT n
    by_cases hn : n = 0
    · subst n
      simp [bound]
    by_cases h1 : n = 1
    · subst n
      simp [bound]
    · rw [norm_mul]
      calc
        ‖(Λ n : ℂ) / (n : ℂ)‖ *
            ‖laplaceIntegralCpowTrunc φ a ((n : ℝ)⁻¹) T‖
            ≤ ‖(Λ n : ℂ) / (n : ℂ)‖ * (C * ((n : ℝ)⁻¹) ^ a) :=
              mul_le_mul_of_nonneg_left (hT n hn h1) (norm_nonneg _)
        _ = C * (‖(Λ n : ℂ) / (n : ℂ)‖ * ((n : ℝ)⁻¹) ^ a) := by ring
        _ = C * (‖(Λ n : ℂ) / (((n : ℝ) : ℂ))‖ * ((n : ℝ)⁻¹) ^ a) := by
          norm_num
        _ = bound n := by
          rw [kadiri_norm_vonMangoldt_nat_inv_cpow_coeff_eq ha n]
  exact kadiri_thm_3_1_q1_eq_14_of_weighted_laplace_trunc_dominated_bound
    hφ hb hφ_decay ha hab ha1 bound hbound_sum hweighted

lemma kadiri_thm_3_1_q1_eq_14_of_uniform_fourier_inv_trunc_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1)
    (C : ℝ)
    (hbound : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖fourierInvTrunc
          (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
          (-Real.log n) T‖ ≤ C) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  refine kadiri_thm_3_1_q1_eq_14_of_uniform_laplace_trunc_cpow_bound
    hφ hb hφ_decay ha hab ha1 C ?_
  filter_upwards [hbound] with T hT n hn h1
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hxpos : 0 < ((n : ℝ)⁻¹) := inv_pos.mpr hnpos
  rw [laplaceIntegralCpowTrunc_eq_laplaceInvLineTrunc
    (sigma := a) (f := φ) (x := ((n : ℝ)⁻¹)) hxpos T]
  rw [laplaceInvLineTrunc_laplaceTransformBilateral_eq_fourierInvTrunc]
  rw [norm_smul]
  have hlog : Real.log ((n : ℝ)⁻¹) = -Real.log n := by
    simp [Real.log_inv]
  have hscale :
      ‖exp ((a : ℂ) * (Real.log ((n : ℝ)⁻¹) : ℂ))‖ = ((n : ℝ)⁻¹) ^ a := by
    rw [Complex.exp_mul_log_of_pos_eq_cpow hxpos (a : ℂ)]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
    simp
  rw [hscale]
  calc
    ((n : ℝ)⁻¹) ^ a *
        ‖fourierInvTrunc
          (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
          (Real.log ((n : ℝ)⁻¹)) T‖
        = ((n : ℝ)⁻¹) ^ a *
            ‖fourierInvTrunc
              (𝓕 (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y))
              (-Real.log n) T‖ := by rw [hlog]
    _ ≤ ((n : ℝ)⁻¹) ^ a * C :=
      mul_le_mul_of_nonneg_left (hT n hn h1)
        (Real.rpow_nonneg (inv_nonneg.mpr hnpos.le) a)
    _ ≤ C * ((n : ℝ)⁻¹) ^ a := by rw [mul_comm]

/-- Kadiri-side bridge from windowed Fourier bounds to equation (14). It leaves
only a source bound and a local principal-value window bound as application
inputs; the mass and far-field tail are handled by `LaplaceInversion`. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_bounds
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R B L M : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hsource : ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B)
    (hmass : ∀ᶠ T in Filter.atTop,
      ‖∫ u in (-R)..R,
        if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)‖ ≤ M)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  have hF_int : Integrable F := by
    have hF_mul :
        Integrable (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) * φ y) :=
      kadiri_laplace_positive_line_weight_integrable hφ hφ_decay ha hab
    simpa [F, smul_eq_mul] using hF_mul
  refine kadiri_thm_3_1_q1_eq_14_of_uniform_fourier_inv_trunc_bound
    hφ hb hφ_decay ha hab ha1
    (M * B + L + (1 / (Real.pi * R)) * ∫ u : ℝ, ‖F u‖) ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ), hmass, hlocal] with
    T hT hmassT hlocalT n hn h1
  have hq : IntervalIntegrable
      (fun u : ℝ =>
        if u = 0 then 0 else (1 / (Real.pi * u) : ℂ) • (F (-Real.log n - u) -
          F (-Real.log n)))
      volume (-R) R := by
    have hq0 := kadiri_laplace_line_local_quotient_integrable
      (φ := φ) hφ a (-Real.log n) hR
    simpa [F, smul_eq_mul] using hq0
  have herr : IntervalIntegrable
      (fun u : ℝ =>
        (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
          (F (-Real.log n - u) - F (-Real.log n)))
      volume (-R) R :=
    intervalIntegrable_sin_div_kernel_error_of_intervalIntegrable_quotient
      (E := ℂ) hq T
  simpa [F] using
    norm_fourierInvTrunc_le_of_windowed_sin_div_bounds (E := ℂ) hF_int hT hR
      (hsource n hn h1) hmassT herr (hlocalT n hn h1)

/-- Kadiri-side bridge from source and local-window bounds to equation (14),
with the scalar finite-window mass discharged by the sinc mass limit. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_local_bounds
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R B L : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hsource : ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖(fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n)‖ ≤ B)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) :=
  kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_bounds
    hφ hb hφ_decay ha hab ha1 hR hsource
    (eventually_norm_intervalIntegral_sin_div_kernel_scalar_mass_le_two hR)
    hlocal

/-- Kadiri-side bridge from the remaining local-window bound to equation (14).
The weighted source bound and scalar mass bound are discharged here. -/
lemma kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_local_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (hb : 0 < b)
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R L : ℝ} (ha : 0 < a) (hab : a < b) (ha1 : a < 1) (hR : 0 < R)
    (hlocal : ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  obtain ⟨B, hsource⟩ :=
    kadiri_laplace_positive_line_nat_inv_bounded (φ := φ) hφ_decay hab
  exact kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_source_local_bounds
    hφ hb hφ_decay ha hab ha1 hR hsource hlocal

private lemma kadiri_laplace_positive_line_local_window_bound
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ)
    {b : ℝ}
    (hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a R : ℝ} (ha : 0 < a) (hab : a < b) (hR : 0 < R) :
    ∃ L : ℝ, ∀ᶠ T in Filter.atTop, ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ‖∫ u in (-R)..R,
          (if u = 0 then (0 : ℂ) else (Real.sin (T * u) / (Real.pi * u) : ℂ)) •
            ((fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n - u) -
              (fun y : ℝ => exp (-((a : ℂ) * (y : ℂ))) • φ y) (-Real.log n))‖ ≤ L := by
  let C : ℝ := -Real.log (2 : ℝ) + R
  let F : ℝ → ℂ := fun y => exp (-((a : ℂ) * (y : ℂ))) • φ y
  obtain ⟨D, hD_nonneg, hD⟩ :=
    kadiri_laplace_positive_line_weight_deriv_boundedOn_Iic
      (φ := φ) hφ hφ_decay hφ'_decay ha hab C
  refine ⟨(D / Real.pi) * |R - (-R)|, Filter.Eventually.of_forall ?_⟩
  intro T n hn0 hn1
  have hn2 : 2 ≤ n := (Nat.two_le_iff n).mpr ⟨hn0, hn1⟩
  have hn2_real : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hlog_le : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) hn2_real
  have hle : -R ≤ R := by linarith
  have hxC : -Real.log (n : ℝ) ∈ Set.Iic C := by
    simp only [Set.mem_Iic, C]
    linarith
  have hmem : ∀ u ∈ Set.uIoc (-R) R, -Real.log (n : ℝ) - u ∈ Set.Iic C := by
    intro u hu
    have huIoc : u ∈ Set.Ioc (-R) R := by
      simpa [Set.uIoc_of_le hle] using hu
    simp only [Set.mem_Iic, C]
    linarith [huIoc.1]
  have hdiff : ∀ y ∈ Set.Iic C, DifferentiableAt ℝ F y := by
    intro y _hy
    simpa [F, smul_eq_mul] using
      ((kadiri_laplace_line_weight_differentiable hφ a) y)
  have hderiv : ∀ y ∈ Set.Iic C, ‖deriv F y‖ ≤ D := by
    intro y hy
    simpa [F, smul_eq_mul] using hD y hy
  have hcore :=
    sin_div_error_interval_bound_of_convex (g := F) (x := -Real.log (n : ℝ)) (T := T)
      (convex_Iic C) hD_nonneg hxC hmem hdiff hderiv
  simpa [F] using hcore

theorem kadiri_thm_3_1_q1_eq_14_core
    {φ : ℝ → ℂ} (_hφ : ContDiff ℝ 1 φ)
    {b : ℝ} (_hb : 0 < b)
    (_hφ_decay : (fun x : ℝ ↦ φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    (_hφ'_decay : (fun x : ℝ ↦ deriv φ x * exp ((x : ℂ) / 2))
        =O[Filter.cocompact ℝ] fun x : ℝ ↦ Real.exp (-(1/2 + b) * |x|))
    {a : ℝ} (_ha : 0 < a) (_hab : a < b) (_ha1 : a < 1) :
    Filter.Tendsto (fun T : ℝ ↦ kadiri_thm_3_1_q1_I_2 φ a T)
      Filter.atTop
      (nhds (-∑' n : ℕ, ((Λ n : ℂ) / (n : ℂ)) * φ (-Real.log n))) := by
  obtain ⟨L, hlocal⟩ :=
    kadiri_laplace_positive_line_local_window_bound
      (φ := φ) _hφ _hφ_decay _hφ'_decay _ha _hab (R := 1) (by norm_num)
  exact kadiri_thm_3_1_q1_eq_14_of_windowed_fourier_local_bound
    _hφ _hb _hφ_decay _ha _hab _ha1 (R := 1) (L := L) (by norm_num) hlocal

end Kadiri

