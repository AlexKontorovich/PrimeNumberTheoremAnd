/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Architect
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Topology.EMetricSpace.Defs
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Analytic.Within
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Complex.AbsMax
import PrimeNumberTheoremAnd.BorelCaratheodory
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.DiffContOnCl
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp

open Complex Metric Real

@[blueprint "DerivativeBound"
  (title := "DerivativeBound")
  (statement := /--
  Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and
  suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
  $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
  for all $|z|\leq r$.
  -/)
  (proof := /--
  By Cauchy's integral formula we know that
  $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=
  \frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
  Thus,
  \begin{equation}\label{pickupPoint0}
      |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}
      \frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
      \leq\frac{1}{2\pi}\int_0^{2\pi}\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
  \end{equation}
  Now applying Theorem \ref{borelCaratheodory-closedBall}, and noting that $r'-r\leq|r'e^{it}-z|$,
  we have that
  $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|
  \leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
  Substituting this into Equation (\ref{pickupPoint0}) and evaluating the integral completes the
  proof.
  -/)
  (proofUses := ["borelCaratheodory-closedBall"])]
theorem derivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R)) (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) (pos_r : 0 < r)
    (z_in_r : z ∈ Metric.closedBall 0 r) (r_le_r' : r < r') (r'_le_R : r' < R) :
    ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by
  have pos_r' : (0 : ℝ) < r' := lt_trans pos_r r_le_r'
  have pos_rr : (0 : ℝ) < r' - r := sub_pos.mpr r_le_r'
  have pos_Rr' : (0 : ℝ) < R - r' := sub_pos.mpr r'_le_R
  have M_nonneg : (0 : ℝ) ≤ M := by
    have h0 := re_f_le_M 0 (mem_closedBall_self (by linarith))
    simp only [f_zero_at_zero, Complex.zero_re] at h0; exact h0
  have hz_norm : ‖z‖ ≤ r := by rwa [mem_closedBall, dist_zero_right] at z_in_r
  set h := fun w : ℂ => f (z + w) with h_def
  have translate_into_R : ∀ w ∈ ball 0 (R - r), z + w ∈ closedBall 0 R := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    have hw_norm : ‖w‖ < R - r := by rwa [mem_ball, dist_zero_right] at hw
    calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ r + (R - r) := by linarith [hw_norm.le]
      _ = R := by ring
  have h_analytic : AnalyticOn ℂ h (ball 0 (R - r)) :=
    analytic_f.comp (analyticOn_const.add analyticOn_id)
      (fun w hw => translate_into_R w hw)
  have h_diffContOnCl : DiffContOnCl ℂ h (ball 0 (r' - r)) :=
    h_analytic.differentiableOn.diffContOnCl_ball
      (closedBall_subset_ball (by linarith))
  have h_hasDerivAt : HasDerivAt h (deriv f z) 0 := by
    have z_in_ball_R : z ∈ ball 0 R := by rw [mem_ball, dist_zero_right]; linarith
    have hfz : HasDerivAt f (deriv f z) z :=
      (analytic_f.analyticAt (closedBall_mem_nhds_of_mem z_in_ball_R)).differentiableAt.hasDerivAt
    have hadd : HasDerivAt (fun w : ℂ => z + w) 1 0 := (hasDerivAt_id (0 : ℂ)).const_add z
    have hfz' : HasDerivAt f (deriv f z) (z + 0) := by simpa using hfz
    simpa using hfz'.comp 0 hadd
  have h_deriv_eq : deriv h 0 = deriv f z := h_hasDerivAt.deriv
  have sphere_in_r' : ∀ w ∈ sphere 0 (r' - r), z + w ∈ closedBall 0 r' := by
    intro w hw
    rw [mem_closedBall, dist_zero_right]
    have hw_norm : ‖w‖ = r' - r := by rwa [mem_sphere, dist_zero_right] at hw
    calc ‖z + w‖ ≤ ‖z‖ + ‖w‖ := norm_add_le _ _
      _ ≤ r + (r' - r) := by linarith [hw_norm.le]
      _ = r' := by ring
  have main_bound : ∀ M' : ℝ, 0 < M' →
      (∀ w ∈ closedBall 0 R, (f w).re ≤ M') →
      ‖deriv h 0‖ ≤ 2 * M' * r' / ((R - r') * (r' - r)) := fun M' hM'pos hM'le => by
    have sphere_bound : ∀ w ∈ sphere 0 (r' - r), ‖h w‖ ≤ 2 * M' * r' / (R - r') := by
      intro w hw; change ‖f (z + w)‖ ≤ 2 * M' * r' / (R - r')
      exact borelCaratheodory_closedBall
        (by linarith) analytic_f f_zero_at_zero hM'pos hM'le r'_le_R (sphere_in_r' w hw)
    have cauchy := norm_deriv_le_of_forall_mem_sphere_norm_le pos_rr h_diffContOnCl sphere_bound
    rw [div_div] at cauchy; linarith
  rw [← h_deriv_eq]
  rcases lt_or_eq_of_le M_nonneg with hMpos | rfl
  · calc ‖deriv h 0‖
        ≤ 2 * M * r' / ((R - r') * (r' - r)) := main_bound M hMpos re_f_le_M
      _ ≤ 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
          have key : 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) =
                     2 * M * r' / ((R - r') * (r' - r)) * (r' / (r' - r)) := by field_simp
          rw [key]; apply le_mul_of_one_le_right (by positivity)
          have hrr : r' / (r' - r) - 1 = r / (r' - r) := by field_simp; ring
          linarith [div_nonneg pos_r.le pos_rr.le]
  · simp only [mul_zero, zero_mul, zero_div]
    apply le_of_forall_pos_le_add; intro δ hδ
    set M' := δ * (R - r') * (r' - r) / (2 * r') with M'_def
    have hM'pos : 0 < M' := by positivity
    have hbound := main_bound M' hM'pos (fun w hw => (re_f_le_M w hw).trans hM'pos.le)
    have heq : 2 * M' * r' / ((R - r') * (r' - r)) = δ := by
      simp only [M'_def]; field_simp
    linarith [heq ▸ hbound]

