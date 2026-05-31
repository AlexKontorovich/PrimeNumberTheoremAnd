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
import PrimeNumberTheoremAnd.StrongPNT

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
  have Rpos : 0 < R := lt_trans pos_r (lt_trans r_le_r' r'_le_R)
  have analytic_f' : AnalyticOn ℂ f (Metric.ball 0 R) :=
    analytic_f.mono Metric.ball_subset_closedBall
  have re_f_le_M' : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ M := fun z hz =>
    re_f_le_M z (Metric.ball_subset_closedBall hz)
  have Mnn : 0 ≤ M := by
    have h0 : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
      simp [Metric.mem_closedBall, Rpos.le]
    have := re_f_le_M 0 h0
    rw [f_zero_at_zero] at this
    simpa using this
  by_cases hM : M = 0
  · subst hM
    have hRr' : 0 < R - r' := by linarith
    have hrr' : 0 < r' - r := by linarith
    have hr'_pos : 0 < r' := lt_of_lt_of_le pos_r r_le_r'.le
    rw [show (2 * (0:ℝ) * (r')^2 / ((R - r') * (r' - r)^2)) = 0 from by ring]
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    rw [zero_add]
    set K : ℝ := 2 * (r')^2 / ((R - r') * (r' - r)^2) with hK_def
    have hKpos : 0 < K := by positivity
    have εK_pos : 0 < ε / K := div_pos hε hKpos
    have re_f_eK : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ ε / K := fun z hz =>
      le_trans (re_f_le_M' z hz) εK_pos.le
    have hDB := DerivativeBound εK_pos pos_r r_le_r' r'_le_R
      analytic_f' f_zero_at_zero re_f_eK z_in_r
    have hKε : 2 * (ε / K) * (r')^2 / ((R - r') * (r' - r)^2) = ε := by
      have h1 : (R - r') ≠ 0 := hRr'.ne'
      have h2 : (r' - r) ≠ 0 := hrr'.ne'
      have h3 : K ≠ 0 := hKpos.ne'
      simp only [hK_def] at h3 ⊢
      field_simp at h3 ⊢
    linarith
  · have Mpos : 0 < M := lt_of_le_of_ne Mnn (Ne.symm hM)
    exact DerivativeBound Mpos pos_r r_le_r' r'_le_R
      analytic_f' f_zero_at_zero re_f_le_M' z_in_r
