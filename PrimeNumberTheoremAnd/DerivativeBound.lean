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
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
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
import Mathlib.Analysis.Complex.Liouville
import PrimeNumberTheoremAnd.BorelCaratheodory

private lemma sphere_sub_closedBall {r r' : ℝ} {z w : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hw : w ∈ Metric.sphere z (r' - r))
    (hr : r < r') :
    w ∈ Metric.closedBall (0 : ℂ) r' := by
  simp +zetaDelta at *
  linarith [norm_sub_norm_le w z]

private lemma analyticOn_to_diffContOnCl {R r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (hz : z ∈ Metric.closedBall (0 : ℂ) r)
    (hr : r < r') (hR : r' < R) :
    DiffContOnCl ℂ f (Metric.ball z (r' - r)) := by
  apply DifferentiableOn.diffContOnCl
  exact (analytic_f.differentiableOn).mono (by
    rw [closure_ball z (by linarith)]
    intro w hw; rw [Metric.mem_closedBall] at *
    exact le_trans (dist_triangle _ _ _) (by norm_num at *; linarith))

private lemma bound_weakening {R M r r' : ℝ}
    (pos_r : 0 < r) (hr : r < r') (hR : r' < R) (hM : 0 ≤ M) :
    2 * M * r' / (R - r') / (r' - r) ≤ 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
  rw [div_div, div_le_div_iff₀] <;> try nlinarith
  · nlinarith [show 0 ≤ 2 * M * r' * (R - r') * (r' - r) from
      mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith)) (by linarith))
        (by linarith)]
  · exact mul_pos (by linarith) (sq_pos_of_pos (by linarith))

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
      |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
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
  (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (f_zero_at_zero : f 0 = 0)
  (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
  (pos_r : 0 < r) (z_in_r : z ∈ Metric.closedBall 0 r)
  (r_le_r' : r < r') (r'_le_R : r' < R) :
  ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by
  have h_bc : ∀ w ∈ Metric.closedBall 0 r', ‖f w‖ ≤ 2 * M * r' / (R - r') := by
    by_cases hM : M ≤ 0
    · have hM0 : M = 0 :=
        le_antisymm hM (by simpa [f_zero_at_zero] using re_f_le_M 0 (by norm_num; linarith))
      have hf0 : ∀ z ∈ Metric.ball 0 R, f z = 0 := by
        intro z hz
        have hre : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ 0 := fun z hz =>
          le_trans (re_f_le_M z <| Metric.ball_subset_closedBall hz) hM0.le
        have hexp : ∀ z ∈ Metric.ball 0 R, Complex.exp (f z) = Complex.exp (f 0) := by
          apply_rules [@Complex.eqOn_of_isPreconnected_of_isMaxOn_norm]
          · exact (convex_ball _ _).isPreconnected
          · exact Metric.isOpen_ball
          · exact DifferentiableOn.cexp
              (analytic_f.differentiableOn.mono Metric.ball_subset_closedBall)
          · exact Metric.mem_ball_self (by linarith)
          · intro w hw; simp_all +decide [Complex.norm_exp]
        simp_all +decide [Complex.exp_eq_exp_iff_exists_int]
        have hk : ∀ z ∈ Metric.ball 0 R, ∃ k : ℤ, f z = 2 * Real.pi * Complex.I * k := by
          intro z hz; specialize hexp z (by simpa using hz)
          rw [Complex.exp_eq_one_iff] at hexp
          obtain ⟨k, hk⟩ := hexp; exact ⟨k, by linear_combination hk⟩
        choose! k hk using hk
        have hcont : ContinuousOn (fun z => k z : ℂ → ℤ) (Metric.ball 0 R) := by
          have : ContinuousOn (fun z => f z / (2 * Real.pi * Complex.I)) (Metric.ball 0 R) :=
            ContinuousOn.div_const
              (analytic_f.continuousOn.mono Metric.ball_subset_closedBall) _
          rw [Metric.continuousOn_iff] at *
          intro b hb ε hε; obtain ⟨δ, hδ, H⟩ := this b hb ε hε; use δ, hδ
          intros a ha hab; specialize H a ha hab
          simp_all +decide [Complex.dist_eq, Complex.normSq]
          norm_cast at H ⊢; erw [Real.dist_eq]; aesop
        have hconst : ∀ z ∈ Metric.ball 0 R, k z = k 0 := by
          have : IsConnected (Set.image k (Metric.ball 0 R)) := by
            apply_rules [IsConnected.image, isConnected_Ioo]
            exact ⟨Metric.nonempty_ball.mpr (by linarith), (convex_ball _ _).isPreconnected⟩
          exact fun z hz => this.isPreconnected.subsingleton ⟨z, hz, rfl⟩
            ⟨0, by simpa using by linarith, rfl⟩
        have := hk 0 (by simpa using by linarith); aesop
      exact fun w hw => by
        rw [hf0 w (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) r'_le_R))]
        norm_num [hM0]
    · push_neg at hM
      exact fun w hw => borelCaratheodory_closedBall (by linarith) analytic_f f_zero_at_zero
        (by linarith) re_f_le_M (by linarith) hw
  have h_sphere : ∀ w ∈ Metric.sphere z (r' - r), ‖f w‖ ≤ 2 * M * r' / (R - r') :=
    fun w hw => h_bc w (sphere_sub_closedBall z_in_r hw r_le_r')
  have h_diff : DiffContOnCl ℂ f (Metric.ball z (r' - r)) :=
    analyticOn_to_diffContOnCl analytic_f z_in_r r_le_r' r'_le_R
  exact le_trans
    (Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr r_le_r') h_diff h_sphere)
    (bound_weakening pos_r r_le_r' r'_le_R (by
      have := re_f_le_M 0 (by norm_num; linarith); norm_num [f_zero_at_zero] at this; linarith))
