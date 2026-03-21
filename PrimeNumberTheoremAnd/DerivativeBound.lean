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
import Mathlib.Analysis.Complex.Liouville
import PrimeNumberTheoremAnd.BorelCaratheodory

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

private lemma derivativeBound_pos {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R)) (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) (pos_r : 0 < r)
    (z_in_r : z ∈ Metric.closedBall 0 r) (r_le_r' : r < r') (r'_le_R : r' < R)
    (hM : 0 < M) :
    ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by
  have hz : ‖z‖ ≤ r := by simpa using z_in_r
  set δ := r' - ‖z‖ with hδ_def
  have hδ_pos : 0 < δ := by linarith
  have hdiff : DiffContOnCl ℂ f (Metric.ball z δ) := by
    apply DifferentiableOn.diffContOnCl
    apply analytic_f.differentiableOn.mono
    rw [closure_ball z (ne_of_gt hδ_pos)]
    intro w hw
    simp only [Metric.mem_closedBall, dist_zero_right] at hw ⊢
    have : ‖w - z‖ ≤ δ := by rwa [dist_eq_norm] at hw
    linarith [norm_le_insert' w z]
  have hbound : ∀ w ∈ Metric.sphere z δ, ‖f w‖ ≤ 2 * M * r' / (R - r') := by
    intro w hw
    apply borelCaratheodory_closedBall (by linarith) analytic_f f_zero_at_zero hM re_f_le_M r'_le_R
    simp only [Metric.mem_closedBall, dist_zero_right]
    have hwz : ‖w - z‖ = δ := by
      rw [← dist_eq_norm]; exact Metric.mem_sphere.mp hw
    linarith [norm_le_insert' w z]
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ_pos hdiff hbound
  have hC_pos : 0 < 2 * M * r' / (R - r') := by
    exact div_pos (mul_pos (mul_pos (by linarith) hM) (by linarith)) (by linarith)
  calc ‖deriv f z‖
    _ ≤ (2 * M * r' / (R - r')) / δ := hcauchy
    _ ≤ (2 * M * r' / (R - r')) / (r' - r) := by
        exact div_le_div_of_nonneg_left hC_pos.le (by linarith) (by linarith)
    _ = 2 * M * r' / ((R - r') * (r' - r)) := by rw [div_div]
    _ ≤ 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
        have h1 : 0 < (R - r') * (r' - r) := mul_pos (by linarith) (by linarith)
        have h2 : 0 < (R - r') * (r' - r) ^ 2 := mul_pos (by linarith) (sq_pos_of_pos (by linarith))
        rw [div_le_div_iff₀ h1 h2]
        have key : r' * (r' - r) ≤ r' ^ 2 := by
          nlinarith [mul_pos (show 0 < r' by linarith) pos_r]
        have h3 : 0 ≤ 2 * M * (R - r') * (r' - r) := by
          apply mul_nonneg
          · apply mul_nonneg
            · exact mul_nonneg (by linarith) hM.le
            · linarith
          · linarith
        calc 2 * M * r' * ((R - r') * (r' - r) ^ 2)
            = (2 * M * (R - r') * (r' - r)) * (r' * (r' - r)) := by ring
          _ ≤ (2 * M * (R - r') * (r' - r)) * (r' ^ 2) :=
              mul_le_mul_of_nonneg_left key h3
          _ = 2 * M * r' ^ 2 * ((R - r') * (r' - r)) := by ring

private lemma derivativeBound_nonpos {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R)) (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) (pos_r : 0 < r)
    (z_in_r : z ∈ Metric.closedBall 0 r) (r_le_r' : r < r') (r'_le_R : r' < R)
    (hM : M ≤ 0) :
    ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by
  by_cases hM_nonpos : M < 0;
  · exact absurd ( re_f_le_M 0 ( Metric.mem_closedBall_self ( by linarith ) ) ) ( by norm_num [ f_zero_at_zero ] ; linarith );
  · have hRe_zero : ∀ z ∈ Metric.ball 0 R, (f z).re = 0 := by
      intro z hz;
      have hRe_zero : ∀ z ∈ Metric.ball 0 R, (f z).re ≤ 0 := by
        exact fun z hz => le_trans ( re_f_le_M z <| Metric.ball_subset_closedBall hz ) hM;
      have hRe_zero : AnalyticOn ℂ (fun z => Complex.exp (f z)) (Metric.ball 0 R) := by
        apply_rules [ DifferentiableOn.analyticOn, Complex.differentiable_exp ];
        · exact Complex.differentiable_exp.comp_differentiableOn ( analytic_f.differentiableOn.mono ( Metric.ball_subset_closedBall ) );
        · exact Metric.isOpen_ball;
      have := @Complex.eqOn_of_isPreconnected_of_isMaxOn_norm ℂ;
      specialize this ( convex_ball 0 R |> Convex.isPreconnected ) ( Metric.isOpen_ball ) ( hRe_zero.differentiableOn ) ( Metric.mem_ball_self ( by linarith ) ) ; simp_all +decide [ IsMaxOn, IsMaxFilter ];
      simp_all +decide [ Complex.norm_exp, Set.EqOn ];
      have := @this z hz; rw [ Complex.exp_eq_one_iff ] at this; aesop;
    -- Since the real part of $f(z)$ is zero everywhere in the ball, the derivative of $f$ must also be zero.
    have h_deriv_zero : ∀ z ∈ Metric.ball 0 R, deriv f z = 0 := by
      intro z hz
      have h_cauchy_riemann : HasDerivAt f (deriv f z) z := by
        exact DifferentiableAt.hasDerivAt ( analytic_f.differentiableOn.differentiableAt ( Metric.closedBall_mem_nhds_of_mem hz ) );
      have h_cauchy_riemann : HasDerivAt (fun x : ℝ => (f (z + x)).re) (deriv f z).re 0 ∧ HasDerivAt (fun x : ℝ => (f (z + Complex.I * x)).re) (-(deriv f z).im) 0 := by
        constructor;
        · rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
          convert Complex.continuous_re.continuousAt.tendsto.comp h_cauchy_riemann |> Filter.Tendsto.comp <| show Filter.Tendsto ( fun t : ℝ => ↑t ) ( nhdsWithin 0 { 0 } ᶜ ) ( nhdsWithin 0 { 0 } ᶜ ) from Filter.Tendsto.inf ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num ) <| by norm_num using 2 ; norm_num;
        · have h_cauchy_riemann : HasDerivAt (fun x : ℝ => f (z + Complex.I * x)) (deriv f z * Complex.I) 0 := by
            convert HasDerivAt.comp _ _ _ using 1;
            · aesop;
            · simpa using HasDerivAt.const_mul Complex.I ( hasDerivAt_id ( 0 : ℝ ) |> HasDerivAt.ofReal_comp );
          rw [ hasDerivAt_iff_tendsto_slope_zero ] at *;
          convert Complex.continuous_re.continuousAt.tendsto.comp h_cauchy_riemann using 2 ; norm_num [ Complex.ext_iff ];
          norm_num [ Complex.ext_iff ];
      have h_cauchy_riemann : HasDerivAt (fun x : ℝ => (f (z + x)).re) 0 0 ∧ HasDerivAt (fun x : ℝ => (f (z + Complex.I * x)).re) 0 0 := by
        have h_cauchy_riemann : ∀ᶠ x in nhds 0, (f (z + x)).re = 0 ∧ (f (z + Complex.I * x)).re = 0 := by
          rw [ Metric.eventually_nhds_iff ];
          obtain ⟨ ε, hε, hε' ⟩ := Metric.mem_nhds_iff.mp ( Metric.isOpen_ball.mem_nhds hz );
          exact ⟨ ε, hε, fun y hy => ⟨ hRe_zero _ <| hε' <| by simpa using hy, hRe_zero _ <| hε' <| by simpa using hy ⟩ ⟩;
        exact ⟨ by exact HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( by filter_upwards [ h_cauchy_riemann.filter_mono <| Complex.continuous_ofReal.continuousAt ] with x hx using hx.1 ), by exact HasDerivAt.congr_of_eventuallyEq ( hasDerivAt_const _ _ ) ( by filter_upwards [ h_cauchy_riemann.filter_mono <| Complex.continuous_ofReal.continuousAt ] with x hx using hx.2 ) ⟩;
      simp_all +decide [ Complex.ext_iff, hasDerivAt_iff_tendsto_slope_zero ];
      exact ⟨ tendsto_nhds_unique ( by tauto ) h_cauchy_riemann.1, neg_eq_zero.mp ( tendsto_nhds_unique ( by tauto ) h_cauchy_riemann.2 ) ⟩;
    rw [ h_deriv_zero z ( Metric.mem_ball.mpr <| lt_of_le_of_lt ( Metric.mem_closedBall.mp z_in_r ) <| by linarith ) ] ; norm_num [ show M = 0 by linarith ]

theorem derivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R)) (f_zero_at_zero : f 0 = 0)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M) (pos_r : 0 < r)
    (z_in_r : z ∈ Metric.closedBall 0 r) (r_le_r' : r < r') (r'_le_R : r' < R) :
        ‖(deriv f) z‖ ≤ 2 * M * (r')^2 / ((R - r') * (r' - r)^2) := by
  by_cases hM : 0 < M
  · exact derivativeBound_pos analytic_f f_zero_at_zero re_f_le_M pos_r z_in_r r_le_r' r'_le_R hM
  · exact derivativeBound_nonpos analytic_f f_zero_at_zero re_f_le_M pos_r z_in_r r_le_r' r'_le_R (not_lt.mp hM)
