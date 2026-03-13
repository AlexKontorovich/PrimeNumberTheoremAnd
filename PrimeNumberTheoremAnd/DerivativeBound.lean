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
    by_cases hM_pos : 0 < M;
    · have h_deriv_bound : ‖deriv f z‖ ≤ (2 * M * r') / (R - r') / (r' - r) := by
        have h_deriv_bound : ∀ w ∈ Metric.sphere z (r' - r), ‖f w‖ ≤ 2 * M * r' / (R - r') := by
          intro w hw
          have hw_closed : w ∈ Metric.closedBall 0 r' := by
            exact mem_closedBall_zero_iff.mpr ( by simpa using le_trans ( norm_add_le ( z ) ( w - z ) ) ( by simpa using add_le_add ( mem_closedBall_zero_iff.mp z_in_r ) ( le_of_eq hw ) ) );
          have := borelCaratheodory_closedBall ( show 0 < R by linarith ) ( show AnalyticOn ℂ f ( Metric.closedBall 0 R ) from analytic_f ) f_zero_at_zero hM_pos ( fun z hz => re_f_le_M z hz ) ( show r' < R by linarith ) hw_closed;
          exact this;
        have := @Complex.norm_deriv_le_of_forall_mem_sphere_norm_le;
        convert this ( show 0 < r' - r by linarith ) _ h_deriv_bound using 1;
        refine' analytic_f.differentiableOn.mono _ |> DifferentiableOn.diffContOnCl;
        rw [ closure_ball _ ( by linarith ) ] ; intro w hw ; exact le_trans ( dist_triangle _ _ _ ) ( by linarith [ Metric.mem_closedBall.mp z_in_r, Metric.mem_closedBall.mp hw ] ) ;
      refine le_trans h_deriv_bound ?_;
      field_simp;
      rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_pos ( sub_pos.mpr r'_le_R ) ( sub_pos.mpr r_le_r' ), mul_pos ( sub_pos.mpr r'_le_R ) ( sub_pos.mpr pos_r ), mul_pos ( sub_pos.mpr r_le_r' ) ( sub_pos.mpr pos_r ) ];
    · have h_deriv_zero : ∀ ε > 0, ‖deriv f z‖ ≤ (2 * ε * r' ^ 2) / ((R - r') * (r' - r) ^ 2) := by
        intro ε hε_pos
        have h_borel_caratheodory : ∀ w ∈ Metric.closedBall z (r' - r), ‖f w‖ ≤ (2 * ε * r') / (R - r') := by
          intros w hw
          have h_w_in_closedBall : w ∈ Metric.closedBall 0 r' := by
            simp +zetaDelta at *;
            linarith [ norm_le_of_mem_closedBall ( show w ∈ Metric.closedBall z ( r' - r ) from hw ), norm_sub_norm_le w z ]
          have h_f_w_le_2εr'_div_R_minus_r' : ‖f w‖ ≤ (2 * ε * r') / (R - r') := by
            have := borelCaratheodory_closedBall ( show 0 < R by linarith ) ( show AnalyticOn ℂ f ( Metric.closedBall 0 R ) from analytic_f ) ( show f 0 = 0 from f_zero_at_zero ) ( show 0 < ε by linarith ) ( show ∀ z ∈ Metric.closedBall 0 R, ( f z |> Complex.re ) ≤ ε by exact fun z hz => by linarith [ re_f_le_M z hz ] ) ( show r' < R by linarith ) ( show w ∈ Metric.closedBall 0 r' from h_w_in_closedBall ) ; aesop;
          exact h_f_w_le_2εr'_div_R_minus_r';
        have h_cauchy : ‖deriv f z‖ ≤ (2 * ε * r') / (R - r') / (r' - r) := by
          apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le;
          · linarith;
          · refine' analytic_f.differentiableOn.mono _ |> DifferentiableOn.diffContOnCl;
            rw [ closure_ball z ( by linarith ) ];
            intro w hw; exact (by
            simp +zetaDelta at *;
            exact le_trans ( norm_le_of_mem_closedBall <| by simpa using hw ) ( by linarith ));
          · exact fun w hw => h_borel_caratheodory w <| Metric.mem_closedBall.mpr <| le_of_eq hw;
        refine le_trans h_cauchy ?_;
        field_simp;
        rw [ div_le_div_iff₀ ] <;> nlinarith [ mul_pos ( sub_pos.mpr r_le_r' ) ( sub_pos.mpr r'_le_R ), mul_pos ( sub_pos.mpr r_le_r' ) ( sub_pos.mpr pos_r ), mul_pos ( sub_pos.mpr r'_le_R ) ( sub_pos.mpr pos_r ) ];
      have h_lim_zero : Filter.Tendsto (fun ε : ℝ => (2 * ε * r' ^ 2) / ((R - r') * (r' - r) ^ 2)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        exact tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ <| by norm_num );
      exact le_of_tendsto_of_tendsto tendsto_const_nhds h_lim_zero ( Filter.eventually_of_mem self_mem_nhdsWithin fun ε hε => h_deriv_zero ε hε ) |> fun h => h.trans ( by norm_num [ show M = 0 by linarith [ show M ≥ 0 from by have := re_f_le_M 0 ( by norm_num; linarith ) ; norm_num [ f_zero_at_zero ] at this; linarith ] ] )
