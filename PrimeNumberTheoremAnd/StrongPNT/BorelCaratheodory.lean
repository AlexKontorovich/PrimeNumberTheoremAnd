/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Maksym Radziwill
-/

import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction
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


noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

-- Away from zero divRemovable_zero f z is equal to f z / z

lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ) (z_ne_0 : z ≠ 0) : divRemovable_zero f z = f z / z := by 
  unfold divRemovable_zero; apply Function.update_of_ne z_ne_0

-- If f is analytic on an open set and f 0 = 0 then f z / z is also
-- analytic on the same open set.

lemma AnalyticOn.divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
  (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
  (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (divRemovable_zero f) s :=
  by
     rw [Complex.analyticOn_iff_differentiableOn o]
     rw [←(Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0)]
     constructor
     · rw [differentiableOn_congr (by intros; apply Function.update_of_ne; grind)]
       exact DifferentiableOn.fun_div
         (AnalyticOn.differentiableOn (AnalyticOn.mono analytic Set.diff_subset))
         (DifferentiableOn.mono (differentiableOn_id (s := Set.univ))
         (Set.subset_univ (s \ {0}))) (by grind)

     · have U := HasDerivAt.continuousAt_div (c := 0) (a := (deriv f) 0) (f := f)
         (DifferentiableOn.hasDerivAt
            ((Complex.analyticOn_iff_differentiableOn o).mp analytic) sInNhds0)
       have T : (fun (x : ℂ) ↦ (f x - 0) / (x - 0)) = (fun (x : ℂ) ↦ (f x) / x) := by funext; grind
       rw [zero, T] at U; exact U

-- The proof of the Lemma below is cumbersome, a proper way would be to
-- show that if f is analytic on a closed set C, then it is analytic on an
-- open set O containing the closed set C and apply the previous lemma.

lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ} {R : ℝ} 
  (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R)) 
  (zero : f 0 = 0): AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
    apply analyticOn_of_locally_analyticOn
    intro x x_hyp
    by_cases h : ‖x‖ = R
    · use Metric.ball x (R / 2)
      constructor
      · exact Metric.isOpen_ball
      · constructor
        · simp; positivity
        · have Z : ∀w ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2), divRemovable_zero f w = f w / w := by
             intro x₂ hyp_x₂
             apply divRemovable_zero_of_ne_zero
             simp [ball_eq] at hyp_x₂
             rw [← norm_pos_iff]
             calc ‖x₂‖
               _ = ‖x - (x - x₂)‖ := by simp
               _ ≥ ‖x‖ - ‖x - x₂‖ := by apply norm_sub_norm_le
               _ = R - ‖x₂ - x‖ := by simp [h, norm_sub_rev]
               _ > 0 := by linarith

          apply AnalyticOn.congr 
          · apply AnalyticOn.div (AnalyticOn.mono analytic Set.inter_subset_left) analyticOn_id 
            · intro x₁ hyp_x₁
              simp [ball_eq] at hyp_x₁
              rw [← norm_pos_iff]
              calc ‖x₁‖
                   _ = ‖x - (-(x₁ - x))‖ := by simp
                   _ ≥ ‖x‖ - ‖-(x₁ - x)‖ := by apply norm_sub_norm_le
                   _ = R - ‖x₁ - x‖ := by simp [h, norm_sub_rev]
                   _ > 0 := by linarith
          · simp [Set.EqOn.eq_1]
            intro x₃ hyp_x₃ dist_hyp
            have : x₃ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2) := by
              apply Set.mem_inter
              · simp [hyp_x₃]
              · rw [Metric.mem_ball]; exact dist_hyp
            exact Z x₃ this

    · use Metric.ball 0 R
      constructor
      · exact Metric.isOpen_ball
      · constructor
        · simp [ball_eq]; simp at x_hyp; grind
        · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R = Metric.ball (0 : ℂ) R := by
            apply Set.inter_eq_self_of_subset_right
            simp at x_hyp
            exact Metric.ball_subset_closedBall
          · rw [si]
            apply AnalyticOn.divRemovable_zero 
            · apply Metric.ball_mem_nhds; positivity
            · exact zero
            · apply Metric.isOpen_ball
            · apply AnalyticOn.mono (t := Metric.closedBall 0 R) (s := Metric.ball 0 R) analytic
              · apply Metric.ball_subset_closedBall 

noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (divRemovable_zero f z) / (2 * M - f z)

-- AnalyticOn.schwartzQuotient establishes that f_{M}(z) is analytic.

lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ} (M : ℝ)
  (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (nonzero: ∀z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
  (zero : f 0 = 0): AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) := by

  have sInNhds0 : Metric.closedBall 0 R ∈ nhds 0 := by
    apply Metric.closedBall_mem_nhds; exact Rpos

  exact AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos
      analytic zero) (AnalyticOn.sub (analyticOn_const) analytic) nonzero

-- If Re x ≤ M then |x| ≤ |2 * M - x|, this simple inequality is used
-- in the proof of borelCaratheodory_closedBall.

lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ} {x : ℂ} 
  (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) : ‖x‖ ≤ ‖2 * M - x‖ := by
  have Z : M ^ 2 = M * M := by grind
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  simp
  ring_nf
  simp [add_comm (-(x.re * M * 4)) (x.re ^ 2), add_assoc,
        le_add_iff_nonneg_right (x.re ^ 2), Z, mul_le_mul_iff_left₀ Mpos]
  exact hyp_re_x

-- This is a version of the maximum modulus principle specialized to closed balls.

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {f : ℂ → ℂ} {C R r : ℝ}  
  (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (hyp_r : r ≤ R) (cond : ∀z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C) 
  (w : ℂ) (wInS : w ∈ Metric.closedBall 0 r) : ‖f w‖ ≤ C :=
    by
      apply Complex.norm_le_of_forall_mem_frontier_norm_le
              (U := Metric.closedBall 0 r) (Metric.isBounded_closedBall)
      · apply DifferentiableOn.diffContOnCl; rw [Metric.closure_closedBall]
        apply AnalyticOn.differentiableOn
        apply AnalyticOn.mono (f := f) (s := Metric.closedBall 0 r) (t := Metric.closedBall 0 R) (𝕜 := ℂ) analytic
        · apply Metric.closedBall_subset_closedBall; linarith
      · rw [frontier_closedBall']; exact cond
      · rw [Metric.closure_closedBall]; exact wInS

-- We can now prove Borel-Caratheodory for closed balls

/-%%
\begin{theorem}[BorelCaratheodory]\label{BorelCaratheodory}\lean{BorelCaratheodory}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose
    $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\sup_{\abs{z}\leq r}\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ} 
  (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
  (zeroAtZero: f 0 = 0) (Mpos : 0 < M)
  (realPartBounded: ∀z ∈ Metric.closedBall 0 R, (f z).re ≤ M) 
  (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
  : ‖f z‖ ≤ (2 * M * r) / (R - r) := by

  have zInSFunc : ∀r ≤ R, ∀z ∈ Metric.sphere (0 : ℂ) r, z ∈ Metric.closedBall (0 : ℂ) R := by
      intro r hyp_r z hyp_z
      apply Set.mem_of_mem_of_subset (s := Metric.sphere 0 r) hyp_z
      · calc Metric.sphere (0 : ℂ) r
          _ ⊆ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall
          _ ⊆ Metric.closedBall (0 : ℂ) R := Metric.closedBall_subset_closedBall hyp_r

  have fPosAll : ∀z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by simp; linarith [realPartBounded z zInS])

  have schwartzQuotientBounded : ∀z ∈ Metric.sphere 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by grind)
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc R (by rfl) z hyp_z
    simp [mem_sphere_iff_norm] at hyp_z

    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by simp [divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0;
        · simp [h]
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
              (Complex.norm_le_norm_two_mul_sub_of_re_le Mpos (realPartBounded z zInS))
      _ ≤ (1 / ‖z‖) := by
        by_cases h : ‖f z‖ = 0
        · simp [h]
        · rw [div_div, mul_comm, ← div_div, div_self]; exact h
      _ = 1 / R := by rw [hyp_z]

  have maxMod: ∀z ∈ Metric.closedBall 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    exact AnalyticOn.norm_le_of_norm_le_on_sphere 
          (AnalyticOn.schwartzQuotient M Rpos
             analytic fPosAll zeroAtZero)
          (by rfl) schwartzQuotientBounded

  have boundForF : ∀r < R, 0 < r → ∀z ∈ Metric.sphere 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc r (by grind) z (zOnR)
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by rw [← norm_pos_iff]; linarith
    rw [divRemovable_zero_of_ne_zero f U] at this
    simp at this
    have U : 0 < r * ‖2 * M - f z‖ := by simp [r_pos, fPosAll z zInS]
    simp [zOnR, div_div, div_le_iff₀' U ] at this
    have U0 : ‖f z‖ ≤ 2 * M * r / R + ( r / R ) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          gcongr; apply norm_sub_le (E := ℂ) ((2 : ℂ) * ↑M) (f z)
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          have U : ‖(2 : ℂ) * M‖ = 2 * M := by simp; linarith
          rw [U]
        _ = 2 * M * r * R⁻¹ + r * ‖f z‖ * R⁻¹ := by grind
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by grind
    have U1 : ‖f z‖ - ‖f z‖ * (r * R⁻¹) = ‖f z‖ * (1 - r * R⁻¹) := by ring
    have U2 : (0 : ℝ) < 1 - r * R⁻¹ := by
      have U1 : 0 < R := by linarith
      have U : r * R⁻¹ < 1 := by simp [← div_lt_one₀ U1] at hyp_r; exact hyp_r
      linarith
    have U3 : r * R⁻¹ * M * 2 / (1 - r * R⁻¹) = 2 * M * r / (R - r) := by grind

    rw [← sub_le_sub_iff_right ((r / R) * ‖f z‖)] at U0; ring_nf at U0
    rw [mul_assoc, U1, ← le_div_iff₀ U2, U3] at U0
    exact U0

  have maxBoundForF: ∀r < R, 0 < r → ∀z ∈ Metric.closedBall 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r pos_r
    exact AnalyticOn.norm_le_of_norm_le_on_sphere
            analytic (by linarith) (boundForF r hyp_r pos_r)

  by_cases pos_r : r = 0
  · have U : z = 0 := by simp [pos_r] at hyp_z; exact hyp_z
    rw [U, pos_r]; simp; exact zeroAtZero
  · have U : 0 ≤ r := by
      rw [mem_closedBall_iff_norm] at hyp_z; simp at hyp_z; linarith [norm_nonneg z]
    exact maxBoundForF r (by grind) (by grind) z hyp_z
