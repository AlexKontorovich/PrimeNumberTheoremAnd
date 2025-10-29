/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
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

/-%%
\begin{definition}\label{divRemovable_zero}\lean{divRemovable_zero}\leanok
    Given a complex function $f$, we define the function
    $$g(z):=\begin{cases}
    \frac{f(z)}{z}, & z\neq 0;\\
    f'(0), & z=0.
    \end{cases}$$
\end{definition}
%%-/
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

/-%%
\begin{lemma}\label{divRemovable_zero_of_ne_zero}\lean{divRemovable_zero_of_ne_zero}\leanok
    Let $f$ be a complex function and let $z\neq 0$. Then, with $g$ defined as in Definition~\ref{divRemovable_zero},
    $$g(z)=\frac{f(z)}{z}.$$
\end{lemma}
%%-/
-- Away from zero divRemovable_zero f z is equal to f z / z
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ) (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  apply Function.update_of_ne z_ne_0
/-%%
\begin{proof}\leanok
    This follows directly from the definition of $g$.
\end{proof}
%%-/

-- If f is analytic on an open set and f 0 = 0 then f z / z is also
-- analytic on the same open set.
/-%%
\begin{lemma}\label{AnalyticOn_divRemovable_zero}\lean{AnalyticOn_divRemovable_zero}\leanok
    Let $f$ be a complex function analytic on an open set $s$ containing $0$ such that $f(0)=0$.
    Then, with $g$ defined as in Definition~\ref{divRemovable_zero}, $g$ is analytic on $s$.
\end{lemma}
%%-/
lemma AnalyticOn.divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (divRemovable_zero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o,
    ←(Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0)]
  constructor
  · rw [differentiableOn_congr
      (by intro x hyp_x; apply Function.update_of_ne; rw [Set.mem_diff,
      Set.mem_singleton_iff] at hyp_x; rw [ne_eq]; exact hyp_x.right)]
    exact DifferentiableOn.fun_div
      (AnalyticOn.differentiableOn (AnalyticOn.mono analytic Set.diff_subset))
      (DifferentiableOn.mono (differentiableOn_id (s := Set.univ))
      (Set.subset_univ (s \ {0}))) (by intro x hyp_x; rw [Set.mem_diff,
      Set.mem_singleton_iff] at hyp_x; rw [ne_eq]; exact hyp_x.right)

  · have U := HasDerivAt.continuousAt_div (c := 0) (a := (deriv f) 0) (f := f)
      (DifferentiableOn.hasDerivAt
         ((Complex.analyticOn_iff_differentiableOn o).mp analytic) sInNhds0)
    have T : (fun (x : ℂ) ↦ (f x - 0) / (x - 0)) = (fun (x : ℂ) ↦ (f x) / x) := by
      funext x; rw [sub_zero, sub_zero]
    rwa [zero, T] at U
/-%%
\begin{proof}\uses{divRemovable_zero}
\leanok
    We need to show that $g$ is complex differentiable at every point in $s$.
    For $z\neq 0$, this follows directly from the definition of $g$ and the fact that $f$ is analytic on $s$.
    For $z=0$, we use the definition of the derivative and the fact that $f(0)=0$:
    \[
    \lim_{z\to 0}\frac{g(z)-g(0)}{z-0}=\lim_{z\to 0}\frac{\frac{f(z)}{z}-f'(0)}{z}=\lim_{z\to 0}\frac{f(z)-f'(0)z}{z^2}=\lim_{z\to 0}\frac{f(z)-f(0)-f'(0)(z-0)}{(z-0)^2}=0,
    \]
    where the last equality follows from the definition of the derivative of $f$ at $0$.
    Thus, $g$ is complex differentiable at $0$ with derivative $0$, completing the proof.
\end{proof}
%%-/


-- The proof of the Lemma below is cumbersome, a proper way would be to
-- show that if f is analytic on a closed set C, then it is analytic on an
-- open set O containing the closed set C and apply the previous lemma.
/-%%
\begin{lemma}\label{AnalyticOn_divRemovable_zero_closedBall}
  \lean{AnalyticOn_divRemovable_zero_closedBall}\leanok
    Let $f$ be a complex function analytic on the closed ball $\abs{z}\leq R$ such that $f(0)=0$.
    Then, with $g$ defined as in Definition~\ref{divRemovable_zero}, $g$ is analytic on
    $\abs{z}\leq R$.
\end{lemma}
%%-/
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ} {R : ℝ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) : AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  by_cases h : ‖x‖ = R
  · use Metric.ball x (R / 2)
    constructor
    · exact Metric.isOpen_ball
    · constructor
      · simp only [Metric.mem_ball, dist_self, Nat.ofNat_pos, div_pos_iff_of_pos_right]; positivity
      · have Z : ∀ w ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2),
            divRemovable_zero f w = f w / w := by
          intro x₂ hyp_x₂
          apply divRemovable_zero_of_ne_zero
          rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
            Set.mem_setOf_eq] at hyp_x₂
          rw [← norm_pos_iff]
          calc 0
            _ < R - ‖x₂ - x‖ := by let ⟨u,v⟩ := hyp_x₂; linarith
            _ = ‖x‖ - ‖x - x₂‖ := by rw [h]; simp only [sub_right_inj]; apply norm_sub_rev
            _ ≤ ‖x - (x - x₂)‖ := by apply norm_sub_norm_le
            _ ≤ ‖x₂‖ := by simp only [sub_sub_cancel, le_refl]

        apply AnalyticOn.congr
        · apply AnalyticOn.div (AnalyticOn.mono analytic Set.inter_subset_left) analyticOn_id
          · intro x₁ hyp_x₁
            rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
              Set.mem_setOf_eq] at hyp_x₁
            rw [← norm_pos_iff]
            calc 0
              _ < R - ‖x₁ - x‖ := by let ⟨u,v⟩ := hyp_x₁; linarith
              _ = ‖x‖ - ‖-(x₁ - x)‖ := by rw [h, neg_sub, sub_right_inj]; apply norm_sub_rev
              _ ≤ ‖x - (-(x₁ - x))‖ := by apply norm_sub_norm_le
              _ = ‖x₁‖ := by rw [neg_sub, sub_sub_cancel]

        · simp only [Set.EqOn.eq_1, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
            Metric.mem_ball, and_imp]
          intro x₃ hyp_x₃ dist_hyp
          have : x₃ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2) := by
            apply Set.mem_inter
            · rw [Metric.mem_closedBall, dist_zero_right]; exact hyp_x₃
            · rw [Metric.mem_ball]; exact dist_hyp
          exact Z x₃ this

  · use Metric.ball 0 R
    constructor
    · exact Metric.isOpen_ball
    · constructor
      · simp only [ball_eq, sub_zero, Set.mem_setOf_eq]; simp only [Metric.mem_closedBall,
          dist_zero_right] at x_hyp
        apply lt_of_le_of_ne x_hyp
        · rw [ne_eq]; exact h
      · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R = Metric.ball (0 : ℂ) R := by
          apply Set.inter_eq_self_of_subset_right
          rw [Metric.mem_closedBall, dist_zero_right] at x_hyp
          exact Metric.ball_subset_closedBall
        rw [si]
        apply AnalyticOn.divRemovable_zero
        · apply Metric.ball_mem_nhds; positivity
        · exact zero
        · apply Metric.isOpen_ball
        · apply AnalyticOn.mono analytic Metric.ball_subset_closedBall
/-%%
\begin{proof}
\uses{AnalyticOn.divRemovable_zero}
\leanok
    The proof is similar to that of Lemma~\ref{AnalyticOn_divRemovable_zero}, but we need to consider two cases:
    when $x$ is on the boundary of the closed ball and when it is in the interior.
    In the first case, we take a small open ball around $x$ that lies entirely within the closed ball,
    and apply Lemma~\ref{AnalyticOn_divRemovable_zero} on this smaller ball.
    In the second case, we can take the entire open ball centered at $0$ with radius $R$,
    and again apply Lemma~\ref{AnalyticOn_divRemovable_zero}.
    In both cases, we use the fact that $f(0)=0$ to ensure that the removable singularity at $0$ is handled correctly.
\end{proof}
%%-/

/-%%
\begin{definition}\label{schwartzQuotient}\lean{schwartzQuotient}
\uses{divRemovable_zero}
\leanok
    Given a complex function $f$ and a real number $M$, we define the function
    $$f_{M}(z):=\frac{g(z)}{2M - f(z)},$$
    where $g$ is defined as in Definition~\ref{divRemovable_zero}.
\end{definition}
%%-/
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (divRemovable_zero f z) / (2 * M - f z)

-- AnalyticOn.schwartzQuotient establishes that f_{M}(z) is analytic.
/-%%
\begin{lemma}\label{AnalyticOn.schwartzQuotient}\lean{AnalyticOn.schwartzQuotient}\leanok
    Let $M>0$. Let $f$ be analytic on the closed ball $\abs{z}\leq R$ such that $f(0)=0$
    and suppose that $2M - f(z)\neq 0$ for all $\abs{z}\leq R$.
    Then, with $f_{M}$ defined as in Definition~\ref{schwartzQuotient}, $f_{M}$ is analytic on
    $\abs{z}\leq R$.
\end{lemma}
%%-/
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ} (M : ℝ)
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) : AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) :=
  AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos analytic zero)
    (AnalyticOn.sub (analyticOn_const) analytic) nonzero
/-%%
\begin{proof}\uses{schwartzQuotient, AnalyticOn_divRemovable_zero_closedBall}\leanok
    This follows directly from Lemma~\ref{AnalyticOn_divRemovable_zero_closedBall} and the fact that the difference of two analytic functions is analytic.
\end{proof}
%%-/


-- If Re x ≤ M then |x| ≤ |2 * M - x|, this simple inequality is used
-- in the proof of borelCaratheodory_closedBall.
/-%%
\begin{lemma}\label{Complex.norm_le_norm_two_mul_sub_of_re_le}\lean{Complex.norm_le_norm_two_mul_sub_of_re_le}\leanok
    Let $M>0$ and let $x$ be a complex number such that $\Re x\leq M$.
    Then, $\abs{x}\leq\abs{2M - x}$.
\end{lemma}
%%-/
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ} {x : ℂ}
    (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) : ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  rw [calc
    (2 * M - x).re * (2 * M - x).re + (2 * M - x).im * (2 * M - x).im =
      (2 * M - x.re) * (2 * M - x.re) + x.im * x.im := by simp
    _ = x.re * x.re + (x.im * x.im + 4 * M * (M - x.re)) := by ring]
  bound
/-%%
\begin{proof}\leanok
    We square both sides and simplify to obtain the equivalent inequality
    $$0\leq 4M^2 -4M\Re x,$$
    which follows directly from the assumption $\Re x\leq M$ and the positivity of $M$.
\end{proof}
%%-/


-- This is a version of the maximum modulus principle specialized to closed balls.

lemma AnalyticOn.norm_le_of_norm_le_on_sphere {f : ℂ → ℂ} {C R r : ℝ}
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (hyp_r : r ≤ R) (cond : ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C)
    (w : ℂ) (wInS : w ∈ Metric.closedBall 0 r) : ‖f w‖ ≤ C := by
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
    $\Re f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\sup_{\abs{z}\leq r}\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Rpos : 0 < R) (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    : ‖f z‖ ≤ (2 * M * r) / (R - r) := by

  have zInSFunc : ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r, z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    apply Set.mem_of_mem_of_subset (s := Metric.sphere 0 r) hyp_z
    · calc Metric.sphere (0 : ℂ) r
        _ ⊆ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall
        _ ⊆ Metric.closedBall (0 : ℂ) R := Metric.closedBall_subset_closedBall hyp_r

  have fPosAll : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re, Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, sub_pos]; linarith [realPartBounded z zInS])

  have schwartzQuotientBounded : ∀ z ∈ Metric.sphere 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc R (by rfl) z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z

    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by simp only [Complex.norm_div, divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0;
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le Mpos (realPartBounded z zInS))
      _ ≤ (1 / ‖z‖) := by
        by_cases h : ‖f z‖ = 0
        · rw [h, zero_div, div_zero, one_div, inv_nonneg]; apply norm_nonneg
        · rw [div_div, mul_comm, ← div_div, div_self]; exact h
      _ = 1 / R := by rw [hyp_z]

  have maxMod : ∀ z ∈ Metric.closedBall 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    exact AnalyticOn.norm_le_of_norm_le_on_sphere
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      (by rfl) schwartzQuotientBounded

  have boundForF : ∀ r < R, 0 < r → ∀ z ∈ Metric.sphere 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R := zInSFunc r (by linarith) z (zOnR)
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by rw [← norm_pos_iff]; linarith
    rw [divRemovable_zero_of_ne_zero f U] at this
    simp only [Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq, fPosAll z zInS, not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 : ‖f z‖ ≤ 2 * M * r / R + ( r / R ) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          gcongr; apply norm_sub_le (E := ℂ) ((2 : ℂ) * ↑M) (f z)
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          have U : ‖(2 : ℂ) * M‖ = 2 * M := by simp only [Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, mul_eq_mul_left_iff,
  abs_eq_self, OfNat.ofNat_ne_zero, or_false]; linarith
          rw [U]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by ring_nf
    have U1 : ‖f z‖ - ‖f z‖ * (r * R⁻¹) = ‖f z‖ * (1 - r * R⁻¹) := by ring
    have U2 : (0 : ℝ) < 1 - r * R⁻¹ := by
      have U1 : 0 < R := by linarith
      have U : r * R⁻¹ < 1 := by simp only [← div_lt_one₀ U1] at hyp_r; exact hyp_r
      linarith
    have U3 : r * R⁻¹ * M * 2 / (1 - r * R⁻¹) = 2 * M * r / (R - r) := by
      have : R ≠ 0 := by linarith
      rw [← mul_div_mul_left (r * R⁻¹ * M * (2 : ℝ)) ((1 : ℝ) - r * R⁻¹) this ];
      ring_nf
      have U : R * r * R⁻¹ = r := by rw [mul_comm, ← mul_assoc, ← mul_comm R R⁻¹, CommGroupWithZero.mul_inv_cancel R this, one_mul]
      rw [U]

    rw [← sub_le_sub_iff_right ((r / R) * ‖f z‖)] at U0; ring_nf at U0
    rw [mul_assoc, U1, ← le_div_iff₀ U2, U3] at U0
    exact U0

  have maxBoundForF : ∀ r < R, 0 < r → ∀ z ∈ Metric.closedBall 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r pos_r
    exact AnalyticOn.norm_le_of_norm_le_on_sphere analytic
      (by linarith) (boundForF r hyp_r pos_r)

  by_cases pos_r : r = 0
  · have U : z = 0 := by rw [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z; exact hyp_z
    rw [U, pos_r]; rw [mul_zero, sub_zero, zero_div, norm_le_zero_iff]; exact zeroAtZero
  · have U : 0 ≤ r := by
      rw [mem_closedBall_iff_norm, sub_zero] at hyp_z; linarith [norm_nonneg z]
    exact maxBoundForF r (by linarith)
      (by
        apply lt_of_le_of_ne U
        · rw [ne_eq, eq_comm]; exact pos_r) z hyp_z
