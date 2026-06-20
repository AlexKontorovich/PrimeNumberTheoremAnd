/-
Copyright (c) 2025 Maksym Radziwill. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors : Maksym Radziwill
-/

import Architect
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.RemovableSingularity
import PrimeNumberTheoremAnd.StrongPNT


@[blueprint "divRemovable_zero"
  (title := "divRemovable-zero")
  (statement := /--
    Given a complex function $f$, we define the function
    $$g(z):=\begin{cases}
    \frac{f(z)}{z}, & z\neq 0;\\
    f'(0), & z=0.
    \end{cases}$$
  -/)]
noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ f z / z) 0 (deriv f 0)

@[blueprint "divRemovable_zero_of_ne_zero"
  (title := "divRemovalbe-zero-of-ne-zero")
  (statement := /--
    Let $f$ be a complex function and let $z\neq 0$. Then, with
    $g$ defined as in Definition~\ref{divRemovable_zero},
    $$g(z)=\frac{f(z)}{z}.$$
  -/)
  (proof := /--
    This follows directly from the definition of $g$.
  -/)
  (latexEnv := "lemma")]
lemma divRemovable_zero_of_ne_zero {z : ℂ} (f : ℂ → ℂ)
    (z_ne_0 : z ≠ 0) :
    divRemovable_zero f z = f z / z := by
  apply Function.update_of_ne z_ne_0

@[blueprint "AnalyticOn_divRemovable_zero"
  (title := "AnalyticOn-divRemovable-zero")
  (statement := /--
    Let $f$ be a complex function analytic on an open set $s$
    containing $0$ such that $f(0)=0$.
    Then, with $g$ defined as in
    Definition~\ref{divRemovable_zero}, $g$ is analytic on $s$.
  -/)
  (proof := /--
    We need to show that $g$ is complex differentiable at every
    point in $s$. For $z\neq 0$, this follows directly from the
    definition of $g$ and the fact that $f$ is analytic on $s$.
    For $z=0$, we use the definition of the derivative and the
    fact that $f(0)=0$:
    \[
    \lim_{z\to 0}\frac{g(z)-g(0)}{z-0}
    =\lim_{z\to 0}\frac{\frac{f(z)}{z}-f'(0)}{z}
    =\lim_{z\to 0}\frac{f(z)-f'(0)z}{z^2}
    =\lim_{z\to 0}\frac{f(z)-f(0)-f'(0)(z-0)}{(z-0)^2}=0,
    \]
    where the last equality follows from the definition of the
    derivative of $f$ at $0$. Thus, $g$ is complex differentiable
    at $0$ with derivative $0$, completing the proof.
  -/)
  (latexEnv := "lemma")]
lemma AnalyticOn_divRemovable_zero {f : ℂ → ℂ} {s : Set ℂ}
    (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
    (analytic : AnalyticOn ℂ f s) :
    AnalyticOn ℂ (divRemovable_zero f) s := by
  rw [Complex.analyticOn_iff_differentiableOn o,
    ← Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0]
  constructor
  · have (x) (hx : x ∈ s \ {0}) : x ≠ 0 := by
      rw [Set.mem_diff, Set.mem_singleton_iff] at hx
      exact hx.right
    rw [differentiableOn_congr (fun x hyp_x => Function.update_of_ne (this x hyp_x) _ _)]
    exact
      (analytic.mono Set.diff_subset).differentiableOn.fun_div
      (differentiableOn_id.mono (Set.subset_univ (s \ {0})))
      this
  · have U :=
      HasDerivAt.continuousAt_div (c := 0) (a := deriv f 0)
        (f := f)
        (DifferentiableOn.hasDerivAt
          ((Complex.analyticOn_iff_differentiableOn o).mp analytic)
          sInNhds0)
    simpa [divRemovable_zero, zero] using U

@[blueprint "AnalyticOn_divRemovable_zero_closedBall"
  (title := "AnalyticOn-divRemovable-zero-closedBall")
  (statement := /--
    Let $f$ be a complex function analytic on the closed ball
    $|z|\leq R$ such that $f(0)=0$.
    Then, with $g$ defined as in
    Definition~\ref{divRemovable_zero}, $g$ is analytic on
    $|z|\leq R$.
  -/)
  (proof := /--
    The proof is similar to that of
    Lemma~\ref{AnalyticOn_divRemovable_zero}, but we need to
    consider two cases: when $x$ is on the boundary of the closed
    ball and when it is in the interior.
    In the first case, we take a small open ball around $x$ that
    lies entirely within the closed ball, and apply
    Lemma~\ref{AnalyticOn_divRemovable_zero} on this smaller ball.
    In the second case, we can take the entire open ball centered
    at $0$ with radius $R$, and again apply
    Lemma~\ref{AnalyticOn_divRemovable_zero}.
    In both cases, we use the fact that $f(0)=0$ to ensure that
    the removable singularity at $0$ is handled correctly.
  -/)
  (latexEnv := "lemma")]
lemma AnalyticOn_divRemovable_zero_closedBall {f : ℂ → ℂ}
    {R : ℝ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zero : f 0 = 0) :
    AnalyticOn ℂ (divRemovable_zero f) (Metric.closedBall 0 R) := by
  apply analyticOn_of_locally_analyticOn
  intro x x_hyp
  simp only [Metric.mem_closedBall, dist_zero_right] at x_hyp
  cases x_hyp.eq_or_lt with
  | inl h =>
    use Metric.ball x (R / 2)
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp [Rpos]
    · have (x₂) (hyp_x₂ : x₂ ∈ Metric.closedBall 0 R ∩ Metric.ball x (R / 2)) : x₂ ≠ 0 := by
        rw [ball_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right,
          Set.mem_setOf_eq] at hyp_x₂
        rw [← norm_pos_iff]
        calc 0
          _ < R - ‖x₂ - x‖ := by
            obtain ⟨-, v⟩ := hyp_x₂
            linarith
          _ = ‖x‖ - ‖x - x₂‖ := by
            rw [h, norm_sub_rev]
          _ ≤ ‖x - (x - x₂)‖ := norm_sub_norm_le ..
          _ ≤ ‖x₂‖ := by rw [sub_sub_cancel]
      apply AnalyticOn.congr
      · exact (analytic.mono Set.inter_subset_left).div analyticOn_id this
      · intro x₃ hyp_x₃
        exact divRemovable_zero_of_ne_zero _ (this _ hyp_x₃)
  | inr h =>
    use Metric.ball 0 R
    refine ⟨Metric.isOpen_ball, ?_, ?_⟩
    · simp only [ball_eq, sub_zero, Set.mem_setOf_eq, h]
    · have si : Metric.closedBall (0 : ℂ) R ∩ Metric.ball (0 : ℂ) R =
        Metric.ball (0 : ℂ) R := by
        apply Set.inter_eq_self_of_subset_right
        exact Metric.ball_subset_closedBall
      rw [si]
      exact AnalyticOn_divRemovable_zero
        (Metric.ball_mem_nhds 0 Rpos)
        zero Metric.isOpen_ball
        (analytic.mono Metric.ball_subset_closedBall)

@[blueprint "schwartzQuotient"
  (title := "schwartzQuotient")
  (statement := /--
    Given a complex function $f$ and a real number $M$, we define
    the function
    $$f_{M}(z):=\frac{g(z)}{2M - f(z)},$$
    where $g$ is defined as in Definition~\ref{divRemovable_zero}.
  -/)]
noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) :
    ℂ → ℂ :=
  fun z ↦ divRemovable_zero f z / (2 * M - f z)

@[blueprint "AnalyticOn.schwartzQuotient"
  (title := "AnalyticOn.schwartzQuotient")
  (statement := /--
    Let $M>0$. Let $f$ be analytic on the closed ball $|z|\leq R$
    such that $f(0)=0$ and suppose that $2M - f(z)\neq 0$ for all
    $|z|\leq R$. Then, with $f_{M}$ defined as in
    Definition~\ref{schwartzQuotient}, $f_{M}$ is analytic on
    $|z|\leq R$.
  -/)
  (proof := /--
    This follows directly from
    Lemma~\ref{AnalyticOn_divRemovable_zero_closedBall} and the
    fact that the difference of two analytic functions is analytic.
  -/)
  (latexEnv := "lemma")]
lemma AnalyticOn.schwartzQuotient {f : ℂ → ℂ} {R : ℝ}
    (M : ℝ) (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (nonzero : ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0)
    (zero : f 0 = 0) :
    AnalyticOn ℂ (schwartzQuotient f M) (Metric.closedBall 0 R) :=
  AnalyticOn.div
    (AnalyticOn_divRemovable_zero_closedBall Rpos analytic zero)
    (AnalyticOn.sub analyticOn_const analytic) nonzero

@[blueprint "Complex.norm_le_norm_two_mul_sub_of_re_le"
  (title := "Complex.norm-le-norm-two-mul-sub-of-re-le")
  (statement := /--
    Let $M>0$ and let $x$ be a complex number such that
    $\Re x\leq M$. Then, $|x|\leq|2M - x|$.
  -/)
  (proof := /--
    We square both sides and simplify to obtain the equivalent
    inequality $$0\leq 4M^2 -4M\Re x,$$ which follows directly
    from the assumption $\Re x\leq M$ and the positivity of $M$.
  -/)
  (latexEnv := "lemma")]
lemma Complex.norm_le_norm_two_mul_sub_of_re_le {M : ℝ}
    {x : ℂ} (Mpos : 0 < M) (hyp_re_x : x.re ≤ M) :
    ‖x‖ ≤ ‖2 * M - x‖ := by
  rw [← sq_le_sq₀ (by positivity) (by positivity)]
  repeat rw [Complex.sq_norm, Complex.normSq_apply]
  rw [calc
    (2 * M - x).re * (2 * M - x).re +
        (2 * M - x).im * (2 * M - x).im =
      (2 * M - x.re) * (2 * M - x.re) +
        x.im * x.im := by simp
    _ = x.re * x.re +
        (x.im * x.im + 4 * M * (M - x.re)) := by ring]
  bound


@[blueprint "borelCaratheodory_closedBall"
  (title := "borelCaratheodory-closedBall")
  (statement := /--
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that
    $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$.
    Then for any $0 < r < R$,
    $$\sup_{|z|\leq r}|f(z)|\leq\frac{2Mr}{R-r}.$$
  -/)
  (proof := /--
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)\neq 0$ because
    $\Re (2M-f(z))=2M-\Re f(z)\geq M>0$. Additionally, since
    $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic
    on $|z|\leq R$. Likewise, $f_M(z)$ is analytic on
    $|z|\leq R$.
    Now note that $|f(z)|\leq|2M-f(z)|$ since $\Re f(z)\leq M$.
    Thus we have that
    $$|f_M(z)|=\frac{|f(z)|/|z|}{|2M-f(z)|}
      \leq\frac{1}{|z|}.$$
    Now by the maximum modulus principle, we know the maximum of
    $|f_M|$ must occur on the boundary where $|z|=R$. Thus,
    $|f_M(z)|\leq 1/R$ for all $|z|\leq R$. So for $|z|=r$ we
    have
    $$|f_M(z)|=\frac{|f(z)|/r}{|2M-f(z)|}\leq\frac{1}{R}
    \implies R\,|f(z)|\leq r\,|2M-f(z)|\leq 2Mr+r\,|f(z)|.$$
    Which by algebraic manipulation gives
    $$|f(z)|\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the
    maximum of $|f|$ must occur on the boundary where $|z|=r$.
    Thus, the desired result immediately follows
  -/)]
theorem borelCaratheodory_closedBall {M R r : ℝ} {z : ℂ}
    {f : ℂ → ℂ} (Rpos : 0 < R)
    (analytic : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R)
    (hyp_z : z ∈ Metric.closedBall 0 r) :
    ‖f z‖ ≤ (2 * M * r) / (R - r) := by
  have zInSFunc :
      ∀ r ≤ R, ∀ z ∈ Metric.sphere (0 : ℂ) r,
      z ∈ Metric.closedBall (0 : ℂ) R := by
    intro r hyp_r z hyp_z
    exact Set.mem_of_mem_of_subset hyp_z <|
      (Metric.sphere_subset_closedBall).trans
        (Metric.closedBall_subset_closedBall hyp_r)
  have fPosAll :
      ∀ z ∈ Metric.closedBall 0 R, 2 * M - f z ≠ 0 := by
    intro z zInS
    exact Complex.ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.mul_re, Complex.re_ofNat, Complex.ofReal_re,
        Complex.im_ofNat, Complex.ofReal_im, mul_zero, sub_zero, sub_pos]
      linarith [realPartBounded z zInS])
  have schwartzQuotientBounded :
      ∀ z ∈ Metric.sphere 0 R,
      ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by linarith)
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc R le_rfl z hyp_z
    rw [mem_sphere_iff_norm, sub_zero] at hyp_z
    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by
        simp only [Complex.norm_div, divRemovable_zero_of_ne_zero f zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0
        · simp only [h, zero_div, div_zero, le_refl]
        · exact div_le_div_of_nonneg_left
            (by positivity) (by positivity)
            (Complex.norm_le_norm_two_mul_sub_of_re_le
              Mpos (realPartBounded z zInS))
      _ ≤ 1 / ‖z‖ := by
        rw [div_right_comm]
        exact div_le_div_of_nonneg_right (div_self_le_one _) (norm_nonneg _)
      _ = 1 / R := by rw [hyp_z]
  have maxMod (z) (hz : z ∈ Metric.closedBall 0 R) : ‖schwartzQuotient f M z‖ ≤ 1 / R :=
    AnalyticOn.norm_le_of_norm_le_on_sphere le_rfl
      (AnalyticOn.schwartzQuotient M Rpos analytic fPosAll zeroAtZero)
      schwartzQuotientBounded hz
  have boundForF :
      ∀ r < R, 0 < r →
      ∀ z ∈ Metric.sphere 0 r,
      ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r hyp_r r_pos z zOnR
    have zInS : z ∈ Metric.closedBall 0 R :=
      zInSFunc r hyp_r.le z zOnR
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z zInS
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by
      rwa [← norm_pos_iff, zOnR]
    simp only [divRemovable_zero_of_ne_zero f U, Complex.norm_div, one_div] at this
    have U : 0 < r * ‖2 * M - f z‖ := by
      simp only [r_pos, mul_pos_iff_of_pos_left, norm_pos_iff, ne_eq, fPosAll z zInS,
        not_false_eq_true]
    rw [zOnR, div_div, div_le_iff₀' U] at this
    have U0 :
        ‖f z‖ ≤ 2 * M * r / R + (r / R) * ‖f z‖ := by
      calc ‖f z‖
        _ ≤ r * ‖2 * M - f z‖ * R⁻¹ := this
        _ ≤ r * (‖(2 : ℂ) * M‖ + ‖f z‖) * R⁻¹ := by
          grw [norm_sub_le]
        _ = r * (2 * M + ‖f z‖) * R⁻¹ := by
          simp [Mpos.le]
        _ = 2 * M * r / R + (r / R) * ‖f z‖ := by
          ring_nf
    rw [← tsub_le_iff_right, ← one_sub_mul, ← le_div_iff₀'] at U0
    · have hR : (R : ℝ) ≠ 0 := Rpos.ne'
      have hRr : R - r ≠ 0 := sub_ne_zero.mpr (ne_of_lt hyp_r).symm
      have heq : 2 * M * r / (R - r) = 2 * M * r / R / (1 - r / R) := by
        rw [one_sub_div hR]; field_simp
      rw [heq]
      exact U0
    · rwa [sub_pos, div_lt_one₀ Rpos]
  have maxBoundForF
      (r) (hyp_r : r < R) (pos_r : 0 < r)
      (z) (hz : z ∈ Metric.closedBall 0 r) :
      ‖f z‖ ≤ 2 * M * r / (R - r) :=
    AnalyticOn.norm_le_of_norm_le_on_sphere hyp_r.le analytic (boundForF r hyp_r pos_r) hz
  have U : 0 ≤ r := by
    rw [mem_closedBall_iff_norm, sub_zero] at hyp_z
    exact (norm_nonneg z).trans hyp_z
  cases U.eq_or_lt' with
  | inl pos_r =>
    obtain rfl : z = 0 := by
      rwa [pos_r, Metric.closedBall_zero, Set.mem_singleton_iff] at hyp_z
    rwa [pos_r, mul_zero, sub_zero, zero_div, norm_le_zero_iff]
  | inr pos_r =>
    exact maxBoundForF r hyp_r pos_r z hyp_z
