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
import StrongPNT.BorelCaratheodory


open Nat Filter

--open scoped ArithmeticFunction

/-%%
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
%%-/

/-%%
\begin{theorem}[BorelCaratheodory]\label{BorelCaratheodory}\lean{BorelCaratheodory}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\sup_{\abs{z}\leq r}\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
\end{theorem}
%%-/

noncomputable abbrev divRemovable_zero (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

-- Away from zero divRemovable_zero f z is equal to f z / z

lemma divRemovable_zero_of_ne_zero (f : ℂ → ℂ) (z : ℂ) : z ≠ 0 → divRemovable_zero f z = f z / z := by
  intro hyp_z; unfold divRemovable_zero; apply Function.update_of_ne hyp_z

-- If f is analytic on an open set and f 0 = 0 then f z / z is also
-- analytic on the same open set.

lemma AnalyticOn.divRemovable_zero (f : ℂ → ℂ) (s : Set ℂ)
  (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
  (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (divRemovable_zero f) s :=
  by
     rw [Complex.analyticOn_iff_differentiableOn o, ←(Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0)]
     constructor
     · rw [differentiableOn_congr (by intros; apply Function.update_of_ne; grind)]
       exact DifferentiableOn.fun_div (AnalyticOn.differentiableOn (AnalyticOn.mono analytic Set.diff_subset)) (DifferentiableOn.mono (differentiableOn_id (s := Set.univ)) (Set.subset_univ (s \ {0}))) (by grind)

     · have U := HasDerivAt.continuousAt_div (c := 0) (a := (deriv f) 0) (f := f) (DifferentiableOn.hasDerivAt ((Complex.analyticOn_iff_differentiableOn o).mp analytic) sInNhds0)
       have T : (fun (x : ℂ) ↦ (f x - 0) / (x - 0)) = (fun (x : ℂ) ↦ (f x) / x) := by funext; grind
       rw [zero, T] at U; exact U

-- The proof of the Lemma below is cumbersome, a proper way would be to
-- show that if f is analytic on a closed set C, then it is analytic on an
-- open set O containing the closed set C and apply the previous lemma.

lemma AnalyticOn_divRemovable_zero_closedBall (f : ℂ → ℂ) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = Metric.closedBall 0 R}
  (analytic : AnalyticOn ℂ f s) (zero : f 0 = 0):
  AnalyticOn ℂ (divRemovable_zero f) s := by
    apply analyticOn_of_locally_analyticOn
    intro x; intro x_hyp
    by_cases h : ‖x‖ = R
    · use Metric.ball x (R / 2)
      constructor
      · exact Metric.isOpen_ball
      · constructor
        · rw [ball_eq]; simp; positivity
        · have Z : ∀w ∈ s ∩ Metric.ball x (R / 2), divRemovable_zero f w = f w / w := by
             intro x₂; intro hyp_x₂
             apply divRemovable_zero_of_ne_zero
             simp [setIsBall, ball_eq] at hyp_x₂
             rw [← norm_pos_iff]
             calc ‖x₂‖
               _ = ‖x - (x - x₂)‖ := by simp
               _ ≥ ‖x‖ - ‖x - x₂‖ := by apply norm_sub_norm_le
               _ = R - ‖x₂ - x‖ := by simp [h, norm_sub_rev]
               _ > 0 := by linarith

          apply AnalyticOn.congr (g := divRemovable_zero f) (f := fun x ↦ f x / x)
          · apply AnalyticOn.div
            · apply AnalyticOn.mono (s := s ∩ Metric.ball x (R / 2)) (t := s)
              · exact analytic
              · exact Set.inter_subset_left
            · exact analyticOn_id
            · intro x₁; intro hyp_x₁
              simp [setIsBall, ball_eq] at hyp_x₁
              rw [← norm_pos_iff]
              calc ‖x₁‖
                   _ = ‖x - (-(x₁ - x))‖ := by simp
                   _ ≥ ‖x‖ - ‖-(x₁ - x)‖ := by apply norm_sub_norm_le
                   _ = R - ‖x₁ - x‖ := by simp [h, norm_sub_rev]
                   _ > 0 := by linarith
          · simp [Set.EqOn.eq_1]
            intro x₃; intro hyp_x₃; intro dist_hyp
            have : x₃ ∈ s ∩ Metric.ball x (R / 2) := by
              apply Set.mem_inter hyp_x₃
              · rw [Metric.mem_ball]; exact dist_hyp
            exact Z x₃ this

    · use Metric.ball 0 R
      constructor
      · exact Metric.isOpen_ball
      · constructor
        · rw [ball_eq]; simp; simp [setIsBall] at x_hyp; grind
        · have si : s ∩ Metric.ball 0 R = Metric.ball 0 R := by
            apply Set.inter_eq_self_of_subset_right
            simp [setIsBall] at x_hyp
            simp [setIsBall]
            exact Metric.ball_subset_closedBall
          · rw [si]; apply AnalyticOn.divRemovable_zero f
            · apply Metric.ball_mem_nhds; positivity
            · exact zero
            · apply Metric.isOpen_ball
            · apply AnalyticOn.mono (t := s) (s := Metric.ball 0 R) analytic
              · rw [setIsBall]; apply Metric.ball_subset_closedBall

noncomputable abbrev schwartzQuotient (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (divRemovable_zero f z) / (2 * M - f z)

-- AnalyticOn.schwartzQuotient establishes that f_{M}(z) is analytic.

lemma AnalyticOn.schwartzQuotient (f : ℂ → ℂ) (M : ℝ) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = Metric.closedBall 0 R}
  (analytic : AnalyticOn ℂ f s) (nonzero: ∀z ∈ s, 2 * M - f z ≠ 0)
  (zero : f 0 = 0): AnalyticOn ℂ (schwartzQuotient f M) s := by

  have sInNhds0 : s ∈ nhds 0 := by
    rw [setIsBall]; apply Metric.closedBall_mem_nhds; exact Rpos

  exact AnalyticOn.div (AnalyticOn_divRemovable_zero_closedBall (R := R) (Rpos := Rpos) (setIsBall := setIsBall) f s analytic zero) (AnalyticOn.sub (analyticOn_const) analytic) nonzero

-- If Re x ≤ M then |x| ≤ |2 * M - x|, this simple inequality is used in the proof of borelCaratheodory_closedBall.

lemma Complex.norm_le_norm_two_mul_sub_of_re_le (x : ℂ) (M : ℝ) (Mpos : 0 < M) : x.re ≤ M → ‖x‖ ≤ ‖2 * M - x‖ := by
  intro hyp_re_x
  have Z : M ^ 2 = M * M := by grind
  rw [← sq_le_sq₀ (by positivity) (by positivity), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]; simp; ring_nf
  simp [add_comm (-(x.re * M * 4)) (x.re ^ 2), add_assoc, le_add_iff_nonneg_right (x.re ^ 2), Z, mul_le_mul_right Mpos]; exact hyp_re_x

-- This is a version of the maximum modulus principle specialized to closed balls.

lemma AnalyticOn.norm_le_of_norm_le_on_sphere (f : ℂ → ℂ) (C : ℝ) (r : ℝ) {R : ℝ} {s : Set ℂ} {setIsBall : s = Metric.closedBall 0 R} (analytic : AnalyticOn ℂ f s) (hyp_r : r ≤ R) (cond : ∀z ∈ Metric.sphere 0 r, ‖f z‖ ≤ C) : ∀w ∈ Metric.closedBall 0 r, ‖f w‖ ≤ C :=
    by
      intro w; intro wInS
      apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := Metric.closedBall 0 r) (Metric.isBounded_closedBall)
      · apply DifferentiableOn.diffContOnCl; rw [Metric.closure_closedBall]
        apply AnalyticOn.differentiableOn
        apply AnalyticOn.mono (f := f) (s := Metric.closedBall 0 r) (t := s) (𝕜 := ℂ) analytic
        · rw [setIsBall]; apply Metric.closedBall_subset_closedBall; grind
      · rw [frontier_closedBall']; exact cond
      · rw [Metric.closure_closedBall]; exact wInS

-- We can now prove Borel-Caratheodory for closed balls

theorem borelCaratheodory_closedBall (M : ℝ) (Mpos : 0 < M) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = Metric.closedBall 0 R}
  (f : ℂ → ℂ) (analytic : AnalyticOn ℂ f s)
  (zeroAtZero: f 0 = 0) (realPartBounded: ∀z ∈ s, (f z).re ≤ M)
  : ∀r < R, ∀z ∈ Metric.closedBall 0 r, ‖f z‖ ≤ (2 * M * r) / (R - r) := by

  intro r; intro hyp_r; intro z; intro hyp_z;

  have zInSFunc : ∀r ≤ R, ∀z ∈ Metric.sphere 0 r, z ∈ s := by
      intro r; intro hyp_r; intro z; intro hyp_z
      apply Set.mem_of_mem_of_subset (s := Metric.sphere 0 r) hyp_z
      · rw [setIsBall]
        calc Metric.sphere (0 : ℂ) r
          _ ⊆ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall
          _ ⊆ Metric.closedBall (0 : ℂ) R := Metric.closedBall_subset_closedBall hyp_r

  have fPosAll : ∀z ∈ s, 2 * M - f z ≠ 0 := by
    intro z; intro zInS
    exact Complex.ne_zero_of_re_pos (by simp; linarith [realPartBounded z zInS])

  have schwartzQuotientBounded : ∀z ∈ Metric.sphere 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    intro z; intro hyp_z
    have zNe0 : z ≠ 0 := by
      rw [mem_sphere_zero_iff_norm] at hyp_z
      exact ne_zero_of_norm_ne_zero (by grind)
    have zInS : z ∈ s := zInSFunc R (by rfl) z hyp_z
    simp [mem_sphere_iff_norm] at hyp_z

    calc ‖schwartzQuotient f M z‖
      _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by simp [divRemovable_zero_of_ne_zero f z zNe0]
      _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
        by_cases h : ‖f z‖ = 0;
        · simp [h]
        · exact div_le_div_of_nonneg_left (by positivity) (by positivity) (Complex.norm_le_norm_two_mul_sub_of_re_le (f z) M Mpos (realPartBounded z zInS))
      _ ≤ (1 / ‖z‖) := by
        by_cases h : ‖f z‖ = 0
        · simp [h]
        · rw [div_div, mul_comm, ← div_div, div_self]; exact h
      _ = 1 / R := by rw [hyp_z]

  have maxMod: ∀z ∈ Metric.closedBall 0 R, ‖schwartzQuotient f M z‖ ≤ 1 / R := by
    exact AnalyticOn.norm_le_of_norm_le_on_sphere (setIsBall := setIsBall) (schwartzQuotient f M) (1 / R) R (AnalyticOn.schwartzQuotient f M s (setIsBall := setIsBall) (R := R) (Rpos := Rpos) analytic fPosAll zeroAtZero) (by rfl) schwartzQuotientBounded

  have boundForF : ∀r < R, 0 < r → ∀z ∈ Metric.sphere 0 r, ‖f z‖ ≤ 2 * M * r / (R - r) := by
    intro r; intro hyp_r; intro r_pos; intro z; intro zOnR
    have zInS : z ∈ s := zInSFunc r (by grind) z (zOnR)
    rw [mem_sphere_zero_iff_norm] at zOnR
    have := maxMod z (by simp [← setIsBall, zInS])
    unfold schwartzQuotient at this
    have U : z ≠ 0 := by rw [← norm_pos_iff]; linarith
    rw [divRemovable_zero_of_ne_zero f z U] at this
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
    intro r; intro hyp_r; intro pos_r
    exact AnalyticOn.norm_le_of_norm_le_on_sphere (setIsBall := setIsBall) f (2 * M * r / (R - r)) r (analytic) (by grind) (boundForF r hyp_r pos_r)

  by_cases pos_r : r = 0
  · have U : z = 0 := by simp [pos_r] at hyp_z; exact hyp_z
    rw [U, pos_r]; simp; exact zeroAtZero
  · have U : 0 ≤ r := by
      rw [mem_closedBall_iff_norm] at hyp_z; simp at hyp_z; linarith [norm_nonneg z]
    exact maxBoundForF r (by grind) (by grind) z hyp_z

/-%%
\begin{proof}
\uses{}
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)≠ 0$ because $ℐfrak{R}(2M-f(z))=2M-ℐfrak{R}f(z)≥ M>0$. Additionally, since $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $\abs{z}\leq R$. Likewise, $f_M(z)$ is analytic on $\abs{z}\leq R$.

    Now note that $\abs{f(z)}\leq\abs{2M-f(z)}$ since $ℐfrak{R}f(z)\leq M$. Thus we have that
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/\abs{z}}{\abs{2M-f(z)}}\leq\frac{1}{\abs{z}}.$$
    Now by the maximum modulus principle, we know the maximum of $\abs{f_M}$ must occur on the boundary where $\abs{z}=R$. Thus, $\abs{f_M(z)}\leq 1/R$ for all $\abs{z}\leq R$. So for $\abs{z}=r$ we have
    $$\abs{f_M(z)}=\frac{\abs{f(z)}/r}{\abs{2M-f(z)}}\leq\frac{1}{R}\implies R\,\abs{f(z)}\leq r\,\abs{2M-f(z)}\leq 2Mr+r\,\abs{f(z)}.$$
    Which by algebraic manipulation gives
    $$\abs{f(z)}\leq\frac{2Mr}{R-r}.$$
    Once more, by the maximum modulus principle, we know the maximum of $\abs{f}$ must occur on the boundary where $\abs{z}=r$. Thus, the desired result immediately follows
\end{proof}
%%-/



/-%%
\begin{lemma}[DerivativeBound]\label{DerivativeBound}\lean{DerivativeBound}
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then we have that
    $$\abs{f'(z)}\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $\abs{z}\leq r$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    By Cauchy's integral formula we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{\abs{w}=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        \abs{f'(z)}=\abs{\frac{1}{2\pi}\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt}\leq\frac{1}{2\pi}\int_0^{2\pi}\abs{\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}}\,dt.
    \end{equation}
    Now applying Theorem \ref{BorelCaratheodory}, and noting that $r'-r\leq\abs{r'e^{it}-z}$, we have that
    $$\abs{\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}}\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral completes the proof.
\end{proof}
%%-/



/-%%
\begin{theorem}[BorelCaratheodoryDeriv]\label{BorelCaratheodoryDeriv}\lean{BorelCaratheodoryDeriv}
    Let $R,\,M>0$. Let $f$ be analytic on $\abs{z}\leq R$ such that $f(0)=0$ and suppose $\mathfrak{R}f(z)\leq M$ for all $\abs{z}\leq R$. Then for any $0 < r < R$,
    $$\abs{f'(z)}\leq\frac{16MR^2}{(R-r)^3}$$
    for all $\abs{z}\leq r$.
\end{theorem}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$, we have that
    $$\abs{f'(z)}\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[LogOfAnalyticFunction]\label{LogOfAnalyticFunction}\lean{LogOfAnalyticFunction}
    Let $0 < r < R<1$. Let $B:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_R}$ with $B(z)\neq 0$ for all $z\in\overline{\mathbb{D}_R}$. Then there exists $J_B:\overline{\mathbb{D}_r}\to\mathbb{C}$ that is analytic on neighborhoods of points in $\overline{\mathbb{D}_r}$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$
        \item $\log\abs{B(z)}-\log\abs{B(0)}=\mathfrak{R}J_B(z)$
    \end{itemize}
    for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    We let $J_B(z)=\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0)$. Then clearly, $J_B(0)=0$ and $J_B'(z)=B'(z)/B(z)$. Showing the third property is a little more difficult, but by no standards terrible. Exponentiating $J_B(z)$ we have that
    $$\exp(J_B(z))=\exp(\mathrm{Log}\,B(z)-\mathrm{Log}\,B(0))=\frac{B(z)}{B(0)}\implies B(z)=B(0)\exp(J_B(z)).$$
    Now taking the modulus
    $$\abs{B(z)}=\abs{B(0)}\cdot\abs{\exp(J_B(z))}=\abs{B(0)}\cdot\exp(\mathfrak{R}J_B(z)).$$
    Taking the real logarithm of both sides and rearranging gives the third point.
\end{proof}
%%-/



/-%%
\begin{definition}[SetOfZeros]\label{SetOfZeros}\lean{SetOfZeros}
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:\abs{\rho}\leq R,\,f(\rho)=0\}$.
\end{definition}
%%-/



/-%%
\begin{definition}[ZeroOrder]\label{ZeroOrder}\lean{ZeroOrder}
    Let $0 < R<1$ and $f:\mathbb{C}\to\mathbb{C}$ be analtyic on neighborhoods of points in $\overline{\mathbb{D}_1}$. For any zero $\rho\in\mathcal{K}_f(R)$, we define $m_f(\rho)$ as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
%%-/



/-%%
\begin{lemma}[ZeroFactorization]\label{ZeroFactorization}\lean{ZeroFactorization}
    Let $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be  analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. For all $\rho\in\mathcal{K}_f(1)$ there exists $h_\rho(z)$ that is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n=(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
\end{proof}
%%-/



/-%%
\begin{definition}[CFunction]\label{CFunction}\lean{CFunction}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $C_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows. This function is constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
\end{definition}
%%-/



/-%%
\begin{definition}[BlaschkeB]\label{BlaschkeB}\lean{BlaschkeB}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a function $B_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}\left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
\end{definition}
%%-/



/-%%
\begin{lemma}[BlaschkeOfZero]\label{BlaschkeOfZero}\lean{BlaschkeOfZero}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then
    $$\abs{B_f(0)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$\abs{B_f(0)}=\abs{C_f(0)}\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}=\abs{f(0)}\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}.$$
\end{proof}
%%-/



/-%%
\begin{lemma}[DiskBound]\label{DiskBound}\lean{DiskBound}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then $\abs{B_f(z)}\leq B$ for $\abs{z}\leq R$ also.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    For $\abs{z}=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$\abs{B_f(z)}=\abs{f(z)}\prod_{\rho\in\mathcal{K}_f(r)}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.$$
    But note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=\frac{\abs{R^2-z\overline{\rho}}/R}{\abs{z-\rho}}=\frac{\abs{z}\cdot\abs{\overline{z-\rho}}/R}{\abs{z-\rho}}=1.$$
    So we have that $\abs{B_f(z)}=\abs{f(z)}\leq B$ when $\abs{z}=R$. Now by the maximum modulus principle, we know that the maximum of $\abs{B_f}$ must occur on the boundary where $\abs{z}=R$. Thus $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[JensenForm]\label{JensenForm}\lean{JensenForm}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Since $f(0)=1$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}=\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}\leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{\abs{\rho}}\right)^{m_f(\rho)}=\abs{B_f(0)}\leq B$$
    whereby Lemma \ref{DiskBound} we know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$.
\end{proof}
%%-/



/-%%
\begin{lemma}[ZerosBound]\label{ZerosBound}\lean{ZerosBound}
    Let $B>1$ and $0 < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for $\abs{z}\leq R$, then
    $$\abs{\mathcal{K}_f(r)}\leq\frac{\log B}{\log(R/r)}.$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Using Lemma \ref{JensenForm} we have that
    $$(R/r)^{\abs{\mathcal{K}_f(r)}}=(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}1}\leq(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}\leq B.$$
    Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
%%-/



/-%%
\begin{definition}[JBlaschke]\label{JBlaschke}\lean{JBlaschke}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define $L_f(z)=J_{B_f}(z)$ where $J$ is from Lemma \ref{LogOfAnalyticFunction} and $B_f$ is from Definition \ref{BlaschkeB}.
\end{definition}
%%-/



/-%%
\begin{lemma}[BlaschkeNonZero]\label{BlaschkeNonZero}\lean{BlaschkeNonZero}
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}(z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        \abs{B_f(z)}=\abs{h_z(z)}\cdot\abs{R-\frac{\abs{z}^2}{R}}^{m_f(z)}\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.
    \end{equation}
    Trivially, $\abs{h_z(z)}\neq 0$. Now note that
    $$\abs{R-\frac{\abs{z}^2}{R}}=0\implies\abs{z}=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. Similarly, note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=0\implies\abs{z}=\frac{R^2}{\abs{\overline{\rho}}}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/\abs{\overline{\rho}}=\abs{z}$, but $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. So, we know that
    $$\abs{R-\frac{\abs{z}^2}{R}}\neq 0\qquad\text{and}\qquad\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $\abs{B_f(z)}\neq 0$. So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        \abs{B_f(z)}=\abs{f(z)}\prod_{\rho\in\mathcal{K}_f(r)}\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}^{m_f(\rho)}.
    \end{equation}
    We know that $\abs{f(z)}\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}=0\implies\abs{z}=\frac{R^2}{\abs{\overline{\rho}}}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that $R < R^2/\abs{\overline{\rho}}=\abs{z}$, but $z\in\overline{\mathbb{D}_r}$ tells us that $\abs{z}\leq r < R$. So, we know that
    $$\abs{\frac{R-z\overline{\rho}/R}{z-\rho}}\neq 0\quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $\abs{B_f(z)}\neq 0$. So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and $z\not\in\mathcal{K}_f(r)$, so the result follows.
\end{proof}
%%-/



/-%%
\begin{lemma}[JBlaschkeDerivBound]\label{JBlaschkeDerivBound}\lean{JBlaschkeDerivBound}
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $\abs{f(z)}\leq B$ for all $\abs{z}\leq R$, then for all $\abs{z}\leq r'$
    $$\abs{L_f'(z)}\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{lemma}
%%-/

/-%%
\begin{proof}
\uses{}
    By Lemma \ref{DiskBound} we immediately know that $\abs{B_f(z)}\leq B$ for all $\abs{z}\leq R$. Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Lemma \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad \mathfrak{R}L_f(z)=\log\abs{B_f(z)}-\log\abs{B_f(0)}\leq\log\abs{B_f(z)}\leq\log B$$
    for all $\abs{z}\leq r$. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$\abs{L_f'(z)}\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $\abs{z}\leq r'$.
\end{proof}
%%-/



/-%

Main Theorem: The Prime Number Theorem in strong form.
\begin{theorem}[PrimeNumberTheorem]\label{StrongPNT}\lean{PrimeNumberTheorem}\uses{thm:StrongZeroFree, ChebyshevPsi, SmoothedChebyshevClose, ZetaBoxEval}
There is a constant $c > 0$ such that
$$
\psi(x) = x + O(x \exp(-c \sqrt{\log x}))
$$
as $x\to \infty$.
\end{theorem}

%-/

-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
