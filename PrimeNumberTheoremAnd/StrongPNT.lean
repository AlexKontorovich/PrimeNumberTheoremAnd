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

noncomputable abbrev fDiv (f : ℂ → ℂ) : ℂ → ℂ :=
  Function.update (fun z ↦ (f z) / z) 0 ((deriv f) 0)

lemma fDivAwayZero (f : ℂ → ℂ) (z : ℂ) : z ≠ 0 → fDiv f z = f z / z := by
  intro hyp_z
  unfold fDiv
  apply Function.update_of_ne
  exact hyp_z

-- If f is analytic on an open set and f 0 = 0 then f z / z is also
-- analytic on the same open set.

lemma fDivAnalytic (f : ℂ → ℂ) (s : Set ℂ)
  (sInNhds0 : s ∈ nhds 0) (zero : f 0 = 0) (o : IsOpen s)
  (analytic : AnalyticOn ℂ f s) : AnalyticOn ℂ (fDiv f) s :=
  by
     rw [Complex.analyticOn_iff_differentiableOn o, ←(Complex.differentiableOn_compl_singleton_and_continuousAt_iff sInNhds0)]
     constructor
     · rw [differentiableOn_congr (by intros; apply Function.update_of_ne; grind)]
       exact DifferentiableOn.fun_div (AnalyticOn.differentiableOn (AnalyticOn.mono analytic Set.diff_subset)) (DifferentiableOn.mono (differentiableOn_id (s := Set.univ)) (Set.subset_univ (s \ {0}))) (by grind)

     · have U := HasDerivAt.continuousAt_div (c := 0) (a := (deriv f) 0) (f := f) (DifferentiableOn.hasDerivAt ((Complex.analyticOn_iff_differentiableOn o).mp analytic) sInNhds0)
       have T : (fun (x : ℂ) ↦ (f x - 0) / (x - 0)) = (fun (x : ℂ) ↦ (f x) / x) := by funext; grind
       rw [zero, T] at U; exact U

-- Proving that fDiv is analytic on a _closed_ ball if f is analytic
-- on a _closed_ ball is cumbersome because we need to show implicitly
-- that there is a larger open set that contains the closed ball on which
-- f is analytic. Only then we can apply the previous Lemma.

lemma fDivAnalyticClosedBall (f : ℂ → ℂ) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = {z | ‖z‖ ≤ R}}
  (analytic : AnalyticOn ℂ f s) (zero : f 0 = 0):
  AnalyticOn ℂ (fDiv f) s := by
    apply analyticOn_of_locally_analyticOn
    intro x
    intro x_hyp
    by_cases h : ‖x‖ = R
    · use Metric.ball x (R / 2)
      constructor
      · exact Metric.isOpen_ball
      · constructor
        · rw [ball_eq]; simp; positivity
        · have Z : ∀w ∈ s ∩ Metric.ball x (R / 2), fDiv f w = f w / w := by
             intro x₂
             intro hyp_x₂
             unfold fDiv
             apply Function.update_of_ne
             rw [setIsBall, ball_eq] at hyp_x₂
             simp at hyp_x₂
             have Z : ‖x₂‖ ≥ R / 2 := by
                calc ‖x₂‖
                  _ = ‖x - (x - x₂)‖ := by simp
                  _ ≥ ‖x‖ - ‖x - x₂‖ := by apply norm_sub_norm_le
                  _ = R - ‖x₂ - x‖ := by simp [h, norm_sub_rev]
                  _ ≥ R - R / 2 := by linarith
                  _ = R / 2 := by linarith
             have U : ‖x₂‖ ≠ 0 := by linarith
             apply ne_zero_of_norm_ne_zero U

          apply AnalyticOn.congr (g := fDiv f) (f := fun x ↦ f x / x)
          · apply AnalyticOn.div
            · apply AnalyticOn.mono (s := s ∩ Metric.ball x (R / 2)) (t := s)
              · exact analytic
              · exact Set.inter_subset_left
            · apply analyticOn_id
            · intro x₁
              intro hyp_x₁
              rw [setIsBall, ball_eq] at hyp_x₁
              simp at hyp_x₁
              have Z : ‖x₁‖ ≥ R / 2 :=
                by
                calc ‖x₁‖
                   _ = ‖x - (-(x₁ - x))‖ := by simp
                   _ ≥ ‖x‖ - ‖-(x₁ - x)‖ := by apply norm_sub_norm_le
                   _ = R - ‖x₁ - x‖ := by simp [h, norm_sub_rev]
                   _ ≥ R / 2 := by linarith
              have U : ‖x₁‖ ≠ 0 := by linarith
              exact ne_zero_of_norm_ne_zero U
          · simp [Set.EqOn.eq_1]
            intro x₃
            intro hyp_x₃
            intro dist_hyp
            have : x₃ ∈ s ∩ Metric.ball x (R / 2) := by
              apply Set.mem_inter
              · exact hyp_x₃
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
            rw [ball_eq]
            simp
            simp [setIsBall]
            grind
          rw [si]
          apply fDivAnalytic
          · apply IsOpen.mem_nhds (s := Metric.ball 0 R) (x := 0)
            · apply Metric.isOpen_ball
            · simp; positivity
          · exact zero
          · apply Metric.isOpen_ball
          · apply AnalyticOn.mono (s := Metric.ball 0 R) (t := s)
            · exact analytic
            · grind

noncomputable abbrev fM (f : ℂ → ℂ) (M : ℝ) : ℂ → ℂ :=
  fun z ↦ (fDiv f z) / (2 * M - f z)

-- We show that f_{M}(z) is analytic.

lemma fMAnalytic (f : ℂ → ℂ) (M : ℝ) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = {z | ‖z‖ ≤ R}}
  (analytic : AnalyticOn ℂ f s) (nonzero: ∀z ∈ s, 2 * M - f z ≠ 0)
  (zero : f 0 = 0): AnalyticOn ℂ (fM f M) s := by

  have sInNhds0 : s ∈ nhds 0 := by
    have U : s = Metric.closedBall 0 R := by apply Set.ext; simp [setIsBall]
    rw [U]; apply Metric.closedBall_mem_nhds; positivity

  have fMAnalytic : AnalyticOn ℂ (fM f M) s := by
     apply AnalyticOn.div
     · exact fDivAnalyticClosedBall (R := R) (Rpos := Rpos) (setIsBall := setIsBall) f s analytic zero
     · apply AnalyticOn.sub
       · apply analyticOn_const
       · exact analytic
     · exact nonzero

  exact fMAnalytic

-- If Re x ≤ M then |x| ≤ |2 * M - x|.

lemma simpleIneq (x : ℂ) (M : ℝ) (Mpos : 0 < M) : x.re ≤ M → ‖x‖ ≤ ‖2 * M - x‖ := by
  intro hyp_re_x
  rw [← sq_le_sq₀ (by positivity) (by positivity), Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring_nf
  rw [add_comm (-(x.re * M * 4)) (x.re ^ 2), add_assoc, le_add_iff_nonneg_right (x.re ^ 2)]
  simp
  have Z : M ^ 2 = M * M := by grind
  rw [Z, (mul_le_mul_right Mpos)]
  exact hyp_re_x

-- Add Lemma that for z ≠ 0 , fDiv f z = f z / z otherwise
-- we redo it every single time.

theorem borel_caratheodory (M : ℝ) (Mpos : M > 0) (s : Set ℂ)
  {R : ℝ} {Rpos : 0 < R} {setIsBall : s = {z | ‖z‖ ≤ R}}
  (f : ℂ → ℂ) (analytic : AnalyticOn ℂ f s)
  (zeroAtZero: f 0 = 0)
  (realPartBounded: ∀z ∈ s, (f z).re ≤ M)
  : ∀(r : ℝ), ∀(z : ℂ), r ≤ R → ‖z‖ ≤ r
  → ‖f z‖ ≤ (2 * M * r) / (R - r) := by

  intro r; intro z; intro hyp_r; intro hyp_z

  have zInS : z ∈ s := by rw [setIsBall]; simp; linarith

  have fPos : 2 * M - f z ≠ 0 := Complex.ne_zero_of_re_pos (by simp; linarith [realPartBounded z zInS])

  have fMBounded : z ≠ 0 → ‖fM f M z‖ ≤ 1 / ‖z‖ := by
    intro hyp_z

    have := calc ‖fM f M z‖
           _ = (‖f z‖ / ‖z‖) / ‖2 * M - f z‖ := by unfold fM; rw [fDivAwayZero f z hyp_z]; simp
           _ ≤ (‖f z‖ / ‖z‖) / ‖f z‖ := by
               by_cases h : ‖f z‖ = 0;
               · rw [h]; simp
               · apply div_le_div_of_nonneg_left
                 · positivity
                 · positivity
                 · exact simpleIneq (f z) M (Mpos) (realPartBounded z zInS)
            _ ≤ (1 / ‖z‖) := by
               by_cases h : ‖f z‖ = 0
               · rw [h]; simp
               · rw [div_div, mul_comm, ← div_div, div_self]; exact h
    exact this

  have maxMod : ‖fM f M z‖ ≤ 1 / R := by
    apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := {z | ‖z‖ ≤ R})
    · sorry
    · sorry
    · sorry
    · sorry



    sorry

  sorry


/-%%
\begin{proof}
\uses{}
    Let
    $$f_M(z)=\frac{f(z)/z}{2M-f(z)}.$$
    Note that $2M-f(z)\neq 0$ because $\mathfrak{R}(2M-f(z))=2M-\mathfrak{R}f(z)\geq M>0$. Additionally, since $f(z)$ has a zero at $0$, we know that $f(z)/z$ is analytic on $\abs{z}\leq R$. Likewise, $f_M(z)$ is analytic on $\abs{z}\leq R$.

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
