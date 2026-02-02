import Architect
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import PrimeNumberTheoremAnd.BorelCaratheodory
import PrimeNumberTheoremAnd.MediumPNT

open Nat Filter Set Function Complex Real ComplexConjugate MeasureTheory

open ArithmeticFunction (vonMangoldt)

local notation (name := mellintransform2) "𝓜" => mellin

local notation "Λ" => vonMangoldt

local notation "ζ" => riemannZeta

local notation "ζ'" => deriv ζ

local notation "ψ" => ChebyshevPsi

--open scoped ArithmeticFunction

blueprint_comment /--
    This upstreamed from https://github.com/math-inc/strongpnt/tree/main
-/



@[blueprint "cauchy_formula_deriv"
  (title := "cauchy-formula-deriv")
  (statement := /--
    Let $f$ be analytic on $|z|\leq R$. For any $z$ with $|z|\leq r$ and any $r'$
    with $0 < r < r' < R$ we have
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw=\frac{1}{2\pi}
    \int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
  -/)
  (proof := /--
    This is just Cauchy's integral formula for derivatives.
  -/)
  (latexEnv := "lemma")]
lemma cauchy_formula_deriv {f : ℂ → ℂ} {R r r' : ℝ}
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (r_lt_r' : r < r') (r'_lt_R : r' < R) {z : ℂ} (hz : z ∈ Metric.closedBall 0 r) :
    deriv f z = (1 / (2 * Real.pi * I)) • ∮ w in C(0, r'), (w - z)⁻¹ ^ 2 • f w := by
  obtain ⟨_, _, h_subset, hf_diff⟩ := hf_domain
  have hz_in_ball : z ∈ Metric.ball 0 r' :=
    Metric.mem_ball.mpr <| (Metric.mem_closedBall.mp hz).trans_lt r_lt_r'
  have hf_on_ball : DifferentiableOn ℂ f (Metric.ball 0 R) :=
    hf_diff.mono <| Metric.ball_subset_closedBall.trans h_subset
  simp [← Complex.two_pi_I_inv_smul_circleIntegral_sub_sq_inv_smul_of_differentiable
      Metric.isOpen_ball (Metric.closedBall_subset_ball r'_lt_R) hf_on_ball hz_in_ball]



@[blueprint "DerivativeBound"
  (title := "DerivativeBound")
  (statement := /--
    Let $R,\,M>0$ and $0 < r < r' < R$. Let $f$ be analytic on $|z|\leq R$ such that
    $f(0)=0$ and suppose $\Re f(z)\leq M$ for all $|z|\leq R$. Then we have that
    $$|f'(z)|\leq\frac{2M(r')^2}{(R-r')(r'-r)^2}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    By Lemma \ref{cauchy_formula_deriv} we know that
    $$f'(z)=\frac{1}{2\pi i}\oint_{|w|=r'}\frac{f(w)}{(w-z)^2}\,dw
      =\frac{1}{2\pi }\int_0^{2\pi}\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt.$$
    Thus,
    \begin{equation}\label{pickupPoint1}
        |f'(z)|=\left|\frac{1}{2\pi}\int_0^{2\pi}
          \frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\,dt\right|
          \leq\frac{1}{2\pi}\int_0^{2\pi}
          \left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|\,dt.
    \end{equation}
    Now applying Theorem \ref{borelCaratheodory_closedBall}, and noting that
    $r'-r\leq|r'e^{it}-z|$, we have that
    $$\left|\frac{r'e^{it}\,f(r'e^{it})}{(r'e^{it}-z)^2}\right|
      \leq\frac{2M(r')^2}{(R-r')(r'-r)^2}.$$
    Substituting this into Equation (\ref{pickupPoint1}) and evaluating the integral
    completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma DerivativeBound {R M r r' : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (Mpos : 0 < M)
    (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (f_zero_at_zero : f 0 = 0)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U)
    (re_f_le_M : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (pos_r : 0 < r) (z_in_r : z ∈ Metric.closedBall 0 r)
    (r_lt_r' : r < r') (r'_lt_R : r' < R) :
    ‖(deriv f) z‖ ≤ 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
    have diff_neg : r - r' < 0 := by linarith
    have cauchy_param : deriv f z = (1 / (2 * Real.pi * I)) *
        (∫ (θ : ℝ) in 0..(2 * Real.pi), (I * r' * Complex.exp (I * θ) *
          ((r' * Complex.exp (I * θ)) - z)⁻¹ ^ 2) * f (r' * Complex.exp (I * θ))) := by
        rw[cauchy_formula_deriv hf_domain r_lt_r' r'_lt_R z_in_r, smul_eq_mul]
        unfold circleIntegral circleMap
        simp only [one_div, mul_inv_rev, inv_I, neg_mul, zero_add, deriv_const_mul_field',
            inv_pow, smul_eq_mul, neg_inj, mul_eq_mul_left_iff, _root_.mul_eq_zero,
            I_ne_zero, inv_eq_zero, ofReal_eq_zero, pi_ne_zero, OfNat.ofNat_ne_zero,
            or_self, or_false]
        congr 1
        funext θ
        rw[deriv_cexp, deriv_mul_const]
        ·   simp only [_root_.deriv_ofReal, one_mul]
            ring_nf
        ·   exact differentiableAt_ofReal θ
        ·   refine DifferentiableAt.mul_const ?_ I
            exact differentiableAt_ofReal θ
    rw[cauchy_param]
    calc ‖1 / (2 * ↑π * I) * ∫ (θ : ℝ) in 0..2 * π,
          I * ↑r' * cexp (I * ↑θ) * (↑r' * cexp (I * ↑θ) - z)⁻¹ ^ 2 * f (↑r' * cexp (I * ↑θ))‖
        = (2 * π)⁻¹ * ‖∫ (θ : ℝ) in 0..2 * π,
          I * ↑r' * cexp (I * ↑θ) * (↑r' * cexp (I * ↑θ) - z)⁻¹ ^ 2 * f (↑r' * cexp (I * ↑θ))‖ := by
            simp only [one_div, mul_inv_rev, inv_I, neg_mul, inv_pow, norm_neg, Complex.norm_mul,
                norm_I, norm_inv, norm_real, norm_eq_abs, Complex.norm_ofNat, one_mul]
            rw [abs_of_pos pi_pos]
        _ ≤ (2 * π)⁻¹ * (r' * ((r' - r) ^ 2)⁻¹ * (2 * M * r' / (R - r'))) * |2 * π - 0| := by
            rw[mul_assoc]
            refine mul_le_mul (by rfl) ?_ (by grind) (inv_nonneg.mpr (le_of_lt two_pi_pos))
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro θ hθ
            simp only [inv_pow, Complex.norm_mul, norm_I, norm_real, norm_eq_abs, one_mul,
                norm_exp_I_mul_ofReal, mul_one, norm_inv, norm_pow]
            rw[abs_of_pos (lt_trans pos_r r_lt_r')]
            refine mul_le_mul₃ (rfl.le) ?_ ?_ (inv_nonneg.mpr (sq_nonneg _))
              (le_of_lt (lt_trans pos_r r_lt_r')) (norm_nonneg (f (↑r' * cexp (I * ↑θ))))
            ·   have hz_norm : ‖z‖ ≤ r := mem_closedBall_zero_iff.mp z_in_r
                refine inv_anti₀ (sq_pos_of_pos (by grind)) (sq_le_sq' ?_ ?_)
                · calc -(‖(r' : ℂ) * cexp (I * θ) - z‖) ≤ 0 := neg_nonpos.mpr (norm_nonneg _)
                    _ ≤ r' - r := by grind
                · calc r' - r ≤ |r'| - ‖z‖ := sub_le_sub (le_abs_self _) hz_norm
                    _ = ‖(r' : ℂ) * cexp (I * θ)‖ - ‖z‖ := by
                      simp [abs_of_pos <| pos_r.trans r_lt_r']
                    _ ≤ ‖r' * cexp (I * θ) - z‖ := norm_sub_norm_le _ _
            ·   exact borelCaratheodory_closedBall (by grind) analytic_f f_zero_at_zero
                    Mpos re_f_le_M r'_lt_R
                    (mem_closedBall_zero_iff.mpr (by simp [abs_of_pos <| pos_r.trans r_lt_r']))
        _ = 2 * M * r' ^ 2 / ((R - r') * (r' - r) ^ 2) := by
            rw[sub_zero, abs_of_pos two_pi_pos]
            field_simp



@[blueprint "BorelCaratheodoryDeriv"
  (title := "BorelCaratheodoryDeriv")
  (statement := /--
    Let $R,\,M>0$. Let $f$ be analytic on $|z|\leq R$ such that $f(0)=0$ and suppose
    $\Re f(z)\leq M$ for all $|z|\leq R$. Then for any $0 < r < R$,
    $$|f'(z)|\leq\frac{16MR^2}{(R-r)^3}$$
    for all $|z|\leq r$.
  -/)
  (proof := /--
    Using Lemma \ref{DerivativeBound} with $r'=(R+r)/2$, and noting that $r < R$,
    we have that
    $$|f'(z)|\leq\frac{4M(R+r)^2}{(R-r)^3}\leq\frac{16MR^2}{(R-r)^3}.$$
  -/)
  (latexEnv := "theorem")]
theorem BorelCaratheodoryDeriv {M R r : ℝ} {z : ℂ} {f : ℂ → ℂ}
    (rpos : 0 < r) (analytic_f : AnalyticOn ℂ f (Metric.closedBall 0 R))
    (zeroAtZero : f 0 = 0) (Mpos : 0 < M)
    (realPartBounded : ∀ z ∈ Metric.closedBall 0 R, (f z).re ≤ M)
    (hyp_r : r < R) (hyp_z : z ∈ Metric.closedBall 0 r)
    (hf_domain : ∃ U, IsOpen U ∧ Metric.closedBall 0 R ⊆ U ∧ DifferentiableOn ℂ f U) :
    ‖deriv f z‖ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
    let r' : ℝ := (R + r) / 2
    calc
        ‖deriv f z‖ ≤ 4 * M * (R + r) ^ 2 / (R - r) ^ 3 := by
            have : 4 * M * (R + r) ^ 2 / (R - r) ^ 3 = 2 * M * (r') ^ 2 / ((R - r') * (r' - r) ^ 2) := by
                simp[r']
                field_simp
                ring_nf
            rw[this]
            simp only [r']
            apply DerivativeBound Mpos analytic_f zeroAtZero hf_domain realPartBounded rpos hyp_z (by linarith) (by linarith)
        _ ≤ 16 * M * R ^ 2 / (R - r) ^ 3 := by
            have : 16 * M * R ^ 2 = 4 * M * (2 * R) ^ 2 := by ring_nf
            rw[this]
            bound



@[blueprint "PathIntegral"
  (title := "PathIntegral")
  (statement := /--
    Let $0 < r < R<1$. Let $f:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_R}$. Define the functon
    $I_f:\overline{\mathbb{D}_r}\to\mathbb{C}$ by
    $$I_f(z)=z\int_0^1f(tz)\,dt.$$
  -/)
  (latexEnv := "definition")]
noncomputable def PathIntegral (f : ℂ → ℂ) :
    ℂ → ℂ := fun c ↦ let γ : ℝ → ℂ := fun s ↦ s * c
    ∫ t in 0..1, f (γ t) * (deriv γ) t



@[blueprint "LogOfAnalyticFunction"
  (title := "LogOfAnalyticFunction")
  (statement := /--
    Let $0 < r < R<1$. Let $B:\overline{\mathbb{D}_R}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_R}$ with $B(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_R}$. Then there exists $J_B:\overline{\mathbb{D}_r}\to\mathbb{C}$ that
    is analytic on neighborhoods of points in $\overline{\mathbb{D}_r}$ such that
    \begin{itemize}
        \item $J_B(0)=0$
        \item $J_B'(z)=B'(z)/B(z)$
        \item $\log|B(z)|-\log|B(0)|=\Re J_B(z)$
    \end{itemize}
    for all $z\in\overline{\mathbb{D}_r}$.
  -/)
  (proof := /--
    We let $J_B(z)=I_{B'/B}(z)$. Then clearly, $J_B(0)=0$. Now note that
    \begin{align*}
        I_{B'/B}(z)=z\int_0^1(B'/B)(tz)\,dt=\int_0^z(B'/B)(u)\,du.
    \end{align*}
    Thus by the fundamental theorem of calculus we have that $J_B'(z)=B'(z)/B(z)$. Now let
    $H(z)=\exp(J_B(z))/B(z)$ and note that
    $$H'(z)=(B(z)\,J_B'(z)-B'(z))\left(\frac{\exp(J_B(z))}{(B(z))^2}\right).$$
    Thus, $H$ is constant since we know that $B(z)\,J_B'(z)-B(z)=0$ from $J_B'(z)=B'(z)/B(z)$. So
    since $H(0)=\exp(J_B(0))/B(0)=1/B(0)$ we know $H(z)=1/B(0)$ for all $z$. So we have,
    $$\frac{1}{B(0)}=\frac{\exp(J_B(z))}{B(z)}\implies\left|\frac{B(z)}{B(0)}\right|
      =\exp(\mathfrak{R}J_B(z)).$$
    Taking the logarithm of both sides completes the proof.
  -/)
  (latexEnv := "theorem")]
theorem LogOfAnalyticFunction {r R : ℝ} (zero_lt_r : 0 < r) (r_lt_R : r < R) (R_lt_one : R < 1)
    {B : ℂ → ℂ} (BanalyticOnNhdOfDR : AnalyticOnNhd ℂ B (Metric.closedBall (0 : ℂ) R)) (Bnonzero : ∀ z ∈ Metric.closedBall (0 : ℂ) R, B z ≠ 0) :
    ∃ (J_B : ℂ → ℂ),
    (AnalyticOnNhd ℂ J_B (Metric.closedBall 0 r)) ∧
    (J_B 0 = 0) ∧
    (∀ z ∈ Metric.closedBall 0 r, (deriv J_B) z = (deriv B) z / (B z)) ∧
    (∀ z ∈ Metric.closedBall 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re) := by
    let L : ℂ → ℂ := fun z ↦ deriv B z / B z
    have LanalyticOnNhdOfDR : AnalyticOnNhd ℂ L (Metric.closedBall (0 : ℂ) R) := AnalyticOnNhd.div (AnalyticOnNhd.deriv BanalyticOnNhdOfDR) BanalyticOnNhdOfDR Bnonzero
    let J_B : ℂ → ℂ := PathIntegral L
    use J_B
    have derivJ_BOnOpenR : ∀ z ∈ Metric.ball 0 R, deriv J_B z = L z := by
        intro w hw
        sorry
    have derivJ_BOnClosedr : ∀ z ∈ Metric.closedBall 0 r, deriv J_B z = L z := by
        intro w hw
        apply derivJ_BOnOpenR
        rw[mem_ball_zero_iff]
        rw[mem_closedBall_zero_iff] at hw
        linarith
    have J_BAnalytic : AnalyticOnNhd ℂ J_B (Metric.closedBall 0 r) := by
        unfold AnalyticOnNhd
        intro z hz
        have hd : DifferentiableOn ℂ J_B (Metric.ball 0 R) := by
            sorry
        have inNhds : Metric.ball 0 R ∈ nhds z := by
            apply IsOpen.mem_nhds (Metric.isOpen_ball)
            rw[mem_ball_zero_iff]
            rw[mem_closedBall_zero_iff] at hz
            linarith
        exact DifferentiableOn.analyticAt hd inNhds
    have J_BZeroAtZero : J_B 0 = 0 := by
        unfold J_B PathIntegral
        simp only [mul_zero, deriv_const', intervalIntegral.integral_zero]
    have J_BLogDiff : ∀ z ∈ Metric.closedBall 0 r, Real.log ‖B z‖ - Real.log ‖B 0‖ = (J_B z).re := by
        intro w hw
        sorry
    exact ⟨J_BAnalytic, J_BZeroAtZero, derivJ_BOnClosedr, J_BLogDiff⟩



blueprint_comment /--
\begin{definition}[SetOfZeros]\label{SetOfZeros}
    Let $R>0$ and $f:\overline{\mathbb{D}_R}\to\mathbb{C}$. Define the set of zeros
    $\mathcal{K}_f(R)=\{\rho\in\mathbb{C}:|\rho|\leq R,\,f(\rho)=0\}$.
\end{definition}
-/



blueprint_comment /--
\begin{definition}[ZeroOrder]\label{ZeroOrder}
    Let $0 < R<1$ and $f:\mathbb{C}\to\mathbb{C}$ be analtyic on neighborhoods of points in
    $\overline{\mathbb{D}_1}$. For any zero $\rho\in\mathcal{K}_f(R)$, we define $m_f(\rho)$
    as the order of the zero $\rho$ w.r.t $f$.
\end{definition}
-/



blueprint_comment /--
\begin{lemma}[ZeroFactorization]\label{ZeroFactorization}
    Let $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on neighborhoods of points in
    $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. For all $\rho\in\mathcal{K}_f(1)$ there
    exists $h_\rho(z)$ that is analytic at $\rho$, $h_\rho(\rho)\neq 0$, and
    $f(z)=(z-\rho)^{m_f(\rho)}\,h_\rho(z)$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
    Since $f$ is analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ we know
    that there exists a series expansion about $\rho$:
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n.$$
    Now if we let $m$ be the smallest number such that $a_m\neq 0$, then
    $$f(z)=\sum_{0\leq n}a_n\,(z-\rho)^n=\sum_{m\leq n}a_n\,(z-\rho)^n
      =(z-\rho)^m\sum_{m\leq n}a_n\,(z-\rho)^{n-m}=(z-\rho)^m\,h_\rho(z).$$
    Trivially, $h_\rho(z)$ is analytic at $\rho$ (we have written down the series
    expansion); now note that
    $$h_\rho(\rho)=\sum_{m\leq n}a_n(\rho-\rho)^{n-m}=\sum_{m\leq n}a_n0^{n-m}=a_m\neq 0.$$
\end{proof}
-/



blueprint_comment /--
\begin{definition}[CFunction]\label{CFunction}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a
    function $C_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows. This function is
    constructed by dividing $f(z)$ by a polynomial whose roots are the zeros of $f$ inside
    $\overline{\mathbb{D}_r}$.
    $$C_f(z)=\begin{cases}
        \displaystyle\frac{f(z)}{\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}
          \qquad\text{for }z\not\in\mathcal{K}_f(r) \\
        \displaystyle\frac{h_z(z)}{\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          (z-\rho)^{m_f(\rho)}}\qquad\text{for }z\in\mathcal{K}_f(r)
    \end{cases}$$
    where $h_z(z)$ comes from Lemma \ref{ZeroFactorization}.
\end{definition}
-/



blueprint_comment /--
\begin{definition}[BlaschkeB]\label{BlaschkeB}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. We define a
    function $B_f:\overline{\mathbb{D}_R}\to\mathbb{C}$ as follows.
    $$B_f(z)=C_f(z)\prod_{\rho\in\mathcal{K}_f(r)}
      \left(R-\frac{z\overline{\rho}}{R}\right)^{m_f(\rho)}$$
\end{definition}
-/



blueprint_comment /--
\begin{lemma}[BlaschkeOfZero]\label{BlaschkeOfZero}
    Let $0 < r < R<1$, and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)\neq 0$. Then
    $$|B_f(0)|=|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{BlaschkeB}
    Since $f(0)\neq 0$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(0)|=|C_f(0)|\prod_{\rho\in\mathcal{K}_f(r)}R^{m_f(\rho)}
      =|f(0)|\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}.$$
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[DiskBound]\label{DiskBound}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $|f(z)|\leq B$ for
    $|z|\leq R$, then $|B_f(z)|\leq B$ for $|z|\leq R$ also.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{BlaschkeB}
    For $|z|=R$, we know that $z\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$|B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.$$
    But note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|
      =\frac{|R^2-z\overline{\rho}|/R}{|z-\rho|}
      =\frac{|z|\cdot|\overline{z-\rho}|/R}{|z-\rho|}=1.$$
    So we have that $|B_f(z)|=|f(z)|\leq B$ when $|z|=R$. Now by the maximum modulus
    principle, we know that the maximum of $|B_f|$ must occur on the boundary where
    $|z|=R$. Thus $|B_f(z)|\leq B$ for all $|z|\leq R$.
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[ZerosBound]\label{ZerosBound}
    Let $B>1$ and $0< r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for $|z|\leq R$, then
    $$\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)\leq\frac{\log B}{\log(R/r)}.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{BlaschkeB, DiskBound}
    Since $f(0)=1$, we know that $0\not\in\mathcal{K}_f(r)$. Thus,
    $$C_f(0)=\frac{f(0)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    $$(R/r)^{\sum_{\rho\in\mathcal{K}_f(r)}m_f(\rho)}
      =\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{r}\right)^{m_f(\rho)}
      \leq\prod_{\rho\in\mathcal{K}_f(r)}\left(\frac{R}{|\rho|}\right)^{m_f(\rho)}
      =|B_f(0)|\leq B$$
    whereby Lemma \ref{DiskBound} we know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Taking the logarithm of both sides and rearranging gives the desired result.
\end{proof}
-/



blueprint_comment /--
\begin{definition}[JBlaschke]\label{JBlaschke}
    Let $B>1$ and $0 < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$, define
    $L_f(z)=J_{B_f}(z)$ where $J$ is from Theorem \ref{LogOfAnalyticFunction} and $B_f$
    is from Definition \ref{BlaschkeB}.
\end{definition}
-/



blueprint_comment /--
\begin{lemma}[BlaschkeNonZero]\label{BlaschkeNonZero}
    Let $0 < r < R<1$ and $f:\overline{\mathbb{D}_1}\to\mathbb{C}$ be analytic on
    neighborhoods of points in $\overline{\mathbb{D}_1}$. Then $B_f(z)\neq 0$ for all
    $z\in\overline{\mathbb{D}_r}$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{ZeroFactorization, BlaschkeB}
    Suppose that $z\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{h_z(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
      (z-\rho)^{m_f(\rho)}}.$$
    where $h_z(z)\neq 0$ according to Lemma \ref{ZeroFactorization}. Thus, substituting
    this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint2}
        |B_f(z)|=|h_z(z)|\cdot\left|R-\frac{|z|^2}{R}\right|^{m_f(z)}
          \prod_{\rho\in\mathcal{K}_f(r)\setminus\{z\}}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    Trivially, $|h_z(z)|\neq 0$. Now note that
    $$\left|R-\frac{|z|^2}{R}\right|=0\implies|z|=R.$$
    However, this is a contradiction because $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. Similarly, note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is also a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|R-\frac{|z|^2}{R}\right|\neq 0\qquad\text{and}\qquad
      \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r)\setminus\{z\}.$$
    Applying this to Equation (\ref{pickupPoint2}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    Now suppose that $z\not\in\mathcal{K}_f(r)$. Then we have that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(r)}(z-\rho)^{m_f(\rho)}}.$$
    Thus, substituting this into Definition \ref{BlaschkeB},
    \begin{equation}\label{pickupPoint3}
        |B_f(z)|=|f(z)|\prod_{\rho\in\mathcal{K}_f(r)}
          \left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|^{m_f(\rho)}.
    \end{equation}
    We know that $|f(z)|\neq 0$ since $z\not\in\mathcal{K}_f(r)$. Now note that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|=0\implies|z|=\frac{R^2}{|\overline{\rho}|}.$$
    However, this is a contradiction because $\rho\in\mathcal{K}_f(r)$ tells us that
    $R < R^2/|\overline{\rho}|=|z|$, but $z\in\overline{\mathbb{D}_r}$ tells us that
    $|z|\leq r < R$. So, we know that
    $$\left|\frac{R-z\overline{\rho}/R}{z-\rho}\right|\neq 0
      \quad\text{for all}\quad\rho\in\mathcal{K}_f(r).$$
    Applying this to Equation (\ref{pickupPoint3}) we have that $|B_f(z)|\neq 0$.
    So, $B_f(z)\neq 0$.

    We have shown that $B_f(z)\neq 0$ for both $z\in\mathcal{K}_f(r)$ and
    $z\not\in\mathcal{K}_f(r)$, so the result follows.
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[JBlaschkeDerivBound]\label{JBlaschkeDerivBound}
    Let $B>1$ and $0 < r' < r < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function analytic
    on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and $|f(z)|\leq B$
    for all $|z|\leq R$, then for all $|z|\leq r'$
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{DiskBound, JBlaschke, LogOfAnalyticFunction, BorelCaratheodoryDeriv}
    By Lemma \ref{DiskBound} we immediately know that $|B_f(z)|\leq B$ for all $|z|\leq R$.
    Now since $L_f=J_{B_f}$ by Definition \ref{JBlaschke}, by Theorem
    \ref{LogOfAnalyticFunction} we know that
    $$L_f(0)=0\qquad\text{and}\qquad
      \Re L_f(z)=\log|B_f(z)|-\log|B_f(0)|\leq\log|B_f(z)|\leq\log B$$
    for all $|z|\leq r$. So by Theorem \ref{BorelCaratheodoryDeriv}, it follows that
    $$|L_f'(z)|\leq\frac{16\log(B)\,r^2}{(r-r')^3}$$
    for all $|z|\leq r'$.
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[FinalBound]\label{FinalBound}
    Let $B>1$ and $0 < r' < r < R' < R<1$. If $f:\mathbb{C}\to\mathbb{C}$ is a function
    analytic on neighborhoods of points in $\overline{\mathbb{D}_1}$ with $f(0)=1$ and
    $|f(z)|\leq B$ for all $|z|\leq R$, then for all
    $z\in\overline{\mathbb{D}_{R'}}\setminus\mathcal{K}_f(R')$ we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log B.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{CFunction, BlaschkeB, JBlaschke, LogOfAnalyticFunction, ZerosBound, JBlaschkeDerivBound}
    Since $z\in\overline{\mathbb{D}_{r'}}\setminus\mathcal{K}_f(R')$ we know that
    $z\not\in\mathcal{K}_f(R')$; thus, by Definition \ref{CFunction} we know that
    $$C_f(z)=\frac{f(z)}{\displaystyle\prod_{\rho\in\mathcal{K}_f(R')}(z-\rho)^{m_f(\rho)}}.$$
    Substituting this into Definition \ref{BlaschkeB} we have that
    $$B_f(z)=f(z)\prod_{\rho\in\mathcal{K}_f(R')}
      \left(\frac{R-z\overline{\rho}/R}{z-\rho}\right)^{m_f(\rho)}.$$
    Taking the complex logarithm of both sides we have that
    $$\mathrm{Log}\,B_f(z)=\mathrm{Log}\,f(z)
      +\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(R-z\overline{\rho}/R)
      -\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho)\,\mathrm{Log}(z-\rho).$$
    Taking the derivative of both sides we have that
    $$\frac{B_f'}{B_f}(z)=\frac{f'}{f}(z)
      +\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\rho}
      -\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}.$$
    By Definition \ref{JBlaschke} and Theorem \ref{LogOfAnalyticFunction} we recall that
    $$L_f(z)=J_{B_f}(z)=\mathrm{Log}\,B_f(z)-\mathrm{Log}\,B_f(0).$$
    Taking the derivative of both sides we have that $L_f'(z)=(B_f'/B_f)(z)$. Thus,
    $$\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}
      =L_f'(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-R^2/\rho}.$$
    Now since $z\in\overline{\mathbb{D}_{R'}}$ and $\rho\in\mathcal{K}_f(R')$, we know that
    $R^2/R'-R'\leq|z-R^2/\rho|$. Thus by the triangle inequality we have
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \leq|L_f'(z)|+\left(\frac{1}{R^2/R'-R'}\right)\sum_{\rho\in\mathcal{K}_f(R')}m_f(\rho).$$
    Now by Theorem \ref{ZerosBound} and \ref{JBlaschkeDerivBound} we get our desired result
    with a little algebraic manipulation.
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[ZetaFixedLowerBound]\label{ZetaFixedLowerBound}
    For all $t\in\mathbb{R}$ one has
    $$|\zeta(3/2+it)|\geq\frac{\zeta(3)}{\zeta(3/2)}.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
    From the Euler product expansion of $\zeta$, we have that for $\Re s>1$
    $$\zeta(s)=\prod_p\frac{1}{1-p^{-s}}.$$
    Thus, we have that
    $$\frac{\zeta(2s)}{\zeta(s)}=\prod_p\frac{1-p^{-s}}{1-p^{-2s}}=\prod_p\frac{1}{1+p^{-s}}.$$
    Now note that $|1-p^{-(3/2+it)}|\leq 1+|p^{-(3/2+it)}|=1+p^{-3/2}$. Thus,
    $$|\zeta(3/2+it)|=\prod_p\frac{1}{|1-p^{-(3/2+it)}|}
      \geq\prod_p\frac{1}{1+p^{-3/2}}=\frac{\zeta(3)}{\zeta(3/2)}$$
    for all $t\in\mathbb{R}$ as desired.
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ZetaAltFormula]\label{ZetaAltFormula}
    Let
    $$\zeta_0(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}.$$
    We have that $\zeta(s)=\zeta_0(s)$ for $\sigma>1$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
    Note that for $\sigma>1$ we have
    $$\zeta(s)=\sum_{n=1}^\infty\frac{1}{n^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n-1}{n^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=0}^\infty\frac{n}{(n+1)^s}
      =\sum_{n=1}^\infty\frac{n}{n^s}-\sum_{n=1}^\infty\frac{n}{(n+1)^s}.$$
    Thus
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s}).$$
    Now we note that
    $$s\int_n^{n+1}x^{-s}\,\frac{dx}{x}
      =s\left(-\frac{1}{s}\,x^{-s}\right)_n^{n+1}=n^{-s}-(n+1)^{-s}.$$
    So, substituting this we have
    $$\zeta(s)=\sum_{n=1}^\infty n\,(n^{-s}-(n+1)^{-s})
      =s\sum_{n=1}^\infty n\int_n^{n+1}x^{-s}\,\frac{dx}{x}
      =s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}.$$
    But noting that $\lfloor x\rfloor =x-\{x\}$ we have that
    $$\zeta(s)=s\int_1^\infty\lfloor x\rfloor\,x^{-s}\,\frac{dx}{x}
      =s\int_1^\infty x^{-s}\,dx-s\int_1^\infty \{x\}\,x^{-s}\,\frac{dx}{x}.$$
    Evaluating the first integral completes the result.
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ZetaAltFormulaAnalytic]\label{ZetaAltFormulaAnalytic}
    We have that $\zeta_0(s)$ is analytic for all $s\in S$ where
    $S=\{s\in\mathbb{C}:\Re s>0,\,s\neq 1\}$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
    Note that we have
    $$\left|\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}\right|
      \leq\int_1^\infty|\{x\}\,x^{-s-1}|\,dx
      \leq\int_1^\infty x^{-\sigma-1}\,dx=\frac{1}{\sigma}.$$
    So this integral converges uniformly on compact subsets of $S$, which tells us that
    it is analytic on $S$. So it immediately follows that $\zeta_0(s)$ is analytic on $S$
    as well, since $S$ avoids the pole at $s=1$ coming from the $(s-1)^{-1}$ term.
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ZetaExtend]\label{ZetaExtend}
    We have that
    $$\zeta(s)=1+\frac{1}{s-1}-s\int_1^\infty\{x\}\,x^{-s}\,\frac{dx}{x}$$
    for all $s\in S$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
    This is an immediate consequence of the identity theorem.
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[GlobalBound]\label{GlobalBound}
    For all $s\in\mathbb{C}$ with $|s|\leq 1$ and $t\in\mathbb{R}$ with $|t|\geq 2$, we have that
    $$|\zeta(s+3/2+it)|\leq 7+2\,|t|.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{ZetaExtend}
    For the sake of clearer proof writing let $z=s+3/2+it$. Since $|s|\leq 1$ we know that
    $1/2\leq\mathfrak{R}z$; additionally, as $|t|\geq 2$, we know $1\leq|\mathfrak{I}z|$.
    So, $z\in S$. Thus, from Lemma \ref{ZetaExtend} we know that
    $$|\zeta(z)|\leq 1+\frac{1}{|z-1|}
      +|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|$$
    by applying the triangle inequality. Now note that $|z-1|\geq 1$. Likewise,
    $$|z|\cdot\left|\int_1^\infty\{x\}\,x^{-z}\,\frac{dx}{x}\right|
      \leq|z|\int_1^\infty|\{x\}\,x^{-z-1}|\,dx
      \leq|z|\int_1^\infty x^{-\Re z-1}\,dx=\frac{|z|}{\Re z}\leq 2\,|z|.$$
    Thus we have that,
    $$|\zeta(s+3/2+it)|=|\zeta(z)|\leq 1+1+2\,|z|=2+2\,|s+3/2+it|
      \leq2+2\,|s|+3+2\,|it|\leq 7+2\,|t|.$$
\end{proof}
-/



blueprint_comment /--
\begin{theorem}[LogDerivZetaFinalBound]\label{LogDerivZetaFinalBound}
    Let $t\in\mathbb{R}$ with $|t|\geq 2$ and $0 < r' < r < R' < R<1$. If
    $f(z)=\zeta(z+3/2+it)$, then for all
    $z\in\overline{\mathbb{D}_R'}\setminus\mathcal{K}_f(R')$ we have that
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|.$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{ZetaFixedLowerBound, GlobalBound, FinalBound}
    Let $g(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$. Note that $g(0)=1$ and for $|z|\leq R$
    $$|g(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}. Thus by Theorem
    \ref{FinalBound} we have that
    $$\left|\frac{g'}{g}(z)-\sum_{\rho\in\mathcal{K}_g(R')}\frac{m_g(\rho)}{z-\rho}\right|
      \leq\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)
      \left(\log|t|+\log\left(\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\right)\right).$$
    Now note that $f'/f=g'/g$, $\mathcal{K}_f(R')=\mathcal{K}_g(R')$, and
    $m_g(\rho)=m_f(\rho)$ for all $\rho\in\mathcal{K}_f(R')$. Thus we have that,
    $$\left|\frac{f'}{f}(z)-\sum_{\rho\in\mathcal{K}_f(R')}\frac{m_f(\rho)}{z-\rho}\right|
      \ll\left(\frac{16r^2}{(r-r')^3}+\frac{1}{(R^2/R'-R')\,\log(R/R')}\right)\log|t|$$
    where the implied constant $C$ is taken to be
    $$C\geq 1+\frac{\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 2}.$$
\end{proof}
-/



blueprint_comment /--
\begin{definition}[ZeroWindows]\label{ZeroWindows}
    Let $\mathcal{Z}_t=\{\rho\in\mathbb{C}:\zeta(\rho)=0,\,|\rho-(3/2+it)|\leq 5/6\}$.
\end{definition}
-/



blueprint_comment /--
\begin{lemma}[SumBoundI]\label{SumBoundI}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{LogDerivZetaFinalBound}
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and
    $R=8/9$. Thus, for all $z\in\overline{\mathbb{D}_{5/6}}\setminus\mathcal{K}_f(5/6)$
    we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$. Now if we let
    $z=-1/2+\delta$, then $z\in(-1/2,1/2)\subseteq\overline{\mathbb{D}_{5/6}}$.
    Additionally, $f(z)=\zeta(1+\delta+it)$, where $1+\delta+it$ lies in the zero-free
    region where $\sigma>1$. Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{-1/2+\delta-\rho}\right|
      \ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$ and
    $|\rho|\leq 5/6$. Thus, $\rho+3/2+it\in\mathcal{Z}_t$. Additionally, note that
    $m_f(\rho)=m_\zeta(\rho+3/2+it)$. So changing variables using these facts gives us
    that
    $$\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|
      \ll\log|t|.$$
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ShiftTwoBound]\label{ShiftTwoBound}
    For all $\delta\in (0,1)$ and $t\in\mathbb{R}$ with $|t|\geq 2$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{SumBoundI}
    Note that, for $\rho\in\mathcal{Z}_{2t}$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
          &=\Re \left(\frac{1+\delta-2it-\overline{\rho}}
            {(1+\delta+2it-\rho)(1+\delta-2it-\overline{\rho})}\right) \\
          &=\frac{\Re (1+\delta-2it-\overline{\rho})}{|1+\delta+2it-\rho|^2}
            =\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}.
    \end{align*}
    Now since $\rho\in\mathcal{Z}_{2t}$, we have that $|\rho-(3/2+2it)|\leq 5/6$. So,
    we have $\Re \rho\in(2/3,7/3)$ and $\mathfrak{I}\rho\in(2t-5/6,2t+5/6)$. Thus, we
    have that
    $$1/3<1+\delta-\Re \rho\qquad\text{and}\qquad
      (1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2<16/9+25/36=89/36.$$
    Which implies that
    \begin{equation}\label{pickupPoint4}
        0\leq\frac{12}{89}
          <\frac{1+\delta-\Re \rho}{(1+\delta-\Re \rho)^2+(2t-\mathfrak{I}\rho)^2}
          =\Re \left(\frac{1}{1+\delta+2it-\rho}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_{2t}}m_\zeta(\rho)\,
      \Re \left(\frac{1}{1+\delta+2it-\rho}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+2it)
      -\sum_{\rho\in\mathcal{Z}_{2t}}\frac{m_\zeta(\rho)}{1+\delta+2it-\rho}\right|
      \ll\log|2t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho\in\mathcal{Z}_{2t}$, the inequality from
    Equation (\ref{pickupPoint4}) tells us that by subtracting the sum from both sides
    we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right)\ll\log|2t|.$$
    Noting that $\log|2t|=\log(2)+\log|t|\leq2\log|t|$ completes the proof.
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ShiftOneBound]\label{ShiftOneBound}
    There exists $C>0$ such that for all $\delta\in(0,1)$ and $t\in\mathbb{R}$ with
    $|t|\geq 3$; if $\zeta(\rho)=0$ with $\rho=\sigma+it$, then
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{1}{1+\delta-\sigma}+C\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{SumBoundI}
    Note that for $\rho'\in\mathcal{Z}_t$
    \begin{align*}
        \Re \left(\frac{1}{1+\delta+it-\rho'}\right)
          &=\Re \left(\frac{1+\delta-it-\overline{\rho'}}
            {(1+\delta+it-\rho')(1+\delta-it-\overline{\rho'})}\right) \\
          &=\frac{\Re (1+\delta-it-\overline{\rho'})}{|1+\delta+it-\rho'|^2}
            =\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}.
    \end{align*}
    Now since $\rho'\in\mathcal{Z}_t$, we have that $|\rho-(3/2+it)|\leq 5/6$. So, we
    have $\Re \rho'\in(2/3,7/3)$ and $\mathfrak{I}\rho'\in(t-5/6,t+5/6)$. Thus we have
    that
    $$1/3<1+\delta-\Re \rho'\qquad\text{and}\qquad
      (1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2<16/9+25/36=89/36.$$
    Which implies that
    \begin{equation}\label{pickupPoint5}
        0\leq\frac{12}{89}
          <\frac{1+\delta-\Re \rho'}{(1+\delta-\Re \rho')^2+(t-\mathfrak{I}\rho')^2}
          =\Re \left(\frac{1}{1+\delta+it-\rho'}\right).
    \end{equation}
    Note that, from Lemma \ref{SumBoundI}, we have
    $$\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)\,
      \Re \left(\frac{1}{1+\delta+it-\rho}\right)
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq\left|\frac{\zeta'}{\zeta}(1+\delta+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{1+\delta+it-\rho}\right|
      \ll\log|t|.$$
    Since $m_\zeta(\rho)\geq 0$ for all $\rho'\in\mathcal{Z}_t$, the inequality from
    Equation (\ref{pickupPoint5}) tells us that by subtracting the sum over all
    $\rho'\in\mathcal{Z}_t\setminus\{\rho\}$ from both sides we have
    $$\frac{m_\zeta(\rho)}{\Re (1+\delta+it-\rho)}
      -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)\ll\log|t|.$$
    But of course we have that $\Re (1+\delta+it-\rho)=1+\delta-\sigma$. So subtracting
    this term from both sides and recalling the implied constant we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
      \leq -\frac{m_\zeta(\rho)}{1+\delta-\sigma}+C\log|t|.$$
    We have that $\sigma\leq 1$ since $\zeta$ is zero free on the right half plane
    $\sigma>1$. Thus $0<1+\delta-\sigma$. Noting this in combination with the fact that
    $1\leq m_\zeta(\rho)$ completes the proof.
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ShiftZeroBound]\label{ShiftZeroBound}
    For all $\delta\in(0,1)$ we have
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\frac{1}{\delta}+O(1).$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{riemannZetaLogDerivResidue}
    From Theorem \ref{riemannZetaLogDerivResidue} we know that
    $$-\frac{\zeta'}{\zeta}(s)=\frac{1}{s-1}+O(1).$$
    Changing variables $s\mapsto 1+\delta$ and applying the triangle inequality we have that
    $$-\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)\leq\left|
      -\frac{\zeta'}{\zeta}(1+\delta)\right|\leq\frac{1}{\delta}+O(1).$$
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[ThreeFourOneTrigIdentity]\label{ThreeFourOneTrigIdentity}
    We have that
    $$0\leq 3+4\cos\theta+\cos2\theta$$
    for all $\theta\in\mathbb{R}$.
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
    We know that $\cos(2\theta)=2\cos^2\theta-1$, thus
    $$3+4\cos\theta+\cos2\theta=2+4\cos\theta+2\cos^2\theta=2\,(1+\cos\theta)^2.$$
    Noting that $0\leq 1+\cos\theta$ completes the proof.
\end{proof}
-/



@[blueprint
  (title := "ZeroInequality")
  (statement := /--
    There exists a constant $0 < E<1$ such that for all $\rho=\sigma+it$ with $\zeta(\rho)=0$
    and $|t|\geq 2$, one has
    $$\sigma\leq 1-\frac{E}{\log|t|}.$$
  -/)
  (proof := /--
    From Theorem \ref{LogDerivativeDirichlet} when $\Re s>1$ we have
    $$-\frac{\zeta'}{\zeta}(s)=\sum_{1\leq n}\frac{\Lambda(n)}{n^s}.$$
    Thus,
    $$-3\,\frac{\zeta'}{\zeta}(1+\delta)
        -4\,\frac{\zeta'}{\zeta}(1+\delta+it)
        -\frac{\zeta'}{\zeta}(1+\delta+2it)
        =\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}\left(3+4n^{-it}+n^{-2it}\right).$$
    Now applying Euler's identity
    \begin{align*}
        -3\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta)\right)&
            -4\,\Re \left(\frac{\zeta'}{\zeta}(1+\delta+it)\right)
            -\Re \left(\frac{\zeta'}{\zeta}(1+\delta+2it)\right) \\
        &\qquad\qquad\qquad=\sum_{1\leq n}\Lambda(n)\,n^{-(1+\delta)}
            \left(3+4\cos(-it\log n)+\cos(-2it\log n)\right)
    \end{align*}
    By Lemma \ref{ThreeFourOneTrigIdentity} we know that the series on the right hand side
    is bounded below by $0$, and by Lemmas \ref{ShiftTwoBound}, \ref{ShiftOneBound},
    and \ref{ShiftZeroBound} we have an upper bound on the left hand side. So,
    $$0\leq\frac{3}{\delta}+3A-\frac{4}{1+\delta-\sigma}+4B\log|t|+C\log|t|$$
    where $A$, $B$, and $C$ are the implied constants coming from Lemmas
    \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively.
    By choosing $D\geq 3A/\log 2+4B+C$ we have
    $$\frac{4}{1+\delta-\sigma}\leq\frac{3}{\delta}+D\log|t|$$
    by some manipulation. Now if we choose $\delta=(2D\log|t|)^{-1}$ then we have
    $$\frac{4}{1-\sigma+1/(2D\log|t|)}\leq7D\log|t|.$$
    So with some manipulation we have that
    $$\sigma\leq 1-\frac{1}{14D\log|t|}.$$
    This is exactly the desired result with the constant $E=(14D)^{-1}$
  -/)
  (proofUses := ["ShiftTwoBound", "LogDerivativeDirichlet", "ShiftOneBound",
    "ThreeFourOneTrigIdentity", "ShiftZeroBound"])
  (latexEnv := "theorem")]
theorem ZeroInequality : ∃ (E : ℝ) (EinIoo : E ∈ Ioo (0 : ℝ) 1),
    ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| := by
    sorry



noncomputable def E : ℝ := ZeroInequality.choose
lemma EinIoo : E ∈ Ioo (0 : ℝ) 1 := by
    exact ZeroInequality.choose_spec.1
theorem ZeroInequalitySpecialized : ∀ (ρ : ℂ) (σ t : ℝ),
    ζ ρ = 0 →
        σ = ρ.re →
            t = ρ.im →
                |t| ≥ 2 →
                    σ ≤ 1 - E / log |t| :=
    by exact ZeroInequality.choose_spec.2
@[blueprint
  (title := "DeltaT")
  (statement := /--
    Let $\delta_t=E/\log|t|$ where $E$ is the constant coming from Theorem \ref{ZeroInequality}.
  -/)]
noncomputable def DeltaT (t : ℝ) : ℝ := E / log |t|



@[blueprint
  (title := "DeltaRange")
  (statement := /--
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ we have that $$\delta_t<1/14.$$
  -/)
  (proof := /--
    Note that $\delta_t=E/\log|t|$ where $E$ is the implied constant from
    Lemma \ref{ZeroInequality}. But we know that $E=(14D)^{-1}$ where $D\geq 3A/\log 2+4B+C$
    where $A$, $B$, and $C$ are the constants coming from
    Lemmas \ref{ShiftZeroBound}, \ref{ShiftOneBound}, and \ref{ShiftTwoBound} respectively. Thus,
    $$E\leq\frac{1}{14\,(3A/\log 2+4B+C)}.$$
    But note that $A\geq 0$ and $B\geq 0$ by Lemmas \ref{ShiftZeroBound} and \ref{ShiftOneBound}
    respectively. However, we have that
    $$C\geq 2+\frac{2\log((13\,\zeta(3/2))/(3\,\zeta(3)))}{\log 2}$$
    by Theorem \ref{LogDerivZetaFinalBound} with Lemmas \ref{SumBoundI} and \ref{ShiftTwoBound}.
    So, by a very lazy estimate we have $C\geq 2$ and $E\leq 1/28$. Thus,
    $$\delta_t=\frac{E}{\log|t|}\leq\frac{1}{28\,\log2}<\frac{1}{14}.$$
  -/)
  (proofUses := ["LogDerivZetaFinalBound", "SumBoundI", "ShiftTwoBound", "ZeroInequality",
    "ShiftOneBound", "ShiftZeroBound"])
  (latexEnv := "lemma")]
lemma DeltaRange : ∀ (t : ℝ),
    |t| ≥ 2 →
        DeltaT t < (1 : ℝ) / 14 := by
    sorry



blueprint_comment /--
\begin{lemma}[SumBoundII]\label{SumBoundII}
    For all $t\in\mathbb{R}$ with $|t|\geq 2$ and $z=\sigma+it$
    where $1-\delta_t/3\leq\sigma\leq 3/2$, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{DeltaRange, LogDerivZetaFinalBound, ZeroInequality}
    By Lemma \ref{DeltaRange} we have that
    $$-11/21<-1/2-\delta_t/3\leq\sigma-3/2\leq0.$$
    We apply Theorem \ref{LogDerivZetaFinalBound} where $r'=2/3$, $r=3/4$, $R'=5/6$, and $R=8/9$.
    Thus for all $z\in\overline{\mathbb{D}_{5/6}}\setminus\mathcal{K}_f(5/6)$ we have that
    $$\left|\frac{\zeta'}{\zeta}(z+3/2+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{z-\rho}\right|\ll\log|t|$$
    where $f(z)=\zeta(z+3/2+it)$ for $t\in\mathbb{R}$ with $|t|\geq 3$.
    Now if we let $z=\sigma-3/2$, then $z\in(-11/21,0)\subseteq\overline{\mathbb{D}_{5/6}}$.
    Additionally, $f(z)=\zeta(\sigma+it)$, where $\sigma+it$ lies in the zero free region given by
    Lemma \ref{ZeroInequality} since $\sigma\geq 1-\delta_t/3\geq 1-\delta_t$.
    Thus, $z\not\in\mathcal{K}_f(5/6)$. So,
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{K}_f(5/6)}\frac{m_f(\rho)}{\sigma-3/2-\rho}\right|\ll\log|t|.$$
    But now note that if $\rho\in\mathcal{K}_f(5/6)$, then $\zeta(\rho+3/2+it)=0$
    and $|\rho|\leq 5/6$. Additionally, note that $m_f(\rho)=m_\zeta(\rho+3/2+it)$.
    So changing variables using these facts gives us that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{\sigma+it-\rho}\right|\ll\log|t|.$$
\end{proof}
-/



blueprint_comment /--
\begin{lemma}[GapSize]\label{GapSize}
   Let $t\in\mathbb{R}$ with $|t|\geq 3$ and $z=\sigma+it$ where $1-\delta_t/3\leq\sigma\leq 3/2$.
   Additionally, let $\rho\in\mathcal{Z}_t$. Then we have that
   $$|z-\rho|\geq\delta_t/6.$$
\end{lemma}
-/

blueprint_comment /--
\begin{proof}
\uses{ZeroInequality}
    Let $\rho=\sigma'+it'$ and note that since $\rho\in\mathcal{Z}_t$, we have $t'\in(t-5/6,t+5/6)$.
    Thus, if $t>1$ we have
    $$\log|t'|\leq\log|t+5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    And otherwise if $t<-1$ we have
    $$\log|t'|\leq\log|t-5/6|\leq\log|2t|=\log 2+\log|t|\leq 2\log|t|.$$
    So by taking reciprocals and multiplying through by a constant we have
    that $\delta_t\leq2\delta_{t'}$. Now note that since $\rho\in\mathcal{Z}_t$
    we know that $\sigma'\leq 1-\delta_{t'}$ by Theorem \ref{ZeroInequality}
    (here we use the fact that $|t|\geq 3$ to give us that $|t'|\geq 2$). Thus,
    $$\delta_t/6\leq\delta_{t'}-\delta_t/3
      =1-\delta_t/3-(1-\delta_{t'})\leq\sigma-\sigma'\leq|z-\rho|.$$
\end{proof}
-/



@[blueprint
  (title := "LogDerivZetaUniformLogSquaredBoundStrip")
  (statement := /--
    There exists a constant $F\in(0,1/2)$ such that
    for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\leq 3/2
      \implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
  -/)
  (proof := /--
    Take $F=E/3$ where $E$ comes from Theorem \ref{ZeroInequality}.
    Then we have that $\sigma\geq 1-\delta_t/3$. So, we apply Lemma \ref{SumBoundII},
    which gives us that
    $$\left|\frac{\zeta'}{\zeta}(z)
      -\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{z-\rho}\right|\ll\log|t|.$$
    Using the reverse triangle inequality and rearranging, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\sum_{\rho\in\mathcal{Z}_t}\frac{m_\zeta(\rho)}{|z-\rho|}+C\,\log|t|$$
    where $C$ is the implied constant in Lemma \ref{SumBoundII}.
    Now applying Lemma \ref{GapSize} we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho\in\mathcal{Z}_t}m_\zeta(\rho)+C\,\log|t|.$$
    Now let $f(z)=\zeta(z+3/2+it)/\zeta(3/2+it)$ with $\rho=\rho'+3/2+it$.
    Then if $\rho\in\mathcal{Z}_t$ we have that
    $$0=\zeta(\rho)=\zeta(\rho'+3/2+it)=f(\rho')$$
    with the same multiplicity of zero, that is $m_\zeta(\rho)=m_f(\rho')$.
    And also if $\rho\in\mathcal{Z}_t$ then
    $$5/6\geq|\rho-(3/2+it)|=|\rho'|.$$
    Thus we change variables to have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|
      \leq\frac{6}{\delta_t}\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')+C\,\log|t|.$$
    Now note that $f(0)=1$ and for $|z|\leq 8/9$ we have
    $$|f(z)|=\frac{|\zeta(z+3/2+it)|}{|\zeta(3/2+it)|}
      \leq\frac{\zeta(3/2)}{\zeta(3)}\cdot(7+2\,|t|)\leq\frac{13\,\zeta(3/2)}{3\,\zeta(3)}\,|t|$$
    by Theorems \ref{ZetaFixedLowerBound} and \ref{GlobalBound}.
    Thus by Theorem \ref{ZerosBound} we have that
    $$\sum_{\rho'\in\mathcal{K}_f(5/6)}m_f(\rho')
      \leq\frac{\log|t|+\log(13\,\zeta(3/2)/(3\,\zeta(3)))}{\log((8/9)/(5/6))}\leq D\log|t|$$
    where $D$ is taken to be sufficiently large.
    Recall, by definition that, $\delta_t=E/\log|t|$ with $E$ coming from
    Theorem \ref{ZeroInequality}. By using this fact and the above, we have that
    $$\left|\frac{\zeta'}{\zeta}(z)\right|\ll\log^2|t|+\log|t|$$
    where the implied constant is taken to be bigger than $\max(6D/E,C)$.
    We know that the RHS is bounded above by $\ll\log^2|t|$; so the result follows.
  -/)
  (proofUses := ["ZetaFixedLowerBound", "ZerosBound", "GlobalBound", "SumBoundII", "ZeroInequality",
    "GapSize"])
  (latexEnv := "lemma")]
lemma LogDerivZetaUniformLogSquaredBoundStrip : ∃ (F : ℝ) (Fequ : F = E / 3) (C : ℝ)
    (Cnonneg : 0 ≤ C), ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 := by
    use E / 3
    refine exists_prop.mpr ?_
    constructor
    ·   rfl
    ·   sorry



noncomputable def F : ℝ := LogDerivZetaUniformLogSquaredBoundStrip.choose
lemma Fequ : F = E / 3 := by
    exact LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.1
lemma LogDerivZetaUniformLogSquaredBoundStripSpec : ∃ (C : ℝ) (_ : 0 ≤ C),
    ∀ (σ t : ℝ),
    3 ≤ |t| →
        σ ∈ Set.Icc (1 - F / Real.log |t|) (3 / 2) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * (Real.log |t|) ^ 2 :=
    by exact LogDerivZetaUniformLogSquaredBoundStrip.choose_spec.2
lemma FLogTtoDeltaT : ∀ (t : ℝ),
    DeltaT t / 3 = F / Real.log |t| := by
    unfold DeltaT
    rw [Fequ]
    ring_nf
    exact fun t ↦ trivial



@[blueprint
  (title := "LogDerivZetaUniformLogSquaredBound")
  (statement := /--
    There exists a constant $F\in(0,1/2)$ such that for all $t\in\mathbb{R}$ with $|t|\geq 3$ one has
    $$1-\frac{F}{\log|t|}\leq\sigma\implies\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|\ll\log^2|t|$$
    where the implied constant is uniform in $\sigma$.
  -/)
  (proof := /--
    Note that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      =\sum_{1\leq n}\frac{\Lambda(n)}{|n^{\sigma+it}|}=\sum_{1\leq n}\frac{\Lambda(n)}{n^\sigma}
      =-\frac{\zeta'}{\zeta}(\sigma)\leq\left|\frac{\zeta'}{\zeta}(\sigma)\right|.$$
    From Theorem \ref{riemannZetaLogDerivResidue}, and applying the triangle inequality we know that
    $$\left|\frac{\zeta'}{\zeta}(s)\right|\leq\frac{1}{|s-1|}+C.$$
    where $C>0$ is some constant. Thus, for $\sigma\geq 3/2$ we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      \leq\left|\frac{\zeta'}{\zeta}(\sigma)\right|
      \leq\frac{1}{\sigma-1}+C\leq 2+C\ll 1\ll\log^2|t|.$$
    Putting this together with Lemma \ref{LogDerivZetaUniformLogSquaredBoundStrip}
    completes the proof.
  -/)
  (proofUses := ["riemannZetaLogDerivResidue", "LogDerivZetaUniformLogSquaredBoundStrip"])
  (latexEnv := "theorem")]
theorem LogDerivZetaUniformLogSquaredBound : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ (σ t : ℝ),
    3 < |t| →
        σ ∈ Set.Ici (1 - F / Real.log |t|) →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log |t| ^ 2 := by
    sorry



@[blueprint
  (title := "LogDerivZetaLogSquaredBoundSmallt")
  (statement := /--
    For $T>0$ and $\sigma'=1-\delta_T/3=1-F/\log T$, if $|t|\leq T$ then we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|\ll\log^2(2+T).$$
  -/)
  (proof := /--
    Note that if $|t|\geq 3$ then from Theorem \ref{LogDerivZetaUniformLogSquaredBound} we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|\ll\log^2|t|\leq\log^2T\leq\log^2(2+T).$$
    Otherwise, if $|t|\leq 3$, then from Theorem \ref{riemannZetaLogDerivResidue}
    and applying the triangle inequality we know
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \leq\frac{1}{|(\sigma'-1)+it|}+C\leq\frac{\log T}{F}+C$$
    where $C\geq 0$. Thus, we have that
    $$\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \leq\left(\frac{\log T}{F\,\log 2}+\frac{C}{\log 2}\right)\,\log(2+|t|)
      \leq\left(\frac{\log(2+T)}{F\,\log 2}+\frac{C}{\log 2}\right)\log(2+T)
      \ll\log^2(2+T).$$
  -/)
  (proofUses := ["LogDerivZetaUniformLogSquaredBound", "riemannZetaLogDerivResidue"])
  (latexEnv := "theorem")]
theorem LogDerivZetaLogSquaredBoundSmallt : ∃ (C : ℝ) (Cnonneg : C ≥ 0),
    ∀ (σ t T : ℝ) (Tpos: T > 0),
    |t| ≤ T →
        σ = 1 - F / Real.log T →
            ‖ζ' (σ + t * I) / ζ (σ + t * I)‖ ≤ C * Real.log (2 + T) ^ 2 := by
    sorry



blueprint_comment /--
From here out we closely follow our previous proof of the Medium PNT and we modify it
using our new estimate in Theorem \ref{LogDerivZetaUniformLogSquaredBound}.
Recall Definition \ref{SmoothedChebyshev}; for fixed $\varepsilon>0$
and a bump function $\nu$ supported on $[1/2,2]$ we have
$$\psi_\varepsilon(X)
  =\frac{1}{2\pi i}\int_{(\sigma)}\left(-\frac{\zeta'}{\zeta}(s)\right)
  \,\mathcal{M}(\tilde{1}_\varepsilon)(s)\,X^s\,ds$$
where $\sigma=1+1/\log X$. Let $T>3$ be a large constant to be chosen later,
and we take $\sigma'=1-\delta_T/3=1-F/\log T$ with $F$ coming from
Theorem \ref{LogDerivZetaUniformLogSquaredBound}. We integrate along the $\sigma$ vertical line,
and we pull contours  accumulating the pole at $s=1$ when we integrate along the curves
\begin{itemize}
    \item $I_1$: $\sigma-i\infty$ to $\sigma-iT$
    \item $I_2$: $\sigma'-iT$ to $\sigma-iT$
    \item $I_3$: $\sigma'-iT$ to $\sigma'+iT$
    \item $I_4$: $\sigma'+iT$ to $\sigma+iT$
    \item $I_5$: $\sigma+iT$ to $\sigma+i\infty$.
\end{itemize}
-/



@[blueprint
  (title := "I1New")
  (statement := /--
    Let
    $$I_1(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_{-\infty}^{-T}\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
  -/)]
noncomputable def I1New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Iic (-T),
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))



@[blueprint
  (title := "I5New")
  (statement := /--
    Let
    $$I_5(\nu,\varepsilon,X,T)=
      \frac{1}{2\pi i}\int_T^\infty\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt.$$
  -/)]
noncomputable def I5New (SmoothingF : ℝ → ℝ) (ε X T : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t : ℝ in Ici T,
      SmoothedChebyshevIntegrand SmoothingF ε X ((1 + (Real.log X)⁻¹) + t * I)))

lemma IntegralLogSqOverTSqBound : ∃ C > 0, ∀ T, 3 < T →
  ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C / Real.sqrt T := by
    have h_log_sq_le_t_fourth_pow :
        ∃ C > 0, ∀ t : ℝ, 3 ≤ t → (Real.log t)^2 / t^2 ≤ C / t^(3/2 : ℝ) := by
      have h_log_sq_le_sqrt :
          ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ^ 2 ≤ C * t ^ (1 / 2 : ℝ) := by
        have h_log_sq_le_sqrt : ∃ C > 0, ∀ t : ℝ, 3 ≤ t → Real.log t ≤ C * t ^ (1 / 4 : ℝ) := by
          use 4, by grind, fun t ht ↦ ?_
          have := Real.log_le_sub_one_of_pos (by positivity : 0 < t ^ (1 / 4 : ℝ))
          rw [Real.log_rpow (by positivity)] at this; linarith
        obtain ⟨C, hC₀, hC⟩ := h_log_sq_le_sqrt; use C^2
        exact ⟨sq_pos_of_pos hC₀, fun t ht ↦
          (pow_le_pow_left₀ (Real.log_nonneg <| by linarith) (hC t ht) 2).trans <| by
            rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
            grind⟩
      obtain ⟨C, hC_pos, hC⟩ := h_log_sq_le_sqrt; use C
      refine ⟨hC_pos, fun t ht ↦ ?_⟩; rw [div_le_div_iff₀] <;> try positivity
      convert mul_le_mul_of_nonneg_right (hC t ht)
        (Real.rpow_nonneg (by linarith : 0 ≤ t) (3 / 2)) using 1
      rw [mul_assoc, ← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; grind
    obtain ⟨C, hC_pos, hC_bound⟩ := h_log_sq_le_t_fourth_pow
    use C * 2
    have h_integral_bound :
        ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, C / t^(3/2 : ℝ) = C * 2 / Real.sqrt T := by
      have h_integral_eval :
          ∀ T : ℝ, 3 < T → ∫ t in Set.Ici T, t ^ (-3 / 2 : ℝ) = 2 / Real.sqrt T := by
        intro T hT
        rw [MeasureTheory.integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt] <;> norm_num
        · rw [Real.sqrt_eq_rpow, Real.rpow_neg] <;> ring_nf; linarith
        · linarith
      intro T hT; convert congr_arg (fun x ↦ C * x) (h_integral_eval T hT) using 1 <;> ring_nf
      rw [← MeasureTheory.integral_const_mul]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici fun x hx ↦ ?_
      rw [← Real.rpow_neg (by linarith [Set.mem_Ici.mp hx])]; ring_nf
    refine ⟨by positivity, fun T hT ↦ (MeasureTheory.setIntegral_mono_on ?_ ?_ measurableSet_Ici
        fun t ht ↦ hC_bound t <| by linarith [ht.out]).trans (h_integral_bound T hT |> le_of_eq)⟩
    · have hInteg : IntegrableOn (fun t ↦ C / t ^ (3 / 2 : ℝ)) (Set.Ici T) := by
        have := h_integral_bound T hT
        contrapose! this; rw [MeasureTheory.integral_undef this]; positivity
      have hMeas : AEStronglyMeasurable (fun t ↦ Real.log t ^ 2 / t ^ 2)
          (MeasureTheory.volume.restrict (Set.Ici T)) :=
        Measurable.aestronglyMeasurable <| Measurable.mul
          (Measurable.pow_const Real.measurable_log _)
          (Measurable.inv (measurable_id.pow_const _))
      have hBound : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ici T),
          ‖Real.log t ^ 2 / t ^ 2‖ ≤ C / t ^ (3 / 2 : ℝ) := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg (by positivity)]
        exact hC_bound t (by linarith [ht.out])
      exact MeasureTheory.Integrable.mono' hInteg hMeas hBound
    · have := h_integral_bound T hT
      contrapose! this; rw [MeasureTheory.integral_undef this]; positivity

lemma NormXPowS {X : ℝ} (X_gt_one : 1 < X) {s : ℂ} (hs : s.re = 1 + (Real.log X)⁻¹) :
    ‖(X : ℂ) ^ s‖ = X * Real.exp 1 := by
  have hX : 0 < X := by positivity
  simp only [Complex.norm_cpow_eq_rpow_re_of_pos hX, hs, Real.rpow_add hX, Real.rpow_one,
    Real.rpow_inv_log hX X_gt_one.ne']

lemma LogDerivZetaBoundForI1 : ∃ C > 0, ∀ {X T : ℝ} (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    let σ := 1 + (Real.log X)⁻¹
    ‖deriv riemannZeta (σ + t * I) / riemannZeta (σ + t * I)‖ ≤ C * (Real.log (-t))^2 := by
  obtain ⟨C, hC⟩ := LogDerivZetaUniformLogSquaredBound
  field_simp
  use C + 1
  refine ⟨by grind, fun {X T} hX hT t ht ↦ (hC.2 _ _ ?_ ?_).trans ?_⟩
  · cases abs_cases t <;> grind
  · apply Set.mem_Ici.mpr
    have hX' : 0 ≤ 1 / Real.log X := one_div_nonneg.mpr (Real.log_nonneg (by grind))
    have ht' : 0 ≤ F / Real.log |t| := by
      apply div_nonneg (Fequ ▸ div_nonneg (le_of_lt EinIoo.1) zero_le_three)
      exact Real.log_nonneg (by cases abs_cases t <;> grind)
    grind
  · simp only [abs_of_nonpos (by grind : t ≤ 0)]
    nlinarith [hC.1, sq_nonneg (Real.log (-t))]

lemma I1NewIntegrandBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Set.Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ C > 0, ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Set.Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T)
    (t : ℝ) (_ht : t ≤ -T),
    ‖SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
    C * (X / ε) * (Real.log (-t))^2 / (-t)^2 := by
  obtain ⟨C₁, hC₁₀, hC₁⟩ := @LogDerivZetaBoundForI1
  obtain ⟨C₂, hC₂₀, hC₂⟩ := @MellinOfSmooth1b SmoothingF ContDiffSmoothingF suppSmoothingF
  refine ⟨C₁ * C₂ * Real.exp 1, by positivity, fun {ε X T} hε hX hT t ht ↦ ?_⟩
  specialize hC₁ hX hT t ht
  specialize hC₂ 1 zero_lt_one (1 + (Real.log X)⁻¹ + t * Complex.I) ?_ ?_ ε hε.1 hε.2 <;> norm_num at *
  · exact Real.log_nonneg (by linarith)
  · linarith [inv_le_one_of_one_le₀ (show 1 ≤ Real.log X from by
      rw [Real.le_log_iff_exp_le (by linarith)]
      exact Real.exp_one_lt_d9.le.trans (by grind))]
  · refine (mul_le_mul_of_nonneg_right
        (mul_le_mul hC₁ hC₂ (by positivity) (by positivity)) (by positivity)).trans ?_
    rw [Complex.norm_cpow_of_ne_zero (by norm_cast; linarith)]
    norm_num [Complex.normSq, Complex.sq_norm]
    ring_nf
    norm_num
    rw [abs_of_pos (by positivity)]
    norm_num [Complex.arg]
    ring_nf
    norm_num
    rw [if_pos (by positivity)]
    norm_num [Real.rpow_add (by positivity : 0 < X), Real.rpow_one]
    ring_nf
    norm_num
    rw [show X ^ (Real.log X)⁻¹ = Real.exp 1 by
      rw [Real.rpow_def_of_pos (by positivity)]
      norm_num [Real.exp_ne_zero, ne_of_gt (Real.log_pos (by linarith : 1 < X))]]
    ring_nf
    norm_num
    field_simp
    gcongr
    · exact mul_pos (sq_pos_of_neg (by linarith)) hε.1
    · linarith
    · exact le_add_of_nonneg_left <| add_nonneg (add_nonneg zero_le_one
          (div_nonneg zero_le_two (Real.log_nonneg (by linarith))))
          (div_nonneg zero_le_one (sq_nonneg _))

@[blueprint
  (title := "I1NewBound")
  (statement := /--
    We have that
    $$|I_1(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$
  -/)
  (proof := /--
    Note that $|I_1(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{-\infty}^{-T}\left(-\frac{\zeta'}{\zeta}(\sigma+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)\,X^{\sigma+it}\,dt\right|
      \ll\int_{-\infty}^{-T}\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma+it)|\cdot X^\sigma\,dt.$$
    Applying Theorem \ref{LogDerivZetaUniformLogSquaredBound} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_1(\nu,\varepsilon,X,T)|
      \ll\int_{-\infty}^{-T}\log^2|t|\cdot\frac{X^\sigma}{\varepsilon\,|\sigma+it|^2}\,dt
      \ll\frac{X}{\varepsilon}\int_T^\infty\frac{\sqrt{t}\,dt}{t^2}
      \ll\frac{X}{\varepsilon\sqrt{T}}.$$
    Here we are using the fact that $\log^2 t$ grows slower than $\sqrt{t}$,
    $|\sigma+it|^2\geq t^2$, and $X^\sigma=X\cdot X^{1/\log X}=eX$.
  -/)
  (proofUses := ["LogDerivZetaUniformLogSquaredBound", "MellinOfSmooth1b"])
  (latexEnv := "lemma")]
lemma I1NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (_Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (_εinIoo : ε ∈ Ioo 0 1) (_Xgt3 : 3 < X) (_Tgt3 : 3 < T),
    ‖I1New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    have h_I1New_bound : ∃ C > 0, ∀ {ε X T : ℝ} (εinIoo : ε ∈ Set.Ioo 0 1) (Xgt3 : 3 < X)
        (Tgt3 : 3 < T),
        ‖∫ t in Set.Iic (-T),
          SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
          C * (X / ε) * (1 / Real.sqrt T) := by
            obtain ⟨C₁, hC₁_pos, hC₁⟩ : ∃ C₁ > 0, ∀ {ε X T : ℝ} (εinIoo : ε ∈ Set.Ioo 0 1)
                (Xgt3 : 3 < X) (Tgt3 : 3 < T)
                (t : ℝ) (ht : t ≤ -T),
                ‖SmoothedChebyshevIntegrand SmoothingF ε X (1 + (Real.log X)⁻¹ + t * I)‖ ≤
                C₁ * (X / ε) * (Real.log (-t))^2 / (-t)^2 :=
              I1NewIntegrandBound suppSmoothingF ContDiffSmoothingF
            obtain ⟨C₂, hC₂_pos, hC₂⟩ : ∃ C₂ > 0, ∀ {T : ℝ} (Tgt3 : 3 < T),
                ∫ t in Set.Ici T, (Real.log t)^2 / t^2 ≤ C₂ / Real.sqrt T :=
                  IntegralLogSqOverTSqBound
            refine ⟨C₁ * C₂, mul_pos hC₁_pos hC₂_pos,
              fun {ε X T} εinIoo Xgt3 Tgt3 ↦
                (MeasureTheory.norm_integral_le_integral_norm _).trans ?_⟩
            refine (MeasureTheory.integral_mono_of_nonneg
              (g := fun t ↦ C₁ * (X / ε) * Real.log (-t) ^ 2 / (-t) ^ 2) ?_ ?_ ?_).trans ?_
            · exact Filter.Eventually.of_forall fun x ↦ norm_nonneg _
            · have h_integrable :
                  MeasureTheory.IntegrableOn (fun t ↦ (Real.log t)^2 / t^2) (Set.Ici T) := by
                have h_integrable :
                    MeasureTheory.IntegrableOn
                      (fun t ↦ (Real.log t)^2 / t^2) (Set.Ioi T) := by
                  have h_bound : ∀ t, t > T → (Real.log t)^2 / t^2 ≤ 4 / t^(3/2 : ℝ) := by
                    intro t ht
                    have h_log_bound : Real.log t ≤ 2 * t^(1/4 : ℝ) := by
                      have := Real.log_le_sub_one_of_pos (show 0 < t ^ (1 / 4 : ℝ) / 2 by
                        exact div_pos (Real.rpow_pos_of_pos (by linarith) _) zero_lt_two)
                      rw [Real.log_div (by exact ne_of_gt (Real.rpow_pos_of_pos (by linarith) _))
                        (by norm_num), Real.log_rpow (by linarith)] at this
                      have := Real.log_two_lt_d9; norm_num at *; linarith
                    rw [div_le_div_iff₀ (by nlinarith)
                      (Real.rpow_pos_of_pos (by linarith) (3 / 2))]
                    refine (mul_le_mul_of_nonneg_right (pow_le_pow_left₀
                      (Real.log_nonneg (by linarith)) h_log_bound 2)
                      (by exact Real.rpow_nonneg (by linarith) _)).trans ?_
                    ring_nf
                    norm_num
                    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith),
                      ← Real.rpow_add (by linarith)]
                    norm_num
                  have h_integrable :
                      MeasureTheory.IntegrableOn (fun t ↦ 4 / t^(3/2 : ℝ)) (Set.Ioi T) := by
                    have h_integrable :
                        MeasureTheory.IntegrableOn (fun t ↦ t ^ (-3 / 2 : ℝ)) (Set.Ioi T) :=
                      integrableOn_Ioi_rpow_of_lt (by norm_num) (by linarith)
                    norm_num [div_eq_mul_inv] at *
                    exact MeasureTheory.Integrable.const_mul (h_integrable.congr_fun
                      (fun x hx ↦ by rw [Real.rpow_neg (by linarith [hx.out])])
                      measurableSet_Ioi) _
                  refine h_integrable.mono' ?_ ?_
                  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
                    have hne : ∀ t ∈ Set.Ioi T, t ≠ 0 := fun t ht ↦ by linarith [ht.out]
                    have hsq : ∀ t ∈ Set.Ioi T, t ^ 2 ≠ 0 := fun t ht ↦ pow_ne_zero 2 (hne t ht)
                    fun_prop (discharger := assumption)
                  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
                      with t ht using by
                        rw [Real.norm_of_nonneg (by positivity)]
                        exact h_bound t ht
                rw [MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_congr_set
                  MeasureTheory.Ioi_ae_eq_Ici] at *
                simp_all only [one_div, mem_Ioo, ofReal_inv, Complex.norm_mul, Complex.norm_div,
                  norm_neg, log_neg_eq_log, even_two, Even.neg_pow]
              have h_integrable : MeasureTheory.IntegrableOn (fun t ↦
                  (Real.log (-t))^2 / (-t)^2) (Set.Iic (-T)) := by
                convert h_integrable.comp_neg using 1; norm_num [Set.indicator]
              simpa only [mul_div_assoc] using h_integrable.const_mul _
            · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Iic] with t ht
                using hC₁ εinIoo Xgt3 Tgt3 t ht
            · convert mul_le_mul_of_nonneg_left (hC₂ Tgt3) (show 0 ≤ C₁ * (X / ε) by
                exact mul_nonneg hC₁_pos.le
                  (div_nonneg (by positivity) (by linarith [εinIoo.1]))) using 1 <;> ring_nf
              rw [← MeasureTheory.integral_const_mul, MeasureTheory.integral_Ici_eq_integral_Ioi,
                ← neg_neg T, ← integral_comp_neg_Iic]
              norm_num
              ring_nf
    obtain ⟨C, hC₀, hC⟩ := h_I1New_bound; use C / (2 * Real.pi)
    refine ⟨by positivity, fun {ε X T} hε hX hT ↦ ?_⟩
    simp_all [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
    ring_nf at *
    convert mul_le_mul_of_nonneg_right (hC hε.1 hε.2 hX hT)
      (show (0 : ℝ) ≤ Real.pi⁻¹ * (1 / 2) by positivity) using 1
    · simp only [I1New, SmoothedChebyshevIntegrand, norm_mul, norm_inv, Complex.norm_I,
        Complex.norm_two, mul_one, one_mul, one_div]
      rw [show ∀ a b : ℝ, (2 * a)⁻¹ * b = b * (a⁻¹ * 2⁻¹) by intro _ _; ring]
      congr 1
      · apply congr_arg
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Iic fun t _ ↦ by
          rw [show (↑t : ℂ) * I = I * ↑t by ring, div_eq_mul_inv, neg_mul,
              show (↑(Real.log X)⁻¹ : ℂ) = (↑(Real.log X))⁻¹ from Complex.ofReal_inv _]
          ring
      · rw [show ‖(↑π : ℂ)‖ = π from (RCLike.norm_ofReal π).trans (abs_of_pos Real.pi_pos)]
    · ring

@[blueprint
  (title := "I5NewBound")
  (statement := /--
    We have that
    $$|I_5(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$
  -/)
  (proof := /--
    By symmetry, note that
    $$|I_1(\nu,\varepsilon,X,T)|=|\overline{I_5(\nu,\varepsilon,X,T)}|=|I_5(\nu,\varepsilon,X,T)|.$$
    Applying Lemma \ref{I1NewBound} completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma I5NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        ‖I5New SmoothingF ε X T‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    obtain ⟨C, Cnonneg, hI1NewBound⟩ := I1NewBound suppSmoothingF ContDiffSmoothingF
    use C, Cnonneg
    intro ε X T εinIoo Xgt3 Tgt3
    have I1NewI5New : I5New SmoothingF ε X T = conj (I1New SmoothingF ε X T) := by
        unfold I1New I5New
        simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
        rw [neg_mul, mul_neg, ← neg_mul]
        congr
        ·   ring
        ·   rw [← integral_conj, ← integral_comp_neg_Ioi, integral_Ici_eq_integral_Ioi]
            apply setIntegral_congr_fun <| measurableSet_Ioi
            intro x hx
            simp only []
            rw[← smoothedChebyshevIntegrand_conj (by linarith)]
            simp only [ofReal_inv, ofReal_neg, neg_mul, map_add, map_one, map_inv₀, conj_ofReal,
              map_neg, map_mul, conj_I, mul_neg, neg_neg]
    rw[I1NewI5New, RCLike.norm_conj]
    exact hI1NewBound εinIoo Xgt3 Tgt3



@[blueprint
  (title := "I2New")
  (statement := /--
    Let
    $$I_2(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0-iT)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)\,X^{\sigma_0-iT}\,d\sigma_0.$$
  -/)]
noncomputable def I2New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ - T * I)))



@[blueprint
  (title := "I4New")
  (statement := /--
    Let
    $$I_4(\nu,\varepsilon,X,T)
    =\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0+iT)\right)
    \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0+iT)\,X^{\sigma_0+iT}\,d\sigma_0.$$
  -/)]
noncomputable def I4New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * ((∫ σ₀ in σ'..(1 + (Real.log X)⁻¹),
    SmoothedChebyshevIntegrand SmoothingF ε X (σ₀ + T * I)))



@[blueprint
  (title := "I2NewBound")
  (statement := /--
    We have that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$
  -/)
  (proof := /--
    Note that $|I_2(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{\sigma'}^\sigma\left(-\frac{\zeta'}{\zeta}(\sigma_0-iT)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)\,X^{\sigma_0-iT}\,d\sigma_0\right|
      \ll\int_{\sigma'}^\sigma\left|\frac{\zeta'}{\zeta}(\sigma_0-iT)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma_0-iT)|\cdot X^{\sigma_0}\,d\sigma_0.$$
    Applying Theorem \ref{LogDerivZetaUniformLogSquaredBound} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\int_{\sigma'}^\sigma\log^2 T
      \cdot\frac{X^{\sigma_0}}{\varepsilon\,|\sigma_0-iT|^2}\,d\sigma_0
      \ll\frac{X\,\log^2T}{\varepsilon\,T^2}\int_{\sigma'}^\sigma d\,\sigma_0
      =\frac{X\,\log^2T}{\varepsilon\,T^2}\,(\sigma-\sigma').$$
    Here we are using the fact that $X^{\sigma_0}\leq X^\sigma=X\cdot X^{1/\log X}=eX$
    and $|\sigma_0-iT|^2\geq T^2$. Now note that
    $$|I_2(\nu,\varepsilon,X,T)|\ll\frac{X\,\log^2T}{\varepsilon\,T^2}\,(\sigma-\sigma')
      =\frac{X\,\log^2T}{\varepsilon\,T^2\,\log X}+\frac{FX\,\log T}{\varepsilon\,T^2}
      \ll\frac{X}{\varepsilon\sqrt{T}}.$$
    Here we are using the fact that $\log T\ll T^{3/2}$, $\log^2T\ll T^{3/2}$, and $X/\log X\ll X$.
  -/)
  (proofUses := ["LogDerivZetaUniformLogSquaredBound", "MellinOfSmooth1b"])
  (latexEnv := "lemma")]
lemma I2NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I2New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    sorry



@[blueprint
  (title := "I4NewBound")
  (statement := /--
    We have that
    $$|I_4(\nu,\varepsilon,X,T)|\ll\frac{X}{\varepsilon\sqrt{T}}.$$
  -/)
  (proof := /--
    By symmetry, note that
    $$|I_2(\nu,\varepsilon,X,T)|=|\overline{I_4(\nu,\varepsilon,X,T)}|=|I_4(\nu,\varepsilon,X,T)|.$$
    Applying Lemma \ref{I2NewBound} completes the proof.
  -/)
  (latexEnv := "lemma")]
lemma I4NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    ∃ (C : ℝ) (_ : 0 ≤ C),
      ∀ {ε X T : ℝ} (_ : ε ∈ Ioo 0 1) (_ : 3 < X) (_ : 3 < T),
        let σ' := 1 - F / Real.log T
        ‖I4New SmoothingF ε X T σ'‖ ≤ C * (X / (ε * Real.sqrt T)) := by
    obtain ⟨C, Cnonneg, hI2NewBound⟩ := I2NewBound suppSmoothingF ContDiffSmoothingF
    use C, Cnonneg
    intro ε X T εinIoo Xgt3 Tgt3 σ'
    have I2NewI4New : I4New SmoothingF ε X T σ' = -conj (I2New SmoothingF ε X T σ') := by
        unfold I2New I4New
        simp only [map_mul, map_div₀, conj_I, conj_ofReal, conj_ofNat, map_one]
        rw [mul_neg, div_neg, neg_mul_comm, ← mul_neg]
        congr
        rw [← intervalIntegral_conj, neg_neg]
        apply intervalIntegral.integral_congr
        intro x hx
        simp only []
        rw[← smoothedChebyshevIntegrand_conj (by linarith)]
        simp only [map_sub, conj_ofReal, map_mul, conj_I, mul_neg, sub_neg_eq_add]
    rw[I2NewI4New, norm_neg, RCLike.norm_conj]
    exact hI2NewBound εinIoo Xgt3 Tgt3



@[blueprint
  (title := "I3New")
  (statement := /--
    Let
    $$I_3(\nu,\varepsilon,X,T)
      =\frac{1}{2\pi i}\int_{-T}^T\left(-\frac{\zeta'}{\zeta}(\sigma'+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)\,X^{\sigma'+it}\,dt.$$
  -/)]
noncomputable def I3New (SmoothingF : ℝ → ℝ) (ε T X σ' : ℝ) : ℂ :=
  (1 / (2 * π * I)) * (I * (∫ t in (-T)..T,
    SmoothedChebyshevIntegrand SmoothingF ε X (σ' + t * I)))



@[blueprint
  (title := "I3NewBound")
  (statement := /--
    We have that
    $$|I_3(\nu,\varepsilon,X,T)|\ll\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}.$$
  -/)
  (proof := /--
    Note that $|I_3(\nu,\varepsilon,X,T)|=$
    $$\left|\frac{1}{2\pi i}\int_{-T}^T\left(-\frac{\zeta'}{\zeta}(\sigma'+it)\right)
      \,\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)\,X^{\sigma'+it}\,dt\right|
      \ll\int_{-T}^T\left|\frac{\zeta'}{\zeta}(\sigma'+it)\right|
      \cdot|\mathcal{M}(\tilde{1}_\varepsilon)(\sigma'+it)|\cdot X^{\sigma'}\,dt.$$
    Applying Theorem \ref{LogDerivZetaLogSquaredBoundSmallt} and Lemma \ref{MellinOfSmooth1b},
    we have that
    $$|I_3(\nu,\varepsilon,X,T)|\ll\int_{-T}^T\log^2(2+T)
      \cdot\frac{X^{\sigma'}}{\varepsilon\,|\sigma'+it|^2}\,dt
      \ll\frac{X^{1-F/\log T}\,\sqrt{T}}{\varepsilon}\int_0^T\frac{dt}{|\sigma'+it|^2}.$$
    Here we are using the fact that this integrand is symmetric in $t$ about $0$
    and that $\log^2(2+T)\ll\sqrt{T}$ for sufficiently large $T$. Now note that,
    by Lemma \ref{DeltaRange}, we have
    $$\frac{1}{|\sigma'+it|^2}=\frac{1}{(1-\delta_T/3)^2+t^2}<\frac{1}{(41/42)^2+t^2}.$$
    Thus,
    $$|I_3(\nu,\varepsilon,X,T)|
      \ll\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}\int_0^T\frac{dt}{|\sigma'+it|^2}
      \leq\frac{X^{1-F/\log T}\sqrt{T}}{\varepsilon}\int_0^\infty\frac{dt}{(41/42)^2+t^2}.$$
    The integral on the right hand side evaluates to $21\pi/41$, which is just a constant,
    so the desired result follows.
  -/)
  (proofUses := ["MellinOfSmooth1b", "DeltaRange", "LogDerivZetaLogSquaredBoundSmallt"])
  (latexEnv := "lemma")]
lemma I3NewBound {SmoothingF : ℝ → ℝ}
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) : ∃ (C : ℝ) (Cnonneg : 0 ≤ C),
    ∀ {ε X T : ℝ} (εinIoo : ε ∈ Ioo 0 1) (Xgt3 : 3 < X) (Tgt3 : 3 < T),
    let σ' := 1 - F / Real.log T
    ‖I3New SmoothingF ε X T σ'‖ ≤ C * (X ^ (1 - F / Real.log T) * Real.sqrt T) / ε := by
    sorry



@[blueprint
  (title := "SmoothedChebyshevPull3")
  (statement := /--
    We have that
    $$\psi_\varepsilon(X)=\mathcal{M}(\tilde{1}_\varepsilon)(1)\,X^1+I_1-I_2+I_3+I_4+I_5.$$
  -/)
  (proof := /--
    Pull contours and accumulate the pole of $\zeta'/\zeta$ at $s=1$.
  -/)]
theorem SmoothedChebyshevPull3 {SmoothingF : ℝ → ℝ} {ε : ℝ} (ε_pos : 0 < ε)
    (ε_lt_one : ε < 1)
    (X : ℝ) (X_gt : 3 < X)
    {T : ℝ} (T_pos : 0 < T) {σ' : ℝ}
    (σ'_pos : 0 < σ') (σ'_lt_one : σ' < 1)
    (holoOn : HolomorphicOn (ζ' / ζ) ((Icc σ' 2) ×ℂ (Icc (-T) T) \ {1}))
    (suppSmoothingF : Function.support SmoothingF ⊆ Icc (1 / 2) 2)
    (SmoothingFnonneg : ∀ x > 0, 0 ≤ SmoothingF x)
    (mass_one : ∫ x in Ioi 0, SmoothingF x / x = 1)
    (ContDiffSmoothingF : ContDiff ℝ 1 SmoothingF) :
    SmoothedChebyshev SmoothingF ε X =
      I1New SmoothingF ε X T -
      I2New SmoothingF ε T X σ' +
      I3New SmoothingF ε T X σ' +
      I4New SmoothingF ε T X σ' +
      I5New SmoothingF ε X T
      + 𝓜 (fun x ↦ (Smooth1 SmoothingF ε x : ℂ)) 1 * X := by
    unfold SmoothedChebyshev VerticalIntegral'
    have X_eq_gt_one : 1 < 1 + (Real.log X)⁻¹ := by
        nth_rewrite 1 [← add_zero 1]
        bound
    have X_eq_lt_two : (1 + (Real.log X)⁻¹) < 2 := by
        rw[← one_add_one_eq_two]
        gcongr
        exact inv_lt_one_of_one_lt₀ <| logt_gt_one X_gt.le
    have X_eq_le_two : 1 + (Real.log X)⁻¹ ≤ 2 := X_eq_lt_two.le
    rw [verticalIntegral_split_three (a := -T) (b := T)]
    swap
    ·   exact SmoothedChebyshevPull1_aux_integrable ε_pos ε_lt_one X_gt X_eq_gt_one
            X_eq_le_two suppSmoothingF SmoothingFnonneg mass_one ContDiffSmoothingF
    ·   have temp : ↑(1 + (Real.log X)⁻¹) = (1 : ℂ) + ↑(Real.log X)⁻¹ := by simp
        unfold I1New
        simp only [smul_eq_mul, mul_add, temp, sub_eq_add_neg, add_assoc, add_left_cancel_iff]
        unfold I5New
        nth_rewrite 6 [add_comm]
        simp only [← add_assoc]
        rw[add_right_cancel_iff, ← add_right_inj (1 / (2 * ↑π * I) *
            -VIntegral (SmoothedChebyshevIntegrand SmoothingF ε X) (1 + (Real.log X)⁻¹) (-T) T),
            ← mul_add, ← sub_eq_neg_add, sub_self, mul_zero]
        unfold VIntegral I2New I3New I4New
        simp only [smul_eq_mul, temp, ← add_assoc, ← mul_neg, ← mul_add]
        let fTempRR : ℝ → ℝ → ℂ := fun x ↦ fun y ↦
            SmoothedChebyshevIntegrand SmoothingF ε X ((x : ℝ) + (y : ℝ) * I)
        let fTempC : ℂ → ℂ := fun z ↦ fTempRR z.re z.im
        have : ∫ (y : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (1 + ↑(Real.log X)⁻¹ + ↑y * I) =
            ∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y := by
            unfold fTempRR
            simp only [temp]
        rw[this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ - ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T) := by
            unfold fTempRR
            simp only [ofReal_neg, neg_mul, sub_eq_add_neg]
        rw[this]
        have : ∫ (t : ℝ) in -T..T,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ' + ↑t * I) =
            ∫ (y : ℝ) in -T..T, fTempRR σ' y := by rfl
        rw[this]
        have : ∫ (σ₀ : ℝ) in σ'..1 + (Real.log X)⁻¹,
            SmoothedChebyshevIntegrand SmoothingF ε X (↑σ₀ + ↑T * I) =
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T := by rfl
        rw[this]
        have : (((I * -∫ (y : ℝ) in -T..T, fTempRR (1 + (Real.log X)⁻¹) y) +
            -∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x (-T)) +
            I * ∫ (y : ℝ) in -T..T, fTempRR σ' y) +
            ∫ (x : ℝ) in σ'..1 + (Real.log X)⁻¹, fTempRR x T =
            -(2 * ↑π * I) * RectangleIntegral' fTempC (σ' - T * I) (1 + ↑(Real.log X)⁻¹ + T * I) := by
            unfold RectangleIntegral' RectangleIntegral HIntegral VIntegral fTempC
            simp only [mul_neg, one_div, mul_inv_rev, inv_I, neg_mul, sub_im, ofReal_im, mul_im,
              ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_sub, ofReal_neg, add_re,
              neg_re, mul_re, sub_self, neg_zero, add_im, neg_im, zero_add, sub_re, sub_zero,
              ofReal_inv, one_re, inv_re, normSq_ofReal, div_self_mul_self', one_im, inv_im,
              zero_div, ofReal_add, ofReal_one, smul_eq_mul, neg_neg]
            ring_nf
            simp only [I_sq, neg_mul, one_mul, ne_eq, ofReal_eq_zero, pi_ne_zero, not_false_eq_true,
              mul_inv_cancel_right₀, sub_neg_eq_add, I_pow_three]
            ring_nf
        rw[this]
        field_simp
        rw[mul_comm, eq_comm, neg_add_eq_zero]

        have pInRectangleInterior : (Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I) ∈ nhds 1) := by
            refine rectangle_mem_nhds_iff.mpr ?_
            refine mem_reProdIm.mpr ?_
            simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                sub_zero, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero,
                sub_im, mul_im, zero_sub, add_im, one_im, inv_im, neg_zero, zero_div, zero_add]
            constructor
            ·   unfold uIoo
                rw [min_eq_left (by linarith), max_eq_right (by linarith)]
                exact mem_Ioo.mpr ⟨σ'_lt_one, (by linarith)⟩
            ·   unfold uIoo
                rw [min_eq_left (by linarith), max_eq_right (by linarith)]
                exact mem_Ioo.mpr ⟨(by linarith), (by linarith)⟩

        apply ResidueTheoremOnRectangleWithSimplePole'
        ·   simp; linarith
        ·   simp; linarith
        ·   simp only [one_div]
            exact pInRectangleInterior
        ·   apply DifferentiableOn.mul
            ·   apply DifferentiableOn.mul
                ·   simp only [re_add_im]
                    have : (fun z ↦ -ζ' z / ζ z) = -(ζ' / ζ) := by ext; simp; ring
                    rw [this]
                    apply DifferentiableOn.neg
                    apply holoOn.mono
                    apply diff_subset_diff_left
                    apply reProdIm_subset_iff'.mpr
                    left
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero, sub_im, mul_im, zero_sub, add_im, one_im, inv_im,
                        neg_zero, zero_div, zero_add]
                    constructor <;> apply uIcc_subset_Icc <;> constructor <;> linarith
                ·   intro s hs
                    apply DifferentiableAt.differentiableWithinAt
                    simp only [re_add_im]
                    apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    have := mem_reProdIm.mp hs.1 |>.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, one_div, ofReal_inv, add_re, one_re, inv_re, normSq_ofReal,
                        div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this
                    linarith [this.1]
            ·   intro s hs
                apply DifferentiableAt.differentiableWithinAt
                simp only [re_add_im]
                apply DifferentiableAt.const_cpow (by fun_prop)
                left
                norm_cast
                linarith
        ·   let U : Set ℂ := Rectangle (σ' - ↑T * I) (1 + (Real.log X)⁻¹ + T * I)
            let f : ℂ → ℂ := fun z ↦ -ζ' z / ζ z
            let g : ℂ → ℂ := fun z ↦ 𝓜 (fun x ↦ ↑(Smooth1 SmoothingF ε x)) z * ↑X ^ z
            unfold fTempC fTempRR SmoothedChebyshevIntegrand
            simp only [re_add_im]
            have g_holc : HolomorphicOn g U := by
                intro u uInU
                apply DifferentiableAt.differentiableWithinAt
                simp only [g]
                apply DifferentiableAt.mul
                ·   apply Smooth1MellinDifferentiable ContDiffSmoothingF suppSmoothingF ⟨ε_pos, ε_lt_one⟩ SmoothingFnonneg mass_one
                    simp only [ofReal_inv, U] at uInU
                    unfold Rectangle at uInU
                    rw[Complex.mem_reProdIm] at uInU
                    have := uInU.1
                    simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
                        sub_zero, add_re, one_re, inv_re, normSq_ofReal, div_self_mul_self', add_zero] at this
                    rw [uIcc_of_le (by linarith)] at this
                    linarith [this.1]
                ·   unfold HPow.hPow instHPow
                    apply DifferentiableAt.const_cpow differentiableAt_fun_id
                    left
                    norm_cast
                    linarith
            have f_near_p : (f - fun (z : ℂ) => 1 * (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by
                simp only [one_mul, f]
                exact riemannZetaLogDerivResidueBigO
            convert ResidueMult g_holc pInRectangleInterior f_near_p using 1
            ext
            simp [f, g]
            ring



blueprint_comment /--
\begin{theorem}[StrongPNT]\label{StrongPNT}
    We have
    $$\sum_{n\leq x}\Lambda(n)=x+O\left(x\exp(-c\sqrt{\log x})\right).$$
\end{theorem}
-/

blueprint_comment /--
\begin{proof}
\uses{SmoothedChebyshevClose, SmoothedChebyshevPull3, MellinOfSmooth1c, I1NewBound, I2NewBound,
  I3NewBound, I4NewBound, I5NewBound}
    By Theorem \ref{SmoothedChebyshevClose} and \ref{SmoothedChebyshevPull3} we have that
    $$\mathcal{M}(\tilde{1}_\varepsilon)(1)\,x^1+I_1-I_2+I_3+I_4+I_5
      =\psi(x)+O(\varepsilon x\log x).$$
    Applying Theorem \ref{MellinOfSmooth1c} and Lemmas \ref{I1NewBound}, \ref{I2NewBound},
    \ref{I3NewBound}, \ref{I4NewBound}, and \ref{I5NewBound} we have that
    $$\psi(x)=x+O(\varepsilon x)+O(\varepsilon x\log x)
      +O\left(\frac{x}{\varepsilon\sqrt{T}}\right)
      +O\left(\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\right).$$
    We absorb the $O(\varepsilon x)$ term into the $O(\varepsilon x\log x)$ term and
    balance the last two terms in $T$.
    $$\frac{x}{\varepsilon\sqrt{T}}
      =\frac{x^{1-F/\log T}\sqrt{T}}{\varepsilon}\implies T
      =\exp(\sqrt{F\log x}).$$
    Thus,
    $$\psi(x)=x+O(\varepsilon x\log x)
      +O\left(\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}\right).$$
    Now we balance the last two terms in $\varepsilon$.
    $$\varepsilon x\log x
      =\frac{x}{\displaystyle\varepsilon\exp((1/2)\cdot\sqrt{F\log x})}
      \implies\varepsilon\log x
      =\frac{\displaystyle\sqrt{\log x}}{\displaystyle\exp((1/4)\cdot\sqrt{F\log x})}.$$
    Thus,
    $$\psi(x)=x+O\left(x\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})\sqrt{\log x}\right).$$
    Absorbing the $\displaystyle\sqrt{\log x}$ into the
    $\displaystyle\exp(-(\sqrt{F}/4)\cdot\sqrt{\log x})$ completes the proof.
\end{proof}
-/

-- *** Prime Number Theorem *** The `ChebyshevPsi` function is asymptotic to `x`.
-- theorem PrimeNumberTheorem : ∃ (c : ℝ) (hc : c > 0),
--     (ChebyshevPsi - id) =O[atTop] (fun (x : ℝ) ↦ x * Real.exp (-c * Real.sqrt (Real.log x))) := by
--  sorry
