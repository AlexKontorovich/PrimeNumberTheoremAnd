import PrimeNumberTheoremAnd.Defs


blueprint_comment /--
\section{Ramanujan's inequality}\label{ramanujan-sec}

Use of prime number theorems to establish Ramanujan's inequality
$$\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$$
for sufficiently large $x$, following \cite{dudek-platt}.
-/

namespace Ramanujan


open Real Chebyshev

noncomputable def ε (M x : ℝ) : ℝ := 72 + 2 * M + (2 * M + 132) / log x + (4 * M + 288) / (log x)^2 + (12 * M + 576) / (log x)^3 + (48 * M) / (log x)^4 + (M^2) / (log x)^5

noncomputable def ε' (m x : ℝ) : ℝ := 206 + m + 364 / log x + 381 / (log x)^2 + 238 / (log x)^3 + 97 / (log x)^4 + 30 / (log x)^5 + 8 / (log x)^6

noncomputable def x' (m M x : ℝ) : ℝ := exp (ε M x - ε' m x)

@[blueprint
  "ramanujan-criterion-1"
  (title := "Criterion for Ramanujan's inequality, substep 1")
  (statement := /--
Let $M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
Then for $x > x_a$ we have
\begin{equation} \label{pipi}
\pi^2(x)  <  x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon_{M_a}(x)}{\log^7 x} \Big\}
\end{equation}
%
where
$$\epsilon_{M_a} (x) = 72 + 2 M_a + \frac{2M_a+132}{\log x} + \frac{4M_a+288}{\log^2 x} + \frac{12 M_a+576}{\log^3 x}+\frac{48M_a}{\log^4 x} + \frac{M_a^2}{\log^5 x}.$$
-/)
  (proof := /-- Direct calculation -/)
  (latexEnv := "sublemma")]
theorem sq_pi_lt (M_a x_a : ℝ) (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > x_a, pi x ^ 2 < x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6) + ε M_a x / log x ^ 7) := by
    sorry

@[blueprint
  "ramanujan-criterion-2"
  (title := "Criterion for Ramanujan's inequality, substep 2")
  (statement := /--
Let $m_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have
$$\pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{m_a x}{\log^6 x}.$$
Then for $x > e x_a$ we have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > x^2 \Big\{ \frac{1}{\log^2 x}+ \frac{2}{\log^3 x}+ \frac{5}{\log^4 x}+ \frac{16}{\log^5 x}+ \frac{64}{\log^6 x} + \frac{\epsilon'_{m_a}(x)}{\log^7 x} \Big\},$$
where
$$\epsilon'_{m_a}(x) = 206+m_a+\frac{364}{\log x} + \frac{381}{\log^2 x}+\frac{238}{\log^3 x} + \frac{97}{\log^4 x} + \frac{30}{\log^5 x} + \frac{8}{\log^6 x}.$$
-/)
  (proof := /-- We have
$$\frac{ex}{\log x} \pi \Big(\frac{x}{e} \Big) > \frac{x^2}{\log x} \Big( \sum_{k=0}^{4} \frac{k!}{(\log x - 1)^{k+1}}\Big) + \frac{m_a x}{(\log x-1)^{6}}$$
Substituting
\begin{eqnarray*}
\frac{1}{(\log x - 1)^{k+1}} & = & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x} + \frac{1}{\log^2 x} + \frac{1}{\log^3 x} + \cdots \Big)^{k+1} \\ \\
& > & \frac{1}{\log^{k+1} x} \Big(1+ \frac{1}{\log x}+ \cdots + \frac{1}{\log^{5-k} x} \Big)^{k+1}
\end{eqnarray*}
we obtain the claim.
  -/)
  (latexEnv := "sublemma")]
theorem ex_pi_gt (m_a x_a : ℝ) (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x) :
    ∀ x > exp 1 * x_a, exp 1 * x / log x * pi (x / exp 1) > x ^ 2 * (∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) + ε' m_a x / log x ^ 7) := by
    sorry

@[blueprint
  "ramanujan-criterion"
  (title := "Criterion for Ramanujan's inequality")
  (statement := /-- \cite[Lemma 2.1]{dudek-platt}
Let $m_a, M_a \in \mathbb{R}$  and suppose that for $x>x_a$ we have

$$ x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+ \frac{m_a x}{\log^6 x} < \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$
%
Then Ramanujan's inequality is true if

$$x > \max( e x_{a},x_{a}' )$$
where $x'_a := \exp( \epsilon_{M_a} (x_{a}) - \epsilon'_{m_a} (x_{a}) )$.
 -/)
  (proof := /-- Combine the previous two sublemmas.
 -/)
  (latexEnv := "proposition")]
theorem criterion (m_a M_a x_a : ℝ)
  (hlower : ∀ x > x_a, x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (m_a * x / log x ^ 6) < pi x)
  (hupper : ∀ x > x_a, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (M_a * x / log x ^ 6)) :
    ∀ x > max (exp 1 * x_a) (x' m_a M_a x_a), pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
  sorry

@[blueprint
  "pi-error-identity"
  (title := "Integral identity for pi - li")
  (statement := /-- If $x \geq 2$, then
$$\pi(x) - \textrm{li}(x) = \frac{\theta(x) - x}{\log x} + \frac{2}{\log 2} + \int_{2}^{x} \frac{\theta(t) -t}{t \log^{2}t}\, dt.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-417} and the fundamental theorem of calculus. -/)
  (latexEnv := "lemma")]
theorem pi_error_identity (x : ℝ) (hx : 2 ≤ x) :
    pi x - li x = (θ x - x) / log x + 2 / log 2 + ∫ t in Set.Icc 2 x, (θ t - t) / (t * log t ^ 2) := by
    sorry

@[blueprint
  "ramanujan-pi-upper"
  (title := "Upper bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\leq \frac{x}{\log x} +a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}+\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")]
theorem pi_upper (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x) :
    pi x ≤ x / log x + a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 + ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    sorry

@[blueprint
  "log-7-int-bound"
  (title := "Bound for integral of an inverse power of log")
  (statement := /-- For $x \geq 2$ we have
$$\int_2^x \frac{dt}{\log^7 t} < \frac{x}{\log^7 x} + 7 \Big( \frac{\sqrt{x}}{\log^8 2} + \frac{2^8 x}{\log^8 x} \Big).$$-/)
  (proof := /-- This follows from the trivial bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 \sqrt{x}}$ and the bound $\int_2^x \frac{dt}{\log^7 t} < \int_2^x \frac{dt}{\log^7 x}$. -/)
  (latexEnv := "lemma")]
theorem log_7_int_bound (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Icc 2 x, 1 / log t ^ 7 < x / log x ^ 7 + 7 * (sqrt x / log 2 ^ 8 + 2 ^ 8 * x / log x ^ 8) := by
    sorry

@[blueprint
  "ramanujan-pi-lower"
  (title := "Lower bound for pi")
  (statement := /-- Suppose that for $x \geq 2$ we have $|\theta(x)-x|\log^{5} x\leq x a(x)$. Then
$$
\pi(x)\geq \frac{x}{\log x} -a(x)\frac{x}{\log^6 x}+\int_2^x\frac{d t}{\log^2 t}-\int_2^x\frac{a(t)}{\log^7 t}\ dt.
$$ (cf. \cite[\S 5]{PT2021})
-/)
  (proof := /-- Follows from Lemma \ref{pi-error-identity} and the triangle inequality. -/)
  (latexEnv := "sublemma")]
theorem pi_lower (a : ℝ → ℝ) (htheta : ∀ x ≥ 2, abs (θ x - x) * log x ^ 5 ≤ x * a x) (x : ℝ) (hx : 2 ≤ x)  :
    pi x ≥ x / log x - a x * x / log x ^ 6 + ∫ t in Set.Icc 2 x, 1 / log t ^ 2 - ∫ t in Set.Icc 2 x, a t / log t ^ 7 := by
    sorry

@[blueprint
  "ramanujan-pibound-1"
  (title := "Error estimate for pi, range 1")
  (statement := /-- For $2 < x \leq 599$ we have
$$E_\pi(x) \leq \frac{2 - \log 2}{2}.$$-/)
  (proof := /-- Trivial. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_1 (x : ℝ) (hx : x ∈ Set.Ico 2 599) :
    Eπ x ≤ (2 - log 2) / 2 := by
    sorry

@[blueprint
  "ramanujan-pibound-2"
  (title := "Error estimate for pi, range 2")
  (statement := /-- For $599 < x \leq \exp(58)$ we have
$$E_\pi(x) \leq \frac{\log^2 x}{8\pi\sqrt{x}}.$$-/)
  (proof := /-- This is \cite[Lemma 6]{PT2021}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_2 (x : ℝ) (hx : x ∈ Set.Ico 599 (exp 58)) :
    Eπ x ≤ log x ^ 2 / (8 * π * sqrt x) := by
    sorry

@[blueprint
  "ramanujan-pibound-3"
  (title := "Error estimate for pi, range 3")
  (statement := /-- For $\exp(58) < x < \exp(1169)$ we have
$$E_\pi(x) \leq \sqrt\frac{8}{17\pi}\left(\frac{\log x}{6.455}\right)^{\frac{1}{4}}\exp\left(-\sqrt{\frac{\log x}{6.455}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_3 (x : ℝ) (hx : x ∈ Set.Ico (exp 58) (exp 1169)) :
    Eπ x ≤ sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455)) := by
    sorry

@[blueprint
  "ramanujan-pibound-4"
  (title := "Error estimate for pi, range 4")
  (statement := /-- For $\exp(1169) \leq x < \exp(2000)$ we have
$$E_\pi(x) \leq 462.0\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_4 (x : ℝ) (hx : x ∈ Set.Ico (exp 1169) (exp 2000)) :
    Eπ x ≤ 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    sorry

@[blueprint
  "ramanujan-pibound-5"
  (title := "Error estimate for pi, range 5")
  (statement := /-- For $\exp(2000) \leq x < \exp(3000)$ we have
$$E_\pi(x) \leq 411.5\left(\frac{\log x}{5.573412}\right)^{1.52}\exp\left(-1.89\sqrt{\frac{\log x}{5.573412}}\right).$$-/)
  (proof := /-- This follows from Corollary \ref{pt_cor_1}. -/)
  (latexEnv := "sublemma")]
theorem pi_bound_5 (x : ℝ) (hx : x ∈ Set.Ico (exp 2000) (exp 3000)) :
    Eπ x ≤ 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)) := by
    sorry

noncomputable def a (x : ℝ) : ℝ := (log x)^5 * (
  if x ∈ Set.Ico 2 599 then (2 - log 2) / 2
  else if x ∈ Set.Ico 599 (exp 58) then log x ^ 2 / (8 * π * sqrt x)
  else if x ∈ Set.Ico (exp 58) (exp 1169) then sqrt (8 / (17 * π)) * (log x / 6.455) ^ (1 / 4) * exp (-sqrt (log x / 6.455))
  else if x ∈ Set.Ico (exp 1169) (exp 2000) then 462.0 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else if x ∈ Set.Ico (exp 2000) (exp 3000) then 411.5 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412))
  else 379.7 * (log x / 5.573412) ^ (1.52 : ℝ) * exp (-1.89 * sqrt (log x / 5.573412)))

@[blueprint
  "pt_eq_18"
  (title := "Equation (18) of Platt-Trudgian")
  (statement := /-- For $x \geq 2$ we have
$$E_\pi(x) \leq a(x).$$-/)
  (proof := /-- This follows from the previous five sublemmas. -/)
  (latexEnv := "proposition")]
theorem pi_bound (x : ℝ) (hx : 2 ≤ x) :
    Eπ x ≤ a x := by
    sorry

noncomputable def xₐ : ℝ := exp 3914

@[blueprint
  "a-mono"
  (title := "Monotonicity of a(x)")
  (statement := /-- The function $a(x)$ is nonincreasing for $x \geq x_a$. -/)
  (proof := /-- This is a direct calculation. -/)
  (latexEnv := "lemma")]
theorem a_mono : AntitoneOn a (Set.Ici xₐ) := by
    sorry

noncomputable def C₁ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 + a t) / log t ^ 7

noncomputable def C₂ : ℝ := log xₐ ^ 6 / xₐ * ∫ t in Set.Icc 2 xₐ, (720 - a t) / log t ^ 7

noncomputable def C₃ : ℝ := 2 * log xₐ ^ 6 / xₐ * ∑ k ∈ Finset.Icc 1 5, k.factorial / log 2 ^ (k + 1)

noncomputable def Mₐ : ℝ := 120 + a xₐ + C₁ + (720 + a xₐ) * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def mₐ : ℝ := 120 - a xₐ - (C₂ + C₃) - a xₐ * (1 / log xₐ + 7 * 2 ^ 8 / log xₐ ^ 2 + 7 * log xₐ ^ 6 / (sqrt xₐ * log 2 ^ 8))

noncomputable def εMₐ : ℝ := 72 + 2 * Mₐ + (2 * Mₐ + 132) / log xₐ + (4 * Mₐ + 288) / log xₐ ^ 2 + (12 * Mₐ + 576) / log xₐ ^ 3 + (48 * Mₐ) / log xₐ ^ 4 + (Mₐ ^ 2) / log xₐ ^ 5

noncomputable def εmₐ : ℝ := 206 + mₐ + 364 / log xₐ + 381 / log xₐ ^ 2 + 238 / log xₐ ^ 3 + 97 / log xₐ ^ 4 + 30 / log xₐ ^ 5 + 8 / log xₐ ^ 6

@[blueprint
  "pi-upper-specific"
  (title := "Specific upper bound on pi")
  (statement := /-- For $x \geq x_a$, $$ \pi(x) < x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}+\frac{M_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")]
theorem pi_upper_specific : ∀ x > xₐ, pi x < x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) + (Mₐ * x / log x ^ 6) := by
    sorry

@[blueprint
  "pi-lower-specific"
  (title := "Specific lower bound on pi")
  (statement := /-- For $x \geq x_a$, $$ \pi(x) > x \sum_{k=0}^{4} \frac{k!}{\log^{k+1}x}-\frac{m_a x}{\log^6 x}.$$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including Lemma \ref{log-7-int-bound}. -/)
  (latexEnv := "lemma")]
theorem pi_lower_specific : ∀ x > xₐ, pi x > x * ∑ k ∈ Finset.range 5, (k.factorial / log x ^ (k + 1)) - (mₐ * x / log x ^ 6) := by
    sorry

@[blueprint
  "epsilon-bound"
  (title := "Bound for εMₐ - εmₐ")
  (statement := /-- We have $\epsilon_{M_a} - \epsilon'_{m_a} < 0$. -/)
  (proof := /-- This is a direct calculation. -/)
  (latexEnv := "lemma")]
theorem epsilon_bound : εMₐ - εmₐ < 0 := by
    sorry

@[blueprint
  "ramanujan-final"
  (title := "Ramanujan's inequality")
  (statement := /-- For $x \geq e x_a$ we have $\pi(x)^2 < \frac{e x}{\log x} \pi\Big(\frac{x}{e}\Big)$. -/)
  (proof := /-- This follows from the previous lemmas and calculations, including the criterion for Ramanujan's inequality. -/)
  (latexEnv := "theorem")]
theorem ramanujan_final : ∀ x > exp 1 * xₐ, pi x ^ 2 < exp 1 * x / log x * pi (x / exp 1) := by
    sorry



end Ramanujan
