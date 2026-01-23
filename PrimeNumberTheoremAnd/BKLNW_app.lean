import PrimeNumberTheoremAnd.ZetaSummary
import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky

blueprint_comment /--
\section{Appendix A of BKLNW}
In this file we record the results from Appendix A of \cite{BKLNW}.
-/

namespace BKLNW_app

open Real

structure Inputs where
  H : ℝ
  hH : riemannZeta.RH_up_to H
  R : ℝ
  hR : riemannZeta.classicalZeroFree R
  ZDB : zero_density_bound


noncomputable def Inputs.default : Inputs := {
  H := 2445999556030
  hH := GW_theorem
  R := 5.5666305  -- a slightly more conservative value of 5.573412 was used in the paper
  hR := MT_theorem_1
  ZDB := FKS.corollary_2_9_merged -- stronger than the Kadiri-Lumley-Ng input used here
}

@[blueprint
  "bklnw-eq_A_7"
  (title := "Equation (A.7)")
  (statement := /-- Let $x \geq e^{1000}$ and $T$ satisfies $50 < T \leq x$. Then
  $$ \frac{\psi(x) - x}{x} = \sum_{|\gamma| < T} \frac{x^{\rho - 1}}{\rho} + \mathcal{O}^*\left(\frac{2(\log x)^2}{T}\right) $$ where $A = \mathcal{O}^*(B)$ means $|A| \leq B$. -/)
  (proof := /-- See Dudek, Theorem 1.3 (TODO: incorporate reference) -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_7 (x T : ℝ) (hx : x ≥ exp 1000) (hT1 : 50 < T) (hT2 : T ≤ x) : ∃ E, ((ψ x - x) / x = riemannZeta.zeroes_sum (Set.Icc 0 1) (Set.Ioo (-T) T) (fun ρ ↦ x^(ρ-1) / ρ) + E ∧ ‖E‖ ≤ 2 * (log x)^2 / T) := by sorry

@[blueprint
  "bklnw-eq_A_8"
  (title := "Equation (A.8)")
  (statement := /-- We denote
  $$ s_0(b, T) = \frac{2b^2}{T}. $$ -/)]
noncomputable def bklnw_eq_A_8 (b T : ℝ) : ℝ := 2 * b^2 / T

@[blueprint
  "bklnw-sigma_1_def"
  (title := "Definition of Sigma 1")
  (statement := /-- We denote $$ \Sigma_1 := \sum_{|\gamma| \leq T; \beta < 1 - \delta} \frac{x^{\rho - 1}}{\rho} $$ -/)]
noncomputable def Sigma₁ (x T δ : ℝ) : ℂ := riemannZeta.zeroes_sum (Set.Ico 0 (1 - δ)) (Set.Ioo (-T) T) (fun ρ ↦ x^(ρ-1) / ρ)

@[blueprint
  "bklnw-sigma_2_def"
  (title := "Definition of Sigma 2")
  (statement := /-- We denote $$ \Sigma_2 := \sum_{|\gamma| \leq T; \beta \geq 1 - \delta} \frac{x^{\rho - 1}}{\rho} $$ -/)]
noncomputable def Sigma₂ (x T δ : ℝ) : ℂ := riemannZeta.zeroes_sum (Set.Ioc (1 - δ) 1) (Set.Ioo (-T) T) (fun ρ ↦ x^(ρ-1) / ρ)

@[blueprint
  "bklnw-eq_A_9"
  (title := "Equation (A.9)")
  (statement := /-- We have
  $$ \sum_{|\gamma| < T} \frac{x^{\rho-1}}{\rho} = \Sigma_1 + \Sigma_2 $$ -/)
  (proof := /-- Follows directly from the definitions of Σ₁ and Σ₂. -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_9 (x T δ : ℝ) : riemannZeta.zeroes_sum (Set.Icc 0 1) (Set.Ioo (-T) T) (fun ρ ↦ x^(ρ-1) / ρ) = Sigma₁ x T δ + Sigma₂ x T δ := by sorry

@[blueprint
  "bklnw-eq_A_10"
  (title := "Equation (A.10)")
  (statement := /-- We have
  $$ |\Sigma_1| \leq x^{-\delta} \left(\frac{1}{2\pi}(\log(T/2\pi))^2 + 1.8642\right). $$ -/)
  (proof := /-- See Demichel, Lemma 2.10 (TODO: incorporate reference) -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_10 (x T δ : ℝ) (hδ : 0.001 ≤ δ) : ‖Sigma₁ x T δ‖ ≤ exp (-δ * log x) * (1 / (2 * π) * (log (T / (2 * π)))^2 + 1.8642) := by sorry

@[blueprint
  "bklnw-eq_A_11"
  (title := "Equation (A.11)")
  (statement := /-- We denote
  $$ s_1(b, \delta, T) = e^{-\delta b} \left(\frac{1}{2\pi}(\log(T/2\pi))^2 + 1.8642\right). $$ -/)]
noncomputable def s₁ (b δ T : ℝ) : ℝ := exp (-δ * b) * (1 / (2 * π) * (log (T / (2 * π)))^2 + 1.8642)

@[blueprint
  "bklnw-eq_A_12"
  (title := "Equation (A.12)")
  (statement := /-- We have
  $$ |\Sigma_2| \leq 2 \sum_{k=0}^{K-1} \frac{\lambda^{k+1} x^{-\frac{1}{R \log(T/\lambda^k)}}}{T} N\left(1 - \delta, \frac{T}{\lambda^k}\right). $$ -/)
  (proof := /-- An argument of Pintz (TODO: incorporate reference) is employed.  The interval $[0,T]$ is split into subintervals $[T/\lambda^{k+1}, T/\lambda^k]$ where $\lambda > 1$, $0 \leq k \leq K-1$, and $K = \lfloor \frac{\log T/H}{\log \lambda} \rfloor + 1$.  Then use the zero-free region to bound $\Re \rho$. -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_12 (I : Inputs) (x T δ lambda : ℝ) (hlambda: 1 < lambda):
  let K := ⌊ log (T / I.H) / log lambda ⌋₊ + 1
  ‖Sigma₂ x T δ‖ ≤ 2 * ∑ k ∈ Finset.range K, (lambda^(k+1) * x^(- (1 / I.R * log (T / lambda^k))) / T) * I.ZDB.N (1 - δ) (T / lambda^k) := by sorry

@[blueprint
  "bklnw-eq_A_13"
  (title := "Equation (A.13)")
  (statement := /-- We have
  $$ |\Sigma_2| \leq \frac{2\lambda}{T} \sum_{k=0}^{K-1} \lambda^k x^{-\frac{1}{R \log(T/\lambda^k)}} \left(c_1 \left(\frac{T}{\lambda^k}\right)^{\frac{8\delta}{3}} (\log(T/\lambda^k))^{3+2\delta} + c_2 (\log(T/\lambda^k))^2\right). $$ -/)
  (proof := /-- Inserting (A.6) into the result of (A.12). -/)
  (latexEnv := "sublemma")]
theorem bklnw_eq_A_13 (I : Inputs) (x T δ lambda : ℝ) (hlambda : 1 < lambda):
  let K := ⌊ log (T / I.H) / log lambda ⌋₊ + 1
  ‖Sigma₂ x T δ‖ ≤ (2 * lambda / T) *
    ∑ k ∈ Finset.range K,
      exp (k * log lambda - (log x) / (I.R * (log T - k * log lambda))) *
      ((I.ZDB.c₁ (1-δ)) * (T / lambda^k)^(8 * δ / 3) * (log (T / lambda^k))^(3 + 2 * δ) + (I.ZDB.c₂ (1-δ)) * (log (T / lambda^k))^2) := by sorry

@[blueprint
  "bklnw-eq_A_14"
  (title := "Equation (A.14)")
  (statement := /-- We denote
  \begin{align}
  s_2(b, \lambda, K, T) &= \frac{2\lambda}{T} \sum_{k=0}^{K-1} \exp\left(k \log \lambda - \frac{b}{R(\log T - k \log \lambda)}\right) \\
  &\quad \times \left(c_1 \left(\frac{T}{\lambda^k}\right)^{\frac{8\delta}{3}} (\log(T/\lambda^k))^{3+2\delta} + c_2 (\log(T/\lambda^k))^2\right). \notag
  \end{align} -/)]
noncomputable def Inputs.s₂ (I : Inputs) (δ b : ℝ) (K : ℕ) (lambda T : ℝ) : ℝ :=
  (2 * lambda / T) *
    ∑ k ∈ Finset.range K,
      exp (k * log lambda - b / (I.R * (log T - k * log lambda))) *
      ((I.ZDB.c₁ (1-δ)) * (T / lambda^k)^(8 * δ / 3) * (log (T / lambda^k))^(3 + 2 * δ) + (I.ZDB.c₂ (1-δ)) * (log (T / lambda^k))^2)

@[blueprint
  "bklnw-thm-13"
  (title := "Theorem 13")
  (statement := /-- Let $b_1, b_2$ satisfy $1000 \leq b_1 < b_2$. Let $0.001 \leq \delta \leq 0.025$, $\lambda > 1$, $H < T < e^{b_1}$, and $K = \left\lfloor \frac{\log \frac{T}{H}}{\log \lambda} \right\rfloor + 1$. Then for all $x \in [e^{b_1}, e^{b_2}]$
  $$ \left|\frac{\psi(x) - x}{x}\right| \leq s_0(b_2, T) + s_1(b_1, \delta, T) + s_2(b_1, \delta, \lambda, K, T), $$ where $s_0, s_1, s_2$ are respectively defined in Definitions \ref{bklnw-eq_A_8}, \ref{bklnw-eq_A_11}, and \ref{bklnw-eq_A_14} -/)
  (proof := /-- Follows from combining Sublemmas \ref{bklnw_eq_A_7}, \ref{bklnw_eq_A_9}, \ref{bklnw_eq_A_10}, and \ref{bklnw_eq_A_13}. -/)
  (latexEnv := "theorem")]
theorem bklnw_thm_15 (I : Inputs) (b₁ b₂ δ lambda T x : ℝ) (hb : 1000 ≤ b₁) (hb' : b₁ < b₂)
  (hδ : 0.001 ≤ δ) (hlambda : 1 < lambda) (hT1 : I.H < T) (hT2 : T < exp b₁) (hx : x ∈ Set.Icc (exp b₁) (exp b₂)) :
  let K := ⌊ log (T / I.H) / log lambda ⌋₊ + 1
  ‖(ψ x - x) / x‖ ≤ bklnw_eq_A_8 b₂ T + s₁ b₁ δ T + I.s₂ δ b₁ K lambda T := by sorry


@[blueprint
  "bklnw-eq_A_16"
  (title := "Equation (A.16)")
  (statement := /-- We define
  $$ k(\sigma, x_0) = \left( \exp\left(\frac{10 - 16 \sigma}{3} \left( \frac{\log x_0}{R} \right)^{1/2} \right) \left( \frac{\log x_0}{R} \right)^{5 - 2 \sigma} \right)^{-1}. $$
  -/)]
noncomputable def Inputs.k (I : Inputs) (σ x₀ : ℝ) : ℝ := (exp ((10 - 16 * σ) / 3 * (log x₀ / I.R)^(1/2)) * (log x₀ / I.R)^(5 - 2 * σ))^(-1:ℝ)

@[blueprint
  "bklnw-eq_A_17"
  (title := "Equation (A.17)")
  (statement := /-- We define
  $$ c_3(\sigma, x_0) = 2 \exp\left( -2 \left( \frac{\log x_0}{R} \right)^{1/2} \right) (\log x_0)^2 k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c3 (I : Inputs) (σ x₀ : ℝ) : ℝ :=
  2 * exp (-2 * (log x₀ / I.R)^(1/2)) * (log x₀)^2 * I.k σ x₀

@[blueprint
  "bklnw-eq_A_18"
  (title := "Equation (A.18)")
  (statement := /-- We define
  $$ c_4(\sigma, x_0) = x_0^{\sigma - 1} \left( \frac{2 \log x_0}{\pi R} + 1.8642 \right) k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c4 (I : Inputs) (σ x₀ : ℝ) : ℝ :=
  x₀^(σ - 1:ℝ) * (2 * log x₀ / π / I.R + 1.8642) * I.k σ x₀

@[blueprint
  "bklnw-eq_A_19"
  (title := "Equation (A.19)")
  (statement := /-- We define
  $$ c_5(\sigma, x_0) = 8.01 \cdot c_2(\sigma) \exp\left( -2 \left( \frac{\log x_0}{R} \right)^{1/2} \right) \frac{\log x_0}{R} k(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.c5 (I : Inputs) (σ x₀ : ℝ) : ℝ :=
  8.01 * I.ZDB.c₂ σ * exp (-2 * (log x₀ / I.R)^(1/2)) * (log x₀ / I.R) * I.k σ x₀

@[blueprint
  "bklnw-eq_A_20"
  (title := "Equation (A.20)")
  (statement := /-- We define
  $$ A(\sigma, x_0) = 2.0025 \cdot 25^{-2 \sigma} \cdot c_1(\sigma) + c_3(\sigma, x_0) + c_4(\sigma, x_0) + c_5(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.A (I : Inputs) (σ x₀ : ℝ) : ℝ :=
  2.0025 * 25^(-2 * σ) * I.ZDB.c₁ σ + I.c3 σ x₀ + I.c4 σ x₀ + I.c5 σ x₀

@[blueprint
  "bklnw-eq_A_21"
  (title := "Equation (A.21)")
  (statement := /-- We define
  $$ B = 5/2 - \sigma, $$
  and
  $$ C = 16 \sigma/3 - \frac{10}{3}. $$
  -/)]
noncomputable def Inputs.B (_ : Inputs) (σ : ℝ) : ℝ := 5/2 - σ

@[blueprint
  "bklnw-eq_A_21"]
noncomputable def Inputs.C (_ : Inputs) (σ : ℝ) : ℝ := 16 * σ / 3 - 10 / 3

@[blueprint
  "bklnw-thm-14"
  (title := "Theorem 14")
  (statement := /-- Let $x_0 \geq 1000$ and let $\sigma \in [0.75, 1)$. For all $x \geq e^{x_0}$,
  $$ \frac{|\psi(x) - x|}{x} \leq A \left( \frac{\log x}{R} \right)^B \exp\left( -C \left( \frac{\log x}{R} \right)^{1/2} \right) $$
  where $A$, $B$, and $C$ are defined in Definitions \ref{bklnw-eq_A_20}, \ref{bklnw-eq_A_21}. -/)
  (proof := /-- This is proven by Platt and Trudgian (TODO: give citation). -/)]
theorem thm_14 (I : Inputs) {x₀ σ x : ℝ} (hx₀ : x₀ ≥ 1000) (hσ : 0.75 ≤ σ ∧ σ < 1) (hx : x ≥ exp x₀) :
  Eψ x ≤ I.A σ x₀ * (log x / I.R)^(I.B σ) * exp (-I.C σ * (log x / I.R)^(1/2:ℝ)) := by sorry

@[blueprint
 "bklnw-eq_A_26"
  (title := "Equation (A.26)")
  (statement := /-- For $100 \leq x \leq 10^{19}$, one has
  $$ | (x - \psi(x)) / \sqrt{x} | \leq 0.94. $$ -/)
  (proof := /-- This follows from Theorem \ref{buthe-theorem-2a}. TODO: create a primary Buthe section to place this result -/)]
theorem bklnw_eq_A_26 (x : ℝ) (hx1 : 100 ≤ x) (hx2 : x ≤ 1e19) :
  Eψ x ≤ 0.94 / sqrt x := by sorry


@[blueprint
  "bklnw-lemma_15"
  (title := "Lemma 15")
  (statement := /-- Let $B_0$, $B$, and $c$ be positive constants such that
  $$ |(x-\psi(x))/\sqrt{x}| ≤ c \hbox{ for all } B_0 < x \leq B$$
  is known.  Furthermore, assume for every $b_0 > 0$ there exists $\varepsilon(b_0) > 0$ such that
\begin{equation}\tag{A.28}
|\psi(x) - x| \leq \varepsilon(b_0) x \quad \text{for all } x \geq e^{b_0}.
\end{equation}
Let $b$ be positive such that $e^b \in (B_0, B]$. Then, for all $x \geq e^b$ we have
\begin{equation}\tag{A.29}
\left|\frac{\psi(x) - x}{x}\right| \leq \max (\frac{c}{e^{\frac{b}{2}}}, \varepsilon(\log B)).\end{equation} -/)
  (proof := /-- Multiplying both sides of (A.27) by $\frac{1}{\sqrt{x}}$ gives
\[
\left|\frac{\psi(x) - x}{x}\right| \leq \frac{c}{e^{\frac{b}{2}}} \quad \text{for all } e^b \leq x \leq B
\]
as $\frac{1}{\sqrt{x}} \leq \frac{1}{e^{\frac{b}{2}}}$. Then, for $x \geq B$ we apply (A.28) with $b_0 = \log B$. Combining these bounds, we derive (A.29). -/)
  (latexEnv := "lemma")]
theorem bklnw_lemma_15 (c B₀ B : ℝ)
  (hbound : ∀ x ∈ Set.Ioc B₀ B, Eψ x ≤ c / sqrt x)
  (ε : ℝ → ℝ)
  (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀, Eψ x ≤ ε b₀)
  (b : ℝ)
  (hb : exp b ∈ Set.Ioc B₀ B) :
  ∀ x ≥ exp b, Eψ x ≤ max (c / exp (b / 2)) (ε (log B)) := by sorry

@[blueprint
 "bklnw-cor_15_1"
  (title := "Corollary 15.1")
  (statement := /-- Let $b$ be a positive constant such that $\log 11 < b \leq 19 \log(10)$. Then we have
  $$ \left|\frac{\psi(x) - x}{x}\right| \leq \max\left\{\frac{0.94}{e^{\frac{b}{2}}}, \varepsilon(19 \log 10)\right\} \quad \text{for all } x \geq e^b. $$
  Note that by Table 8, we have $\varepsilon(19 \log 10) = 1.93378 \cdot 10^{-8}$. -/)
  (proof := /-- By (1.5) of Buthe2 (TODO: provide reference), (A.27) holds with $B_0 = 11$, $B = 10^{19}$, and $c = 0.94$. Thus we may apply Lemma \ref{bklnw-lemma_15} with $B_0 = 11$, $B = 10^{19}$, and $c = 0.94$ from (1.5) of Buthe2 to obtain the claim. -/)
  (latexEnv := "corollary")]
theorem bklnw_cor_15_1 (b : ℝ) (hb1 : log 11 < b) (hb2 : b ≤ 19 * log 10)
  (ε : ℝ → ℝ)
  (hε : ∀ b₀ > 0, ∀ x ≥ exp b₀, Eψ x ≤ ε b₀) :
  ∀ x ≥ exp b, Eψ x ≤ max (0.94 / exp (b / 2)) (ε (19 * log 10)) := by sorry

@[blueprint
  "logan-function"
  (title := "Logan's function")
  (statement := /-- We define Logan's function
  $$ \ell_{c,\varepsilon}(\xi) = \frac{c}{\sinh c} \frac{\sin(\sqrt{(\xi\varepsilon)^2 - c^2})}{\sqrt{(\xi\varepsilon)^2 - c^2}}. $$ -/)
  (latexEnv := "definition")]
noncomputable def ℓ (c ε ξ : ℝ) : ℝ := (c / sinh c) * (sin (sqrt ((ξ * ε)^2 - c^2))) / (sqrt ((ξ * ε)^2 - c^2))

def ν (c α : ℝ) : ℝ := sorry

def μ (c α : ℝ) : ℝ := sorry

@[blueprint
  "bklnw-thm_16"
  (title := "Theorem 16")
  (statement := /-- Let $0 < \varepsilon < 10^{-3}$, $c \geq 3$, $x_0 \geq 100$ and $\alpha \in [0, 1)$ such that the inequality
  $$ B_0 := \frac{\varepsilon e^{-\varepsilon} x_0 |\nu_c(\alpha)|}{2(\mu_c)_+(\alpha)} > 1 $$
  holds. We denote the zeros of the Riemann zeta function by $\rho = \beta + i\gamma$ with $\beta, \gamma \in \mathbb{R}$. Then, if $\beta = \frac{1}{2}$ holds for $0 < \gamma \leq \frac{c}{\varepsilon}$, the inequality
  $$ |\psi(x) - x| \leq x e^{\varepsilon\alpha}(\mathcal{E}_1 + \mathcal{E}_2 + \mathcal{E}_3) $$
  holds for all $x \geq e^{\varepsilon\alpha} x_0$, where
  \begin{align*}
  \mathcal{E}_1 &= e^{2\varepsilon} \log(e^\varepsilon x_0) \left[\frac{2\varepsilon|\nu_c(\alpha)|}{\log B_0} + \frac{2.01\varepsilon}{\sqrt{x_0}} + \frac{\log\log(2x_0^2)}{2x_0}\right] + e^{\varepsilon\alpha} - 1, \\
  \mathcal{E}_2 &= 0.16 \frac{1 + x_0^{-1}}{\sinh c} e^{0.71\sqrt{c\varepsilon}} \log\left(\frac{c}{\varepsilon}\right), \quad \text{and} \\
  \mathcal{E}_3 &= \frac{2}{\sqrt{x_0}} \sum_{0 < \gamma < \frac{c}{\varepsilon}} \frac{\ell_{c,\varepsilon}(\gamma)}{\gamma} + \frac{2}{x_0}.
  \end{align*}
  The $\nu_c(\alpha) = \nu_{c,1}(\alpha)$ and $\mu_c(\alpha) = \mu_{c,1}(\alpha)$ where $\nu_{c,\varepsilon}(\alpha)$ and $\mu_{c,\varepsilon}(\alpha)$ are defined by \cite[p.~2490]Buthe2 (TODO: provide reference). -/)
  (proof := /-- This is Theorem 1 of Buthe2. -/)
  (latexEnv := "theorem")]
theorem bklnw_thm_16 (ε c x₀ α : ℝ)
  (hε : 0 < ε ∧ ε < 1e-3)
  (hc : 3 ≤ c)
  (hx₀ : 100 ≤ x₀)
  (hα : 0 ≤ α ∧ α < 1)
  (hB0 : (ε * exp (-ε) * x₀ * |ν c α|) / (2 * (μ c α)) > 1)
  (hRH : riemannZeta.RH_up_to (c / ε))
  (x : ℝ)
  (hx : x ≥ exp (ε * α) * x₀) :
  let E₁ := exp (2 * ε) * log (exp ε * x₀) *
        (2 * ε * |ν c α| / log ((ε * exp (-ε) * x₀ * |ν c α|) / (2 * (μ c α))) +
         2.01 * ε / sqrt x₀ +
         log (log (2 * x₀^2) / (2 * x₀))) + exp (ε * α) - 1
  let E₂ := 0.16 * (1 + x₀^(-1:ℝ)) / sinh c * exp (0.71 * sqrt (c * ε)) * log (c / ε)
  let E₃ := 2 / sqrt x₀ * riemannZeta.zeroes_sum (Set.Icc 0 1) (Set.Ioo 0 (c / ε)) (fun ρ ↦ (ℓ c ε ρ.im) / ρ.im) + 2 / x₀
  Eψ x ≤ exp (ε * α) * (E₁ + E₂ + E₃) :=
    by sorry

noncomputable def table_8_ε (b : ℝ) : ℝ :=
  if b < 20 then 1   -- junk value
  else if b < 21 then 4.2670e-5
  else if b < 22 then 2.58843e-5
  else if b < 23 then 1.56996e-5
  else if b < 24 then 9.52229e-6
  else if b < 25 then 5.77556e-6
  else if b < 30 then 3.50306e-6
  else if b < 35 then 2.87549e-7
  else if b < 40 then 2.36034e-8
  else if b < 45 then 1.93378e-8
  else if b < 50 then 1.09073e-8
  else if b < 100 then 1.11990e-9
  else if b < 200 then 2.45299e-12
  else if b < 300 then 2.18154e-12
  else if b < 400 then 2.09022e-12
  else if b < 500 then 2.03981e-12
  else if b < 600 then 1.99986e-12
  else if b < 700 then 1.98894e-12
  else if b < 800 then 1.97643e-12
  else if b < 900 then 1.96710e-12
  else if b < 1000 then 1.95987e-12
  else if b < 1500 then 1.94751e-12
  else if b < 2000 then 1.93677e-12
  else if b < 2500 then 1.92279e-12
  else if b < 3000 then 9.06304e-13
  else if b < 3500 then 4.59972e-14
  else if b < 4000 then 2.48641e-15
  else if b < 4500 then 1.42633e-16
  else if b < 5000 then 8.68295e-18
  else if b < 5500 then 5.63030e-19
  else if b < 6000 then 3.91348e-20
  else if b < 6500 then 2.94288e-21
  else if b < 7000 then 2.38493e-22
  else if b < 7500 then 2.07655e-23
  else if b < 8000 then 1.96150e-24
  else if b < 8500 then 1.97611e-25
  else if b < 9000 then 2.12970e-26
  else if b < 9500 then 2.44532e-27
  else if b < 10000 then 2.97001e-28
  else if b < 10500 then 3.78493e-29
  else if b < 11000 then 5.10153e-30
  else if b < 11500 then 7.14264e-31
  else if b < 12000 then 1.04329e-31
  else if b < 12500 then 1.59755e-32
  else if b < 13000 then 2.53362e-33
  else if b < 13500 then 4.13554e-34
  else if b < 14000 then 7.21538e-35
  else if b < 15000 then 1.22655e-35
  else if b < 16000 then 4.10696e-37
  else if b < 17000 then 1.51402e-38
  else if b < 18000 then 6.20397e-40
  else if b < 19000 then 2.82833e-41
  else if b < 20000 then 1.36785e-42
  else if b < 21000 then 7.16209e-44
  else if b < 22000 then 4.11842e-45
  else if b < 23000 then 2.43916e-46
  else if b < 24000 then 1.56474e-47
  else if b < 25000 then 1.07022e-48
  else 7.57240e-50

@[blueprint
  "bknlw-theorem-2"
  (title := "Theorem 2")
  (statement := /-- If $b>0$ then $|\psi(x) - x| \leq \varepsilon(b) x$ for all $x \geq \exp(b)$, where $\varepsilon$ is as in \cite[Table 8]{BKLNW}. -/)
  (latexEnv := "theorem")
  (proof := /-- Values for $20 \leq b \leq 2000$ are computed using Theorem \ref{bklnw-thm-16}, and values for $2500 \leq b \leq 25000$ are computed as using Theorem \ref{bklnw-thm-13}.  For $b > 25000$ we use Theorem \ref{bklnw-thm-14}. -/)]
theorem theorem_2 : ∀ b ≥ 0, ∀ x ≥ exp b,
    |ψ x - x| ≤ table_8_ε b * x := by sorry

@[blueprint
 "bklnw-cor_15_1_alt"
  (title := "Corollary 15.1, alternative version")
  (statement := /-- Let $b$ be a positive constant such that $\log 11 < b \leq 19 \log(10)$. Then we have
  $$ \left|\frac{\psi(x) - x}{x}\right| \leq \max\left\{\frac{0.94}{e^{\frac{b}{2}}}, 1.93378 \cdot 10^{-8}\right\} \quad \text{for all } x \geq e^b. $$
   -/)
  (proof := /-- From Table 8 we have $\varepsilon(19 \log 10) = 1.93378 \cdot 10^{-8}$.
  Now apply Corollary \ref{bklnw-cor_15_1} and Theorem \ref{bklnw-theorem-2}. -/)
  (latexEnv := "corollary")]
theorem bklnw_cor_15_1' (b : ℝ) (hb1 : log 11 < b) (hb2 : b ≤ 19 * log 10) :
  ∀ x ≥ exp b, Eψ x ≤ max (0.94 / exp (b / 2)) 1.93378e-8 := by sorry









end BKLNW_app
