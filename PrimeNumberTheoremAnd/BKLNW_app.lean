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

/-
\subsection{The Prime Number Theorem with a small constant error term}

In \cite[Theorem 1.3]{Dudek}, Platt and Trudgian use an explicit version of Perron's formula proven by Dudek: Let $x \geq e^{1000}$ and $T$ satisfies $50 < T \leq x$. Then
\begin{equation}\tag{A.7}
\frac{\psi(x) - x}{x} = \sum_{|\gamma| < T} \frac{x^{\rho - 1}}{\rho} + \mathcal{O}^*\left(\frac{2(\log x)^2}{T}\right)
\end{equation}
where $A = \mathcal{O}^*(B)$ means $|A| \leq B$. Writing $b = \log x$, we denote
\begin{equation}\tag{A.8}
s_0(b, T) = \frac{2b^2}{T}.
\end{equation}
The sum over the zeros is then split vertically at a fixed value $1 - \delta$ with $0.001 \leq \delta \leq 0.025$.
\begin{equation}\tag{A.9}
\sum_{|\gamma| < T} \frac{x^{\rho - 1}}{\rho} = \Sigma_1 + \Sigma_2, \quad \text{with } \Sigma_1 = \sum_{\substack{|\gamma| \leq T \\ \beta < 1 - \delta}} \frac{x^{\rho - 1}}{\rho}, \quad \Sigma_2 = \sum_{\substack{|\gamma| \leq T \\ \beta \geq 1 - \delta}} \frac{x^{\rho - 1}}{\rho}.
\end{equation}
The first sum $\Sigma_1$ is evaluated in \cite[Lemma 2.10]{Demichel} by
\begin{equation}\tag{A.10}
|\Sigma_1| \leq x^{-\delta} \left(\frac{1}{2\pi}(\log(T/2\pi))^2 + 1.8642\right).
\end{equation}
We denote
\begin{equation}\tag{A.11}
s_1(b, \delta, T) = e^{-\delta b} \left(\frac{1}{2\pi}(\log(T/2\pi))^2 + 1.8642\right).
\end{equation}
To estimate $\Sigma_2$, an argument of Pintz \cite{Pintz} is employed. The interval $[0, T]$ is split into subintervals $\left[\frac{T}{\lambda^{k+1}}, \frac{T}{\lambda^k}\right]$ where $\lambda > 1$, $0 \leq k \leq K - 1$, and $K = \left\lfloor \frac{\log \frac{T}{H}}{\log \lambda} \right\rfloor + 1$. Using the zero-free region (A.4) to bound $\mathrm{Re}(\rho)$ we find
\begin{equation}\tag{A.12}
|\Sigma_2| \leq 2 \sum_{k=0}^{K-1} \frac{\lambda^{k+1} x^{-\frac{1}{R \log(T/\lambda^k)}}}{T} N\left(1 - \delta, \frac{T}{\lambda^k}\right).
\end{equation}
Inserting (A.6) we obtain the following:
\begin{equation}\tag{A.13}
|\Sigma_2| \leq \frac{2\lambda}{T} \sum_{k=0}^{K-1} \lambda^k x^{-\frac{1}{R \log(T/\lambda^k)}} \left(c_1 \left(\frac{T}{\lambda^k}\right)^{\frac{8\delta}{3}} (\log(T/\lambda^k))^{3+2\delta} + c_2 (\log(T/\lambda^k))^2\right).
\end{equation}
We denote
\begin{align}\tag{A.14}
s_2(b, \lambda, K, T) &= \frac{2\lambda}{T} \sum_{k=0}^{K-1} \exp\left(k \log \lambda - \frac{b}{R(\log T - k \log \lambda)}\right) \\
&\quad \times \left(c_1 \left(\frac{T}{\lambda^k}\right)^{\frac{8\delta}{3}} (\log(T/\lambda^k))^{3+2\delta} + c_2 (\log(T/\lambda^k))^2\right). \notag
\end{align}
Finally, putting together (A.7), (A.9), (A.10), and (A.13) gives the following result.

\begin{theorem}
Let $b_1, b_2$ satisfy $1000 \leq b_1 < b_2$. Let $0.001 \leq \delta \leq 0.025$, $\lambda > 1$, $H < T < e^{b_1}$, and $K = \left\lfloor \frac{\log \frac{T}{H}}{\log \lambda} \right\rfloor + 1$. Then for all $x \in [e^{b_1}, e^{b_2}]$
\begin{equation}\tag{A.15}
\left|\frac{\psi(x) - x}{x}\right| \leq s_0(b_2, T) + s_1(b_1, \delta, T) + s_2(b_1, \delta, \lambda, K, T),
\end{equation}
where $s_0, s_1, s_2$ are respectively defined in \textnormal{(A.8)}, \textnormal{(A.11)}, and \textnormal{(A.14)}.
\end{theorem}
-/

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











end BKLNW_app
