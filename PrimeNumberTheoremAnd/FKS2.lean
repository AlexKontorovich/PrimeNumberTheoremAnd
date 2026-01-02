import PrimeNumberTheoremAnd.SecondaryDefinitions

/-%%
\section{The implications of FKS2}

In this file we record the implications in the paper

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

that allow one to convert primary bounds on Eψ into secondary bounds on Eπ, Eθ.
%%-/

open Real

/-%%
\begin{proposition}[Remark in FKS2 Section 1.1]\label{fks2-rem}\lean{fks2_rem}\leanok $\li(x) - \Li(x) = \li(2)$.
\end{proposition}
%%-/

theorem fks2_rem : ∀ x > 2, li x - Li x = li 2 := sorry

/-%%
\begin{definition}[Dawson function, FKS2 (19)]\label{fks2-eq-19}\lean{dawson}\leanok The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$.
\end{definition}
%%-/

noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)


/-%%
\begin{definition}[mu asymptotic function, FKS2 (9)]\label{fks2-eq-9}\lean{mu_asymp}\leanok For $x_0,x_1 > 0$, we define
$$ mu_{asymp}(x_0,x_1) :=
\frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)} \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| + \frac{2D_+(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}}{\sqrt{\log x_1}}$$
\end{definition}
-/

noncomputable def mu_asymp (A B C R x₀ x₁ : ℝ) : ℝ := (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| + 2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))










/-%%
\begin{theorem}[FKS2 Theorem 3]\label{fks2-theorem-3}\lean{fks2_theorem_3}\leanok If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound with parameters $A,B,C,x_0$ for $E_\theta$, and
$$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
then
$$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x_1) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
for all $x \geq x_1$.  In other words, we have an admissible bound with parameters $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.
\end{theorem}
%%-/

theorem fks_theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hEθ : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
  Eπ.classicalBound (A * (1 + mu_asymp A B C R x₀ x₁)) B C R x₁ :=
  sorry
