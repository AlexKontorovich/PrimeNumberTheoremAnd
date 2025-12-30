import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.FioriKadiriSwidinsky

/-%%
\section{The implications of FKS2}

In this file we record the implications in the paper

FKS2: Fiori--Kadiri--Swidninsky arXiv:2206.12557

that allow one to convert primary bounds on Eψ into secondary bounds on Eπ, Eθ.
%%-/

open Real

namespace FKS2

/-%%
\begin{proposition}[Remark in FKS2 Section 1.1]\label{fks2-rem}\lean{fks2_rem}\leanok $\li(x) - \Li(x) = \li(2)$.
\end{proposition}
%%-/

theorem sec_1_1_rem : ∀ x > 2, li x - Li x = li 2 := sorry

/-%%
\begin{definition}[Dawson function, FKS2 (19)]\label{fks2-eq-19}\lean{dawson}\leanok The Dawson function $D_+ : \mathbb{R} \to \mathbb{R}$ is defined by the formula $D_+(x) := e^{-x^2} \int_0^x e^{t^2}\ dt$.
\end{definition}
%%-/

noncomputable def dawson (x : ℝ) : ℝ := exp (-x ^ 2) * ∫ t in 0..x, exp (t ^ 2)

noncomputable def g_bound (a b c x : ℝ) : ℝ := x^(-a) * (log x)^b * exp (c * (log x)^(1/2))

/-%%
\begin{lemma}[FKS2 equation (17)]\label{FKS2_eq_17} For any $2 \leq x_0 < x$ one has
    $$ (\pi(x) - Li(x)) - (\pi(x_0) - Li(x_0)) = \frac{\theta(x) - x}{\log x} - \frac{\theta(x_0) - x_0}{\log x_0} + \int_{x_0}^x \frac{\theta(t) - t}{t \log^2 t} dt.$$
\end{lemma}
%%-/

theorem eq_17 {x₀ x : ℝ} (hx₀ : x₀ ≥ 2) (hx : x > x₀) :
  (pi x - Li x) - (pi x₀ - Li x₀) =
    (θ x - x) / log x - (θ x₀ - x₀) / log x₀ +
    ∫ t in x₀..x, (θ t - t) / (t * log t ^ 2) :=
  sorry

/-%%
\begin{lemma}[FKS2 Lemma 10a]\label{FKS2_lemma_10a} If $a>0$, $c>0$ and $b < -c^2/16a$, then $g(a,b,c,x)$ decreases with $x$.
\end{lemma}

\begin{lemma}[FKS2 Lemma 10b]\label{FKS2_lemma_10b} For any $a>0$, $c>0$ and $b \geq -c^2/16a$, $g(a,b,c,x)$ decreases with $x$ for $x > \exp((\frac{c}{4a} + \frac{1}{2a} \sqrt{\frac{c^2}{4} + 4ab})^2)$.
\end{lemma}

\begin{lemma}[FKS2 Lemma 10c]\label{FKS2_lemma_10c} If $c>0$, $g(0,b,c,x)$ decreases with $x$ for $\sqrt{\log x} > -2b/c$.
\end{lemma}
%%-/

theorem lemma_10a {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b < -c ^ 2 / (16 * a)) :
  StrictAnti (g_bound a b c) :=
  sorry

theorem lemma_10b {a b c : ℝ} (ha : a > 0) (hc : c > 0) (hb : b ≥ -c ^ 2 / (16 * a)) : StrictAntiOn (g_bound a b c) (Set.Ioi (exp ((c / (4 * a) + (1 / (2 * a)) * sqrt (c ^ 2 / 4 + 4 * a * b)) ^ 2))) :=
  sorry

theorem lemma_10c {b c : ℝ} (hc : c > 0) : StrictAntiOn (g_bound 0 b c) (Set.Ioi (exp ((-2 * b / c) ^ 2))) := sorry

/-%%
\begin{corollary}[FKS2 Corollary 11]\label{FKS2_corollary_11} If $B \geq 1 + C^2 / 16R$ then $g(1,1-B,C/\sqrt{R},x)$ is decreasing in $x$.
\end{corollary}
%%-/

theorem corollary_11 {B C R : ℝ} (hB : B ≥ 1 + C ^ 2 / (16 * R)) : StrictAnti (g_bound 1 (1 - B) (C / sqrt R)) :=
  sorry

/-%%
\begin{lemma}[FKS2 remark after Corollary 11]\label{FKS2_remark_after_corollary_11} The Dawson function has a single maximum at $x \approx 0.942$, after which the function is decreasing.
\end{lemma}
%%-/

theorem remark_after_corollary_11 : ∃ x₀ : ℝ, x₀ ∈ Set.Icc 0.942 0.943 ∧ (∀ x, dawson x ≤ dawson x₀) ∧ StrictAntiOn dawson (Set.Ioi x₀) := sorry


/-%%
\begin{lemma}[FKS2 Lemma 12]\label{FKS2_lemma_12} Suppose that $E_\theta$ satisfies an admissible classical bound with parameters $A,B,C,R,x_0$. Then, for all $x \geq x_0$,
    $$ \int_{x_0}^x |\frac{E_\theta(t)}{\log^2 t} dt| \leq \frac{2A}{R^B} x m(x_0,x) \exp(-C \sqrt{\frac{\log x}{R}}) D_+( \sqrt{\log x} - \frac{C}{2\sqrt{R} )$$
    where
    $$ m(x_0,x) = \max ( (\log x_0)^{(2B-3)/2}, (\log x)^{(2B-3)/2} ). $$
\end{lemma}
%%-/

theorem lemma_12 {A B C R x₀ x : ℝ} (hEθ : Eθ.classicalBound A B C R x₀) (hx : x ≥ x₀) :
  ∫ t in x₀..x, |Eθ t| / log t ^ 2 ≤
    (2 * A) / (R ^ B) * x * max ((log x₀) ^ ((2 * B - 3) / 2)) ((log x) ^ ((2 * B - 3) / 2)) *
    exp (-C * sqrt (log x / R)) * dawson (sqrt (log x) - C / (2 * sqrt R)) :=
  sorry

/-%%
\begin{proposition}[FKS2 Proposition 13]\label{FKS2_Proposition_13} Suppose that $A_\psi,B,C,R,x_0$ give an admissible bound for $E_\psi$.  If $B > C^2/8R$, then $A_\theta, B, C, R, x_0$ give an admissible bound for $E_\theta$, where
    $$ A_\theta = A_\psi (1 + \nu_{asymp}(x_0))$$
with
$$ \nu_{asymp}(x_0) = \frac{1}{A_\psi} (\frac{R}{\log x_0})^B \exp(C \sqrt{\frac{\log x_0}{R}}) (a_1 (\log x_0) x_0^{-1/2} + a_2 (\log x_0) x_0^{-2/3}).$$
\end{proposition}
%%-/

theorem proposition_13
  (Aψ B C R x₀ : ℝ)
  (h_bound : Eψ.classicalBound Aψ B C R x₀)
  (hB : B > C ^ 2 / (8 * R)) :
  Eθ.classicalBound (Aψ * (1 + (1 / Aψ) * (R / log x₀) ^ B * exp (C * sqrt (log x₀ / R)) * (BKLNW.a₁ (log x₀) * (log x₀) * x₀ ^ (-(1:ℝ)/2) + BKLNW.a₂ (log x₀) * (log x₀) * x₀ ^ (-(2:ℝ)/3)))) B C R x₀ := by sorry


/-%%
\begin{corollary}[FKS2 Corollary 14]\label{FKS2_corollary_14} We have an admissible bound for $E_\theta$ with $A = 121.0961$, $B=3/2$, $C=2$, $R = 5.5666305$, $x_0=2$.
\end{corollary}
%%-/

theorem corollary_14 : Eθ.classicalBound 121.0961 (3/2) 2 5.5666305 2 := sorry


/-%%
\begin{definition}[mu asymptotic function, FKS2 (9)]\label{fks2-eq-9}\lean{mu_asymp}\leanok For $x_0,x_1 > 0$, we define
$$ \mu_{asymp}(x_0,x_1) :=
\frac{x_0 \log(x_1)}{\epsilon_{\theta,asymp}(x_1) x_1 \log(x_0)} \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right| + \frac{2D_+(\sqrt{\log(x_1)} - \frac{C}{2\sqrt{R}}}{\sqrt{\log x_1}}$$
\end{definition}
%%-/

noncomputable def μ_asymp (A B C R x₀ x₁ : ℝ) : ℝ := (x₀ * log x₁) / ((admissible_bound A B C R x₁) * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| + 2 * (dawson (sqrt (log x₁) - C / (2 * sqrt R))) / (sqrt (log x₁))

/-%%
\begin{definition}[FKS2, Definition 5]\label{FKS2_numerical} Let $x_0 > 2$. We say a (step) function $ε_{\diamond,num}(x_0)$ gives an admissible numerical
bound for $E_\diamond(x)$ if
$E_\diamond(x) \leq ε_{\diamond,num}(x_0)$ for all $x \geq x_0$.
\end{definition}
%%-/
def _root_.Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ (ε x₀)

def _root_.Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

noncomputable def μ_num_1 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ x₂ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    (log x₂) / x₂ * (Li x₂ - x₂ / log x₂ - Li x₁ + x₁ / log x₁)

noncomputable def μ_num_2 {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) : ℝ :=
  (x₀ * log x₁) / (εθ_num x₁ * x₁ * log x₀) * |Eπ x₀ - Eθ x₀| +
  (log x₁) / (εθ_num x₁ * x₁) *
    (∑ i ∈ Finset.Iio (Fin.last N), εθ_num (exp (b i)) *
      (Li (exp (b (i + 1))) - Li (exp (b i)) +
      exp (b i) / b i - exp (b (i + 1)) / b (i + 1))) +
    1 / (log x₁ + log (log x₁) - 1)

noncomputable def μ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ :=
  if x₂ ≤ x₁ * log x₁ then
    μ_num_1 b εθ_num x₀ x₁ x₂.toReal
  else
    μ_num_2 b εθ_num x₀ x₁

noncomputable def επ_num {N : ℕ} (b : Fin (N + 1) → ℝ) (εθ_num : ℝ → ℝ) (x₀ x₁ : ℝ) (x₂ : EReal) : ℝ := εθ_num x₁ * (1 + μ_num b εθ_num x₀ x₁ x₂)

noncomputable def default_b (x₀ x₁ : ℝ) : Fin 2 → ℝ := fun i ↦ if i = 0 then log x₀ else log x₁

/-%%
\begin{theorem}[FKS2 Theorem 6]\label{FKS2_theorem_6}  Let $x_0 > 0$ be chosen such that $\pi(x_0)$ and $\theta(x_0)$ are computable, and let $x_1 \geq \max(x_0, 14)$. Let $\{b_i\}_{i=1}^N$ be a finite partition of $[\log x_0, \log x_1]$, with $b_1 = \log x_0$ and $b_N = \log x_1$, and suppose that $\varepsilon_{\theta,\mathrm{num}}$ gives computable admissible numerical bounds for $x = \exp(b_i)$, for each $i=1,\dots,N$.  For $x_1 \leq x_2 \leq x_1 \log x_1$, we define
    $$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_0) x_1 \log x_0} \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$

$$ + \frac{\log x_1}{\varepsilon_{theta,num}(x_1) x_1} \sum_{i=1}^{N-1} \varepsilon_{\theta,num}(\exp(b_i)) \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}}$$
$$ + \frac{\log x_2}{x_2} \left( Li(x_2) - \frac{x_2}{\log x_2} - Li(x_1) + \frac{x_1}{\log x_1} \right)$$
and for $x_2 > x_1 \log x_1$, including the case $x_2 = \infty$, we define
$$ \mu_{num}(x_0,x_1,x_2) = \frac{x_0 \log x_1}{\varepsilon_{\theta,num}(x_1) x_1 \log x_0} \left|\frac{\pi(x_0) - \Li(x_0)}{x_0/\log x_0} - \frac{\theta(x_0) - x_0}{x_0}\right|$$
$$ + \frac{\log x_1}{\varepsilon_{\theta,num}(x_1) x_1} \sum_{i=1}^{N-1} \varepsilon_{\theta,num}(\exp(b_i)) \left( Li(e^{b_{i+1}}) - Li(e^{b_i}) + \frac{e^{b_i}}{b_i} - \frac{e^{b_{i+1}}}{b_{i+1}} \right)$$
$$ + \frac{1}{\log x_1 + \log\log x_1 - 1}.$$
Then, for all $x_1 \leq x \leq x_2$ we have
$$ E_\pi(x) \leq \varepsilon_{\pi,num}(x_1,x_2) := \varepsilon_{\theta,num}(x_1)(1 + \mu_{num}(x_0,x_1,x_2)).$$
\end{theorem}
%%-/
theorem theorem_6 {x₀ x₁ : ℝ} (x₂ : EReal) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x.toEReal ≤ x₂) :
  Eπ x ≤ επ_num b εθ_num x₀ x₁ x₂ :=
  sorry

theorem theorem_6_alt {x₀ x₁ : ℝ} (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) :
  Eπ x ≤ εθ_num x₁ * (1 + μ_num_2 b εθ_num x₀ x₁) :=
  sorry

/-%%
\begin{proposition}[FKS2 Remark 7]\label{FKS2_remark_7} If
    $$ \frac{d}{dx} \frac{\log x}{x} \left( Li(x) - \frac{x}{\log x} - Li(x_1) + \frac{x_1}{\log x_1} \right)|_{x_2} \geq 0 $$
    then $\mu_{num,1}(x_0,x_1,x_2) < \mu_{num,2}(x_0,x_1)$.
\end{proposition}
%%-/
theorem remark_7 {x₀ x₁ : ℝ} (x₂ : ℝ) (h : x₁ ≥ max x₀ 14)
  {N : ℕ} (b : Fin (N + 1) → ℝ) (hmono : Monotone b)
  (h_b_start : b 0 = log x₀)
  (h_b_end : b (Fin.last N) = log x₁)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx₁ : x₁ ≤ x) (hx₂ : x ≤ x₂)
  (hderiv : deriv (fun x ↦ (log x) / x * (Li x - x / log x - Li x₁ + x₁ / log x₁)) x₂ ≥ 0) :
  μ_num_1 b εθ_num x₀ x₁ x₂ < μ_num_2 b εθ_num x₀ x₁ := by sorry

/-%%
\begin{corollary}[FKS2 Corollary 8]\label{FKS2_corollary_8} Let $\{b'_i\}_{i=1}^M$ be a set of finite subdivisions of $[\log(x_1),\infty)$, with $b'_1 = \log(x_1)$ and $b'_M = \infty$. Define
    $$ \varepsilon_{\pi, num}(x_1) := \max_{1 \leq i \leq M-1}\varepsilon_{\pi, num}(\exp(b'_i), \exp(b'_{i+1})).$$
    Then $E_\pi(x) \leq \varepsilon_{\pi,num}(x_1)$ for all $x \geq x_1$.
\end{corollary}
%%-/


theorem corollary_8 {x₁ : ℝ} (hx₁ : x₁ ≥ 14)
  {M : ℕ} (b' : Fin (M + 1) → EReal) (hmono : Monotone b')
  (h_b_start : b' 0 = log x₁)
  (h_b_end : b' (Fin.last M) = ⊤)
  (εθ_num : ℝ → ℝ)
  (h_εθ_num : Eθ.numericalBound x₁ εθ_num) (x : ℝ) (hx : x ≥ x₁) :
  Eπ x ≤ iSup (fun i : Finset.Iio (Fin.last M) ↦ επ_num (fun j : Fin (i.val.val+1) ↦ (b' ⟨ j.val, by grind ⟩).toReal) εθ_num x₁ (exp (b' i.val).toReal) (if (i+1) = Fin.last M then ⊤ else exp (b' (i+1)).toReal) ) :=
  sorry

/-%%
\begin{theorem}[FKS2 Remark 15]\label{FKS2_remark_15} If $\log x_0 \geq 1000$ then we have an admissible bound for $E_\theta$ with the indicated choice of $A(x_0)$, $B = 3/2$, $C = 2$, and $R = 5.5666305$.
\end{theorem}
%%-/
theorem remark_15 (x₀ : ℝ) (h : log x₀ ≥ 1000) : Eθ.classicalBound (FKS.A x₀) (3/2) 2 5.5666305 x₀ := by sorry

/-%%
\begin{theorem}[FKS2 Theorem 3]\label{fks2-theorem-3}\lean{fks2_theorem_3}\leanok If $B \geq \max(3/2, 1 + C^2/16 R)$, $x_0 > 0$, and one has an admissible asymptotic bound with parameters $A,B,C,x_0$ for $E_\theta$, and
$$ x_1 \geq \max( x_0, \exp( (1 + \frac{C}{2\sqrt{R}}))^2),$$
then
$$ E_\pi(x) \leq \epsilon_{\theta,asymp}(x_1) ( 1 + \mu_{asymp}(x_0,x_1) ) $$
for all $x \geq x_1$.  In other words, we have an admissible bound with parameters $(1+\mu_{asymp}(x_0,x_1))A, B, C, x_1$ for $E_\pi$.
\end{theorem}
%%-/

theorem theorem_3 (A B C R x₀ x₁ : ℝ)
  (hB : B ≥ max (3 / 2) (1 + C ^ 2 / (16 * R)))
  (hx0 : x₀ > 0)
  (hEθ : Eθ.classicalBound A B C R x₀)
  (hx1 : x₁ ≥ max x₀ (exp ((1 + C / (2 * sqrt R)) ^ 2))) :
  Eπ.classicalBound (A * (1 + μ_asymp A B C R x₀ x₁)) B C R x₁ :=
  sorry

end FKS2
