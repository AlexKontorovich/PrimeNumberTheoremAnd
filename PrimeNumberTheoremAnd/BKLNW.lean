import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{Tools from BKLNW}
In this file we record the results from \cite{BKLNW}.
--/

open Real

namespace BKLNW

structure Inputs where
  α : ℝ
  hα : ∀ x > 0, θ x ≤ (1 + α) * x
  ε : ℝ → ℝ
  hε : ∀ b ≥ 0, ∀ x ≥ exp b, |ψ x - x| ≤ ε b * x
  x₁ : ℝ
  hx₁ : x₁ ≥ exp 7
  hx₁' : ∀ x ∈ Set.Icc 1 x₁, θ x < x

@[blueprint
  "bklnw-cor-2-1"
  (title := "Corollary 2.1")
  (statement := /-- $\theta(x) \leq (1 + 1.93378 \times 10^{-8}) x$. -/)
  (latexEnv := "corollary")]
theorem cor_2_1 : ∀ x > 0, θ x ≤ (1 + 1.93378e-8) * x := by sorry

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
  (statement := /-- If $b>0$ then $|\psi(x) - x| \leq \varepsilon(b) x$ for all $x \geq \exp(b)$. -/)
  (latexEnv := "theorem")]
theorem theorem_2 : ∀ b ≥ 0, ∀ x ≥ exp b,
    |ψ x - x| ≤ table_8_ε b * x := by sorry

@[blueprint
  "buthe-eq-1-7"
  (title := "Buthe equation (1.7)")
  (statement := /-- $\theta(x) < x$ for all $1 \leq x \leq 10^{19}$. -/)
  (latexEnv := "sublemma")]
theorem buthe_eq_1_7 : ∀ x ∈ Set.Icc 1 1e19, θ x < x := by sorry

@[blueprint
  "bklnw-inputs"
  (title := "Default input parameters")
  (statement := /-- We take $\alpha = 1.93378 \times 10^{-8}$, $\varepsilon$ as in Table 8 of \cite{BKLNW}, and $x_1 = 10^{19}$. -/)]
noncomputable def Inputs.default : Inputs := {
  α := 1.93378e-8
  hα := cor_2_1
  ε := table_8_ε
  hε := theorem_2
  x₁ := 1e19
  hx₁ := by grw [← exp_one_rpow, rpow_ofNat, exp_one_lt_three]; norm_num
  hx₁' := buthe_eq_1_7
}


@[blueprint
  "bklnw-eq-2-4"
  (title := "Equation 2.4")
  (statement := /--
  $$ f(x) := \sum_{k=3}^{\lfloor \log x / \log 2 \rfloor} x^{1/k - 1/3}.$$
  -/)]
noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 3 ⌊ (log x)/(log 2) ⌋₊, x^(1/k - 1/3 : ℝ)

@[blueprint
  "bklnw-prop-3-sub-1"
  (title := "Proposition 3, substep 1")
  (statement := /-- Let $x \geq x_0$ and let $\alpha$ be admissible. Then
\[
\frac{\psi(x) - \theta(x) - \theta(x^{1/2})}{x^{1/3}} \leq (1 + \alpha) \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
\]
-/)
  (proof := /-- Bound each $\theta(x^{1/k})$ term by $(1 + \alpha)x^{1/k}$. -/)
  (latexEnv := "sublemma")
  (discussion := 630)]
theorem prop_3_sub_1 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 1)
    (hx : x ≥ x₀) :
    (ψ x - θ x - θ (x^(1/2))) / x^(1/3) ≤ (1 + I.α) * f x := by sorry

@[blueprint
  "bklnw-prop-3-sub-2"
  (title := "Proposition 3, substep 2")
  (statement := /-- $f$ decreases on $[2^n, 2^{n+1})$.-/)
  (proof := /-- Clear. -/)
  (latexEnv := "sublemma")
  (discussion := 632)]
theorem prop_3_sub_2 (n : ℕ) : StrictAntiOn f (Set.Ico (2^n) (2^(n + 1))) := by sorry

noncomputable def u (n : ℕ) : ℝ := ∑ k ∈ Finset.Icc 4 n, 2^((n/k:ℝ) - (n/3:ℝ))

@[blueprint
  "bklnw-prop-3-sub-3"
  (title := "Proposition 3, substep 3")
  (statement := /-- $f(2^n) = 1 + u_n$.-/)
  (proof := /-- Clear. -/)
  (latexEnv := "sublemma")
  (discussion := 633)]
theorem prop_3_sub_3 (n : ℕ) (hn : n ≥ 3) : f (2^n) = 1 + u n := by
  have sum_bound : ⌊ (log (2 ^ n)) / (log 2) ⌋₊ = n := by norm_num
  rw [f, u, sum_bound, ← Finset.add_sum_Ioc_eq_sum_Icc (by linarith), ← Finset.Ioc_eq_Icc]
  congr
  · norm_num
  ext k
  calc (2 ^ n : ℝ) ^ (1 / ↑k - 1 / 3 : ℝ)
    _ = 2 ^ (n * (1 / ↑k - 1 / 3 : ℝ)) := by rw [← rpow_natCast _ n, ← rpow_mul (by norm_num)]
    _ = _ := by field_simp

@[blueprint
  "bklnw-prop-3-sub-4"
  (title := "Proposition 3, substep 4")
  (statement := /-- $u_{n+1} < u_n$ for $n \geq 9$.-/)
  (proof := /-- We have
\begin{equation}
u_{n+1} - u_n = \sum_{k=4}^{n} 2^{\frac{n+1}{k} - \frac{n+1}{3}}(1 - 2^{\frac{1}{3} - \frac{1}{k}}) + 2^{1 - \frac{n+1}{3}} = 2^{-\frac{n+1}{3}} \left( 2 - \sum_{k=4}^{n} 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1) \right).
\end{equation}
Observe that if $n \geq 20$, then
\[
\sum_{k=4}^{n} 2^{\frac{n+1}{k}}(2^{\frac{1}{3} - \frac{1}{k}} - 1) > 2^{\frac{n+1}{4}}(2^{\frac{1}{3} - \frac{1}{4}} - 1) \geq 2^{\frac{21}{4}}(2^{\frac{1}{12}} - 1) > 2
\]
and it follows that $u_{n+1} - u_n < 0$ for $n \geq 20$. Finally, a numerical calculation verifies that the right hand side of the equation above is negative for $9 \leq n \leq 19$. -/)
  (latexEnv := "sublemma")
  (discussion := 634)]
theorem prop_3_sub_4 (n : ℕ) (hn : n ≥ 9) : u (n + 1) < u n := by sorry

@[blueprint
  "bklnw-prop-3-sub-5"
  (title := "Proposition 3, substep 5")
  (statement := /-- $f(2^n) > f(2^{n+1})$ for $n \geq 9$. -/)
  (proof := /-- This follows from Sublemmas \ref{bklnw-prop-3-sub-3} and \ref{bklnw-prop-3-sub-4}. -/)
  (latexEnv := "sublemma")
  (discussion := 635)]
theorem prop_3_sub_5 (n : ℕ) (hn : n ≥ 9) : f (2^n) > f (2^(n + 1)) := by sorry

@[blueprint
  "bklnw-prop-3-sub-6"
  (title := "Proposition 3, substep 6")
  (statement := /-- $f(x) \leq f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$ on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1}, \infty)$. -/)
  (proof := /-- Follows from Sublemmas \ref{bklnw-prop-3-sub-2} and \ref{bklnw-prop-3-sub-5}. -/)
  (latexEnv := "sublemma")
  (discussion := 636)]
theorem prop_3_sub_6 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ 2 ^ (⌊(log x₀) / (log 2)⌋ + 1)) :
    f x ≤ f (2 ^ (⌊(log x₀)/(log 2)⌋ + 1)) := by sorry

@[blueprint
  "bklnw-prop-3-sub-7"
  (title := "Proposition 3, substep 7")
  (statement := /-- $f(x) \leq f(x_0)$ for $x \in [x_0, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$. -/)
  (proof := /-- Follows since $f(x)$ decreases on $[2^{\lfloor \frac{\log x_0}{\log 2} \rfloor}, 2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})$. -/)
  (latexEnv := "sublemma")
  (discussion := 637)]
theorem prop_3_sub_7 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ∈ Set.Icc x₀ (2 ^ (⌊(log x₀) / (log 2)⌋ + 1))) :
    f x ≤ f x₀ := by sorry

@[blueprint
  "bklnw-prop-3-sub-8"
  (title := "Proposition 3, substep 8")
  (statement := /--  $f(x) \leq \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)$. -/)
  (proof := /-- Combines previous sublemmas. -/)
  (latexEnv := "sublemma")
  (discussion := 638)]
theorem prop_3_sub_8 (x₀ : ℝ) (hx₀ : x₀ ≥ 2 ^ 9) (x : ℝ)
    (hx : x ≥ x₀) :
    f x ≤ max (f x₀) (f (2 ^ (⌊ (log x₀)/(log 2) ⌋ + 1))) := by sorry

@[blueprint
  "bklnw-prop-3"
  (title := "Proposition 3")
  (statement := /--  Let $x_0 \geq 2^9$. Let $\alpha > 0$ exist such that $\theta(x) \leq (1 + \alpha)x$ for $x > 0$. Then for $x \geq x_0$,
\begin{equation}
\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k}) \leq \eta x^{1/3},
\end{equation}
where
\begin{equation}
\eta = \eta(x_0) = (1 + \alpha) \max\left(f(x_0), f(2^{\lfloor \frac{\log x_0}{\log 2} \rfloor + 1})\right)
\end{equation}
with
\begin{equation}
f(x) := \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
\end{equation}
 -/)
  (proof := /-- Combines previous sublemmas. -/)
  (latexEnv := "proposition")
  (discussion := 639)]
theorem prop_3 (I : Inputs) {x₀ x : ℝ} (hx₀ : x₀ ≥ 2 ^ 9)
    (hx : x ≥ x₀) :
    ∑ k ∈ Finset.Icc 3 ⌊ (log x)/(log 2) ⌋, θ (x^(1/k)) ≤
      (1 + I.α) * max (f x₀) (f (2^(⌊ (log x₀)/(log 2) ⌋ + 1))) * x^(1/3) := by sorry

@[blueprint
  "bklnw-cor-3-1"
  (title := "Corollary 3.1")
  (statement := /--  Let $b \geq 7$. Assume $x \geq e^b$. Then we have
\[
\psi(x) - \theta(x) - \theta(x^{1/2}) \leq \eta x^{1/3},
\]
where
\begin{equation}
\eta = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)
\end{equation}
 -/)
  (proof := /-- We apply Proposition \ref{bklnw-prop-3} with $x_0 = e^b$ where we observe that $x_0 = e^b \geq e^7 > 2^9$.
 -/)
  (latexEnv := "corollary")
  (discussion := 640)]
theorem cor_3_1 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (x : ℝ) (hx : x ≥ exp b) :
    ψ x - θ x - θ (x^(1/2)) ≤
      (1 + I.α) * max (f (exp b)) (f (2^(⌊ b/(log 2) ⌋ + 1))) * x^(1/3) := by sorry

@[blueprint
  "bklnw-prop-4-a"
  (title := "Proposition 4, part a")
  (statement := /--  If $b \leq 2\log x_1$, then we have
\begin{equation}
\theta(x^{1/2}) < (1 + \varepsilon(\log x_1))x^{1/2} \quad \text{for } x \geq e^b.
\end{equation}
 -/)
  (proof := /-- If $e^b \leq x \leq x_1^2$, then $x^{1/2} \leq x_1$, and thus
\[
\theta(x^{1/2}) < x^{1/2} \quad \text{for } e^b \leq x \leq x_1^2.
\]
On the other hand, if $x^{1/2} > x_1 = e^{\log x_1}$, then we have by (2.7)
\[
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(\log x_1))x^{1/2},
\]
since $\log x_1 \geq 7$. The last two inequalities for $\theta(x^{1/2})$ combine to establish (2.8).
 -/)
  (latexEnv := "proposition")
  (discussion := 641)]
theorem prop_4_a (I : Inputs) {b x : ℝ} (hb : b ≤ 2 * log I.x₁) (hx : x ≥ exp b) :
    θ (x^(1/2)) < (1 + I.ε (log I.x₁)) * x^(1/2) := by sorry

@[blueprint
  "bklnw-prop-4-b"
  (title := "Proposition 4, part b")
  (statement := /--  If $b > 2\log x_1$, then we have
\[
\theta(x^{1/2}) < (1 + \varepsilon(b/2))x^{1/2} \quad \text{for } x \geq e^b.
\]
 -/)
  (proof := /-- As in the above subcase, we have for $x \geq e^b$
\[
\theta(x^{1/2}) \leq \psi(x^{1/2}) \leq (1 + \varepsilon(b/2))x^{1/2},
\]
since $x^{1/2} > e^{b/2} > x_1 \geq e^7$.
 -/)
  (latexEnv := "proposition")
  (discussion := 642)]
theorem prop_4_b (I : Inputs) {b x : ℝ} (hb : b > 2 * log I.x₁) (hx : x ≥ exp b) :
    θ (x^(1/2)) < (1 + I.ε (b / 2)) * x^(1/2) := by sorry

noncomputable def Inputs.a₁ (I : Inputs) (b : ℝ) : ℝ :=
  if b ≤ 2 * log I.x₁ then 1 + I.ε (log I.x₁)
  else 1 + I.ε (b / 2)

noncomputable def Inputs.a₂ (I : Inputs) (b : ℝ) : ℝ :=
  (1 + I.α) * (max (f (exp b)) (f (⌊ b / (log 2) ⌋ + 1)))

@[blueprint
  "bklnw-thm-5"
  (title := "Theorem 5")
  (statement := /--  Let $\alpha > 0$ exist such that
\[
\theta(x) \leq (1 + \alpha)x \quad \text{for all } x > 0.
\]
Assume for every $b \geq 7$ there exists a positive constant $\varepsilon(b)$ such that
\[
\psi(x) - x \leq \varepsilon(b)x \quad \text{for all } x \geq e^b.
\]
Assume there exists $x_1 \geq e^7$ such that
\begin{equation}
\theta(x) < x \quad \text{for } x \leq x_1.
\end{equation}
Let $b \geq 7$. Then, for all $x \geq e^b$ we have
\[
\psi(x) - \theta(x) < a_1 x^{1/2} + a_2 x^{1/3},
\]
where
\[
a_1 = \begin{cases}
1 + \varepsilon(\log x_1) & \text{if } b \leq 2\log x_1, \\
1 + \varepsilon(b/2) & \text{if } b > 2\log x_1,
\end{cases}
\]
and
\[
a_2 = (1 + \alpha) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right).
\]
  -/)
  (proof := /-- We have $\psi(x) - \theta(x) = \theta(x^{1/2}) + \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$. For any $b \geq 7$, setting $x_0 = e^b$ in Proposition 4, we bound $\sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} \theta(x^{1/k})$ by $\eta x^{1/3}$ as defined in (2.3). We bound $\theta(x^{1/2})$ with Proposition \ref{bklnw-prop-4} by taking either $a_1 = 1 + \varepsilon(\log x_1)$ for $b \leq 2\log x_1$ or $a_1 = 1 + \varepsilon(b/2)$ for $b > 2\log x_1$.
 -/)
  (latexEnv := "theorem")
  (discussion := 643)]
theorem thm_5 (I : Inputs) {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x < Inputs.a₁ I b * x^(1/2) + Inputs.a₂ I b * x^(1/3) := by sorry


noncomputable def a₁ : ℝ → ℝ := Inputs.default.a₁

noncomputable def a₂ : ℝ → ℝ := Inputs.default.a₂

end BKLNW
