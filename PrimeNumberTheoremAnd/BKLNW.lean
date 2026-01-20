import PrimeNumberTheoremAnd.FioriKadiriSwidinsky
import PrimeNumberTheoremAnd.SecondaryDefinitions
import PrimeNumberTheoremAnd.CostaPereira

blueprint_comment /--
\section{Tools from BKLNW}
In this file we record the results from \cite{BKLNW}.
-/

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
  R : ℝ
  hR : riemannZeta.classicalZeroFree R
  ZDB : zero_density_bound

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
  R := 5.5666305  -- a slightly more conservative value of 5.573412 was used in the paper
  hR := MT_theorem_1
  ZDB := FKS.corollary_2_9_merged -- stronger than what was used here, I think
}


@[blueprint
  "bklnw-eq-2-4"
  (title := "Equation 2.4")
  (statement := /--
  $$ f(x) := \sum_{k=3}^{\lfloor \log x / \log 2 \rfloor} x^{1/k - 1/3}.$$
  -/)]
noncomputable def f (x : ℝ) : ℝ := ∑ k ∈ Finset.Icc 3 ⌊ (log x)/(log 2) ⌋, x^(1/k - 1/3)

@[blueprint
  "bklnw-prop-3-sub-1"
  (title := "Proposition 3, substep 1")
  (statement := /-- Let $x \geq x_0$ and let $\alpha$ be admissible. Then
\[
\frac{\psi(x) - \theta(x) - \theta(x^{1/2})}{x^{1/3}} \leq (1 + \alpha) \sum_{k=3}^{\lfloor \frac{\log x}{\log 2} \rfloor} x^{\frac{1}{k} - \frac{1}{3}}.
\]
-/)
  (proof := /-- Bound each $\theta(x^{1/k})$ term by $(1 + \alpha)x^{1/k}$ in Sublemma \ref{costa-pereira-sublemma-1-1}. -/)
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
theorem prop_3_sub_3 (n : ℕ) : f (2^n) = 1 + u n := by sorry

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
theorem prop_3_sub_4 (n : ℕ) (hn : 9 ≤ n) : u (n + 1) < u n := by
  suffices u (n + 1) - u n < 0 from by linarith
  unfold u
  calc
    _ = (∑ k ∈ Finset.Icc 4 n, (2 : ℝ) ^ ((n + 1) / (k : ℝ) - (n + 1) / 3) * (1 - 2 ^
      (1 / (3 : ℝ) - 1 / ↑k))) + 2 ^ (1 - (n + 1) / (3 : ℝ)) := by
      sorry
    _ = (2 : ℝ) ^ (- (n + 1 : ℝ) / 3) * (2 - ∑ k ∈ Finset.Icc 4 n, 2 ^ ((n + 1) / (k : ℝ)) *
      (2 ^ (1 / (3 : ℝ) - 1 / k) - 1)) := by
      sorry
  by_cases h : 20 ≤ n
  · suffices 2 < ∑ k ∈ Finset.Icc 4 n, (2 : ℝ) ^ ((n + 1) / (k : ℝ)) *
      (2 ^ (1 / (3 : ℝ) - 1 / k) - 1) from mul_neg_of_pos_of_neg (by positivity) (by linarith)
    calc
    _ < 2 ^ (21 / (4 : ℝ)) * (2 ^ (1 / (12 : ℝ)) - 1) := by sorry
    _ < (2 : ℝ) ^ ((n + 1) / (4 : ℝ)) * (2 ^ (1 / (3 : ℝ) - 1 / 4) - 1) := by
      sorry
    _ < ∑ k ∈ Finset.Icc 4 n, (2 : ℝ) ^ ((n + 1) / (k : ℝ)) * (2 ^ (1 / (3 : ℝ) - 1 / k) - 1) := by
      refine Finset.single_lt_sum (f := fun k : ℕ => (2 : ℝ) ^ ((n + 1) / (k : ℝ)) * (2 ^
        (1 / (3 : ℝ) - 1 / k) - 1)) (j := 5) (by linarith) (by grind) (by grind) ?_ (fun k hk => ?_)
      · sorry
      · sorry
  · interval_cases n
    repeat sorry

@[blueprint
  "bklnw-prop-3-sub-5"
  (title := "Proposition 3, substep 5")
  (statement := /-- $f(2^n) > f(2^{n+1})$ for $n \geq 9$. -/)
  (proof := /-- This follows from Sublemmas \ref{bklnw-prop-3-sub-3} and \ref{bklnw-prop-3-sub-4}. -/)
  (latexEnv := "sublemma")
  (discussion := 635)]
theorem prop_3_sub_5 (n : ℕ) (hn : n ≥ 9) : f (2^n) > f (2^(n + 1)) := by
  simp [prop_3_sub_3, prop_3_sub_4 n hn]

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
      (1 + I.α) * max (f x₀) (f (2^(⌊ (log x₀)/(log 2) ⌋ + 1))) * x^(1/3:ℝ) := by sorry

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
    ψ x - θ x - θ (x^(1/2:ℝ)) ≤
      (1 + I.α) * max (f (exp b)) (f (2^(⌊ b/(log 2) ⌋ + 1))) * x^(1/3:ℝ) := by sorry

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
    θ (x^(1/2:ℝ)) < (1 + I.ε (log I.x₁)) * x^(1/2:ℝ) := by sorry

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
    ψ x - θ x < Inputs.a₁ I b * x^(1/2:ℝ) + Inputs.a₂ I b * x^(1/3:ℝ) := by sorry

noncomputable def a₁ : ℝ → ℝ := Inputs.default.a₁

noncomputable def a₂ : ℝ → ℝ := Inputs.default.a₂

@[blueprint
  "bklnw-cor-5-1"
  (title := "Corollary 5.1")
  (statement := /--  Let $b \geq 7$. Then for all $x \geq e^b$ we have $\psi(x) - \vartheta(x) < a_1 x^{1/2} + a_2 x^{1/3}$, where $a_1 = a_1(b) = 1 + 1.93378 \times 10^{-8}$ if $b \leq 38 \log 10$, $1 + \varepsilon(b/2)$ if $b > 38 \log 10$, and $a_2 = a_2(b) = (1 + 1.93378 \times 10^{-8}) \max\left( f(e^b), f(2^{\lfloor \frac{b}{\log 2} \rfloor + 1}) \right)$, where $f$ is defined by (2.4) and values for $\varepsilon(b/2)$ are from Table 8. -/)
  (proof := /-- This is Theorem 5 applied to the default inputs in Definition \ref{bklnw-inputs}. -/)]
theorem cor_5_1 {b x : ℝ} (hb : b ≥ 7) (hx : x ≥ exp b) :
    ψ x - θ x < a₁ b * x^(1/2:ℝ) + a₂ b * x^(1/3:ℝ) := by sorry

/- We have the following values for a2. b 20 25 30 35 40 43 a2 1.4263 1.2196 1.1211 1.07086 1.04320 1.03253 1.01718 b 100 150 200 250 a2 1+2.421·10−4 1+3.749·10−6 1+7.712·10−8 1+2.024·10−8 1+1.936·10−8 -/

def table_cor_5_1 : List (ℝ × ℝ × ℕ) :=
  [ (20, 1.4263, 4)
  , (25, 1.2196, 4)
  , (30, 1.1211, 4)
  , (35, 1.07086, 5)
  , (40, 1.04320, 5)
  , (43, 1.03253, 5)
  , (100, 1 + 2.421e-4, 7)
  , (150, 1 + 3.749e-6, 8)
  , (200, 1 + 7.712e-8, 9)
  , (250, 1 + 2.024e-8, 9)
  , (300, 1 + 1.936e-8, 9)
  ]

@[blueprint
  "bklnw-cor-5-1-rem"
  (title := "Remark after Corollary 5.1")
  (statement := /--  We have the following values for $a_2$, given by the table after \cite[Corollary 5.1]{BKLNW} -/)
  (latexEnv := "remark")]
theorem cor_5_1_rem (b a₂b : ℝ) (m : ℕ) (hb : (b, a₂b, m) ∈ table_cor_5_1) :
    a₂ b ∈ Set.Icc a₂b (a₂b + 10^(-m:ℝ)) := by sorry

noncomputable def Table_14 : List (ℝ × ℝ × ℝ) := [
  (20, 4.2676e-5, 9.1639e-5),
  (25, 3.5031e-6, 7.4366e-6),
  (30, 2.8755e-7, 6.0751e-7),
  (35, 2.3603e-8, 4.9766e-8),
  (40, 1.9338e-8, 2.1482e-8),
  (19 * log 10, 1.9338e-8, 1.9667e-8),
  (45, 1.0907e-8, 1.1084e-8),
  (50, 1.1199e-9, 1.1344e-9),
  (60, 1.2215e-11, 1.2312e-11),
  (70, 2.7923e-12, 2.7930e-12),
  (80, 2.6108e-12, 2.6108e-12),
  (90, 2.5213e-12, 2.5213e-12),
  (100, 2.4530e-12, 2.4530e-12),
  (200, 2.1815e-12, 2.1816e-12),
  (300, 2.0902e-12, 2.0903e-12),
  (400, 2.0398e-12, 2.0399e-12),
  (500, 1.9999e-12, 1.9999e-12),
  (700, 1.9764e-12, 1.9765e-12),
  (1000, 1.9475e-12, 1.9476e-12),
  (2000, 1.9228e-12, 1.9228e-12),
  (3000, 4.5997e-14, 4.5998e-14),
  (4000, 1.4263e-16, 1.4264e-16),
  (5000, 5.6303e-19, 5.6303e-19),
  (7000, 2.0765e-23, 2.0766e-23),
  (10000, 3.7849e-29, 3.7850e-29),
  (11000, 7.1426e-31, 7.1427e-31),
  (12000, 1.5975e-32, 1.5976e-32),
  (13000, 4.1355e-34, 4.1356e-34),
  (13800.7464, 2.5423e-35, 2.5424e-35),
  (15000, 4.1070e-37, 4.1070e-37),
  (17000, 6.2040e-40, 6.2040e-40),
  (20000, 7.1621e-44, 7.1621e-44),
  (22000, 2.4392e-46, 2.4392e-46),
  (25000, 7.5724e-50, 7.5724e-50)
]

noncomputable def Table_15 : List (ℝ × (Fin 5 → ℝ)) := [
  (0, ![1.2323e0, 3.9649e0, 2.0829e1, 1.5123e2, 1.3441e5]),
  (log 1e5, ![5.5316e-2, 6.4673e-1, 7.5612e0, 8.9346e1, 1.3441e5]),
  (log 5e5, ![2.6724e-2, 3.5744e-1, 4.7808e0, 6.3944e1, 1.3441e5]),
  (log 1e6, ![2.3240e-2, 3.2309e-1, 4.4916e0, 6.2444e1, 1.3441e5]),
  (log 5e6, ![1.0236e-2, 1.5952e-1, 2.4860e0, 5.7184e1, 1.3441e5]),
  (log 1e7, ![8.4725e-3, 1.3675e-1, 2.2071e0, 5.7184e1, 1.3441e5]),
  (log 5e7, ![3.8550e-3, 6.8701e-2, 1.2244e0, 5.7184e1, 1.3441e5]),
  (log 1e8, ![2.7457e-3, 5.0612e-2, 9.4259e-1, 5.7184e1, 1.3441e5]),
  (log 1e9, ![9.5913e-4, 2.0087e-2, 4.2065e-1, 5.7184e1, 1.3441e5]),
  (log 1e10, ![3.7787e-4, 8.7526e-3, 2.0274e-1, 5.7184e1, 1.3441e5]),
  (log 19035709163, ![2.6773e-4, 6.3370e-3, 1.5000e-1, 5.7184e1, 1.3441e5]),
  (log 2e10, ![2.4601e-4, 5.8365e-3, 1.3848e-1, 5.7184e1, 1.3441e5]),
  (log 5e10, ![1.8556e-4, 4.5722e-3, 1.1266e-1, 5.7184e1, 1.3441e5]),
  (log 1e11, ![1.3392e-4, 3.4053e-3, 8.6589e-2, 5.7184e1, 1.3441e5]),
  (log 2e11, ![7.8683e-5, 2.0591e-3, 5.3886e-2, 5.7184e1, 1.3441e5]),
  (log 3e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 4e11, ![7.0193e-5, 1.8758e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 5e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (log 6e11, ![6.9322e-5, 1.8717e-3, 5.0536e-2, 5.7184e1, 1.3441e5]),
  (28, ![4.3555e-5, 1.2196e-3, 3.4148e-2, 5.7184e1, 1.3441e5]),
  (29, ![2.7336e-5, 7.9272e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (30, ![1.7139e-5, 5.1415e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (31, ![1.0735e-5, 3.3277e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (32, ![7.0053e-6, 2.2417e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (33, ![4.3798e-6, 1.4454e-4, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (34, ![2.7360e-6, 9.3023e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (35, ![1.7078e-6, 5.9771e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (36, ![1.0652e-6, 3.8345e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (37, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (38, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (39, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (40, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (41, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (42, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (43, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (19 * log 10, ![8.6315e-7, 3.7979e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (44, ![7.8163e-7, 3.5174e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (45, ![5.0646e-7, 2.3298e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (46, ![3.2935e-7, 1.5480e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (47, ![2.1308e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (48, ![1.3791e-7, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (49, ![8.9140e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (50, ![5.7545e-8, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (55, ![6.3417e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (60, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (65, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (70, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (80, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (90, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (100, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (200, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (300, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (400, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (600, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (700, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (800, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (900, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (1500, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2000, ![4.4627e-9, 1.0376e-5, 2.4334e-2, 5.7184e1, 1.3441e5]),
  (2500, ![2.2885e-9, 5.7783e-6, 1.4591e-2, 3.6840e1, 9.3021e4]),
  (3000, ![1.3915e-10, 4.2091e-7, 1.2733e-3, 3.8516e0, 1.1651e4]),
  (3500, ![8.7646e-12, 3.0896e-8, 1.0891e-4, 3.8390e-1, 1.3533e3]),
  (4000, ![5.7410e-13, 2.3108e-9, 9.3007e-6, 3.7436e-2, 1.5068e2]),
  (5000, ![2.8715e-15, 1.4645e-11, 7.4687e-8, 3.8091e-4, 1.9426e0]),
  (6000, ![1.7952e-17, 1.0951e-13, 6.6798e-10, 4.0747e-6, 2.4856e-2]),
  (7000, ![1.4744e-19, 1.0468e-15, 7.4322e-12, 5.2769e-8, 3.7466e-4]),
  (8000, ![1.6007e-21, 1.2966e-17, 1.0502e-13, 8.5065e-10, 6.8903e-6]),
  (9000, ![2.2253e-23, 2.0250e-19, 1.8428e-15, 1.6769e-11, 1.5260e-7]),
  (10000, ![3.8228e-25, 3.8610e-21, 3.8997e-17, 3.9387e-13, 3.9780e-9]),
  (11000, ![7.9284e-27, 8.8005e-23, 9.7685e-19, 1.0844e-14, 1.2036e-10]),
  (12000, ![1.9331e-28, 2.3390e-24, 2.8302e-20, 3.4245e-16, 4.1437e-12]),
  (13000, ![5.5830e-30, 7.5371e-26, 1.0175e-21, 1.3737e-17, 1.8544e-13]),
  (14000, ![1.8399e-31, 2.7598e-27, 4.1396e-23, 6.2094e-19, 9.3141e-15]),
  (15000, ![6.5712e-33, 1.0514e-28, 1.6823e-24, 2.6916e-20, 4.3065e-16]),
  (16000, ![2.5739e-34, 4.3756e-30, 7.4384e-26, 1.2646e-21, 2.1497e-17]),
  (17000, ![1.1168e-35, 2.0101e-31, 3.6182e-27, 6.5127e-23, 1.1723e-18]),
  (18000, ![5.3739e-37, 1.0211e-32, 1.9400e-28, 3.6860e-24, 7.0033e-20]),
  (19000, ![2.7357e-38, 5.4714e-34, 1.0943e-29, 2.1886e-25, 4.3772e-21]),
  (20000, ![1.5041e-39, 3.1585e-35, 6.6329e-31, 1.3929e-26, 2.9251e-22]),
  (21000, ![9.0606e-41, 1.9934e-36, 4.3853e-32, 9.6477e-28, 2.1225e-23]),
  (22000, ![5.6101e-42, 1.2904e-37, 2.9678e-33, 6.8258e-29, 1.5700e-24]),
  (23000, ![3.7554e-43, 9.0129e-39, 2.1631e-34, 5.1915e-30, 1.2460e-25]),
  (24000, ![2.6756e-44, 6.6889e-40, 1.6723e-35, 4.1806e-31, 1.0452e-26]),
  (25000, ![7.5635e-45, 1.8909e-40, 4.7272e-36, 1.1818e-31, 2.9545e-27])
]

-- TODO: input the statements and arguments from Section 3 used to prove Theorem 1 below

/- Theorem 1. Let k be an integer with 0 ≤ k ≤ 5. For any fixed X0 ≥ 1, there exists mk > 0 such that, for all x ≥ X0 (1.1) x 1− mk (log x)k ≤ θ(x). For any fixed X1 ≥ 1, there exists Mk > 0 such that, for all x ≥ X1 (1.2) θ(x) ≤ x 1+ Mk (log x)k . In the case k = 0 and X0,X1 ≥ e20, we have m0 =ε(logX0)+1.03883(X−1/2 0 +X−2/3 0 +X−4/5 0 ) and M0=ε(logX1). See Table 14 for values of m0 and M0, and Table 15 for values of mk and Mk, for k ∈ {1,2,3,4,5}. -/

@[blueprint
  "bklnw-thm-1a"
  (title := "Theorem 1a")
  (statement := /--  For any fixed $X_0 \geq 1$, there exists $m_0 > 0$ such that, for all $x \geq X_0$
  $$ x(1 - m_0) \leq \theta(x). $$
  For any fixed $X_1 \geq 1$, there exists $M_0 > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + M_0). $$
  For $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$
  -/)
  (latexEnv := "theorem")]
theorem thm_1a {X₀ X₁ x : ℝ} (hX₀ : X₀ ≥ exp 20) (hX₁ : X₁ ≥ exp 20) (hx₀ : x ≥ X₀) (hx₁ : x ≥ X₁) :
  let m₀ := Inputs.default.ε (log X₀) + 1.03883 * (X₀^(-1/2:ℝ) + X₀^(-2/3:ℝ) + X₀^(-4/5:ℝ))
  let M₀ := Inputs.default.ε (log X₁)
  x * (1 - m₀) ≤ θ x ∧ θ x ≤ x * (1 + M₀) := by sorry

@[blueprint
  "bklnw-thm-1a"
  (statement := /-- See \cite[Table 14]{BKLNW} for values of $m_0$ and $M_0$ -/)
  (latexEnv := "theorem")]
theorem thm_1a_table {X₀ m₀ M₀ : ℝ} (h : (X₀, M₀, m₀) ∈ Table_14) {x : ℝ} (hx : x ≥ X₀) :
  x * (1 - m₀) ≤ θ x ∧ θ x ≤ x * (1 + M₀) :=
  by sorry

@[blueprint
  "bklnw-thm-1b"
  (title := "Theorem 1b")
  (statement := /--  Let $k$ be an integer with $1 \leq k \leq 5$. For any fixed $X_0 \geq 1$, there exists $m_k > 0$ such that, for all $x \geq X_0$
  $$ x(1 - \frac{m_k}{(\log x)^k}) \leq \theta(x). $$
  For any fixed $X_1 \geq 1$, there exists $M_k > 0$ such that, for all $x \geq X_1$
  $$ \theta(x) \leq x(1 + \frac{M_k}{(\log x)^k}). $$
  In the case $k = 0$ and $X_0, X_1 \geq e^{20}$, we have
  $$ m_0 = \varepsilon(\log X_0) + 1.03883 \left( X_0^{-1/2} + X_0^{-2/3} + X_0^{-4/5} \right) $$
  and
  $$ M_0 = \varepsilon(\log X_1). $$
  -/)
  (latexEnv := "theorem")]
theorem thm_1b (k : ℕ) (hk : k ≤ 5) {X₀ X₁ x : ℝ} (hx₀ : x ≥ X₀) (hx₁ : x ≥ X₁) : ∃ mₖ Mₖ,
  (x * (1 - mₖ / (log x)^k) ≤ θ x) ∧ (θ x ≤ x * (1 + Mₖ / (log x)^k)) := by sorry

@[blueprint
  "bklnw-thm-1b"
  (title := "Theorem 1b")
  (statement := /--  See \cite[Table 15]{BKLNW} for values of $m_k$ and $M_k$, for $k \in \{1,2,3,4,5\}$.
  -/)
  (latexEnv := "theorem")]
theorem thm_1b_table {X₀ : ℝ} {M : Fin 5 → ℝ} (h : (X₀, M) ∈ Table_15) (k : Fin 5) {x : ℝ} (hx : x ≥ X₀) :
  x * (1 - M k / (log x)^(k.val + 1)) ≤ θ x ∧ θ x ≤ x * (1 + M k / (log x)^(k.val + 1)) :=
  by sorry

-- TODO: input the statements and arguments from Appendix A

noncomputable def Inputs.c1 (I : Inputs) (σ : ℝ) : ℝ := I.ZDB.c₁ σ
noncomputable def Inputs.c2 (I : Inputs) (σ : ℝ) : ℝ := I.ZDB.c₂ σ

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
  8.01 * I.c2 σ * exp (-2 * (log x₀ / I.R)^(1/2)) * (log x₀ / I.R) * I.k σ x₀

@[blueprint
  "bklnw-eq_A_20"
  (title := "Equation (A.20)")
  (statement := /-- We define
  $$ A(\sigma, x_0) = 2.0025 \cdot 25^{-2 \sigma} \cdot c_1(\sigma) + c_3(\sigma, x_0) + c_4(\sigma, x_0) + c_5(\sigma, x_0). $$
  -/)]
noncomputable def Inputs.A (I : Inputs) (σ x₀ : ℝ) : ℝ :=
  2.0025 * 25^(-2 * σ) * I.c1 σ + I.c3 σ x₀ + I.c4 σ x₀ + I.c5 σ x₀

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
  where $A$, $B$, and $C$ are defined in (A.20) and (A.21). -/)]
theorem thm_14 {I : Inputs} {x₀ σ x : ℝ} (hx₀ : x₀ ≥ 1000) (hσ : 0.75 ≤ σ ∧ σ < 1) (hx : x ≥ exp x₀) :
  Eψ x ≤ I.A σ x₀ * (log x / I.R)^(I.B σ) * exp (-I.C σ * (log x / I.R)^(1/2:ℝ)) := by sorry

@[blueprint
  "bklnw-cor-14.1"
  (title := "Corollary 14.1")
  (statement := /-- Let $x_0 \geq 1000$. For all $x \geq e^{x_0}$,
  $$ \frac{|\theta(x) - x|}{x} \leq A' \left( \frac{\log x}{R} \right)^B \exp\left( -C \left( \frac{\log x}{R} \right)^{1/2} \right) $$
  where $B$ and $C$ are defined in (A.21) and
  $$ A' = A \left( 1 + \frac{1}{A} \left( \frac{R}{\log x_0} \right)^B \exp\left( C \frac{\log x_0}{R} \right) \left( a_1(x_0) \exp\left( -\frac{x_0}{2} \right) + a_2(x_0) \exp\left( -\frac{2 x_0}{3} \right) \right) \right), $$
  where $a_1$ and $a_2$ are defined in Corollary 5.1. -/)]
theorem cor_14_1 {I : Inputs} {x₀ σ x : ℝ} (hx₀ : x₀ ≥ 1000) (hσ : 0.75 ≤ σ ∧ σ < 1) (hx : x ≥ exp x₀) :
  Eθ x ≤ I.A σ x₀ * (1 + (1 / I.A σ x₀) * (I.R / log x₀)^(I.B σ) * exp (I.C σ * (log x₀ / I.R)) *
    (I.a₁ x₀ * exp (-x₀ / 2) + I.a₂ x₀ * exp (-2 * x₀ / 3))) *
    (log x / I.R)^(I.B σ) * exp (-I.C σ * (log x / I.R)^(1/2:ℝ)) := by sorry

end BKLNW
