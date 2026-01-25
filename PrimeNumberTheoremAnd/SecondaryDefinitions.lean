import Architect
import Mathlib.Topology.Order.Basic
import Mathlib.NumberTheory.PrimeCounting

import PrimeNumberTheoremAnd.PrimaryDefinitions


blueprint_comment /--
\section{Definitions}
-/

blueprint_comment /--
In this section we define the basic types of secondary estimates we will work with in the project.
-/

open Real Finset

/- Standard arithmetic functions. TODO: align this with notation used elsewhere in PNT+ -/

@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /-- $\pi(x)$ is the number of primes less than or equal to $x$. -/)]
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊

open Topology

@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /-- $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the principal value sense) and $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ := lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t

@[blueprint
  "log_upper"
  (title := "Log upper bound")
  (statement := /-- For $t > -1$, one has $\log (1+t) \leq t$. -/)
  (proof := /-- This follows from the mean value theorem. -/)
  (latexEnv := "sublemma")]
theorem log_le (t : ℝ) (ht : t > -1) : log (1 + t) ≤ t :=
  (Real.log_le_sub_one_of_pos (neg_lt_iff_pos_add'.mp ht)).trans add_tsub_le_left

@[blueprint
  "log_lower_1"
  (title := "First log lower bound")
  (statement := /-- For $t \geq 0$, one has $t - \frac{t^2}{2} \leq \log(1+t)$. -/)
  (proof := /-- Use Taylor's theorem with remainder and the fact that the second derivative of $\log(1+t)$ is at most $1$ for $t \geq 0$.-/)
  (latexEnv := "sublemma")
  (discussion := 765)]
theorem log_ge {t : ℝ} (ht : 0 ≤ t) :
    t - t ^ 2 / 2 ≤ log (1 + t) := by
  rcases ht.eq_or_lt with rfl|ht
  · simp
  -- Define the function $f(t) = \ln(1+t) - (t - t^2/2)$ and show that $f(t) \geq 0$ for $t \geq 0$.
  set f : ℝ → ℝ := fun t => Real.log (1 + t) - (t - t^2 / 2)
  have hf_deriv_pos : ∀ t > 0, 0 ≤ deriv f t := by
    intro t ht
    unfold f
    norm_num [ add_comm, show t + 1 ≠ 0 by linarith ]
    ring_nf
    nlinarith [ inv_mul_cancel₀ ( by linarith : ( 1 + t ) ≠ 0 ) ]
  -- Since $f$ is differentiable and its derivative is non-negative for $t > 0$, we can apply the Mean Value Theorem to $f$ on the interval $[0, t]$.
  have h_mvt : ∃ c ∈ Set.Ioo 0 t, deriv f c = (f t - f 0) / (t - 0) := by
    apply exists_deriv_eq_slope _ ht <;> unfold f
    · exact fun x hx ↦ ContinuousAt.continuousWithinAt (by fun_prop (disch := grind))
    · exact fun x hx ↦ DifferentiableAt.differentiableWithinAt (by fun_prop (disch := grind))
  norm_num +zetaDelta at h_mvt
  obtain ⟨ c, ⟨ hc₁, hc₂ ⟩, hc ⟩ := h_mvt
  nlinarith [ hf_deriv_pos c hc₁, mul_div_cancel₀ ( Real.log ( 1 + t ) - ( t - t ^ 2 / 2 ) ) ( by linarith : t ≠ 0 ) ]

@[blueprint
  "log_lower_2"
  (title := "Second log lower bound")
  (statement := /-- For $0 \leq t \leq t_0 < 1$, one has $\frac{t}{t_0} \log (1-t_0) \leq \log(1-t)$. -/)
  (proof := /-- Use concavity of log.-/)
  (latexEnv := "sublemma")
  (discussion := 766)]
theorem log_ge'
    (t t₀ : ℝ) (ht : 0 ≤ t) (ht0 : t ≤ t₀) (ht0' : t₀ < 1) :
    (t / t₀) * log (1 - t₀) ≤ log (1 - t) := by
    sorry

@[blueprint
  "symm_inv_log"
  (title := "Symmetrization of inverse log")
  (statement := /-- For $0 < t \leq 1/2$, one has $| \frac{1}{\log(1+t)} + \frac{1}{\log(1-t)}| \leq \frac{\log(4/3)}{4/3}$. -/)
  (proof := /-- The expression can be written as $\frac{|\log(1-t^2)|}{|\log(1-t)| |\log(1+t)|}$. Now use the previous upper and lower bounds, noting that $t^2 \leq 1/4$. -/)
  (latexEnv := "sublemma")
  (discussion := 767)]
theorem symm_inv_log
    (t : ℝ) (ht : 0 < t) (ht' : t ≤ 1 / 2) :
    |1 / log (1 + t) + 1 / log (1 - t)| ≤ log (4 / 3) / (4 / 3) := by
    sorry

@[blueprint
  "li-approx"
  (title := "li approximation")
  (statement := /-- If $x \geq 2$ and $0 < \eps \leq 1$, then $\mathrm{li}(x) = \int_{[0,x] \backslash [-\eps, \eps]} \frac{dt}{\log t} + O_*( \frac{\log(4/3)}{4/3} \eps)$. -/)
  (proof := /-- Symmetrize the principal value integral around 1 using the previous lemma. -/)
  (latexEnv := "sublemma")
  (discussion := 768)]
theorem li.eq
    (x ε : ℝ) (hx : x ≥ 2) (hε1 : 0 < ε) (hε2 : ε ≤ 1) : ∃ E,
    li x = ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1 - ε) (1 + ε)), 1 / log t + E ∧
    |E| ≤ log (4 / 3) / (4 / 3) * ε := by
    sorry

@[blueprint
  "li_minus_Li"
  (title := "li minus Li")
  (statement := /-- $\li(x) - \Li(x) = \li(2)$. -/)
  (proof := /-- This follows from the previous estimate. -/)
  (latexEnv := "remark")
  (discussion := 758)]
theorem li.sub_Li
    (x : ℝ) (h2x : 2 ≤ x) :
    li x - Li x = li 2 := by
    sorry

@[blueprint
  "Ramanujan-Soldner-constant"
  (title := "Ramanujan-Soldner constant")
  (statement := /-- $\li(2) = 1.0451\dots$. -/)
  (proof := /-- Use Sublemma \ref{li-approx} and some numerical integration. -/)
  (latexEnv := "lemma")
  (discussion := 759)]
theorem li.two_approx : li 2 ∈ Set.Icc 1.0451 1.0452 := by
  sorry


@[blueprint
  "theta-def"
  (title := "theta")
  (statement := /-- $\theta(x) = \sum_{p \leq x} \log p$ where the sum is over primes $p$. -/)]
noncomputable def θ (x : ℝ) := Chebyshev.theta x


@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /-- $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| / \mathrm{Li}(x)$ -/)]
noncomputable def Eπ (x : ℝ) : ℝ := |pi x - Li x| / (x / log x)


@[blueprint
  "Etheta-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\theta(x) = |\theta(x) - x| / x$ -/)]
noncomputable def Eθ (x : ℝ) : ℝ := |θ x - x| / x


@[blueprint
  "classical-bound-theta"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\theta$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  We say that it obeys a \emph{numerical bound} with parameter $ε(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq ε(x_0). \]
  -/)]
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

@[blueprint "classical-bound-pi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  We say that it obeys a \emph{numerical bound} with parameter $ε(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq ε(x_0). \]
  -/)]
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))


def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)
