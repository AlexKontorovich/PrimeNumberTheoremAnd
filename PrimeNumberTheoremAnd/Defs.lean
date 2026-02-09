import Architect
import PrimeNumberTheoremAnd.Fourier
import Mathlib.NumberTheory.Chebyshev

open ArithmeticFunction hiding log
open Nat hiding log
open Finset Topology
open BigOperators Filter Real Classical Asymptotics MeasureTheory intervalIntegral
open scoped ArithmeticFunction.Moebius ArithmeticFunction.Omega Chebyshev

blueprint_comment /--
Let $p_n$ denote the $n^{th}$ prime.
-/

noncomputable abbrev nth_prime (n : ℕ) : ℕ := Nat.nth Nat.Prime n


noncomputable abbrev Psi (x : ℝ) : ℝ := ψ x

noncomputable def M (x : ℝ) : ℝ := ∑ n ∈ Iic ⌊x⌋₊, (μ n : ℝ)

noncomputable abbrev nth_prime_gap (n : ℕ) : ℕ := nth_prime (n+1) - (nth_prime n)

def prime_gap_record (p g : ℕ) : Prop := ∃ n, nth_prime n = p ∧ nth_prime_gap n = g ∧ ∀ k, nth_prime k < p → nth_prime_gap k < g

open Classical in
@[blueprint
  "first-gap-def"
  (title := "First prime gap")
  (statement := /--
  $P(g)$ is the first prime $p_n$ for which the prime gap $p_{n+1}-p_n$ is equal to $g$, or $0$ if no such gap exists. -/)]
noncomputable def first_gap (g : ℕ) : ℕ := if h : ∃ n, nth_prime_gap n = g then nth_prime (Nat.find h) else 0

def first_gap_record (g P : ℕ) : Prop := first_gap g = P ∧ ∀ g' ∈ Finset.Ico 1 g, Even g' ∨ g' = 1 → first_gap g' ∈ Set.Ico 1 P


def HasPrimeInInterval (x h : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p ≤ x + h

def HasPrimeInInterval.log_thm (X₀ : ℝ) (k : ℝ) :=
  ∀ x ≥ X₀, HasPrimeInInterval x (x / (log x)^k)



@[blueprint
  "pi-def"
  (title := "pi")
  (statement := /-- $\pi(x)$ is the number of primes less than or equal to $x$. -/)]
noncomputable def pi (x : ℝ) : ℝ :=  Nat.primeCounting ⌊x⌋₊


@[blueprint
  "li-def"
  (title := "li and Li")
  (statement := /-- $\mathrm{li}(x) = \int_0^x \frac{dt}{\log t}$ (in the principal value sense) and $\mathrm{Li}(x) = \int_2^x \frac{dt}{\log t}$. -/)]
noncomputable def li (x : ℝ) : ℝ := lim ((𝓝[>] (0 : ℝ)).map (fun ε ↦ ∫ t in Set.diff (Set.Ioc 0 x) (Set.Ioo (1-ε) (1+ε)), 1 / log t))

@[blueprint "li-def"]
noncomputable def Li (x : ℝ) : ℝ := ∫ t in 2..x, 1 / log t


@[blueprint
  "Epsi-def"
  (title := "Equation (2) of FKS2")
  (statement := /-- $E_\psi(x) = |\psi(x) - x| / x$ -/)]
noncomputable def Eψ (x : ℝ) : ℝ := |ψ x - x| / x

noncomputable def admissible_bound (A B C R : ℝ) (x : ℝ) := A * (log x / R) ^ B * exp (-C * (log x / R) ^ ((1:ℝ)/(2:ℝ)))

@[blueprint
  "classical-bound-psi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\psi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\psi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]

  We say that it obeys a \emph{numerical bound} with parameter $\varepsilon(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\psi(x) \leq \varepsilon(x_0). \]
  -/)]
def Eψ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ admissible_bound A B C R x

def Eψ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eψ x ≤ ε

def Eψ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := Eψ.bound (ε x₀) x₀

@[blueprint
  "Epi-def"
  (title := "Equation (1) of FKS2")
  (statement := /-- $E_\pi(x) = |\pi(x) - \mathrm{Li}(x)| / \mathrm{Li}(x)$. -/)]
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
  We say that it obeys a \emph{numerical bound} with parameter $\varepsilon(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\theta(x) \leq \varepsilon(x_0). \]
  -/)]
def Eθ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ admissible_bound A B C R x

def Eθ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := ∀ x ≥ x₀, Eθ x ≤ (ε x₀)

@[blueprint "classical-bound-pi"
  (title := "Definitions 1, 5, FKS2")
  (statement := /--
  We say that $E_\pi$ satisfies a \emph{classical bound} with parameters $A, B, C, R, x_0$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq A \left(\frac{\log x}{R}\right)^B \exp\left(-C \left(\frac{\log x}{R}\right)^{1/2}\right). \]
  We say that it obeys a \emph{numerical bound} with parameter $\varepsilon(x_0)$ if for all $x \geq x_0$ we have
  \[ E_\pi(x) \leq \varepsilon(x_0). \]
  -/)]
def Eπ.classicalBound (A B C R x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ admissible_bound A B C R x

def Eπ.bound (ε x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ ε

def Eπ.numericalBound (x₀ : ℝ) (ε : ℝ → ℝ) : Prop := Eπ.bound (ε x₀) x₀

def Eπ.vinogradovBound (A B C x₀ : ℝ) : Prop := ∀ x ≥ x₀, Eπ x ≤ A * (log x) ^ B * exp (-C * (log x) ^ (3/5) / (log (log x)) ^ (1/5))


@[blueprint
  "admissible-bound-monotone"
  (title := "Admissible bound decreasing for large x")
  (statement := /--
  If $A,B,C,R > 0$ then the classical bound is monotone decreasing for $x \geq \exp( R (2B/C)^2 )$. -/)
  (proof := /-- Differentiate the bound and check the sign. -/)
  (latexEnv := "lemma")
  (discussion := 900)]
lemma admissible_bound.mono (A B C R : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C) (hR : 0 < R) :
    AntitoneOn (admissible_bound A B C R) (Set.Ici (Real.exp (R * (2 * B / C) ^ 2))) := by
  sorry

@[blueprint
  "classical-to-numeric"
  (title := "Classic bound implies numerical bound")
  (statement := /--
  A classical bound for $x \geq x_0$ implies a numerical bound for $x \geq \max(x_0, \exp( R (2B/C)^2  ))$. -/)
  (proof := /-- Immediate from previous lemma -/)
  (latexEnv := "lemma")
  (discussion := 901)]
lemma Eψ.classicalBound.to_numericalBound (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hR : 0 < R) (hEψ : Eψ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
     Eψ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦ le_trans (hEψ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
    (admissible_bound.mono A B C R hA hB hC hR (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

@[blueprint "classical-to-numeric"]
lemma Eθ.classicalBound.to_numericalBound (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hR : 0 < R) (hEθ : Eθ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eθ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦ le_trans (hEθ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
    (admissible_bound.mono A B C R hA hB hC hR (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)

@[blueprint "classical-to-numeric"]
lemma Eπ.classicalBound.to_numericalBound (A B C R x₀ x₁ : ℝ) (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
    (hR : 0 < R) (hEπ : Eπ.classicalBound A B C R x₀)
    (hx₁ : x₁ ≥ max x₀ (Real.exp (R * (2 * B / C) ^ 2))) :
    Eπ.numericalBound x₁ (fun x ↦ admissible_bound A B C R x) :=
  fun x hx ↦ le_trans (hEπ x (le_trans (le_max_left ..) (le_trans hx₁ hx)))
    (admissible_bound.mono A B C R hA hB hC hR (Set.mem_Ici.mpr (le_trans (le_max_right ..) hx₁))
        (Set.mem_Ici.mpr (le_trans (le_max_right ..) (le_trans hx₁ hx))) hx)
