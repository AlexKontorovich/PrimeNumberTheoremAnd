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

def first_gap_record (g P : ℕ) : Prop := first_gap g = P ∧ ∀ g' ∈ Finset.Ico 1 g, Even g' ∨ g' = 1 → first_gap g' < P


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
