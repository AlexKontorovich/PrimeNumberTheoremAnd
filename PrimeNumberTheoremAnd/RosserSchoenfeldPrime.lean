import Architect
import Mathlib.MeasureTheory.Measure.Stieltjes
import PrimeNumberTheoremAnd.SecondaryDefinitions

blueprint_comment /--
\section{The prime number bounds of Rosser and Schoenfeld}
-/

blueprint_comment /--
In this section we formalize the prime number bounds of Rosser and Schoenfeld \cite{rs-prime}.
-/

namespace RS_prime

open Chebyshev Finset Nat Real

@[blueprint
  "rs-pnt"
  (title := "A medium version of the prime number theorem")
  (statement := /-- $\vartheta(x) = x + O( x / \log^2 x)$. -/)
  (proof := /-- This in principle follows by establishing an analogue of Theorem \ref{chebyshev-asymptotic}, using mediumPNT in place of weakPNT. -/)
  (latexEnv := "theorem")
  (discussion := 597)]
theorem pnt : ∃ C, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by sorry

@[blueprint
  "rs-B"
  (title := "Meissel-Mertens constant B")
  (statement := /--
  $B := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{1}{p} - \log \log x \right)$. -/)]
noncomputable def B : ℝ :=
  lim (Filter.atTop.comap (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.range ⌊x⌋₊), 1 / p - log (log x)))


@[blueprint
  "rs-E"
  (title := "Mertens constant E")
  (statement := /--
  $E := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{\log p}{p} - \log x \right)$. -/)]
noncomputable def E : ℝ :=
  lim (Filter.atTop.comap (fun x : ℝ ↦ ∑ p ∈ Finset.filter Nat.Prime (Finset.range ⌊x⌋₊), Real.log p / p - log x))

@[blueprint
  "theta-stieltjes"
  (title := "The Chebyshev function is Stieltjes")
  (statement := /-- The function $\vartheta(x) = \sum_{p \leq x} \log p$ defines a Stieltjes function (monotone and right continuous). -/)
  (proof := /-- Trivial -/)
  (latexEnv := "sublemma")
  (discussion := 598)]
noncomputable def θ.Stieltjes : StieltjesFunction ℝ := {
  toFun := θ
  mono' := theta_mono
  right_continuous' := fun x ↦ by
    rw [ContinuousWithinAt, theta_eq_theta_coe_floor x]
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    obtain hx | hx := le_total 0 x
    · filter_upwards [Ico_mem_nhdsGE_of_mem ⟨floor_le hx, lt_floor_add_one x⟩] with y hy
      rw [theta_eq_theta_coe_floor y, floor_eq_on_Ico _ _ hy]
    · filter_upwards [Ico_mem_nhdsGE (by grind : x < 1)] with y hy
      simp [floor_of_nonpos hx, theta_eq_theta_coe_floor y, floor_eq_zero.mpr hy.2]
}

@[blueprint
  "rs-pre-413"
  (title := "RS-prime display before (4.13)")
  (statement := /-- $\sum_{p \leq x} f(p) = \int_{2}^x \frac{f(y)}{\log y}\ d\vartheta(y)$. -/)
  (proof := /-- This follows from the definition of the Stieltjes integral. -/)
  (latexEnv := "sublemma")
  (discussion := 599)]
theorem pre_413 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 2)) (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), f p =
      ∫ y in Set.Icc 2 x, f y / log y ∂θ.Stieltjes.measure := by sorry

@[blueprint
  "rs-413"
  (title := "RS equation (4.13)")
  (statement := /-- $\sum_{p \leq x} f(p) = \frac{f(x) \vartheta(x)}{\log x} - \int_2^x \vartheta(x) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-pre-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 650)]
theorem eq_413 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), f p =
      f x * θ x / log x -
      ∫ y in 2..x, θ y * deriv (fun t ↦ f t / log t) y := by sorry

@[blueprint
  "rs-414"
  (title := "RS equation (4.14)")
  (statement := /--
  $$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + \frac{2 f(2)}{\log 2} $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} - \int_2^x (\vartheta(y) - y) \frac{d}{dy} \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 600)]
theorem eq_414 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), f p =
      ∫ y in 2..x, f y / log y + 2 * f 2 / Real.log 2 +
      f x * (θ x - x) / log x -
      ∫ y in 2..x, (θ y - y) * deriv (fun t ↦ deriv (fun s ↦ f s / log s) t) y := by sorry

@[blueprint
  "rs-416"
  (title := "RS equation (4.16)")
  (statement := /--
  $$L_f := \frac{2f(2)}{\log 2} - \int_2^\infty (\vartheta(y) - y) \frac{d}{dy} (\frac{f(y)}{\log y})\ dy.$$ -/)
  (latexEnv := "sublemma")]
noncomputable def L (f : ℝ → ℝ) : ℝ :=
    2 * f 2 / Real.log 2 - ∫ y in Set.Ici 2, (θ y - y) * deriv (fun t ↦ f t / log t) y

@[blueprint
  "rs-415"
  (title := "RS equation (4.15)")
  (statement := /--
  $$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + L_f $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} + \int_x^\infty (\vartheta(y) - y) \frac{d}{dy} \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-414} and Definition \ref{rs-416}. -/)
  (latexEnv := "sublemma")
  (discussion := 601)]
theorem eq_415 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) (x : ℝ)
   (hbound : ∃ C, ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
   ∑ p ∈ filter Prime (range ⌊x⌋₊), f p = ∫ y in 2..x, f y / log y + L f +
    f x * (θ x - x) / log x + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun t ↦ deriv (fun s ↦ f s / log s) t) y := by sorry

@[blueprint
  "rs-417"
  (title := "RS equation (4.17)")
  (statement := /--
  $$\pi(x) = \frac{\vartheta(x)}{\log x} + \int_2^x \frac{\vartheta(y)\ dy}{y \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1$. -/)
  (latexEnv := "sublemma")
  (discussion := 602)]
theorem eq_417 (x : ℝ) :
    pi x = θ x / log x + ∫ y in 2..x, θ y / (y * log y ^ 2) := by sorry

@[blueprint
  "rs-418"
  (title := "RS equation (4.18)")
  (statement := /--
  $$\sum_{p \leq x} \frac{1}{p} = \frac{\vartheta(x)}{x \log x} + \int_2^x \frac{\vartheta(y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. -/)
  (latexEnv := "sublemma")
  (discussion := 652)]
theorem eq_418 (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), 1 / p =
      θ x / (x * log x) + ∫ y in 2..x, θ y * (1 + log y) / (y ^ 2 * log y ^ 2) := by sorry

@[blueprint
  "rs-419"]
theorem mertens_second_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (range ⌊x⌋₊), 1 / p - log (log x) - B) (nhds 0) := by sorry

@[blueprint
  "rs-419"
  (title := "RS equation (4.19) and Mertens' second theorem")
  (statement := /--
  $$\sum_{p \leq x} \frac{1}{p} = \log \log x + B + \frac{\vartheta(x) - x}{x \log x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. One can also use this identity to demonstrate convergence of the limit defining $B$.-/)
  (latexEnv := "sublemma")
  (discussion := 603)]
theorem eq_419 (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), 1 / p =
      log (log x) + B + (θ x - x) / (x * log x) - ∫ y in 2..x, (θ y - y) * (1 + log y) / (y ^ 2 * log y ^ 2) := by sorry

@[blueprint
  "rs-419"]
theorem mertens_second_theorem' :
    ∃ C, ∀ x, |∑ p ∈ filter Prime (range ⌊x⌋₊), 1 / p - log (log x)| ≤ C := by sorry

@[blueprint
  "rs-420"]
theorem mertens_first_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (range ⌊x⌋₊), Real.log p / p - log x - E) (nhds 0) := by sorry

@[blueprint
  "rs-420"
  (title := "RS equation (4.19) and Mertens' first theorem")
  (statement := /--
  $$\sum_{p \leq x} \frac{\log p}{p} = \log x + E + \frac{\vartheta(x) - x}{x} $$
  $$ - \int_2^x \frac{(\vartheta(y)-y)\ dy}{y^2}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = \log t / t$.  Convergence will need Theorem \ref{rs-pnt}. -/)
  (latexEnv := "sublemma")
  (discussion := 604)]
theorem eq_420 (x : ℝ) :
    ∑ p ∈ filter Prime (range ⌊x⌋₊), Real.log p / p =
      log x + E + (θ x - x) / x - ∫ y in 2..x, (θ y - y) / (y ^ 2) := by sorry

@[blueprint
  "rs-420"]
theorem mertens_first_theorem' :
    ∃ C, ∀ x, |∑ p ∈ filter Prime (range ⌊x⌋₊), Real.log p / p - Real.log x| ≤ C := by sorry


end RS_prime
