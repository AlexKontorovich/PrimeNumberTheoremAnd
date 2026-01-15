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

open Real

@[blueprint
  "theta-stieltjes"
  (title := "The Chebyshev function is Stieltjes")
  (statement := /-- The function $\vartheta(x) = \sum_{p \leq x} \log p$ defines a Stieltjes function (monotone and right continuous). -/)
  (proof := /-- Trivial -/)
  (latexEnv := "sublemma")]
noncomputable def θ.Stieltjes : StieltjesFunction := {
  toFun := θ
  mono' := by sorry
  right_continuous' := by sorry
}

@[blueprint
  "rs-pre-413"
  (title := "RS-prime display before (4.13)")
  (statement := /-- $\sum_{p ≤ x} f(p) = \int_{2^-}^x \frac{f(y)}{\log y}\ d\vartheta(y)$. -/)
  (proof := /-- This follows from the definition of the Stieltjes integral. -/)
  (latexEnv := "lemma")]
theorem pre_413 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 2)) (x : ℝ) :
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range ⌊x⌋₊), f p =
      ∫ y in Set.Icc 2 x, f y / log y ∂θ.Stieltjes.measure := by sorry





end RS_prime
