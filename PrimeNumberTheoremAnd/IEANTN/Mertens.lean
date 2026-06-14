import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Group.Submonoid.BigOperators
import PrimeNumberTheoremAnd.EulerMaclaurin
import PrimeNumberTheoremAnd.IEANTN.LiSeries
import Architect

open scoped Topology

theorem Filter.EventuallyEq.iff_eventually {α : Type _} {β : Type _} {l : Filter α} {f g : α → β} : f =ᶠ[l] g ↔ ∀ᶠ (x : α) in l, f x = g x := by rfl


namespace Real

open Filter Asymptotics

theorem inv_log_eq_o_one : (fun x ↦ 1 / log x) =o[atTop] (fun _ ↦ (1:ℝ)) := by
    rw [isLittleO_one_iff]
    convert tendsto_log_atTop.inv_tendsto_atTop using 1
    ext; simp

theorem one_eq_o_log_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log (log x)) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp (tendsto_log_atTop.comp tendsto_log_atTop)

end Real

section IntegralTest

/-! The integral test for convergence. -/

open MeasureTheory Set

variable {f : ℝ → ℝ}

theorem AntitoneOn.sum_range_le_integral (N : ℕ) (anti : AntitoneOn f (Icc 0 (N : ℝ)))
    (integrable : IntegrableOn f (Ioi 0) volume) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑ n ∈ Finset.range N, f ((n + 1 : ℕ)) ≤ ∫ x in Ioi 0, f x := by
  trans ∫ x in 0..N, f x
  · convert AntitoneOn.sum_le_integral (x₀ := 0) (a := N) (f := f) (by simpa) using 2
    · simp
    · ring
  · rw [intervalIntegral.integral_of_le (by simp)]
    apply setIntegral_mono_set integrable _ (Ioc_subset_Ioi_self.eventuallyLE)
    · filter_upwards [ae_restrict_mem (by measurability)] with t ht using nonneg t ht

theorem AntitoneOn.summable_of_integrable (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    Summable (fun (n : ℕ) ↦ f n ) := by
  rw [← summable_nat_add_iff 1]
  apply summable_of_sum_range_le
  · exact fun n ↦ nonneg _ (by simp; grind)
  · exact fun N ↦ (anti.mono Icc_subset_Ici_self).sum_range_le_integral _ integrable nonneg

theorem AntitoneOn.tsum_add_one_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑' (n : ℕ),  f (n + 1 : ℕ) ≤ ∫ x in Ioi 0, f x  := by
  apply Summable.tsum_le_of_sum_range_le
  · exact summable_nat_add_iff _|>.mpr (anti.summable_of_integrable integrable nonneg)
  · exact fun N ↦ (anti.mono Icc_subset_Ici_self).sum_range_le_integral _ integrable nonneg

theorem AntitoneOn.tsum_le_integral (anti : AntitoneOn f (Ici 0))
    (integrable : IntegrableOn f (Ioi 0)) (nonneg : ∀ t ∈ Ioi 0, 0 ≤ f t) :
    ∑' (n : ℕ),  f n ≤ f 0 + ∫ x in Ioi 0, f x  := by
  rw [(anti.summable_of_integrable integrable nonneg).tsum_eq_zero_add]
  gcongr
  · simp
  · exact anti.tsum_add_one_le_integral integrable nonneg

end IntegralTest

namespace Mertens

blueprint_comment /--
\section{Mertens' theorems}

In this section we give explicit versions of Mertens' theorems:
\begin{itemize}
\item Mertens' first theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x + O(1)$.
\item Mertens' first theorem (prime form): $\sum_{p \leq x} \frac{\log p}{p} = \log x + O(1)$.
\item Mertens' second theorem (von Mangoldt form): $\sum_{n \leq x} \frac{\Lambda(n)}{n \log n} = \log \log x + \gamma + O(1/\log x)$.
\item Mertens' second theorem (prime form): $\sum_{p \leq x} \frac{1}{p} = \log \log x + M + O(1/\log x)$, where $M$ is the Meissel-Mertens constant.
\item Mertens' third theorem: $\prod_{p \leq x} (1 - \frac{1}{p}) = e^{-\gamma}/\log x + O(1/\log^2 x)$.
\end{itemize}
We aim to upstreaming these results to Mathlib.  In particular, the arguments here should be self-contained and written for efficiency, coherency, and clarity.  As such, extensive use of AI tools is \emph{strongly discouraged} in this section.

The arguments here are drawn from Leo Goldmakher's ``A quick proof of Mertens' theorem'' from https://web.williams.edu/Mathematics/lg5/mertens.pdf

The unfinished formalization of Mertens' theorems by Arend Mellendijk in https://github.com/FLDutchmann/Analytic/blob/main/Analytic/Mertens.lean may also be relevant here.
-/


open Real Finset Filter Asymptotics
open ArithmeticFunction hiding log

lemma sum_Ioc_one_eq_sum_Ioc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf : f 1 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Ioc 0 x, f n := by
  rw [(by rfl : Ioc 0 x = Icc 1 x), ← add_sum_Ioc_eq_sum_Icc hx]
  simpa

@[blueprint
  "Mertens-sum-log"
  (title := "Partial sum of logarithm identity")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n = x \log x - (\{ x \}-1/2) \log x - x + 1 + \int_1^x (\{ t \}-1/2) \frac{dt}{t} $$
(NOTE: this identity is not actually needed in the proof of Mertens' theorems, but may be worth recording nevertheless.)
 -/)
  (proof := /-- Apply the Euler-Maclaurin formula.
 -/)
  (latexEnv := "lemma")
  (discussion := 1303)]
theorem sum_log_eq {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n =
      x * log x - (x - ⌊x⌋₊ - 1 / 2) * log x - x + 1 + ∫ t in 1..x, (t - ⌊t⌋₊ - 1 / 2) / t := by
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  have : 1 = ⌊(1 : ℝ)⌋₊ := by simp
  nth_rw 1 [this]
  rw [sum_eq_integral_add_integral_deriv (by norm_num) hx (fun _ _ ↦ (by fun_prop (disch := grind)))]
  · simp only [log_one, B1, Nat.floor_one, Nat.cast_one, sub_self, zero_sub,
    RCLike.ofReal_real_eq_id, id_eq, mul_neg, zero_mul, neg_zero, integral_log, mul_zero, sub_zero,
    deriv_log']
    ring_nf
    congr
    ext
    ring
  · simp only [deriv_log', Set.uIcc_of_le hx]
    fun_prop (disch := grind)

@[blueprint
  "Mertens-sum-log-le"
  (title := "Partial sum of logarithm upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n \leq x \log x.$$
 -/)
  (proof := /-- Trivial since $\log n \leq \log x$.
 -/)
  (latexEnv := "lemma")
  (discussion := 1304)]
theorem sum_log_le {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≤ x * log x := by
  calc
  _ ≤ ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log x := by
    refine sum_le_sum fun n hn ↦ ?_
    simp only [mem_Ioc] at hn
    exact log_le_log (by exact_mod_cast hn.1) (Nat.le_floor_iff (by linarith)|>.mp hn.2)
  _ = ⌊x⌋₊ * log x := by simp
  _ ≤ _ := by
    gcongr
    · exact log_nonneg hx
    · exact Nat.floor_le (by linarith)


lemma integral_log_le {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, log t ≤ log b * (b - a) := by
  apply le_of_abs_le
  have : ∀ t ∈ Set.uIoc a b, ‖log t‖ ≤ log b := by
    intro t ht
    rw [Set.uIoc_of_le hab, Set.mem_Ioc] at ht
    rw [norm_of_nonneg <| log_nonneg (by linarith)]
    gcongr <;> linarith
  grw [← norm_eq_abs, intervalIntegral.norm_integral_le_of_norm_le_const this,
    abs_of_nonneg (by linarith)]

@[blueprint
  "Mertens-sum-log-ge"
  (title := "Partial sum of logarithm lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n \geq x \log x - 2 x.$$
 -/)
  (proof := /-- We have
 \begin{align*}
 \sum_{n \leq x} \log n &= \sum_{2 \leq n \leq \lfloor x \rfloor} \log n \\
 &\geq \sum_{2 \leq n \leq \lfloor x \rfloor} \int_{n-1}^n \log t \, dt \\
 &= \int_1^{\lfloor x \rfloor} \log t \, dt \\
 &\geq \int_1^x \log t\ dt - \log x \\
 &= x \log x - x - \log x \\
 &\geq x \log x - 2 x.
\end{align*}
Here we use the monotonicity of $\log n$ (and its vanishing at $n=1$) and the crude bound $\log x \leq x$. Note: the tools at Mathlib.Analysis.SumIntegralComparisons may be useful.
 -/)
  (latexEnv := "corollary")
  (discussion := 1305)]
theorem sum_log_ge {x : ℝ} (hx : 1 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n ≥ x * log x - 2 * x := by
  have one_le_floor : 1 ≤ ⌊x⌋₊ := by simpa
  calc
  _ = ∑ n ∈ Icc 1 ⌊ x ⌋₊, log n := by rfl
  _ = ∑ n ∈ Ico (1 + 1) (⌊ x ⌋₊ + 1), log n := by
    rw [← add_sum_Ioc_eq_sum_Icc one_le_floor]
    simp
    rfl
  _ = ∑ n ∈ Ico 1 ⌊ x ⌋₊, log ((n + 1 : ℕ)) := by
    rw [← Finset.sum_Ico_add']
  _ ≥ ∫ t in 1..⌊x⌋₊, log t := by
    convert MonotoneOn.integral_le_sum_Ico one_le_floor ?_|>.ge
    · norm_cast
    · exact StrictMonoOn.monotoneOn (strictMonoOn_log.mono fun y hy ↦ (by simp_all; linarith))
  _ = (∫ t in 1..x, log t) - ∫ t in ⌊x⌋₊..x, log t := by
    nth_rw 3 [intervalIntegral.integral_symm]
    rw [sub_neg_eq_add, intervalIntegral.integral_add_adjacent_intervals] <;> exact intervalIntegral.intervalIntegrable_log'
  _ ≥ (∫ t in 1..x, log t) - log x := by
    gcongr
    grw [integral_log_le (by simpa) (Nat.floor_le (by linarith))]
    nth_rw 2 [← mul_one (log x)]
    gcongr
    · exact log_nonneg hx
    · linarith [Nat.lt_floor_add_one x]
  _ ≥ x * log x - x - log x := by simp
  _ ≥ _ := by linarith [log_le_self (by linarith : 0 ≤ x)]

@[blueprint
  "Mertens-sum-log-eq-log-factorial"
  (title := "Partial sum of logarithm as logarithm of factorial")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \log n = \log(\lfloor x \rfloor!). $$
 -/)
  (proof := /-- Follows from the definition of the factorial function.  Is not needed for the Mertens theorems, but is a natural fact to have.
 -/)
  (latexEnv := "proposition")
  (discussion := 1315)]
theorem sum_log_eq_log_factorial (x : ℝ) :
    ∑ n ∈ Ioc 0 ⌊ x ⌋₊, log n = log (Nat.floor x).factorial := by
    rw [←prod_Ico_id_eq_factorial, ←log_prod, prod_natCast]
    · congr
    intro x hx
    simp at hx ⊢; grind

@[blueprint
  "Mertens-sum-log-eq-sum-mangoldt"
  (title := "Partial sum of logarithm as sum of $\\Lambda(d)/d$")
  (statement := /-- For any real $x$, one has
$$ \sum_{n \leq x} \log n = \sum_{d \leq x} \Lambda(d) \lfloor \frac{x}{d} \rfloor.$$
-/)
  (proof := /-- We have
\begin{align*}
\sum_{n \leq x} \log n
&= \sum_{n \leq x} \sum_{d \mid n} \Lambda(d)
= \sum_{d \leq x} \Lambda(d) \sum_{n \leq x, d \mid n} 1
= \sum_{d \leq x} \Lambda(d) \left\lfloor \frac{x}{d} \right\rfloor.
\end{align*}
 -/)
  (latexEnv := "lemma")
  (discussion := 1306)]
theorem sum_log_eq_sum_mangoldt {x : ℝ} :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, log n = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
  have : ∀ n : ℕ, log n = (Λ * zeta) n := by simp [vonMangoldt_mul_zeta]
  simp_rw [this, sum_Ioc_mul_zeta_eq_sum, ← Nat.floor_div_natCast]

@[blueprint
  "Mertens-first-error-mangoldt"
  (title := "The remainder term in Mertens first theorem (von Mangoldt form)")
  (statement := /-- We define $E_{1,\Lambda}(x) := \sum_{d \leq x} \frac{\Lambda(d)}{d} - \log x$.
-/)]
noncomputable abbrev E₁Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x

theorem sum_mangoldt_div_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d = log x + E₁Λ x := by
    grind

@[blueprint
  "Mertens-first-error-mangoldt-ge"
  (title := "Partial sum of $\\Lambda(d)/d$ lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,\Lambda}(x) \geq - 2.$$
-/)
  (proof := /-- Insert Lemma \ref{Mertens-sum-log-eq-sum-mangoldt} into Lemma \ref{Mertens-sum-log-ge} and lower bound $x/d$ by $\lfloor x/d \rfloor$.
  -/)
  (latexEnv := "corollary")
  (discussion := 1307)]
theorem E₁Λ.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x  ≥ -2 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d  ≥ x * (log x - 2) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≥ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * ⌊x / d⌋₊ := by
    gcongr
    · exact vonMangoldt_nonneg
    · exact Nat.floor_le <| div_nonneg (by linarith) (by linarith)
  _ ≥ x * log x - 2 * x :=
    sum_log_eq_sum_mangoldt ▸ sum_log_ge hx
  _ = _ := by ring



@[blueprint
  "Mertens-first-error-mangoldt-le"
  (title := "Partial sum of $\\Lambda(d)/d$ upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,\Lambda}(x) \leq \log 4 + 4.$$
-/)
  (proof := /-- Insert Lemma \ref{Mertens-sum-log-eq-sum-mangoldt} into Lemma \ref{Mertens-sum-log-le} and upper bound $x/d$ by $\lfloor x/d \rfloor + 1$, and use the Mathlib bound $\psi(x) \leq (\log 4 + 4) x$.
  -/)
  (latexEnv := "corollary")
  (discussion := 1308)]
theorem E₁Λ.le {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ log 4 + 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + log 4 + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
  _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
    rw [Finset.mul_sum]
    ring_nf
  _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
    gcongr
    · exact vonMangoldt_nonneg
    · exact Nat.lt_floor_add_one _|>.le
  _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
    simp_rw [mul_add, mul_one]
    rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
  _ ≤ x * log x + (log 4 + 4) * x := by
    gcongr
    · exact sum_log_le hx
    · exact Chebyshev.psi_le_const_mul_self (by linarith)
  _ = _ := by ring

@[blueprint
  "Mertens-first-theorem-mangoldt"
  (title := "Mertens' first theorem (von Mangoldt form)")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x + O(1). $$
-/)
  (proof := /-- Immediate from previous two corollaries.
  -/)
  (latexEnv := "corollary")
  (discussion := 1309)]
theorem sum_mangoldt_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d - log x| ≤ log 4 + 4 := by
  grind [E₁Λ.le hx, E₁Λ.ge hx, log_nonneg]

theorem E₁Λ.bounded' : ∃ c > 0, ∀ x ≥ 1, |E₁Λ x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun x hx ↦ sum_mangoldt_div_eq_log hx⟩



@[blueprint
  "Mertens-first-error-mangoldt"
  (discussion := 1309)]
theorem E₁Λ.bounded : E₁Λ =O[atTop] (fun _ ↦ (1:ℝ)) := by
  simp only [isBigO_iff, norm_eq_abs, norm_one, mul_one,
    eventually_atTop, ge_iff_le]
  exact ⟨log 4 + 4, 1, fun _ hx ↦ sum_mangoldt_div_eq_log hx⟩

theorem one_eq_o_log : (fun _ ↦ (1:ℝ)) =o[atTop] (fun x ↦ log x) := by
    simp only [isLittleO_one_left_iff, norm_eq_abs]
    exact tendsto_abs_atTop_atTop.comp tendsto_log_atTop

@[blueprint
  "Mertens-first-error-mangoldt"
  (discussion := 1309)]
theorem sum_mangoldt_div_eq_log' :
    (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / d) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert E₁Λ.bounded using 1

@[blueprint
  "Mertens-first-error-prime"
  (title := "The remainder term in Mertens first theorem (prime form)")
  (statement := /-- We define $E_{1,p}(x) := \sum_{p \leq x} \frac{\log p}{p} - \log x$.
-/)]
noncomputable abbrev E₁p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x

theorem sum_log_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p = log x + E₁p x := by
    grind

@[blueprint
  "Mertens-first-error-prime-le-mangoldt"
  (title := "Prime error for Mertens first theorem bounded by von Mangoldt error")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,p}(x) \leq E_{1,\Lambda}(x). $$
-/)
  (proof := /-- Drop all terms in Lemma \ref{Mertens-sum-log-eq-sum-mangoldt} arising from prime powers.
  -/)
  (latexEnv := "corollary")
  (discussion := 1311)]
theorem E₁p.le_E₁Λ (x : ℝ) :
    E₁p x ≤ E₁Λ x := by
    unfold E₁p E₁Λ; rw [sum_filter]
    gcongr with p _
    split_ifs with hp
    · simp [vonMangoldt_apply_prime hp]
    have : 0 ≤ Λ p := vonMangoldt_nonneg
    positivity

@[blueprint
  "Mertens-first-error-prime-le"
  (title := "Partial sum of $\\frac{\\log p}{p}$ upper bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,p}(x) \leq \log 4 + 4.$$
-/)
  (proof := /-- Drop all terms in Lemma \ref{Mertens-sum-mangoldt-div-le} arising from prime powers.
  -/)
  (latexEnv := "corollary")]
theorem E₁p.le {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≤ log 4 + 4 := by
    linarith [E₁Λ.le hx, E₁p.le_E₁Λ x]

noncomputable abbrev E₁ : ℝ := ∑' p : ℕ, if p.Prime then (log p) / (p*(p-1)) else 0

lemma E₁.summand_nonneg (p : ℕ) : 0 ≤ if p.Prime then (log p) / (p*(p-1)) else 0 := by
  split_ifs with h
  · refine div_nonneg (log_natCast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) ?_)
    suffices 1 ≤ (p : ℝ) by linarith
    exact_mod_cast h.one_le
  · rfl

@[blueprint
  "E1_summable"
  (title := "$E_1$ summable")
  (statement := /-- The series $E_1 := \sum_p \frac{\log p}{p(p-1)}$ converges. -/)
  (proof := /-- We have $\sum_{n=2}^\infty \frac{\log n}{n(n-1)}$ converges by comparison with $\sum_{n=2}^\infty \frac{2\log n}{n^2}$, which converges by the integral test.  By a further application of comparison test we can conclude that $E_1$ converges as well.
  Alternatively bound $\log n$ by $2\sqrt n$ and use the existing Mathlib API for $\sum n^{-3/2}$.-/)
  (latexEnv := "proposition")
  (discussion := 1352)]
theorem E₁.summable : Summable (fun p : ℕ ↦ if p.Prime then (log p) / (p*(p-1)) else 0) := by
  refine (Real.summable_one_div_nat_rpow.mpr (by norm_num: 1 < (3 : ℝ) / 2)|>.const_div
    4).of_nonneg_of_le E₁.summand_nonneg fun n ↦ ?_
  split_ifs with h
  · grw [Real.log_le_rpow_div (Nat.cast_nonneg _) (by norm_num : 0 < (1 : ℝ) / 2)]
    · have denom : (n : ℝ) * ((n : ℝ) - 1) ≥ n ^ 2/ 2 := by
        rw [sq, mul_div_assoc]
        gcongr
        suffices (n : ℝ) ≥ 2 by linarith
        exact_mod_cast h.two_le
      grw [denom]
      · apply le_of_eq
        rw [← Real.rpow_natCast]
        field_simp
        rw [mul_div_assoc, ← Real.rpow_sub (mod_cast h.pos)]
        norm_num
        rw [Real.rpow_neg (Nat.cast_nonneg _)]
        field
      · exact div_pos (pow_pos (mod_cast h.pos) _) (by norm_num)
    · apply mul_nonneg (Nat.cast_nonneg _)
      suffices 1 ≤ (n : ℝ) by linarith
      exact_mod_cast h.one_le
  · positivity

private lemma antitoneOn_log_div_sq :
    AntitoneOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ici 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp at ht
    have : (t + 2) ≠ 0 := by simp; linarith
    fun_prop (disch := grind)
  · refine fun t ht ↦ DifferentiableAt.differentiableWithinAt ?_
    simp at ht
    have : (t + 2) ^ 2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · intro t ht
    simp at ht
    rw [deriv_fun_div (by fun_prop (disch := grind)) (by fun_prop) (by simp; grind), deriv_comp_add_const, deriv_log]
    simp
    field_simp
    simp only [mul_zero, tsub_le_iff_right, zero_add]
    rw [← log_rpow (by linarith), ← log_exp 1, rpow_ofNat]
    gcongr
    nlinarith [exp_one_lt_three]

private lemma log_div_sq_nonneg :
    ∀ t ∈ Set.Ioi 0, 0 ≤ log (t + 2) / (t + 2) ^ 2 := by
  exact fun t ht ↦  div_nonneg (log_nonneg (by simp_all; linarith)) (by positivity)

private lemma log_div_sq_is_deriv :
    ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ (-log (t + 2) - 1) / (t + 2)) (log (x + 2) / (x + 2) ^ 2) x := by
  intro t ht
  simp at ht
  apply HasDerivAt.comp_add_const (f := (fun t ↦ (-log t - 1)/ t)) t 2
  convert HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
    · ext; ring
    · simp

private lemma integrableOn_log_div_sq :
    MeasureTheory.IntegrableOn (fun t ↦ log (t + 2) / (t + 2) ^ 2) (Set.Ioi 0) := by
  exact MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq

private lemma integral_log_div_sq :
    ∫ t in Set.Ioi 0, log (t + 2) / (t + 2) ^ 2 = (log 2 + 1) / 2 := by
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' log_div_sq_is_deriv log_div_sq_nonneg tendsto_antideriv_log_div_sq]
  ring_nf

private lemma summable_log_div_sq :
    Summable (fun (n : ℕ)↦ log (n + 3) / (n + 3) ^ 2) := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  suffices Summable (fun (n : ℕ) ↦ g n ) by
    convert summable_nat_add_iff 1|>.mpr this using 2
    unfold g
    push_cast
    ring_nf
  exact antitoneOn_log_div_sq.summable_of_integrable integrableOn_log_div_sq log_div_sq_nonneg

private lemma sum_log_div_sq_le :
    ∑' (n : ℕ), log (n + 3) / (n + 3) ^2 ≤ (log 2 + 1) / 2 := by
  let g : ℝ → ℝ := (fun n ↦ log (n + 2) / (n + 2) ^ 2)
  calc
  _ = ∑' (n : ℕ), g (n + 1 : ℕ):= by
    unfold g
    congr
    push_cast
    ring_nf
  _ ≤ ∫ x in Set.Ioi 0, g x := by
    exact antitoneOn_log_div_sq.tsum_add_one_le_integral integrableOn_log_div_sq log_div_sq_nonneg
  _ = _ := by
    exact integral_log_div_sq

@[blueprint
  "E1_bound"
  (title := "Upper bound on $E_1$")
  (statement := /-- One has $E_1 \leq \frac{5 \log 2 + 3}{4}$-/)
  (proof := /-- We can bound $E_1 \leq \sum_{n=2}^\infty \frac{\log n}{n(n-1)} \leq \frac{\log 2}{2} + \frac{3}{2} \sum_{n=3}^\infty \frac{\log n}{n^2}$.  Calculus shows that $\log x / x^2$ is decreasing for $x \geq 2 > e^{1/2}$, so we can bound $\sum_{n=3}^\infty \frac{\log n}{n^2} \leq \int_2^\infty \frac{\log t}{t^2}\ dt = \frac{\log 2+1}{2}$.-/)
  (latexEnv := "proposition")
  (discussion := 1316)]
theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
  unfold E₁
  calc
  _ = log 2 / 2 + ∑' (n : ℕ), if (n + 3).Prime then log (n + 3) / ((n + 3) * (n + 2)) else 0 := by
    rw [← E₁.summable.sum_add_tsum_nat_add 3, (by rfl : range 3 = {0, 1, 2})]
    simp [Nat.prime_two]
    ring_nf
  _ ≤ log 2 / 2 + ∑' (n : ℕ), (3 / 2) * (log (n + 3) / (n + 3) ^ 2) := by
    gcongr with n
    · convert summable_nat_add_iff 3|>.mpr E₁.summable using 4
      · norm_cast
      · push_cast; ring
    · exact summable_log_div_sq.mul_left _
    · split_ifs with h
      · grw [(by linarith : (n + 2 : ℝ) ≥ 2 * (n + 3) / 3)]
        · field_simp
          rfl
        · exact log_nonneg (by grind)
      · exact mul_nonneg (by norm_num) (div_nonneg (log_nonneg (by grind)) (by positivity))
  _ = log 2 / 2 + (3 / 2) * ∑' (n : ℕ), log (n + 3) / (n + 3) ^ 2 := by
    rw [tsum_mul_left]
  _ ≤ _ := by
    grw [sum_log_div_sq_le]
    ring_nf
    rfl

theorem E₁.nonneg : E₁ ≥ 0 :=
  tsum_nonneg E₁.summand_nonneg

@[blueprint
  "Mertens-first-error-prime-ge"
  (title := "Partial sum of $\\frac{\\log p}{p}$ lower bound")
  (statement := /-- For any $x \geq 1$, one has
$$ E_{1,\Lambda}(x) \leq E_{1,p}(x) + E_1$$
and thus
$$ E_{1,p}(x) \geq -2 - E_1$$
where
$$ E_1 := \sum_{p} \frac{\log p}{p(p-1)}. $$
-/)
  (proof := /-- Use the triangle inequality and the geometric series formula to estimate in Lemma \ref{Mertens-sum-mangoldt-div-le} arising from prime powers.
  -/)
  (latexEnv := "corollary")
  (discussion := 1312)]
theorem E₁Λ.le_E₁p_add_E₁ {x : ℝ} (hx : 1 ≤ x) :
    E₁Λ x ≤ E₁p x + E₁ := by
  unfold E₁Λ E₁p
  suffices ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / p + E₁ by linarith
  simp_rw [vonMangoldt_apply, ite_div, zero_div, ← sum_filter, Chebyshev.sum_PrimePow_eq_sum_sum _ (by linarith)]
  calc
  _ = ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x ^ (1 / (k : ℝ))⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    refine sum_congr rfl fun k hk ↦ sum_congr rfl fun p hp ↦ ?_
    rw [Nat.Prime.pow_minFac (by simp_all) (by simp_all; linarith)]
  _ ≤ ∑ k ∈ Icc 1 ⌊log x / log 2⌋₊, ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    gcongr with k hk
    apply rpow_le_self_of_one_le hx
    simp only [mem_Icc] at hk
    exact div_le_one₀ (by norm_cast; linarith)|>.mpr (mod_cast hk.1)
  _ ≤ ∑ k ∈ Icc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    apply sum_le_sum_of_subset_of_nonneg
    · gcongr
      exact le_max_right ..
    · exact fun _ _ _ ↦ sum_nonneg fun _ _ ↦ (by positivity)
  _ = ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, (log p / p) + ∑ k ∈ Ioc 1 (max 1 ⌊log x / log 2⌋₊), ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p ^ k : ℕ) := by
    rw [← add_sum_Ioc_eq_sum_Icc (le_max_left ..)]
    simp
  _ ≤ _ := by
    gcongr
    rw [sum_comm]
    conv => lhs; arg 2; ext p; arg 2; ext k; rw [← mul_one_div, Nat.cast_pow, ← one_div_pow]
    simp_rw [← mul_sum]
    calc
    _ ≤ ∑ p ∈ Ioc 0 ⌊x⌋₊ with Nat.Prime p, log p / (p * (p - 1)) := by
      gcongr with p hp
      simp only [mem_filter, mem_Ioc] at hp
      conv => rhs; rw [← mul_one_div]
      gcongr
      rw [(by rfl : Ioc 1 (max 1 ⌊log x / log 2⌋₊) = Ico 2 (max 1 ⌊log x / log 2⌋₊  + 1))]
      grw [geom_sum_Ico_le_of_lt_one (by simp)]
      · apply le_of_eq
        have : (p : ℝ) ≠ 0 := by exact_mod_cast hp.1.1.ne.symm
        field
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast hp.2.one_lt)
    _ ≤ _ := by
      rw [sum_filter]
      exact E₁.summable.sum_le_tsum _ fun p hp ↦ E₁.summand_nonneg p

theorem E₁p.ge {x : ℝ} (hx : 1 ≤ x) :
    E₁p x ≥ -2 - E₁ := by
    linarith [E₁Λ.le_E₁p_add_E₁ hx, E₁Λ.ge hx]


@[blueprint
  "Mertens-first-theorem-prime-bounded"
  (title := "Error term in Mertens' first theorem bounded (prime form)")
  (statement := /-- For any $x \geq 1$, one has
$$ \sum_{p \leq x} \frac{\log p}{p} = \log x + O(1). $$
-/)
  (proof := /-- Immediate from previous two corollaries.
  -/)
  (discussion := 1313)]
theorem sum_log_prime_div_eq_log {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p - log x| ≤ log 4 + 4 := by
    rw [abs_le']
    refine ⟨ E₁p.le hx, ?_ ⟩
    have : log 2 > 0 := by apply log_pos; norm_num
    have : log 4 = 2 * log 2 := by rw [←Real.log_rpow (by norm_num)]; norm_num
    grind [E₁p.ge hx, E₁.le]

theorem E₁p.bounded : ∃ c > 0, ∀ x ≥ 1, |E₁p x| ≤ c := by
  exact ⟨log 4 + 4, (by positivity), fun _ hx ↦ sum_log_prime_div_eq_log  hx⟩

@[blueprint
  "Mertens-first-theorem-prime-bounded"]
theorem sum_log_prime_div_eq_log' : E₁p =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, ge_iff_le, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

@[blueprint
  "Mertens-first-theorem-prime-bounded"]
theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert sum_log_prime_div_eq_log' using 1

@[blueprint
  "Euler-Mascheroni-const-alt"
  (title := "Alternate Formula for Euler-Mascheroni constant")
  (statement := /-- We set $\gamma := \int_2^\infty \frac{E_{1,\Lambda}(t)}{t \log^2 t} \, dt + 1 - \log \log 2$.
-/)]
noncomputable abbrev γ : ℝ := (∫ t in Set.Ioi 2, E₁Λ t / (t * log t^2)) + 1 - log (log 2)

@[blueprint
  "Mertens-second-error-mangoldt"
  (title := "The remainder term in Mertens second theorem (von Mangoldt form)")
  (statement := /-- We define $E_{2,\Lambda}(x) := \sum_{d \leq x} \frac{\Lambda(d)}{d \log d} - \log \log x - \gamma$.
-/)]
noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

lemma sum_Ioc_one_eq_sum_Icc_zero {f : ℕ → ℝ} {x : ℕ} (hx : 1 ≤ x) (hf1 : f 1 = 0) (hf0 : f 0 = 0) :
    ∑ n ∈ Ioc 1 x, f n = ∑ n ∈ Icc 0 x, f n := by
  rw [sum_Ioc_one_eq_sum_Ioc_zero hx hf1, ← add_sum_Ioc_eq_sum_Icc (by linarith)]
  simpa

@[blueprint
  "Mertens-integral-ident"
  (title := "Integral identity involving inverse log weight")
  (statement := /-- For any $x \geq 2$ and any $f : {\mathbb N} \mapsto {\mathbb R}$, one has
$$ \sum_{2 \leq n \leq x} \frac{f(n)}{\log n} = \frac{1}{\log x} \sum_{2 \leq n \leq x} f(n) + \int_2^x \frac{1}{t \log^2 t} \sum_{2 \leq n \leq t} f(n) \, dt$$-/)
  (proof := /-- Establish the identity
  $$ \frac{1}{\log n} = \frac{1}{\log x} + \int_2^x \frac{1}{t \log^2 t} 1_{t \geq n}\ dt$$
  for $2 \leq n \leq x$,multiply by $f(n)$, then sum.

  -/)
  (latexEnv := "sublemma")]
private theorem sum_div_log_eq {x : ℝ} (hx : 2 ≤ x) (f : ℕ → ℝ) :
    ∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n / log n =
      (∑ n ∈ Ioc 1 ⌊ x ⌋₊, f n) / log x + ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊ t ⌋₊, f n) / (t * log t^2) := by
  let g : ℕ → ℝ := (fun n ↦ if n < 2 then 0 else f n)
  trans ∑ n ∈ Icc 0 ⌊ x ⌋₊, (log n)⁻¹ * g n
  · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp) (by simp)]
    refine sum_congr rfl fun n hn ↦ ?_
    have : ¬(n ≤ 1) := by simp_all
    simp [g, this]
    field
  rw [sum_mul_eq_sub_integral_mul₁ g (f := (fun n ↦ (log n)⁻¹)) (by simp [g]) (by simp [g])]
  · rw [intervalIntegral.integral_of_le hx, mul_comm, ← div_eq_mul_inv, ← sub_neg_eq_add]
    simp_rw [deriv_inv_log]
    congr 1
    · rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      congr 1
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
    · rw [← MeasureTheory.integral_neg]
      refine  MeasureTheory.setIntegral_congr_fun (by measurability) fun t ht ↦ ?_
      simp only [Set.mem_Ioc] at ht
      rw [← sum_Ioc_one_eq_sum_Icc_zero (Nat.le_floor (by grind)) (by simp [g]) (by simp [g])]
      field_simp
      congr 2
      refine sum_congr rfl fun n hn ↦ ?_
      simp only [mem_Ioc] at hn
      have : ¬(n ≤ 1) := by linarith
      simp [g, this]
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.integrableOn_Icc fun t ht ↦ ContinuousAt.continuousWithinAt ?_
    simp only [Set.mem_Icc] at ht
    conv => arg 1; ext x; rw [deriv_inv_log]
    have : log t ^2 ≠ 0 := by simp; grind
    fun_prop (disch := grind)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply MeasureTheory.Integrable.const_mul
  refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

attribute [fun_prop] measurable_from_top

private theorem integrable_E₁Λ_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁Λ x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁Λ.bounded'
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

private theorem integrable_E₁p_div_mul_log_sq {x : ℝ} (hx : 2 ≤ x) :
    MeasureTheory.IntegrableOn (fun x ↦ E₁p x / (x * log x ^ 2)) (Set.Ioi x) MeasureTheory.volume := by
  obtain ⟨c, hc1, hc2⟩ := E₁p.bounded
  apply MeasureTheory.Integrable.mono (integrable_const_div_mul_log_sq c hx)
  · exact Measurable.aestronglyMeasurable (by fun_prop)
  · filter_upwards [MeasureTheory.ae_restrict_mem (by measurability)] with t ht
    simp only [Set.mem_Ioi] at ht
    simp only [norm_div, norm_eq_abs, norm_mul, norm_pow, sq_abs, abs_of_pos hc1]
    gcongr
    exact hc2 t (by linarith)

lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = 1 / (x * log x) := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, 1 / (t * log t) = log (log x) - log (log 2) := by
  rw [← intervalIntegral.integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [deriv_log_log]
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    linarith
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine ContinuousOn.intervalIntegrable ?_
    apply ContinuousOn.congr (f := (fun t ↦ 1 / (t * log t)))
    · refine fun t ht ↦ ContinuousAt.continuousWithinAt ?_
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      have : log t ≠ 0 := by simp; grind
      fun_prop (disch := grind)
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

lemma intervalIntegrable_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    IntervalIntegrable (fun t ↦ 1 / (t * log t)) MeasureTheory.volume 2 x := by
  refine ContinuousOn.intervalIntegrable fun t ht ↦ ContinuousAt.continuousWithinAt ?_
  rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
  have : log t ≠ 0 := by simp; grind
  fun_prop (disch := grind)

@[blueprint
  "Mertens-second-error-mangoldt-eq"
  (title := "Integral form for second error (von Mangoldt form)")
  (statement := /-- For any $x \geq 2$, one has
$$ E_{2,\Lambda}(x) = \frac{E_{1,\Lambda}(x)}{\log x} - \int_x^\infty \frac{E_{1,\Lambda}(t)}{t \log^2 t}\ dt$$
-/)
  (proof := /--
From Lemma \ref{Mertens-integral-ident} one has
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n \log n} = \frac{1}{\log x} \sum_{n \leq x} \frac{\Lambda(n)}{n} + \int_2^x \frac{1}{t \log^2 t} \sum_{n \leq t} \frac{\Lambda(n)}{n} \, dt.$$
Now substitute the definitions of $E_{1,\Lambda}$, $E_{2,\Lambda}$, $\gamma$ and simplify.
  -/)
  (latexEnv := "corollary")
  (discussion := 1317)]
theorem E₂Λ.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂Λ x = E₁Λ x / log x - ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) := by
  unfold E₂Λ
  rw [← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp)]
  conv => lhs; arg 1; arg 1; arg 2; ext n; rw [(by field : Λ n / (n * log n) = (Λ n / n) / log n)]
  rw [sum_div_log_eq hx]
  rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, Λ n / n) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁Λ t / (t * log t ^ 2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), sum_mangoldt_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold γ
    calc
    _ = E₁Λ x / log x + (∫ (x : ℝ) in 2..x, E₁Λ x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁Λ t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁Λ_div_mul_log_sq (by rfl)) (integrable_E₁Λ_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁Λ_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

private theorem integ_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioi x, c / (t * log t^2) = c / log x := by
    convert MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := fun x ↦ - c / log x) ?_
      (integrable_const_div_mul_log_sq c hx) ?_ using 1
    · grind
    · intro t ht; simp at ht
      convert HasDerivAt.fun_div (hasDerivAt_const _ (-c)) (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert tendsto_log_atTop.inv_tendsto_atTop.const_mul (-c) using 1
    simp

@[blueprint
  "Mertens-second-error-mangoldt-bound"
  (title := "Bound for second Mertens error (von Mangoldt form)")
  (statement := /-- For any $x \geq 2$, one has
$$ |E_{2,\Lambda}(x)| \leq \frac{\log 4 + 6}{\log x}.$$
-/)
  (proof := /--
  Insert Lemma \ref{Mertens-first-error-mangoldt-le} and Lemma \ref{Mertens-first-error-mangoldt-ge} into Lemma \ref{Mertens-second-error-mangoldt-eq} and use the triangle inequality to obtain the required upper and lower bounds.
  -/)
  (latexEnv := "corollary")
  (discussion := 1318)]
theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂Λ.eq hx, abs_le']
    constructor
    · grw [E₁Λ.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≥ - 2 / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2) hx)
            (integrable_E₁Λ_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2) hx
      grw [this]
      grind
    grw [E₁Λ.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁Λ t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁Λ_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁Λ.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind


@[blueprint
  "Mertens-second-error-mangoldt-bound"]
theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop, ge_iff_le]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

@[blueprint
  "Mertens-second-error-mangoldt-bound"]
theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

private noncomputable abbrev logZetaCoeff (n : ℕ) : ℝ := Λ n / (n * log n)

private lemma logZetaCoeff_nonneg (n : ℕ) : 0 ≤ logZetaCoeff n := by
  dsimp [logZetaCoeff]
  exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n))
    (mul_nonneg (Nat.cast_nonneg n) (Real.log_natCast_nonneg n))

private lemma mangoldt_div_nonneg (n : ℕ) : 0 ≤ Λ n / (n : ℝ) := by
  exact div_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (Nat.cast_nonneg n)

private lemma logZetaCoeff_le_const_mul_mangoldt_div (n : ℕ) :
    logZetaCoeff n ≤ (1 / log 2) * (Λ n / (n : ℝ)) := by
  by_cases hn0 : n = 0
  · simp [logZetaCoeff, hn0]
  by_cases hn1 : n = 1
  · simp [logZetaCoeff, hn1]
  have hn2 : 2 ≤ n := by omega
  have hlog2pos : 0 < log 2 := log_pos (by norm_num)
  have hlognpos : 0 < log (n : ℝ) :=
    log_pos (by exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hn2))
  have hlog2le : log 2 ≤ log (n : ℝ) :=
    log_le_log (by norm_num) (by exact_mod_cast hn2)
  calc
    logZetaCoeff n = (Λ n / (n : ℝ)) / log n := by
      dsimp [logZetaCoeff]
      field
    _ ≤ (Λ n / (n : ℝ)) / log 2 := by
      exact div_le_div_of_nonneg_left (mangoldt_div_nonneg n) hlog2pos hlog2le
    _ = (1 / log 2) * (Λ n / (n : ℝ)) := by ring

private lemma sum_Icc_one_eq_sum_Ioc_zero (f : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ k ∈ Ioc 0 n, f k := by
  refine Finset.sum_congr ?_ fun _ _ ↦ rfl
  ext k
  simp [Nat.succ_le_iff]

private lemma logZetaCoeff_partial_sum_isBigO_rpow {r : ℝ} (hr : 0 < r) :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, logZetaCoeff k) =O[atTop]
      fun n : ℕ ↦ (n : ℝ) ^ r := by
  have hcoeff_to_lambda :
      (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, logZetaCoeff k) =O[atTop]
        fun n : ℕ ↦ ∑ k ∈ Icc 1 n, Λ k / (k : ℝ) := by
    refine IsBigO.of_bound (1 / log 2) (Eventually.of_forall ?_)
    intro n
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    have hleft_nonneg : 0 ≤ ∑ k ∈ Icc 1 n, logZetaCoeff k :=
      Finset.sum_nonneg fun k _ ↦ logZetaCoeff_nonneg k
    have hright_nonneg : 0 ≤ ∑ k ∈ Icc 1 n, Λ k / (k : ℝ) :=
      Finset.sum_nonneg fun k _ ↦ mangoldt_div_nonneg k
    rw [abs_of_nonneg hleft_nonneg, abs_of_nonneg hright_nonneg]
    calc
      ∑ k ∈ Icc 1 n, logZetaCoeff k
          ≤ ∑ k ∈ Icc 1 n, (1 / log 2) * (Λ k / (k : ℝ)) := by
        exact Finset.sum_le_sum fun k _ ↦ logZetaCoeff_le_const_mul_mangoldt_div k
      _ = (1 / log 2) * ∑ k ∈ Icc 1 n, Λ k / (k : ℝ) := by
        rw [Finset.mul_sum]
  have hlambda_log_ioc :
      (fun n : ℕ ↦ ∑ d ∈ Ioc 0 ⌊(n : ℝ)⌋₊, Λ d / (d : ℝ)) =O[atTop]
        fun n : ℕ ↦ log (n : ℝ) := by
    simpa [Function.comp_def] using
      (sum_mangoldt_div_eq_log'.isBigO.comp_tendsto
        (k := fun n : ℕ ↦ (n : ℝ)) tendsto_natCast_atTop_atTop)
  have hlambda_log :
      (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, Λ k / (k : ℝ)) =O[atTop]
        fun n : ℕ ↦ log (n : ℝ) := by
    refine (Filter.EventuallyEq.isBigO ?_).trans hlambda_log_ioc
    filter_upwards with n
    rw [Nat.floor_natCast, sum_Icc_one_eq_sum_Ioc_zero]
  have hlog_rpow : (fun n : ℕ ↦ log (n : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ r := by
    simpa [Function.comp_def] using
      ((isLittleO_log_rpow_atTop hr).isBigO.comp_tendsto
        (k := fun n : ℕ ↦ (n : ℝ)) tendsto_natCast_atTop_atTop)
  exact hcoeff_to_lambda.trans (hlambda_log.trans hlog_rpow)

private theorem logZetaCoeff_LSeries_eq_integral (s : ℝ) (hs : 1 < s) :
    LSeries (fun n : ℕ ↦ (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ)) =
      (((s - 1 : ℝ) : ℂ)) *
        ∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, (logZetaCoeff k : ℂ)) *
            (t : ℂ) ^ (-((((s - 1 : ℝ) : ℂ)) + 1)) := by
  have hr : 0 ≤ (s - 1) / 2 := by linarith
  have hsr : (s - 1) / 2 < ((((s - 1 : ℝ) : ℂ)) : ℂ).re := by
    simp
    linarith
  simpa using
    LSeries_eq_mul_integral_of_nonneg logZetaCoeff hr (s := (((s - 1 : ℝ) : ℂ))) hsr
      (logZetaCoeff_partial_sum_isBigO_rpow (by linarith)) logZetaCoeff_nonneg

private lemma logZetaCoeff_LSeriesSummable (s : ℝ) (hs : 1 < s) :
    LSeriesSummable (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ)) := by
  have hr : 0 ≤ (s - 1) / 2 := by linarith
  have hsr : (s - 1) / 2 < ((((s - 1 : ℝ) : ℂ)) : ℂ).re := by
    simp
    linarith
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (logZetaCoeff_partial_sum_isBigO_rpow (by linarith)) logZetaCoeff_nonneg hr hsr

private lemma eulerLogTerm_eq_ofReal {s : ℝ} (hs : 1 < s) (p : Nat.Primes) :
    -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) =
      ((-Real.log (1 - (p : ℝ) ^ (-s)) : ℝ) : ℂ) := by
  have hpow : (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    simpa [Complex.ofReal_natCast, Complex.ofReal_neg] using
      (Complex.ofReal_cpow (show 0 ≤ (p : ℝ) by positivity) (-s)).symm
  have hpos : 0 ≤ 1 - (p : ℝ) ^ (-s) := by
    exact (sub_pos.mpr
      (Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith))).le
  have hsub :
      (1 : ℂ) - (((p : ℝ) ^ (-s) : ℝ) : ℂ) =
        ((1 - (p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    norm_num [Complex.ofReal_sub]
  rw [hpow, hsub, ← Complex.ofReal_log hpos]
  norm_num

private lemma summable_eulerLogTerm {s : ℝ} (hs : 1 < s) :
    Summable fun p : Nat.Primes => -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) := by
  have h := DirichletCharacter.summable_neg_log_one_sub_mul_prime_cpow
    (1 : DirichletCharacter ℂ 1) (s := (s : ℂ)) (by simpa using hs)
  refine h.congr ?_
  intro p
  have hχ : (1 : DirichletCharacter ℂ 1) p = 1 := by
    exact congr_fun (DirichletCharacter.modOne_eq_one (χ := (1 : DirichletCharacter ℂ 1)))
      (p : ℕ)
  rw [hχ, one_mul]

private lemma eulerProduct_log_im_zero {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).im = 0 := by
  rw [Complex.im_tsum (summable_eulerLogTerm hs)]
  convert tsum_zero with p
  rw [eulerLogTerm_eq_ofReal hs p]
  simp

private lemma eulerProduct_log_re_eq_log_zeta {s : ℝ} (hs : 1 < s) :
    (∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))).re =
      log (riemannZeta (s : ℂ)).re := by
  let z : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ)))
  have him : z.im = 0 := by
    simpa [z] using eulerProduct_log_im_zero hs
  have hexp : Complex.exp z = riemannZeta (s : ℂ) := by
    simpa [z] using riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) (by simpa using hs)
  have hzeta_re : (riemannZeta (s : ℂ)).re = Real.exp z.re := by
    rw [← hexp, Complex.exp_re, him, Real.cos_zero, mul_one]
  calc
    z.re = log (riemannZeta (s : ℂ)).re := by
      rw [hzeta_re, Real.log_exp]

private lemma logZetaCoeff_prime_pow (p : Nat.Primes) (k : ℕ) :
    logZetaCoeff (p ^ (k + 1)) =
      (1 : ℝ) / ((k + 1 : ℝ) * (p : ℝ) ^ (k + 1)) := by
  have hp : Nat.Prime (p : ℕ) := p.2
  have hk : k + 1 ≠ 0 := by omega
  have hlog : Real.log (p : ℝ) ≠ 0 := by
    exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  dsimp [logZetaCoeff]
  rw [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  rw [Nat.cast_pow, Real.log_pow]
  field_simp [hlog]
  norm_num [Nat.cast_add, Nat.cast_one]

private lemma cpow_prime_pow_neg (p : Nat.Primes) (k : ℕ) (s : ℝ) :
    ((p : ℂ) ^ (k + 1)) ^ (-(s : ℂ)) = ((p : ℂ) ^ (-(s : ℂ))) ^ (k + 1) := by
  have harg : (p : ℂ).arg = 0 := by simp
  rw [← Complex.cpow_nat_mul']
  · rw [Complex.cpow_nat_mul]
  · rw [harg]
    simpa using Real.pi_pos
  · rw [harg]
    nlinarith [Real.pi_pos]

private lemma inv_mul_cpow_one_sub {a : ℂ} (ha : a ≠ 0) (s : ℝ) :
    a⁻¹ * a ^ (1 - (s : ℂ)) = a ^ (-(s : ℂ)) := by
  rw [show (1 - (s : ℂ)) = 1 + -(s : ℂ) by ring]
  rw [Complex.cpow_add _ _ ha, Complex.cpow_one]
  field_simp [ha]

private lemma logZetaCoeff_LSeries_term_prime_pow {s : ℝ} (p : Nat.Primes) (k : ℕ) :
    LSeries.term (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ))
        (p ^ (k + 1)) =
      ((p : ℂ) ^ (-(s : ℂ))) ^ (k + 1) / ((k + 1 : ℕ) : ℂ) := by
  have hf0 : (fun n : ℕ => (logZetaCoeff n : ℂ)) 0 = 0 := by simp [logZetaCoeff]
  have hp_ne : ((p : ℂ) ^ (k + 1)) ≠ 0 := by
    exact pow_ne_zero _ (by exact_mod_cast p.2.ne_zero)
  rw [LSeries.term_def₀ hf0]
  rw [logZetaCoeff_prime_pow]
  norm_num [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_pow]
  change
    ((p : ℂ) ^ (k + 1))⁻¹ * ((k : ℂ) + 1)⁻¹ *
        ((p : ℂ) ^ (k + 1)) ^ (1 - (s : ℂ)) =
      ((p : ℂ) ^ (-(s : ℂ))) ^ (k + 1) / ((k : ℂ) + 1)
  rw [show
      ((p : ℂ) ^ (k + 1))⁻¹ * ((k : ℂ) + 1)⁻¹ *
          ((p : ℂ) ^ (k + 1)) ^ (1 - (s : ℂ)) =
        ((k : ℂ) + 1)⁻¹ *
          (((p : ℂ) ^ (k + 1))⁻¹ * ((p : ℂ) ^ (k + 1)) ^ (1 - (s : ℂ))) by
    ring]
  rw [inv_mul_cpow_one_sub hp_ne s, cpow_prime_pow_neg p k s]
  ring

private lemma logZetaCoeff_LSeries_inner_tsum_prime_power {s : ℝ} (hs : 1 < s)
    (p : Nat.Primes) :
    (∑' k : ℕ, LSeries.term (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ))
        (p ^ (k + 1))) =
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) := by
  have hz_norm : ‖(p : ℂ) ^ (-(s : ℂ))‖ < 1 := by
    have hnorm : ‖(p : ℂ) ^ (-(s : ℂ))‖ = (p : ℝ) ^ (-s) := by
      simpa [Complex.ofReal_natCast] using
        (Complex.norm_cpow_eq_rpow_re_of_pos
          (show 0 < (p : ℝ) by exact_mod_cast p.2.pos) (-(s : ℂ)))
    rw [hnorm]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (by linarith)
  have hsum := Complex.hasSum_taylorSeries_neg_log hz_norm
  rw [← hsum.tsum_eq]
  rw [hsum.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add]
  congr
  ext k
  simpa [logZetaCoeff, Complex.ofReal_div, Complex.ofReal_mul,
    Complex.ofReal_log (Nat.cast_nonneg _)] using
    logZetaCoeff_LSeries_term_prime_pow (s := s) p k

private lemma support_logZetaCoeff_LSeriesTerm_subset_primePowers {z : ℂ} :
    Function.support (LSeries.term (fun n : ℕ => (logZetaCoeff n : ℂ)) z) ⊆
      {n | IsPrimePow n} := by
  intro n hn
  rw [Function.mem_support] at hn
  change IsPrimePow n
  rw [← vonMangoldt_ne_zero_iff]
  intro hΛ
  apply hn
  rw [LSeries.term]
  split_ifs with hn0
  · rfl
  · simp [logZetaCoeff, hΛ]

private lemma logZetaCoeff_LSeries_eq_eulerProduct_log (s : ℝ) (hs : 1 < s) :
    LSeries (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ)) =
      ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) := by
  rw [LSeries]
  rw [tsum_eq_tsum_primes_of_support_subset_prime_powers
    (logZetaCoeff_LSeriesSummable s hs) support_logZetaCoeff_LSeriesTerm_subset_primePowers]
  exact tsum_congr fun p => logZetaCoeff_LSeries_inner_tsum_prime_power hs p

private lemma log_zeta_eq_LSeries_re (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s : ℂ)).re =
      (LSeries (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ))).re := by
  rw [logZetaCoeff_LSeries_eq_eulerProduct_log s hs]
  exact (eulerProduct_log_re_eq_log_zeta hs).symm

private lemma logZetaCoeff_complex_integrand_eq_ofReal (s : ℝ) {t : ℝ}
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    (∑ k ∈ Icc 1 ⌊t⌋₊, (logZetaCoeff k : ℂ)) *
        (t : ℂ) ^ (-((((s - 1 : ℝ) : ℂ)) + 1)) =
      (((∑ d ∈ Ioc 0 ⌊t⌋₊, Λ d / (d * log d)) * ((t : ℝ) ^ (-s)) : ℝ) : ℂ) := by
  have htpos : 0 < t := by linarith [Set.mem_Ioi.mp ht]
  have hpow :
      (t : ℂ) ^ (-((((s - 1 : ℝ) : ℂ)) + 1)) = (((t : ℝ) ^ (-s) : ℝ) : ℂ) := by
    have hexp : -((((s - 1 : ℝ) : ℂ)) + 1) = ((-s : ℝ) : ℂ) := by
      norm_num
    rw [hexp]
    simpa [Complex.ofReal_neg] using (Complex.ofReal_cpow htpos.le (-s)).symm
  rw [hpow, ← Complex.ofReal_sum, sum_Icc_one_eq_sum_Ioc_zero]
  rw [← Complex.ofReal_mul]

private lemma logZetaCoeff_LSeries_re_eq_summatory_integral (s : ℝ) (hs : 1 < s) :
    (LSeries (fun n : ℕ => (logZetaCoeff n : ℂ)) (((s - 1 : ℝ) : ℂ))).re =
      (s - 1) * ∫ x in Set.Ioi (1 : ℝ),
        (∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / (d * log d)) * ((x : ℝ) ^ (-s)) := by
  have h := congrArg Complex.re (logZetaCoeff_LSeries_eq_integral s hs)
  have hInt :
      (∫ t in Set.Ioi (1 : ℝ),
          (∑ k ∈ Icc 1 ⌊t⌋₊, (logZetaCoeff k : ℂ)) *
            (t : ℂ) ^ (-((((s - 1 : ℝ) : ℂ)) + 1))) =
        ((∫ t in Set.Ioi (1 : ℝ),
          (((∑ d ∈ Ioc 0 ⌊t⌋₊, Λ d / (d * log d)) *
            ((t : ℝ) ^ (-s)) : ℝ)) : ℝ) : ℂ) := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => logZetaCoeff_complex_integrand_eq_ofReal s ht)]
    exact (_root_.integral_ofReal (𝕜 := ℂ)
      (μ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ)))
      (f := fun t : ℝ =>
        (∑ d ∈ Ioc 0 ⌊t⌋₊, Λ d / (d * log d)) * ((t : ℝ) ^ (-s)))
      )
  rw [hInt] at h
  simpa [Complex.ofReal_mul] using h

private lemma mul_integral_Ioi_rpow_eq_one (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (1 : ℝ), x ^ (-s) = 1 := by
  rw [integral_Ioi_rpow_of_lt (by linarith : -s < -1) zero_lt_one]
  rw [Real.one_rpow]
  rw [show -s + 1 = -(s - 1) by ring]
  field_simp [sub_ne_zero.mpr (by linarith : s ≠ 1)]

private lemma exp_image_Ioi_zero : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [Set.mem_Ioi] at hu ⊢
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr hu
  · intro hx
    rw [Set.mem_Ioi] at hx
    refine ⟨Real.log x, ?_, Real.exp_log (by linarith : 0 < x)⟩
    rw [Set.mem_Ioi]
    rw [← Real.log_one]
    exact Real.log_lt_log (by norm_num) hx

private lemma exp_injOn_Ioi_zero : Set.InjOn Real.exp (Set.Ioi (0 : ℝ)) := by
  intro x _ y _ hxy
  exact Real.exp_injective hxy

private lemma integral_Ioi_one_loglog_rpow_eq_exp (s : ℝ) :
    (∫ x in Set.Ioi (1 : ℝ), Real.log (Real.log x) * x ^ (-s)) =
      ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-(s - 1) * u) := by
  let g : ℝ → ℝ := fun x => Real.log (Real.log x) * x ^ (-s)
  have hderiv :
      ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt Real.exp (Real.exp u) (Set.Ioi (0 : ℝ)) u := by
    intro u _
    exact (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hsubst := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hderiv exp_injOn_Ioi_zero g
  rw [exp_image_Ioi_zero] at hsubst
  rw [hsubst]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
  intro u hu
  rw [Set.mem_Ioi] at hu
  dsimp [g]
  rw [abs_of_pos (Real.exp_pos u), Real.log_exp]
  have hpow : (Real.exp u) ^ (-s) = Real.exp (-s * u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
    congr 1
    ring
  rw [hpow]
  calc
    Real.exp u * (Real.log u * Real.exp (-s * u)) =
        Real.log u * (Real.exp u * Real.exp (-s * u)) := by ring
    _ = Real.log u * Real.exp (u + (-s * u)) := by rw [Real.exp_add]
    _ = Real.log u * Real.exp (-(s - 1) * u) := by
      congr 1
      ring_nf

private lemma integrableOn_log_mul_exp_neg_Ioi_zero :
    MeasureTheory.IntegrableOn (fun t : ℝ => Real.log t * Real.exp (-t)) (Set.Ioi (0 : ℝ)) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  exact LiSeries.FubiniLogExpNeg.integrableOn_log_mul_exp_neg_Ioc.union
    LiSeries.FubiniLogExpNeg.integrableOn_log_mul_exp_neg_Ioi_one

private lemma deriv_Gamma_one_eq_integral_log_exp_neg :
    deriv Real.Gamma 1 = ∫ t in Set.Ioi (0 : ℝ), Real.log t * Real.exp (-t) := by
  have h1 := LiSeries.eulerMascheroni_eq_neg_integral
  have h2 := Real.eulerMascheroniConstant_eq_neg_deriv
  linarith

private lemma integral_log_div_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    (∫ v in Set.Ioi (0 : ℝ), Real.log (v / a) * Real.exp (-v)) =
      deriv Real.Gamma 1 - Real.log a := by
  have hcongr :
      (∫ v in Set.Ioi (0 : ℝ), Real.log (v / a) * Real.exp (-v)) =
        ∫ v in Set.Ioi (0 : ℝ), (Real.log v * Real.exp (-v) - Real.log a * Real.exp (-v)) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro v hv
    rw [Set.mem_Ioi] at hv
    dsimp
    rw [Real.log_div (by linarith : v ≠ 0) ha.ne']
    ring
  rw [hcongr]
  rw [MeasureTheory.integral_sub]
  · rw [deriv_Gamma_one_eq_integral_log_exp_neg, MeasureTheory.integral_const_mul,
      integral_exp_neg_Ioi_zero]
    ring
  · exact integrableOn_log_mul_exp_neg_Ioi_zero
  · simpa [mul_comm] using (integrableOn_exp_neg_Ioi 0).const_mul (Real.log a)

private lemma integrableOn_log_div_mul_exp_neg (a : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun v : ℝ => Real.log (v / a) * Real.exp (-v)) (Set.Ioi (0 : ℝ)) := by
  have hsub :
      MeasureTheory.IntegrableOn
        (fun v : ℝ => Real.log v * Real.exp (-v) - Real.log a * Real.exp (-v))
        (Set.Ioi (0 : ℝ)) := by
    exact integrableOn_log_mul_exp_neg_Ioi_zero.sub
      (by simpa [mul_comm] using (integrableOn_exp_neg_Ioi 0).const_mul (Real.log a))
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro v hv
  rw [Set.mem_Ioi] at hv
  dsimp
  rw [Real.log_div (by linarith : v ≠ 0) ha.ne']
  ring

private lemma integrableOn_log_exp_neg_mul (a : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => Real.log u * Real.exp (-a * u)) (Set.Ioi (0 : ℝ)) := by
  let g : ℝ → ℝ := fun v => Real.log (v / a) * Real.exp (-v)
  have hscale :
      MeasureTheory.IntegrableOn (fun u => g (a * u)) (Set.Ioi (0 : ℝ)) :=
    (MeasureTheory.integrableOn_Ioi_comp_mul_left_iff g 0 ha).mpr (by
      simpa [g, mul_zero] using integrableOn_log_div_mul_exp_neg a ha)
  refine hscale.congr_fun ?_ measurableSet_Ioi
  intro u hu
  rw [Set.mem_Ioi] at hu
  dsimp [g]
  rw [mul_div_cancel_left₀ u ha.ne']
  ring_nf

private lemma integrableOn_Ioi_one_loglog_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.log (Real.log x) * x ^ (-s)) (Set.Ioi (1 : ℝ)) := by
  let g : ℝ → ℝ := fun x => Real.log (Real.log x) * x ^ (-s)
  have hderiv :
      ∀ u ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt Real.exp (Real.exp u) (Set.Ioi (0 : ℝ)) u := by
    intro u _
    exact (Real.hasDerivAt_exp u).hasDerivWithinAt
  have hiff := MeasureTheory.integrableOn_image_iff_integrableOn_abs_deriv_smul
    (s := Set.Ioi (0 : ℝ)) measurableSet_Ioi hderiv exp_injOn_Ioi_zero g
  rw [exp_image_Ioi_zero] at hiff
  refine hiff.mpr ?_
  refine (integrableOn_log_exp_neg_mul (s - 1) (by linarith)).congr_fun ?_ measurableSet_Ioi
  intro u hu
  rw [Set.mem_Ioi] at hu
  dsimp [g]
  rw [abs_of_pos (Real.exp_pos u), Real.log_exp]
  have hpow : (Real.exp u) ^ (-s) = Real.exp (-s * u) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]
    congr 1
    ring
  rw [hpow]
  symm
  calc
    Real.exp u * (Real.log u * Real.exp (-s * u)) =
        Real.log u * (Real.exp u * Real.exp (-s * u)) := by ring
    _ = Real.log u * Real.exp (u + (-s * u)) := by rw [Real.exp_add]
    _ = Real.log u * Real.exp (-(s - 1) * u) := by
      congr 1
      ring_nf

private lemma mul_integral_Ioi_log_exp_neg_mul_eq (a : ℝ) (ha : 0 < a) :
    a * (∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-a * u)) =
      deriv Real.Gamma 1 - Real.log a := by
  let g : ℝ → ℝ := fun v => Real.log (v / a) * Real.exp (-v)
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi g 0 ha
  have hleft :
      (∫ u in Set.Ioi (0 : ℝ), g (a * u)) =
        ∫ u in Set.Ioi (0 : ℝ), Real.log u * Real.exp (-a * u) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro u hu
    rw [Set.mem_Ioi] at hu
    dsimp [g]
    rw [mul_div_cancel_left₀ u ha.ne']
    ring_nf
  rw [hleft, mul_zero] at hscale
  rw [hscale]
  rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
  exact integral_log_div_mul_exp_neg a ha

private lemma mul_integral_Ioi_loglog_rpow_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Set.Ioi (1 : ℝ), Real.log (Real.log x) * x ^ (-s) =
      -Real.log (s - 1) + deriv Real.Gamma 1 := by
  rw [integral_Ioi_one_loglog_rpow_eq_exp]
  have h := mul_integral_Ioi_log_exp_neg_mul_eq (s - 1) (by linarith)
  linarith

private lemma zeta_pole_mul_re_tendsto_one :
    Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re) (𝓝[>] 1) (𝓝 1) := by
  have hsub :
      Tendsto (fun s : ℝ => (riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)).re)
        (𝓝[>] 1) (𝓝 Real.eulerMascheroniConstant) := by
    exact (Complex.continuous_re.tendsto (Real.eulerMascheroniConstant : ℂ)).comp
      ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right
  have hmul0 :
      Tendsto
        (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)).re)
        (𝓝[>] 1) (𝓝 0) := by
    have hsminus : Tendsto (fun s : ℝ => s - 1) (𝓝[>] 1) (𝓝 0) := by
      rw [show (0 : ℝ) = 1 - 1 by ring]
      exact (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub tendsto_const_nhds
    simpa using hsminus.mul hsub
  have hsplit :
      (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re) =ᶠ[𝓝[>] 1]
        fun s : ℝ =>
          (s - 1) * (riemannZeta (s : ℂ) - 1 / ((s : ℂ) - 1)).re + 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    have h_inv_re : (1 / ((s : ℂ) - 1)).re = 1 / (s - 1) := by
      simp [Complex.normSq]
    rw [Complex.sub_re, h_inv_re]
    field_simp [sub_ne_zero.mpr (by linarith : s ≠ 1)]
    ring
  simpa using (hmul0.add tendsto_const_nhds).congr' (hsplit.mono fun s hs => hs.symm)

private lemma zeta_log_cancel_tendsto_zero :
    Tendsto (fun s : ℝ => log (riemannZeta (s : ℂ)).re + log (s - 1))
      (𝓝[>] 1) (𝓝 0) := by
  have hlog :
      Tendsto (fun s : ℝ => log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (𝓝[>] 1) (𝓝 (log 1)) :=
    zeta_pole_mul_re_tendsto_one.log (by norm_num)
  have hEq :
      (fun s : ℝ => log (riemannZeta (s : ℂ)).re + log (s - 1)) =ᶠ[𝓝[>] 1]
        fun s : ℝ => log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [Set.mem_Ioi] at hs
    have hspos : 0 < s - 1 := by linarith
    have hzpos : 0 < (riemannZeta (s : ℂ)).re := riemannZeta_re_pos_of_one_lt hs
    rw [← Real.log_mul hzpos.ne' hspos.ne']
    congr 1
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

@[blueprint
  "log-zeta-eq"
  (title := "An identity for $\\log \\zeta(s)$")
  (statement := /-- If $s > 1$ then $\log\zeta(s) = - \log (s-1) + \Gamma'(1) + \gamma + (s-1) \int_1^\infty E_{2,\Lambda}(x) x^{-s}\ ds$.
-/)
  (proof := /-- First write
$$ \log \zeta(s) = \sum_n \frac{\Lambda(n)}{n^s \log n}$$
and integrate by parts to write this as
$$ (s-1) \int_0^\infty (\log \log x + \gamma + E_{2,\Lambda}(x)) x^{-s}\ dx.$$
Standard calculations give
$$ (s-1) \int_0^\infty \log \log x \cdot x^{-s}\ dx = -\log (s-1) + \Gamma'(1)$$
and
$$ (s-1) \int_0^\infty \gamma \cdot x^{-s}\ dx = \gamma$$
giving the claim.-/)
  (latexEnv := "theorem")
  (discussion := 1319)]
private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
    sorry

#check Real.eulerMascheroniConstant_eq_neg_deriv

@[blueprint
  "Euler-Mascheroni-eq"
  (title := "Compatibility with Mathlib Euler-Mascheroni constant")
  (statement := /-- $\gamma$ is the Euler--Mascheroni constant.
-/)
  (proof := /-- Take limits as $s \to 1$ in the previous asymptotic using known asymptotics for $\zeta(s)$, and using that $- \Gamma'(1)$ is the Euler--Mascheroni constant. -/)
  (latexEnv := "theorem")
  (discussion := 1320)]
theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by sorry

theorem sum_mangoldt_div_log_eq (x : ℝ) : ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) = log (log x) + eulerMascheroniConstant + E₂Λ x := by
    grind [γ.eq_eulerMascheroni]

@[blueprint
  "Mertens-second-theorem-mangoldt-weak"
  (title := "Mertens' second theorem (weak von Mangoldt form)")
  (statement := /-- For any $x \geq 2$, one has
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n \log n} = \log \log x + O(1). $$
-/)
  (proof := /-- Immediate from previous two corollaries.
  -/)
  (discussion := 1321)]
theorem sum_mangoldt_div_log_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)| ≤ C := by
    use (log 4 + 6)/log 2 + |eulerMascheroniConstant|
    intro x hx
    rw [sum_mangoldt_div_log_eq]
    calc
      _ = |E₂Λ x + eulerMascheroniConstant| := by ring_nf
      _ ≤ (log 4 + 6)/log x + |eulerMascheroniConstant| := by grw [abs_add_le, E₂Λ.abs_le hx]
      _ ≤ _ := by gcongr

@[blueprint
  "Mertens-second-theorem-mangoldt-weak"]
theorem sum_mangoldt_div_log_eq_log_log' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, ge_iff_le]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2


@[blueprint
  "Mertens-second-theorem-mangoldt-weak"]
theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert sum_mangoldt_div_log_eq_log_log' using 1

@[blueprint
  "Meissel-Mertens-constant"
  (title := "The Meissel-Mertens constant")
  (statement := /-- We define $M := \int_2^\infty \frac{E_{1,p}(t)}{t \log^2 t} \, dt + 1 - \log \log 2$.-/)]
noncomputable def M : ℝ := (∫ t in Set.Ioi 2, E₁p t / (t * log t^2)) + 1 - log (log 2)

@[blueprint
  "Mertens-second-constant-prime-le"
  (title := "Upper bound for $M$")
  (statement := /-- One has $M \leq \frac{\log 4 + 4}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-prime-le} into the definition of $M$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")
  (discussion := 1323)]
theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := calc
    _ ≤ (∫ t in Set.Ioi 2, (log 4 + 4) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.le (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

@[blueprint
  "Mertens-second-constant-prime-ge"
  (title := "Lower bound for $M$")
  (statement := /-- One has $M \geq -\frac{2 + E_1}{\log 2} + 1 - \log \log 2$.
-/)
  (proof := /-- Insert Lemma \ref{Mertens-first-error-prime-ge} into the definition of $M$ and use the fact that $\int_2^\infty \frac{dt}{t \log^2 t} = 1/\log 2$.
  -/)
  (latexEnv := "corollary")
  (discussion := 1324)]
theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := calc
    _ ≥ (∫ t in Set.Ioi 2, (-2 - E₁) / (t * log t^2)) + 1 - log (log 2) := by
      unfold M; gcongr with x hx
      · exact integrable_const_div_mul_log_sq _ (by norm_num)
      · exact integrable_E₁p_div_mul_log_sq (by norm_num)
      · measurability
      · simp at hx; positivity
      simp at hx; exact E₁p.ge (by linarith)
    _ = _ := by rw [integ_div_mul_log_sq _ (by norm_num)]

@[blueprint
  "Mertens-second-error-mangoldt"
  (title := "The remainder term in Mertens second theorem (von Mangoldt form)")
  (statement := /-- We define $E_{2,p}(x) := \sum_{p \leq x} \frac{1}{p} - \log \log x - M$.
-/)]
noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

@[blueprint
  "Mertens-second-error-prime-eq"
  (title := "Integral form for second error (prime form)")
  (statement := /-- For any $x \geq 2$, one has
$$ E_{2,p}(x) = \frac{E_{1,p}(x)}{\log x} - \int_x^\infty \frac{E_{1,p}(t)}{t \log^2 t}\ dt$$
-/)
  (proof := /--
From Lemma \ref{Mertens-integral-ident} one has
$$ \sum_{p \leq x} \frac{1}{p} = \frac{1}{\log x} \sum_{p \leq x} \frac{\log p}{p} + \int_2^x \frac{1}{t \log^2 t} \sum_{p \leq t} \frac{\log p}{p} \, dt.$$
Now substitute the definitions of $E_{1,p}$, $E_{2,p}$, $M$ and simplify.
  -/)
  (latexEnv := "corollary")
  (discussion := 1325)]
theorem E₂p.eq {x : ℝ} (hx : 2 ≤ x) :
    E₂p x = E₁p x / log x - ∫ t in Set.Ioi x, E₁p t / (t * log t^2) := by
  unfold E₂p
  rw [sum_filter, ← sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp [Nat.not_prime_one])]
  have (n : ℕ) : (if Nat.Prime n then (1 : ℝ) / n else 0) = (if Nat.Prime n then log n / n else 0) / log n := by
    split_ifs with h
    · have : log n ≠ 0 := by simp; grind [h.two_le]
      field
    · simp
  simp_rw [this]
  rw [sum_div_log_eq hx, sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter]
  rw [sum_log_prime_div_eq]
  have : ∫ t in 2..x, (∑ n ∈ Ioc 1 ⌊t⌋₊, if Nat.Prime n then log ↑n / ↑n else 0) / (t * log t ^ 2) = ∫ t in 2..x, (1 / (t * log t) + E₁p t / (t * log t ^2)) := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [sum_Ioc_one_eq_sum_Ioc_zero (Nat.le_floor (by grind)) (by simp), ← sum_filter, sum_log_prime_div_eq]
    field
  rw [this, intervalIntegral.integral_add]
  · rw [integral_one_div_mul_log hx, add_div, div_self (by simp; grind)]
    unfold M
    calc
    _ = E₁p x / log x + (∫ (x : ℝ) in 2..x, E₁p x / (x * log x ^ 2)) -
      ((∫ (t : ℝ) in Set.Ioi 2, E₁p t / (t * log t ^ 2))) := by ring
    _ = _ := by
      rw [← intervalIntegral.integral_interval_add_Ioi (integrable_E₁p_div_mul_log_sq (by rfl)) (integrable_E₁p_div_mul_log_sq hx)]
      ring
  · exact intervalIntegrable_one_div_mul_log hx
  · rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    exact integrable_E₁p_div_mul_log_sq (x := 2) (by rfl)|>.mono (by grind) (by rfl)

@[blueprint
  "Mertens-second-error-prime-abs-le"
  (title := "Bound for second error (prime form)")
  (statement := /-- For any $x \geq 2$, one has
$$ |E_{2,p}(x)| \leq \frac{\log 4 + 6 + E_1}{\log x}.$$
-/)
  (proof := /-- Similar to Lemma \ref{Mertens-second-error-prime-eq}.
  -/)
  (latexEnv := "corollary")
  (discussion := 1326)]
theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
    have : 0 < log x := by apply log_pos; linarith
    rw [E₂p.eq hx, abs_le']
    constructor
    · grw [E₁p.le (by linarith)]
      have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≥ (- 2 - E₁) / log x := calc
        _ ≥ ∫ t in Set.Ioi x, (-2 - E₁) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_const_div_mul_log_sq (-2 - E₁) hx)
            (integrable_E₁p_div_mul_log_sq hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.ge (by linarith)
        _ = _ := integ_div_mul_log_sq (-2 - E₁) hx
      grw [this]
      grind
    grw [E₁p.ge (by linarith)]
    have : ∫ t in Set.Ioi x, E₁p t / (t * log t^2) ≤ (log 4 + 4) / log x := calc
        _ ≤ ∫ t in Set.Ioi x, (log 4 + 4) / (t * log t^2) := by
          apply MeasureTheory.setIntegral_mono_on (integrable_E₁p_div_mul_log_sq hx)
            (integrable_const_div_mul_log_sq (log 4 + 4) hx) (by measurability)
          intro y hy; simp at hy
          have : 1 < y := by linarith
          have : 0 < log y := log_pos this
          gcongr; exact E₁p.le (by linarith)
        _ = _ := integ_div_mul_log_sq (log 4 + 4) hx
    grw [this]
    grind

@[blueprint
  "Mertens-second-error-prime-abs-le"]
theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop, ge_iff_le]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

@[blueprint
  "Mertens-second-error-prime-abs-le"]
theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

@[blueprint
  "Mertens-second-theorem-prime-weak"
  (title := "Mertens' second theorem (weak prime form)")
  (statement := /-- For any $x \geq 2$, one has
$$ \sum_{p \leq x} \frac{1}{p} = \log \log x + O(1). $$
-/)
  (proof := /-- Immediate from previous two corollaries.
  -/)
  (discussion := 1327)]
theorem sum_prime_div_eq_log_log : ∃ C, ∀ x, 2 ≤ x →
    |∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)| ≤ C := by
    use |M| + (log 4 + 6 + E₁) / log 2
    intro x hx
    rw [sum_prime_div_eq]
    calc
      _ = |M + E₂p x| := by ring_nf
      _ ≤ |M| + (log 4 + 6 + E₁) / log x := by grw [abs_add_le, E₂p.abs_le hx]
      _ ≤ _ := by
        gcongr
        have : 0 < log 4 := by apply log_pos; norm_num
        linarith [E₁.nonneg]

@[blueprint
  "Mertens-second-theorem-prime-weak"]
theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop, ge_iff_le]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

@[blueprint
  "Mertens-second-theorem-prime-weak"]
theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert sum_prime_div_eq_log_log' using 1

lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
  · ext
    rw [div_pow, one_pow, div_div]
    ring
  · ring
  · simp only [one_div, abs_inv, Nat.abs_cast]
    exact inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)

lemma E₂Λ_sub_E₂p_tendsto :
    Tendsto (E₂Λ - E₂p) atTop (nhds 0) := by
  exact isLittleO_one_iff ℝ|>.mp <| E₂Λ.bound'.sub E₂p.bound'

/-- Function used in the proof of `M.eq`, `Λ n / n * log n` restricted to not primes. -/
noncomputable abbrev M_eq_f (n : ℕ) :=
    if ¬n.Prime then Λ n /(n * log n) else 0

lemma E₂Λ_sub_E₂p_eq (x : ℝ) :
    E₂Λ x - E₂p x = ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n - (γ - M) := by
  calc
  _ = ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / (n * log n) - ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p - (γ - M) := by ring
  _ = _ := by
    rw [sum_filter, ← sum_sub_distrib]
    congr
    ext n
    split_ifs with hn
    · rw [vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · ring

lemma M_eq_f.sum_tendsto :
    Tendsto (fun (x : ℝ) ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_f n) atTop (nhds (γ - M)) := by
  apply tendsto_sub_nhds_zero_iff.mp
  convert E₂Λ_sub_E₂p_tendsto using 1
  ext
  rw [← E₂Λ_sub_E₂p_eq]
  simp

lemma M_eq_f.sum_tendsto' :
    Tendsto (fun (N : ℕ) ↦ ∑ n ∈ range N, M_eq_f n) atTop (nhds (γ - M)) := by
  have : Tendsto (fun (N : ℕ) ↦ (∑ n ∈ Ioc 0 ⌊(N : ℝ)⌋₊, M_eq_f n)) atTop (nhds (γ - M)) := M_eq_f.sum_tendsto.comp tendsto_natCast_atTop_atTop
  simp_rw [Nat.floor_natCast] at this
  apply (this.comp (tendsto_sub_atTop_nat 1)).congr'
  filter_upwards [eventually_ge_atTop 1] with N hn
  rw [Nat.range_eq_Icc_zero_sub_one, ← add_sum_Ioc_eq_sum_Icc] <;> grind

lemma M_eq_f.HasSum :
    HasSum M_eq_f (γ - M) := by
  refine hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ ?_) _|>.mpr M_eq_f.sum_tendsto'
  unfold M_eq_f
  split_ifs with hn
  · rfl
  · exact div_nonneg vonMangoldt_nonneg (by positivity)

lemma M_eq_f.sum_primes :
    ∑' (p : Nat.Primes), M_eq_f p = 0 := by
  convert tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert _root_.tsum_subtype Nat.Prime f using 2
  ext
  simp [Set.indicator]
  congr

lemma tsum_M_eq_f_eq_tsum :
    -∑' (n : ℕ), M_eq_f n = ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [tsum_eq_tsum_primes_add_tsum_primes_of_support_subset_prime_powers M_eq_f.HasSum.summable
    (fun n hn ↦ (by simp_all [vonMangoldt_ne_zero_iff])), M_eq_f.sum_primes, zero_add,
    tsum_primes_eq_tsum_ite (fun p ↦ ∑' (k : ℕ), M_eq_f (p ^ (k + 2))), ← tsum_neg]
  refine tsum_congr fun n ↦ ?_
  split_ifs with hn
  · rw [← HasSum_log_one_sub_one_div_prime hn|>.tsum_eq, HasSum_log_one_sub_one_div_prime hn|>.summable.tsum_eq_zero_add]
    simp only [ite_not, Nat.cast_pow, log_pow, Nat.cast_add, Nat.cast_ofNat, CharP.cast_eq_zero,
      zero_add, pow_one, one_mul, Nat.cast_one, one_div]
    trans -∑' (k : ℕ), (1 : ℝ) / ((k + 2) * n ^ (k + 2))
    · congr
      ext k
      have : ¬(Nat.Prime (n ^ (k + 2))) := by exact Nat.Prime.not_prime_pow (by grind)
      simp only [this, ↓reduceIte, one_div, mul_inv_rev]
      rw [vonMangoldt_apply_pow (by grind), vonMangoldt_apply_prime hn]
      have : log n ≠ 0 := by simp; grind [hn.two_le]
      field
    · rw [← tsum_neg]
      ring_nf
      congr
      ext
      ring_nf
  · ring

@[blueprint
  "Meissel-Mertens-eq"
  (title := "Formula for Meissel-Mertens constant")
  (statement := /-- One has $M = \gamma + \sum_p \log(1-\frac{1}{p}) + \frac{1}{p}$.
-/)
  (proof := /-- The RHS can be Taylor expanded as $\sum_{j=2}^\infty \sum_p \frac{1}{jp^j}$.  Meanwhile, the difference between $\sum_{n \leq x} \frac{\Lambda(n)}{n \log n}$ and $\sum_{p \leq x} \frac{1}{p}$ is equal to $\sum_{j=2}^\infty \sum_{p: p^j \leq x} \frac{1}{j p^j}$.  Applying the monotone convergence theorem, Lemma \ref{Mertens-second-error-prime-abs-le}, and Lemma \ref{Mertens-second-error-mangoldt-bound} gives the claim.  -/)
  (discussion := 1328)]
theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
  rw [← tsum_M_eq_f_eq_tsum, M_eq_f.HasSum.tsum_eq]
  ring

@[blueprint
  "Mertens-third-error"
  (title := "The remainder term in Mertens third theorem ")
  (statement := /-- We define $E_3(x) := \sum_{p \leq x} \log (1 - \frac{1}{p}) + \log\log x + \gamma$.
-/)]
noncomputable def E₃ (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, log (1 - (1:ℝ) / p) + log (log x) + eulerMascheroniConstant

@[blueprint
  "Mertens-third-theorem-error"
  (title := "Mertens' third theorem error term")
  (statement := /-- For any $x \geq 2$, one has
$$ \prod_{p \leq x} \left(1 - \frac{1}{p}\right) = \frac{e^{-\gamma}}{\log x} \exp(E_3(x)). $$
-/)
  (proof := /-- Immediate from definition
  -/)
  (discussion := 1329)]
theorem prod_one_minus_div_prime_eq {x : ℝ} (hx : 1 < x) :
    ∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p) =
      exp (-eulerMascheroniConstant) * exp (E₃ x) / log x := by
  have hlog : 0 < log x := log_pos hx
  have hpos : ∀ {p : ℕ}, p.Prime → (0 : ℝ) < 1 - 1 / p := fun {p} hp ↦ by
    have : (2 : ℝ) ≤ p := mod_cast hp.two_le
    grind [one_div_le_one_div_of_le two_pos this]
  rw [E₃, exp_add, exp_add, exp_sum, exp_log hlog, exp_neg,
    prod_congr rfl fun p hp ↦ exp_log (hpos (mem_filter.mp hp).2)]
  field_simp

noncomputable abbrev M_eq_summand (p : ℕ) := if p.Prime then log (1 - 1 / p) + 1 / p else 0

lemma M_eq_summand_bound (n : ℕ) :
    |M_eq_summand n| ≤ 2 / n ^ 2 := by
  unfold M_eq_summand
  split_ifs with h
  · trans 1 / n ^ 2 / (1 - 1 / n)
    · convert abs_log_sub_add_sum_range_le (x := 1 / n) _ 1 using 1
      · rw [add_comm]
        simp
      · rw [abs_of_nonneg (by simp)]
        ring
      · simpa using inv_lt_one_of_one_lt₀ (mod_cast h.one_lt)
    rw [(by ring : (2 : ℝ) / n ^ 2 = 1 / n ^ 2 / (1 / 2))]
    gcongr
    suffices (1 : ℝ) / n ≤ 1 / 2 by linarith
    gcongr
    exact_mod_cast h.two_le
  · rw [abs_zero]
    positivity

lemma M_eq_summable : Summable M_eq_summand := by
  apply Summable.of_abs
  exact Summable.of_nonneg_of_le (by simp) M_eq_summand_bound (Summable.const_div (by simp) _)

lemma tsum_M_eq_summand_eq :
    ∑' (n : ℕ), M_eq_summand n = M - γ := by
  rw [M.eq]
  grind

lemma sum_one_div_sq_le {N : ℝ} (hN : 1 ≤ N) :
    ∑' (n : ℕ), (1 : ℝ) / (n + N) ^ 2 ≤ 2 / N := by
  grw [AntitoneOn.tsum_le_integral (f := (fun t ↦ 1 / (t + N) ^ 2))]
  · have hd : ∀ x ∈ Set.Ici 0, HasDerivAt (fun t ↦ -1 / (t + N)) (1 / (x + N) ^ 2) x := by
      intro t ht
      convert HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
      · ring
      · simpa using hasDerivAt_id' t
      · simp at ht
        linarith
    have lim : Tendsto (fun t ↦ -1 / (t + N)) atTop (nhds 0) := by
      exact (tendsto_atTop_add_const_right atTop N tendsto_id).const_div_atTop _
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd (fun _ _ ↦ (by positivity)) lim]
    ring_nf
    rw [mul_two]
    gcongr
    field_simp
    exact hN
  · unfold AntitoneOn
    intro a ha b hb h
    beta_reduce
    simp at ha hb
    gcongr
  · convert integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
    simp
    rfl
  · exact fun _ _ ↦ (by positivity)

lemma sum_M_eq_summand_le {N : ℕ} (hN : 0 < N) :
    |∑ n ∈ range N, M_eq_summand n - (M - γ)| ≤ 4 / N := by
  rw [← tsum_M_eq_summand_eq, ← M_eq_summable.sum_add_tsum_nat_add N]
  simp only [sub_add_cancel_left, abs_neg]
  rw [← norm_eq_abs]
  have summable := summable_nat_add_iff N|>.mpr M_eq_summable.norm
  apply norm_tsum_le_tsum_norm summable|>.trans
  apply Summable.tsum_le_tsum (fun _ ↦ M_eq_summand_bound _) summable _|>.trans
  · conv => lhs; arg 1; ext; rw [← mul_one_div]
    rw [tsum_mul_left]
    push_cast
    grw [sum_one_div_sq_le (mod_cast hN)]
    ring_nf
    rfl
  · exact (summable_nat_add_iff N|>.mpr (summable_one_div_nat_pow.mpr one_lt_two))|>.const_div _

lemma sum_M_eq_summand_le' {x : ℝ} (hx : 2 ≤ x) :
    |∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)| ≤ 4 / x := by
  have := sum_M_eq_summand_le (by grind : 0 < ⌊x⌋₊ + 1)
  rw [Nat.range_eq_Icc_zero_sub_one _ (by grind), ← add_sum_Ioc_eq_sum_Icc (by grind),
    (by simp : M_eq_summand 0 = 0), zero_add] at this
  simp only [add_tsub_cancel_right, Nat.cast_add, Nat.cast_one] at this
  grw [this]
  gcongr
  exact Nat.lt_floor_add_one _|>.le

@[blueprint
  "Mertens-third-theorem-error-le"
  (title := "Mertens' third theorem error bound")
  (statement := /-- For any $x \geq 2$, one has
$$ E_3(x) = O\left(\frac{1}{\log x}\right) $$
-/)
  (proof := /--Estimating the error in \ref{Meissel-Mertens-eq} using the first order Taylor expansion of log one gets 
$$\sum_{p \le x}(\log (1-1/p)+1/p) = (M - \gamma) + O(1/x).$$
The result follows by combining with \ref{Mertens-second-error-prime-abs-le}.
  -/)
  (discussion := 1330)]
theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
  unfold E₃
  refine ⟨4 + (log 4 + 6 + E₁), fun x hx ↦ ?_⟩
  calc
  _ = |(∑ n ∈ Ioc 0 ⌊x⌋₊, M_eq_summand n - (M - γ)) - E₂p x| := by
    unfold E₂p
    have (n : ℕ) : M_eq_summand n = (if n.Prime then log (1 - 1 / n) else 0) + (if n.Prime then (1 : ℝ) / n else 0) := by
      unfold M_eq_summand
      split_ifs
      · rfl
      · ring
    simp_rw [this]
    rw [sum_filter, sum_filter, sum_add_distrib, γ.eq_eulerMascheroni]
    ring_nf
  _ ≤ _ := by
    grw [abs_sub, E₂p.abs_le hx, sum_M_eq_summand_le' hx]
    have : 4 / x ≤ 4 / log x := by
      gcongr
      · exact log_pos (by linarith)
      · exact log_le_self (by linarith)
    grw [this]
    rw [← add_div]

@[blueprint
  "Mertens-third-theorem-error-le"]
theorem E₃.bound : E₃ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop, ge_iff_le]
    obtain ⟨ C, hC ⟩ := E₃.abs_le
    use C, 2
    convert hC using 3 with x hx
    have : 0 < log x := by apply log_pos; linarith
    have : 0 < 1 / log x := by positivity
    grind [abs_of_pos this]

@[blueprint
  "Mertens-third-theorem-error-le"]
theorem E₃.bound' : E₃ =o[atTop] (fun _ ↦ (1:ℝ)) := E₃.bound.trans_isLittleO inv_log_eq_o_one

@[blueprint
  "Mertens-third-theorem-error-le"]
theorem E₃.bound'' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p)) ~[atTop] (fun x ↦ exp (-eulerMascheroniConstant) / log x) := by
   rw [isEquivalent_iff_tendsto_one]
   · convert Tendsto.congr' ?_ (Tendsto.rexp ((isLittleO_one_iff ℝ).mp E₃.bound')) using 2 with x
     · simp
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop, ge_iff_le]; use 2; intro x hx
     rw [prod_one_minus_div_prime_eq (by linarith)]
     have : 0 < log x := by apply log_pos; linarith
     field_simp
   simp only [ne_eq, div_eq_zero_iff, exp_ne_zero, log_eq_zero, eventually_atTop]; use 2
   grind

@[blueprint
  "Mertens-third-theorem-error-le"]
theorem E₃.bound''' : (fun x ↦ ∏ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1 - (1:ℝ) / p) - exp (-eulerMascheroniConstant) / log x) =O[atTop] (fun x ↦ 1 / (log x)^2) := by
  obtain ⟨c, hc⟩ := E₃.abs_le
  rw [isBigO_iff]
  refine ⟨exp (-eulerMascheroniConstant) * 2 * c, ?_⟩
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop c.exp] with x hx hx2
  rw [prod_one_minus_div_prime_eq (by linarith)]
  specialize hc x hx
  rw [norm_eq_abs, norm_eq_abs]
  calc
  _ = |exp (-eulerMascheroniConstant) / log x * (exp (E₃ x) - 1)| := by ring_nf
  _ = |exp (-eulerMascheroniConstant) / log x| * |exp (E₃ x) - 1| := by rw [abs_mul]
  _ ≤ _ := by
    have : |E₃ x| ≤ 1 := by
      apply hc.trans
      have := log_le_log (exp_pos _) hx2
      rw [log_exp] at this
      apply div_le_one_iff.mpr <| Or.inl ⟨log_pos (by linarith), this⟩
    grw [abs_exp_sub_one_le this, hc]
    apply le_of_eq
    rw [abs_div, abs_div, abs_one, abs_of_nonneg (exp_nonneg _), abs_of_nonneg (log_nonneg (by linarith)), abs_of_nonneg (sq_nonneg _)]
    ring

end Mertens
