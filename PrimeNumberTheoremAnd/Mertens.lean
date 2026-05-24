import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Architect


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

section EulerMaclaurin
open Finset Interval MeasureTheory

/-! We prove the 1st order Euler-Maclaurin formula by specialising Abel summation and manipulating integrals. -/

variable {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {a b : ℝ}

/-- The 1st Bernoulli function. -/
noncomputable def B1 (x : ℝ) : ℝ := x - ⌊x⌋₊ - 1 / 2

@[fun_prop]
lemma aestronglyMeasurable_B1 : AEStronglyMeasurable B1 := by
  unfold B1
  fun_prop

lemma abs_B1_le_half {x : ℝ} (hx : 0 ≤ x) : |B1 x| ≤ 1 / 2 := by
  unfold B1
  refine abs_le.mpr ⟨?_, ?_⟩
  · grind [Nat.floor_le hx]
  · grind [Nat.lt_succ_floor x]

lemma integral_deriv_mul_add_const (c : 𝕜) (hab : a ≤ b) (h_int : IntervalIntegrable (deriv f) volume a b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) :
    ∫ t in a..b, (t + c) * deriv f t = (b + c) * f b - (a + c) * f a - ∫ t in a..b, f t := by
  rw [← Set.uIcc_of_le hab] at hf_diff
  have : ∀ t ∈ [[a, b]], HasDerivAt (fun (t : ℝ) ↦ t + c) 1 t := by
    intro t ht
    simp only [hasDerivAt_add_const_iff]
    convert ContinuousLinearMap.hasDerivAt (RCLike.ofRealCLM (K := 𝕜)) using 1
    simp
  replace hf_diff := fun t ht ↦ (hf_diff t ht).hasDerivAt
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul this hf_diff (by simp) h_int]
  simp

lemma intervalIntegrable_deriv_mul_B1 (ha : 0 ≤ a) (hab : a ≤ b) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    IntervalIntegrable (fun t ↦ deriv f t * B1 t) volume a b := by
  refine IntervalIntegrable.continuousOn_mul ?_ h_cont
  rw [intervalIntegrable_iff']
  apply MeasureTheory.Measure.integrableOn_of_bounded (by simp) (by fun_prop) (M := 1 / 2)
  filter_upwards [self_mem_ae_restrict (by measurability)] with x hx
  rw [Set.uIcc_of_le hab, Set.mem_Icc] at hx
  norm_cast
  exact abs_B1_le_half (by linarith)

lemma integral_deriv_mul_floor_add_one (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t) (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∫ t in a..b, deriv f t * (⌊t⌋₊ + 1) = (b + 1 / 2) * f b - (a + 1 / 2) * f a - (∫ t in a..b, f t) - ∫ t in a..b, deriv f t * B1 t := by
  calc
  _ = ∫ t in a..b, (deriv f t * (t + 1 / 2) -deriv f t * B1 t) := by
    congr
    ext
    simp only [B1]
    push_cast
    ring
  _ = (∫ t in a..b, deriv f t * (t + 1 / 2)) - ∫ t in a..b, deriv f t * B1 t := by
    exact intervalIntegral.integral_sub (ContinuousOn.intervalIntegrable (by fun_prop)) (intervalIntegrable_deriv_mul_B1 ha hab h_cont)
  _ = _ := by
    conv => lhs; arg 1; arg 1; ext; rw [mul_comm]
    rw [integral_deriv_mul_add_const _ hab h_cont.intervalIntegrable hf_diff]

theorem sum_eq_integral_add_integral_deriv (ha : 0 ≤ a) (hab : a ≤ b)
    (hf_diff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t)
    (h_cont : ContinuousOn (deriv f) [[a, b]]) :
    ∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, f k =
      f a * B1 a - f b * B1 b + (∫ t in a..b, f t) + ∫ t in a..b, deriv f t * B1 t  := by
  have := sum_mul_eq_sub_sub_integral_mul (fun _ ↦ 1) ha hab hf_diff (Set.uIcc_of_le hab ▸ h_cont).integrableOn_Icc
  simp only [mul_one, sum_const, Nat.card_Icc, tsub_zero, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_one] at this
  rw [this, ← intervalIntegral.integral_of_le hab]
  rw [integral_deriv_mul_floor_add_one ha hab hf_diff h_cont]
  unfold B1
  push_cast
  ring

end EulerMaclaurin

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

#check ArithmeticFunction.vonMangoldt_sum

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
  rw [isBigO_iff]
  obtain ⟨c, hc1, hc2⟩:= E₁Λ.bounded'
  use c
  filter_upwards [eventually_ge_atTop 1] with x hx
  convert hc2 x hx
  simp


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



@[blueprint
  "E1_bound"
  (title := "Upper bound on $E_1$")
  (statement := /-- One has $E_1 \leq \frac{5 \log 2 + 3}{4}$-/)
  (proof := /-- We can bound $E_1 \leq \sum_{n=2}^\infty \frac{\log n}{n(n-1)} \leq \frac{\log 2}{2} + \frac{3}{2} \sum_{n=3}^\infty \frac{\log n}{n^2}$.  Calculus shows that $\log x / x^2$ is decreasing for $x \geq 2 > e^{1/2}$, so we can bound $\sum_{n=3}^\infty \frac{\log n}{n^2} \leq \int_2^\infty \frac{\log t}{t^2}\ dt = \frac{\log 2+1}{2}$.-/)
  (latexEnv := "proposition")
  (discussion := 1316)]
theorem E₁.le : E₁ ≤ (5 * log 2 + 3) / 4 := by
    sorry

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

@[blueprint
  "Meissel-Mertens-eq"
  (title := "Formula for Meissel-Mertens constant")
  (statement := /-- One has $M = \gamma + \sum_p \log(1-\frac{1}{p}) + \frac{1}{p}$.
-/)
  (proof := /-- The RHS can be Taylor expanded as $\sum_{j=2}^\infty \sum_p \frac{1}{jp^j}$.  Meanwhile, the difference between $\sum_{n \leq x} \frac{\Lambda(n)}{n \log n}$ and $\sum_{p \leq x} \frac{1}{p}$ is equal to $\sum_{j=2}^\infty \sum_{p: p^j \leq x} \frac{1}{j p^j}$.  Applying the monotone convergence theorem, Lemma \ref{Mertens-second-error-prime-abs-le}, and Lemma \ref{Mertens-second-error-mangoldt-bound} gives the claim.  -/)
  (discussion := 1328)]
theorem M.eq : M = γ + ∑' p : ℕ, if p.Prime then log (1 - 1 / p) + 1 / p else 0 := by
    sorry

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

@[blueprint
  "Mertens-third-theorem-error-le"
  (title := "Mertens' third theorem error bound")
  (statement := /-- For any $x \geq 2$, one has
$$ E_3(x) = O\left(\frac{1}{\log x}\right) $$
-/)
  (proof := /-- Using the Taylor expansion
  $$ \log (1 - \frac{1}{p}) = \sum_{j=1}^\infty \frac{1}{jp^j} = \sum_{j=1}^\infty \frac{\Lambda(p^j)}{p^j \log p^j}$$
  one can write
  $$ E_3(x) = E_{2,\Lambda}(x) + \sum_{p \leq x} \sum_{j \geq 2: p^j > x} \frac{j}{p^j}.$$
One can bound $\sum_{j \geq 2: p^j > x} \frac{j}{p^j}$ by $O(1/p^2)$ when $p > \sqrt{x}$ and by $O(1/x)$ when $p \leq \sqrt{x}$, so the second error here is $O(1/\sqrt{x})$, giving the claim.
  -/)
  (discussion := 1330)]
theorem E₃.abs_le : ∃ C, ∀ x, 2 ≤ x → |E₃ x| ≤ C / log x := by
    sorry

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
    sorry

end Mertens
