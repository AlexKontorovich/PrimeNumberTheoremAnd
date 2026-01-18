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

open scoped Topology
open Chebyshev Finset Nat Real MeasureTheory

lemma Chebyshev.theta_pos {y : ℝ} (hy : 2 ≤ y) : 0 < θ y := by
  refine sum_pos (fun n hn ↦ log_pos ?_) ⟨2, ?_⟩
  · simp only [mem_filter] at hn; exact_mod_cast hn.2.one_lt
  · simpa using ⟨(le_floor_iff (by grind : 0 ≤ y)).2 hy, Nat.prime_two⟩

@[blueprint
  "rs-pnt"
  (title := "A medium version of the prime number theorem")
  (statement := /-- $\vartheta(x) = x + O( x / \log^2 x)$. -/)
  (proof := /-- This in principle follows by establishing an analogue of Theorem \ref{chebyshev-asymptotic}, using mediumPNT in place of weakPNT. -/)
  (latexEnv := "theorem")
  (discussion := 597)]
theorem pnt : ∃ C, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by sorry

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
theorem pre_413 {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Ici 2)) {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
      ∫ y in Set.Icc 2 x, f y / log y ∂θ.Stieltjes.measure := by sorry

@[blueprint
  "rs-413"
  (title := "RS equation (4.13)")
  (statement := /-- $\sum_{p \leq x} f(p) = \frac{f(x) \vartheta(x)}{\log x} - \int_2^x \vartheta(y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-pre-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 650)]
theorem eq_413 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x)) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = f x * θ x / log x -
      ∫ y in 2..x, θ y * deriv (fun t ↦ f t / log t) y := by
  sorry

@[blueprint
  "rs-414"
  (title := "RS equation (4.14)")
  (statement := /--
  $$\sum_{p \leq x} f(p) = \int_2^x \frac{f(y)\ dy}{\log y} + \frac{2 f(2)}{\log 2} $$
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} - \int_2^x (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-413} and integration by parts. -/)
  (latexEnv := "sublemma")
  (discussion := 600)]
theorem eq_414 {f : ℝ → ℝ} {x : ℝ} (hx : 2 ≤ x) (hf : DifferentiableOn ℝ f (Set.Icc 2 x))
    (hd : IntervalIntegrable (fun t => deriv (fun s ↦ f s / log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p =
      (∫ y in 2..x, f y / log y) + 2 * f 2 / Real.log 2 +
      f x * (θ x - x) / log x -
      ∫ y in 2..x, (θ y - y) * deriv (fun s ↦ f s / log s) y :=
    let hcc := Set.uIcc_of_le hx
    let hoc := Set.uIoc_of_le hx
    have hm : Set.Ioo 2 x ∈ ae (volume.restrict (Set.Ioc 2 x)) := by
      by_cases hp : 2 < x
      · rw [mem_ae_iff, Measure.restrict_apply' measurableSet_Ioc, ← Set.diff_eq_compl_inter,
          Set.Ioc_diff_Ioo_same hp, volume_singleton]
      · simp_all
    have hae : (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
      derivWithin (fun t ↦ f t / Real.log t) (Set.uIcc 2 x) := by
      filter_upwards [hm] with y hy
      have : Set.Icc 2 x ∈ 𝓝 y := mem_nhds_iff.2
        ⟨Set.Ioo 2 x, Set.Ioo_subset_Icc_self, ⟨isOpen_Ioo, hy⟩⟩
      refine (DifferentiableAt.derivWithin ?_ (uniqueDiffWithinAt_of_mem_nhds (hcc ▸ this))).symm
      refine DifferentiableAt.fun_div ?_ (differentiableAt_log (by simp_all; linarith)) ?_
      · refine DifferentiableWithinAt.differentiableAt (hf y (Set.Ioo_subset_Icc_self hy)) this
      · linarith [Real.log_pos (by simp_all; linarith)]
    calc
    _ = f x * (θ x - x) / log x + x * f x / log x -
      (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
      ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
      rw [eq_413 hx hf, ← tsub_add_eq_tsub_tsub, ← intervalIntegral.integral_add _
        (IntervalIntegrable.continuousOn_mul hd (by fun_prop))]
      · ring_nf
      · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 ?_
        have hsm : AEStronglyMeasurable (fun t => θ t - t) (volume.restrict (Set.Ioc 2 x)) := by
          refine AEStronglyMeasurable.sub ?_ (by fun_prop)
          sorry
        have hb : ∀ᵐ y ∂volume.restrict (Set.Ioc 2 x), ‖θ y - y‖ ≤ θ x + x := by
          refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
          calc
          _ ≤ ‖θ y‖ + ‖y‖ := by bound
          _ = θ y + y := by rw [norm_of_nonneg (theta_nonneg y), norm_of_nonneg (by grind : 0 ≤ y)]
          _ ≤ θ x + x := add_le_add (theta_mono hy.2) hy.2
        exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hd).bdd_mul hsm hb
    _ = f x * (θ x - x) / log x +
      ((∫ y in 2..x, 1 * (f y / log y)+ y * derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) y) +
      2 * f 2 / log (2 : ℝ)) -
      (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
      ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
      rw [← sub_add_cancel (x * f x / log x) (2 * f 2 / log (2 : ℝ)),
        intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt, mul_div, mul_div]
      · intro y _; exact (hasDerivAt_id' y).hasDerivWithinAt
      · refine fun y hy => DifferentiableWithinAt.hasDerivWithinAt (hcc ▸
          DifferentiableWithinAt.fun_div (hf y (hcc ▸ hy)) ?_ ?_)
        · exact (differentiableAt_log (by simp_all; linarith)).differentiableWithinAt
        · linarith [Real.log_pos (by simp_all; linarith)]
      · exact intervalIntegral.intervalIntegrable_const
      · exact hd.congr_ae (hoc ▸ hae)
    _ = f x * (θ x - x) / log x +
      ((∫ y in 2..x, f y / log y) + (∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y) +
      2 * f 2 / log (2 : ℝ)) -
      (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
      ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
      have : (fun y ↦ y * deriv (fun t ↦ f t / Real.log t) y) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
        fun y ↦ y * derivWithin (fun t ↦ f t / Real.log t) (Set.uIcc 2 x) y := by
        filter_upwards [Filter.eventually_iff.1 hae.eventually] with y hy
        grind
      have hi := intervalIntegral.integral_congr_ae_restrict (hoc ▸ this)
      simp only [one_mul, sub_left_inj, add_right_inj, add_left_inj, hi]
      refine intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hx ?_) ?_
      · exact ContinuousOn.div₀ (by fun_prop) (continuousOn_log.mono (by grind))
          (fun x hx => by linarith [Real.log_pos (by simp_all; linarith)])
      · exact IntervalIntegrable.congr_ae (f := fun t ↦ t * deriv (fun s ↦ f s / log s) t)
          (IntervalIntegrable.continuousOn_mul hd (by fun_prop)) (hoc ▸ this)
    _ = (∫ y in 2..x, f y / log y) + 2 * f 2 / Real.log 2 +
      f x * (θ x - x) / log x -
      ∫ y in 2..x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by ring

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
  $$ + \frac{f(x) (\vartheta(x) - x)}{\log x} + \int_x^\infty (\vartheta(y) - y) \frac{d}{dy}( \frac{f(y)}{\log y} )\ dy.$$ -/)
  (proof := /-- Follows from Sublemma \ref{rs-414} and Definition \ref{rs-416}. -/)
  (latexEnv := "sublemma")
  (discussion := 601)]
theorem eq_415 {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {x : ℝ} (hx : 2 ≤ x)
   (hbound : ∃ C, ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
   ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = (∫ y in 2..x, f y / log y) + L f +
    f x * (θ x - x) / log x + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by sorry

@[blueprint
  "rs-417"
  (title := "RS equation (4.17)")
  (statement := /--
  $$\pi(x) = \frac{\vartheta(x)}{\log x} + \int_2^x \frac{\vartheta(y)\ dy}{y \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1$. -/)
  (latexEnv := "sublemma")
  (discussion := 602)]
theorem eq_417 {x : ℝ} (hx : 2 ≤ x) :
    pi x = θ x / log x + ∫ y in 2..x, θ y / (y * log y ^ 2) := by
  exact Chebyshev.primeCounting_eq_theta_div_log_add_integral hx

@[blueprint
  "rs-418"
  (title := "RS equation (4.18)")
  (statement := /--
  $$\sum_{p \leq x} \frac{1}{p} = \frac{\vartheta(x)}{x \log x} + \int_2^x \frac{\vartheta(y) (1 + \log y)\ dy}{y^2 \log^2 y}.$$
-/)
  (proof := /-- Follows from Sublemma \ref{rs-413} applied to $f(t) = 1/t$. -/)
  (latexEnv := "sublemma")
  (discussion := 652)]
theorem eq_418 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) = θ x / (x * log x) +
      ∫ y in 2..x, θ y * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  have : DifferentiableOn ℝ (fun y : ℝ ↦ 1 / y) (Set.Icc 2 x) :=
    fun y hy => by simpa [one_div] using differentiableWithinAt_inv (by grind) (Set.Icc 2 x)
  rw [eq_413 (f := fun x => 1 / x) hx this, mul_comm_div, one_mul, div_div, sub_eq_add_neg,
    ← intervalIntegral.integral_neg, add_left_cancel_iff]
  refine intervalIntegral.integral_congr fun y hy => ?_
  have hy := Set.uIcc_of_le hx ▸ hy
  have := deriv_fun_inv'' (y.hasDerivAt_mul_log (by grind)).differentiableAt
    (mul_ne_zero_iff.2 ⟨by grind, by linarith [Real.log_pos (by grind : 1 < y)]⟩)
  simp only [neg_mul_eq_mul_neg, mul_div_assoc, mul_left_cancel_iff_of_pos
  (Chebyshev.theta_pos hy.1), div_div, fun t : ℝ => one_div (t * log t), this,
  deriv_mul_log (by grind : y ≠ 0)]
  ring

@[blueprint
  "rs-419"]
theorem mertens_second_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (range ⌊x⌋₊), 1 / (p : ℝ) - log (log x) - meisselMertensConstant) (nhds 0) := by sorry

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
theorem eq_419 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
      log (log x) + meisselMertensConstant + (θ x - x) / (x * log x) - ∫ y in 2..x, (θ y - y) * (1 + log y) / (y ^ 2 * log y ^ 2) := by sorry

@[blueprint
  "rs-419"]
theorem mertens_second_theorem' :
    ∃ C, ∀ x, |∑ p ∈ filter Prime (range ⌊x⌋₊), 1 / (p : ℝ) - log (log x)| ≤ C := by sorry

@[blueprint
  "rs-420"]
theorem mertens_first_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (range ⌊x⌋₊), Real.log p / p - log x - mertensConstant) (nhds 0) := by sorry

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
theorem eq_420 {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), Real.log p / p =
      log x + mertensConstant + (θ x - x) / x - ∫ y in 2..x, (θ y - y) / (y ^ 2) := by sorry

@[blueprint
  "rs-420"]
theorem mertens_first_theorem' :
    ∃ C, ∀ x, |∑ p ∈ filter Prime (range ⌊x⌋₊), Real.log p / p - Real.log x| ≤ C := by sorry


end RS_prime
