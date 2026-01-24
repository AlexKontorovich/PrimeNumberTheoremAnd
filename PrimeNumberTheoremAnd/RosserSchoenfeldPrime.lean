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
open Chebyshev Finset Nat Real MeasureTheory Filter

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
theorem pnt : ∃ C ≥ 0, ∀ x ≥ 2, |θ x - x| ≤ C * x / log x ^ 2 := by sorry

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
  have hae : (fun t ↦ deriv (fun s ↦ f s / log s) t) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
    derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) := by
    filter_upwards [hm] with y hy
    have : Set.Icc 2 x ∈ 𝓝 y := mem_nhds_iff.2
      ⟨Set.Ioo 2 x, Set.Ioo_subset_Icc_self, ⟨isOpen_Ioo, hy⟩⟩
    refine (DifferentiableAt.derivWithin ?_ (uniqueDiffWithinAt_of_mem_nhds (hcc ▸ this))).symm
    refine ((hf y (Set.Ioo_subset_Icc_self hy)).differentiableAt this).fun_div
      (differentiableAt_log (by simp_all; linarith)) ?_
    linarith [Real.log_pos (by simp_all; linarith)]
  calc
  _ = f x * (θ x - x) / log x + x * f x / log x -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    rw [eq_413 hx hf, ← tsub_add_eq_tsub_tsub, ← intervalIntegral.integral_add _
      (hd.continuousOn_mul (by fun_prop))]
    · ring_nf
    · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 ?_
      have hb : ∀ᵐ y ∂volume.restrict (Set.Ioc 2 x), ‖θ y - y‖ ≤ θ x + x := by
        refine ae_restrict_of_forall_mem measurableSet_Ioc (fun y hy => ?_)
        calc
        _ ≤ ‖θ y‖ + ‖y‖ := by bound
        _ = θ y + y := by rw [norm_of_nonneg (theta_nonneg y), norm_of_nonneg (by grind : 0 ≤ y)]
        _ ≤ θ x + x := add_le_add (theta_mono hy.2) hy.2
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 hd).bdd_mul
        (theta_mono.measurable.aestronglyMeasurable.sub (by fun_prop)) hb
  _ = f x * (θ x - x) / log x +
    ((∫ y in 2..x, 1 * (f y / log y) + y * derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) y) +
    2 * f 2 / log (2 : ℝ)) -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    rw [← sub_add_cancel (x * f x / log x) (2 * f 2 / log (2 : ℝ)),
      intervalIntegral.integral_deriv_mul_eq_sub_of_hasDerivWithinAt, mul_div, mul_div]
    · intro y _; exact (hasDerivAt_id' y).hasDerivWithinAt
    · refine fun y hy => (hcc ▸ (hf y (hcc ▸ hy)).fun_div ?_ ?_).hasDerivWithinAt
      · exact (differentiableAt_log (by simp_all; linarith)).differentiableWithinAt
      · linarith [Real.log_pos (by simp_all; linarith)]
    · exact intervalIntegral.intervalIntegrable_const
    · exact hd.congr_ae (hoc ▸ hae)
  _ = f x * (θ x - x) / log x +
    ((∫ y in 2..x, f y / log y) + (∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y) +
    2 * f 2 / log (2 : ℝ)) -
    (∫ y in 2..x, (θ y - y) * deriv (fun t ↦ f t / log t) y) -
    ∫ y in 2..x, y * deriv (fun t ↦ f t / log t) y := by
    have : (fun y ↦ y * deriv (fun t ↦ f t / log t) y) =ᶠ[ae (volume.restrict (Set.Ioc 2 x))]
      fun y ↦ y * derivWithin (fun t ↦ f t / log t) (Set.uIcc 2 x) y := by
      filter_upwards [Filter.eventually_iff.1 hae.eventually] with y hy
      grind
    have hi := intervalIntegral.integral_congr_ae_restrict (hoc ▸ this)
    simp only [one_mul, sub_left_inj, add_right_inj, add_left_inj, hi]
    refine intervalIntegral.integral_add (ContinuousOn.intervalIntegrable_of_Icc hx ?_) ?_
    · exact ContinuousOn.div₀ (by fun_prop) (continuousOn_log.mono (by grind))
        (fun x hx => by linarith [Real.log_pos (by simp_all; linarith)])
    · exact (hd.continuousOn_mul (by fun_prop)).congr_ae (hoc ▸ this)
  _ = _ := by ring

@[blueprint
  "rs-416"
  (title := "RS equation (4.16)")
  (statement := /--
  $$L_f := \frac{2f(2)}{\log 2} - \int_2^\infty (\vartheta(y) - y) \frac{d}{dy} (\frac{f(y)}{\log y})\ dy.$$ -/)]
noncomputable def L (f : ℝ → ℝ) : ℝ :=
    2 * f 2 / Real.log 2 - ∫ y in Set.Ioi 2, (θ y - y) * deriv (fun t ↦ f t / log t) y

open intervalIntegral in
theorem _root_.intervalIntegral.interval_add_Ioi {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {a b : ℝ} {f : ℝ → E} {μ : Measure ℝ} (ha : IntegrableOn f (Set.Ioi a) μ)
    (hb : IntegrableOn f (Set.Ioi b) μ) :
    ∫ (x : ℝ) in a..b, f x ∂μ + ∫ (x : ℝ) in Set.Ioi b, f x ∂μ
    = ∫ (x : ℝ) in Set.Ioi a, f x ∂μ := by
  wlog hab : a ≤ b generalizing a b
  · rw [integral_symm, ← this hb ha (le_of_not_ge hab)]; grind
  rw [integral_of_le hab, ← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (ha.mono_set Set.Ioc_subset_Ioi_self) hb, Set.Ioc_union_Ioi_eq_Ioi hab]

theorem intervalIntegrable_inv_log_pow (n : ℕ) (m : ℕ) {x : ℝ} (hx : 1 < x) (y : ℝ) :
    IntegrableOn (fun t ↦ 1 / (t ^ n * Real.log t ^ m)) (Set.Ioc x y) volume := by
  by_cases h : x < y
  · refine (ContinuousOn.integrableOn_Icc ?_).mono_set Set.Ioc_subset_Icc_self
    refine ContinuousOn.div₀ (by fun_prop) (ContinuousOn.mul (by fun_prop) ?_) ?_
    · exact (continuousOn_log.mono (by grind)).pow m
    · simp_all; grind
  · simp_all

theorem ioiIntegrable_inv_log_pow {n : ℕ} (hn : 1 < n) {x : ℝ} (hx : 1 < x) :
    IntegrableOn (fun t ↦ 1 / (t * Real.log t ^ n)) (Set.Ioi x) volume := by
  refine integrableOn_Ioi_of_intervalIntegral_norm_tendsto (log x ^ (1 - (n : ℝ)) / (n - 1)) x
    (fun k => ?_) tendsto_natCast_atTop_atTop ?_
  · simpa using intervalIntegrable_inv_log_pow 1 n hx k
  · have : 0 < (n : ℝ) - 1 := by linarith [(one_lt_cast (α := ℝ)).2 hn]
    refine Tendsto.congr' (f₁ := fun i : ℕ => (log i : ℝ) ^ (1 - (n : ℝ)) / (1 - (n : ℝ)) -
      (log x) ^ (1 - (n : ℝ)) / (1 - (n : ℝ))) ?_ ?_
    · have := tendsto_def.1 tendsto_natCast_atTop_atTop (Set.Ici x) (Ici_mem_atTop x)
      filter_upwards [this] with i hi
      refine (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun r => log r ^ (1 - (n : ℝ)) / (1 - (n : ℝ))) (fun z hz => ?_) ?_).symm
      · simp_all only [preimage_Ici, Set.mem_Ici, ceil_le, Set.uIcc_of_le, Set.mem_Icc]
        have := Real.log_pos (by linarith)
        rw [norm_of_nonneg <| one_div_nonneg.2 (mul_nonneg (by grind) (pow_nonneg this.le n))]
        refine (((hasDerivAt_log (by grind)).rpow_const (by grind)).div_const _).congr_deriv ?_
        have : 1 - (n : ℝ) ≠ 0 := by linarith
        simp [field]
      · apply IntervalIntegrable.norm
        simpa using (intervalIntegrable_iff_integrableOn_Ioc_of_le hi).2
          (intervalIntegrable_inv_log_pow 1 n hx i)
    · suffices h : Tendsto (fun i : ℕ ↦ Real.log i ^ (1 - (n : ℝ)) / (1 - n)) atTop (𝓝 0) from by
        have : (log x ^ (1 - (n : ℝ)) / (n - 1)) = 0 - (log x ^ (1 - (n : ℝ)) / (1 - n)) := by grind
        exact this ▸ h.sub_const (log x ^ (1 - (n : ℝ)) / (1 - n))
      simpa using (((tendsto_rpow_neg_atTop this).comp tendsto_log_atTop).comp
        tendsto_natCast_atTop_atTop).div_const (1 - (n : ℝ))

theorem bound_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    ∀ᵐ (a : ℝ) ∂volume.restrict (Set.Ioi 2), ‖deriv (fun t ↦ f t / log t) a‖ ≤
    C * (1 / (a ^ 2 * log a) + 1 / (a ^ 2 * log a ^ 2)) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  calc
  _ = ‖deriv f a / log a - f a / (a * log a ^ 2)‖ := by
    congr
    rw [deriv_fun_div, deriv_log]
    · field_simp
    · exact hf.differentiableAt (mem_nhds_iff.2 ⟨Set.Ioi 2, Set.Ioi_subset_Ici_self,
        ⟨isOpen_Ioi, ha⟩⟩)
    · exact differentiableAt_log_iff.2 (by grind)
    · simp_all; grind
  _ ≤ ‖deriv f a‖ / ‖log a‖ + ‖f a‖ / ‖a * log a ^ 2‖ := by rw [← norm_div, ← norm_div]; bound
  _ = |deriv f a| / ‖log a‖ + |f a| / ‖a * log a ^ 2‖ := by simp
  _ ≤ C / a ^ 2 / ‖log a‖ + C / a / ‖a * log a ^ 2‖ := by
    gcongr
    exacts [(hC a (Set.Ioi_subset_Ici_self ha)).2, (hC a (Set.Ioi_subset_Ici_self ha)).1]
  _ = C / a ^ 2 / log a + C / a / (a * log a ^ 2) := by
    congr <;> rw [norm_of_nonneg]
    · exact log_nonneg (by grind)
    · exact mul_nonneg (by grind) (pow_nonneg (log_nonneg (by grind)) 2)
  _ = _ := by field_simp

theorem integrableOn_deriv {f : ℝ → ℝ} (hf : DifferentiableOn ℝ f (Set.Ici 2)) {C : ℝ}
    (hC : ∀ x ∈ Set.Ici 2, |f x| ≤ C / x ∧ |deriv f x| ≤ C / x ^ 2) :
    IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume
    ∧ ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x := by
  obtain ⟨A, hA⟩ := pnt
  refine ⟨Integrable.mono' (g := fun t => (A * C) * (1 / (t * log t ^ 3) + 1 / (t * log t ^ 4)))
    ?_ ?_ ?_, fun x hx => ?_⟩
  · refine ((ioiIntegrable_inv_log_pow ?_ ?_).add (ioiIntegrable_inv_log_pow ?_ ?_)).const_mul
      (A * C) <;> linarith
  · exact (theta_mono.measurable.aestronglyMeasurable.sub (by fun_prop)).mul
      (aestronglyMeasurable_deriv _ _)
  · filter_upwards [bound_deriv hf hC, ae_restrict_mem measurableSet_Ioi] with a ha ho
    calc
    _ = |(θ a - a)| * ‖deriv (fun t ↦ f t / log t) a‖ := by simp
    _ ≤ A * a / log a ^ 2 * (C * (1 / (a ^ 2 * log a) + 1 / (a ^ 2 * log a ^ 2))) := by
      gcongr
      · exact div_nonneg (mul_nonneg hA.1 (by grind)) (pow_nonneg (log_nonneg (by grind)) 2)
      · exact hA.2 a (Set.mem_Ioi.1 ho).le
    _ = _ := by field_simp
  · refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (Integrable.mono'
      (Integrable.const_mul (Integrable.add ?_ ?_) C) (aestronglyMeasurable_deriv _ _)
      (ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Ioi_self (bound_deriv hf hC)))
    · simpa using intervalIntegrable_inv_log_pow 2 1 (by linarith : 1 < (2 : ℝ)) x
    · simpa using intervalIntegrable_inv_log_pow 2 2 (by linarith : 1 < (2 : ℝ)) x

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
    (hft : IntegrableOn (fun y ↦ (θ y - y) * deriv (fun t ↦ f t / log t) y) (Set.Ioi 2) volume)
    (hfi : IntervalIntegrable (fun t ↦ deriv (fun s ↦ f s / Real.log s) t) volume 2 x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), f p = (∫ y in 2..x, f y / log y) + L f +
    f x * (θ x - x) / log x + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ f s / log s) y := by
  rw [eq_414 hx (hf.mono Set.Icc_subset_Ici_self) hfi, L, ← intervalIntegral.interval_add_Ioi hft
    (hft.mono_set (Set.Ioi_subset_Ioi hx))]
  ring

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

lemma integral_eq_loglog {x : ℝ} (hx : 2 ≤ x) :
    ∫ y in 2..x, 1 / y / log y = log (log x) - log (log 2) := by
  have {y} (hy : y ∈ Set.uIcc 2 x) := (Set.uIcc_of_le hx ▸ hy).1
  have {y} (hy : y ∈ Set.uIcc 2 x) : log y ≠ 0 := log_ne_zero_of_pos_of_ne_one (by grind) (by grind)
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.log ∘ log) (fun y hy => ?_) ?_
  · convert (hasDerivAt_log (this hy)).comp y (hasDerivAt_log (by grind)) using 1
    field_simp
  · exact ContinuousOn.intervalIntegrable_of_Icc hx (by fun_prop (disch := aesop))

theorem ioiIntegral_tendsto_zero {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {μ : Measure ℝ} (a : ℝ) (hfi : IntegrableOn f (Set.Ioi a) μ)
    {l : Filter ι} {b : ι → ℝ} [IsCountablyGenerated l] (hb : Tendsto b l atTop) :
    Tendsto (fun i => ∫ x in Set.Ioi (b i), f x ∂μ) l (𝓝 0) := by
  have : ∀ᶠ i in l, ∫ x in Set.Ioi a, f x ∂μ - ∫ x in a..b i, f x ∂μ =
    ∫ x in Set.Ioi (b i), f x ∂μ := by
    filter_upwards [hb.eventually_mem (Ici_mem_atTop a)] with i hi
    rw [sub_eq_iff_eq_add', intervalIntegral.interval_add_Ioi hfi
      (hfi.mono_set (Set.Ioi_subset_Ioi hi))]
  exact Tendsto.congr' this (sub_self (∫ x in Set.Ioi a, f x ∂μ) ▸ (Tendsto.const_sub _ <|
    intervalIntegral_tendsto_integral_Ioi a hfi hb))

@[blueprint
  "Meissel-Mertens-constant"
  (title := "Meissel-Mertens constant B")
  (statement := /--
  $B := \lim_{x \to \infty} \left( \sum_{p \leq x} \frac{1}{p} - \log \log x \right)$. -/)]
noncomputable def _root_.meisselMertensConstant : ℝ := - log (log 2) + L (fun x => 1 / x)

theorem integrableOn_deriv_inv : IntegrableOn (fun y ↦ (θ y - y) *
    deriv (fun t ↦ 1 / t / Real.log t) y) (Set.Ioi 2) volume ∧
    ∀ x ≥ 2, IntervalIntegrable (fun t ↦ deriv (fun s ↦ 1 / s / Real.log s) t) volume 2 x := by
  refine integrableOn_deriv (C := 1) (by fun_prop (disch := grind)) (fun x hx => ⟨?_, ?_⟩)
  · rw [abs_of_nonneg (one_div_nonneg.2 (by grind))]
  · rw [deriv_fun_div (differentiableAt_const 1) differentiableAt_id (by grind), abs_div]
    simp

theorem meisselMertensConstant_identity {x : ℝ} (hx : 2 ≤ x) :
    ∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) =
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x) +
    ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y := by
  rw [eq_415 (by fun_prop (disch := grind)) hx integrableOn_deriv_inv.1
    (integrableOn_deriv_inv.2 x hx), integral_eq_loglog hx, meisselMertensConstant]
  ring

@[blueprint
  "rs-419"]
theorem mertens_second_theorem : Filter.atTop.Tendsto (fun x : ℝ ↦
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)) (𝓝 meisselMertensConstant) := by
  have lem : ∀ᶠ x in atTop, meisselMertensConstant + ((θ x - x) / (x * log x) +
    ∫ y in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y) =
    ∑ p ∈ filter Nat.Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x):= by
    filter_upwards [Ici_mem_atTop 2] with y hy
    rw [meisselMertensConstant_identity hy]
    ring
  rw [← add_zero meisselMertensConstant, ← add_zero 0]
  refine (tendsto_const_nhds.add (Tendsto.add ?_
    (ioiIntegral_tendsto_zero 2 integrableOn_deriv_inv.1 tendsto_id))).congr' lem
  · obtain ⟨C, hC⟩ := pnt
    refine squeeze_zero_norm' (a := fun x => C / Real.log x ^ 3) ?_ ?_
    · filter_upwards [Ici_mem_atTop 2] with y hy
      have h1 {y : ℝ} (hy : y ∈ Set.Ici 2) : 0 < y := by grind
      have h2 {y : ℝ} (hy : y ∈ Set.Ici 2) : 0 ≤ log y := log_nonneg (by grind)
      simp only [norm_div, norm_mul, norm_of_nonneg (h1 hy).le, norm_eq_abs, norm_of_nonneg (h2 hy)]
      grw [hC.2 y hy]
      · rw [div_right_comm, ← div_div, mul_div_cancel_right₀ _ (by grind)]; field_simp; rfl
      · exact mul_nonneg (h1 hy).le (h2 hy)
    · exact ((tendsto_pow_atTop (by linarith : 3 ≠ 0)).comp tendsto_log_atTop).const_div_atTop C

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
    log (log x) + meisselMertensConstant + (θ x - x) / (x * log x)
    - ∫ y in Set.Ioi x, (θ y - y) * (1 + log y) / (y ^ 2 * log y ^ 2) := by
  simp_rw [meisselMertensConstant_identity hx, sub_eq_add_neg _ (∫ y in Set.Ioi x, _),
    ← integral_neg, ← div_neg, mul_div_assoc]
  have : ∫ (y : ℝ) in Set.Ioi x, (θ y - y) * deriv (fun s ↦ 1 / s / Real.log s) y =
    ∫ (a : ℝ) in Set.Ioi x, (θ a - a) * ((1 + Real.log a) / -(a ^ 2 * Real.log a ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => mul_eq_mul_left_iff.2 (Or.inl ?_)
    have := deriv_fun_inv'' (y.hasDerivAt_mul_log (by grind)).differentiableAt
      (mul_ne_zero_iff.2 ⟨by grind, by linarith [Real.log_pos (by grind : 1 < y)]⟩)
    simp_all [deriv_mul_log (by grind : y ≠ 0), div_eq_mul_inv, mul_comm]
    ring
  congr

@[blueprint
  "rs-419"]
theorem mertens_second_theorem' :
    ∃ C, ∀ x ≥ 2, |∑ p ∈ filter Prime (Iic ⌊x⌋₊), 1 / (p : ℝ) - log (log x)| ≤ C := by
  obtain ⟨C, hC⟩ := pnt
  refine ⟨|meisselMertensConstant| + C / Real.log 2 ^ 3 +
    ∫ y in Set.Ioi 2, |(θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y|, fun x hx => ?_⟩
  calc
  _ ≤ |meisselMertensConstant + (θ x - x) / (x * log x)
    + ∫ y in Set.Ioi x, (θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y| := by
    rw [meisselMertensConstant_identity hx]; ring_nf; rfl
  _ ≤ |meisselMertensConstant| + |(θ x - x) / (x * log x)|
    + ∫ y in Set.Ioi x, |(θ y - y) * deriv (fun t ↦ 1 / t / Real.log t) y| := by
    grw [sub_eq_add_neg, abs_add_le, abs_add_le, abs_integral_le_integral_abs]
  _ ≤ _ := by
    gcongr
    · grw [abs_div, hC.2 x hx, abs_of_nonneg (mul_nonneg (by grind) (log_nonneg (by grind))),
        div_right_comm, ← div_div, mul_div_cancel_right₀ _ (by grind)]
      ring_nf
      gcongr
      · exact hC.1
      · exact inv_nonneg.2 (log_nonneg (by grind))
    · filter_upwards with a
      apply abs_nonneg
    · exact integrableOn_deriv_inv.1.abs

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
