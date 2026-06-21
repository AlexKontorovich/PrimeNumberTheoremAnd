import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Algebra.Group.Submonoid.BigOperators
import PrimeNumberTheoremAnd.EulerMaclaurin
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

section Issue1584
open MeasureTheory Set Filter Topology

/-- The integrand `log v * exp (-v)` is integrable on `Ioi 0`. -/
private lemma integrableOn_log_mul_exp_neg :
    IntegrableOn (fun v : ℝ => Real.log v * Real.exp (-v)) (Ioi 0) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (zero_le_one' ℝ), integrableOn_union]
  constructor
  · -- On `Ioc 0 1`: dominate by `|log v|`, which is integrable.
    have hlog : IntegrableOn (fun v : ℝ => Real.log v) (Ioc 0 1) volume := by
      have := (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1))
      rwa [intervalIntegrable_iff_integrableOn_Ioc_of_le (zero_le_one' ℝ)] at this
    apply Integrable.mono' hlog.norm
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with v hv
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      have h2 : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.1])
      rw [h1]
      nlinarith [abs_nonneg (Real.log v), Real.exp_pos (-v)]
  · -- On `Ioi 1`: dominate by `2 * exp (-v/2)`, integrable.
    have hexp : IntegrableOn (fun v : ℝ => (2 : ℝ) * Real.exp ((-1/2) * v)) (Ioi 1) volume := by
      exact (integrableOn_exp_mul_Ioi (by norm_num : (-1/2 : ℝ) < 0) 1).const_mul 2
    apply Integrable.mono' hexp
    · apply (Measurable.aestronglyMeasurable ?_)
      exact (Real.measurable_log.mul (Real.measurable_exp.comp measurable_neg))
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with v hv
      have hv1 : (1 : ℝ) ≤ v := le_of_lt hv
      have hvpos : (0 : ℝ) < v := by linarith
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hlogabs : |Real.log v| = Real.log v :=
        abs_of_nonneg (Real.log_nonneg hv1)
      have hexpabs : |Real.exp (-v)| = Real.exp (-v) := abs_of_pos (Real.exp_pos _)
      rw [hlogabs, hexpabs]
      -- `log v ≤ v`
      have hlogv : Real.log v ≤ v := (Real.log_le_sub_one_of_pos hvpos).trans (by linarith)
      -- `v ≤ 2 * exp (v/2)`
      have hvexp : v ≤ 2 * Real.exp (v/2) := by
        have := Real.add_one_le_exp (v/2)
        nlinarith [Real.exp_pos (v/2)]
      -- combine: log v * exp(-v) ≤ v * exp(-v) ≤ 2 exp(v/2) exp(-v) = 2 exp(-v/2)
      have hstep : Real.log v * Real.exp (-v) ≤ 2 * Real.exp (v/2) * Real.exp (-v) := by
        apply mul_le_mul_of_nonneg_right (hlogv.trans hvexp) (le_of_lt (Real.exp_pos _))
      have heq : 2 * Real.exp (v/2) * Real.exp (-v) = 2 * Real.exp ((-1/2) * v) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
      rw [heq] at hstep
      exact hstep

/-- Helper: `∫_0^∞ log t · e^{-t} dt = Γ'(1)` (real). -/
private lemma integral_log_mul_exp_neg_eq_deriv_Gamma :
    ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) = deriv Real.Gamma 1 := by
  set I : ℝ := ∫ t in Ioi (0:ℝ), Real.log t * Real.exp (-t) with hI
  -- Step 1: derivative of GammaIntegral at 1.
  have h1 := Complex.hasDerivAt_GammaIntegral (s := (1 : ℂ)) (by norm_num)
  -- Step 2: simplify the integrand to `↑(log t * exp (-t))` and pull out `ofReal`.
  have hval : (∫ t : ℝ in Ioi 0, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t))))
      = (I : ℂ) := by
    have key : ∀ t : ℝ, (↑t : ℂ) ^ ((1 : ℂ) - 1) * (↑(Real.log t) * ↑(Real.exp (-t)))
        = ((Real.log t * Real.exp (-t) : ℝ) : ℂ) := by
      intro t
      rw [sub_self, Complex.cpow_zero, one_mul, Complex.ofReal_mul]
    simp_rw [key]
    rw [integral_complex_ofReal, hI]
  rw [hval] at h1
  -- Step 3: transfer to Complex.Gamma (agrees with GammaIntegral on `{re > 0}`).
  have h2 : HasDerivAt Complex.Gamma (I : ℂ) 1 := by
    apply h1.congr_of_eventuallyEq
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (show (0:ℝ) < (1:ℂ).re by norm_num)] with z hz
    exact Complex.Gamma_eq_integral hz
  -- Step 4: transfer ℂ → ℝ.
  have h3 := h2.real_of_complex
  have h4 : HasDerivAt Real.Gamma I 1 := by
    have hcongr : (fun x : ℝ => (Complex.Gamma ↑x).re) = Real.Gamma := by
      funext x
      rw [Complex.Gamma_ofReal, Complex.ofReal_re]
    rw [hcongr, Complex.ofReal_re] at h3
    exact h3
  rw [← h4.deriv]

/-- Core of #1584, stated with explicit qualifiers (outside `namespace Mertens`,
where `Finset` is open and would clash with `Set.Ioi`). -/
private theorem mul_integ_log_log_eq_aux (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) =
      - Real.log (s - 1) + deriv Real.Gamma 1 := by
  have hs0 : 0 < s - 1 := by linarith
  set f : ℝ → ℝ := fun x => (s - 1) * Real.log x with hf_def
  set f' : ℝ → ℝ := fun x => (s - 1) / x with hf'_def
  set g : ℝ → ℝ := fun u => (Real.log u - Real.log (s - 1)) * Real.exp (-u) with hg_def
  -- f 1 = 0
  have hf1 : f 1 = 0 := by simp [hf_def]
  -- ContinuousOn f (Ici 1)
  have hf_cont : ContinuousOn f (Ici 1) := by
    apply ContinuousOn.mul continuousOn_const
    apply Real.continuousOn_log.mono
    intro x hx
    simp only [mem_Ici] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  -- Tendsto f atTop atTop
  have hft : Tendsto f atTop atTop := by
    apply Filter.Tendsto.const_mul_atTop hs0
    exact Real.tendsto_log_atTop
  -- HasDerivWithinAt f (f' x) (Ioi x) x for x ∈ Ioi 1
  have hff' : ∀ x ∈ Ioi (1:ℝ), HasDerivWithinAt f (f' x) (Ioi x) x := by
    intro x hx
    simp only [mem_Ioi] at hx
    have hxne : x ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hxne).const_mul (s - 1)
    have h2 : HasDerivAt f ((s - 1) * x⁻¹) x := this
    have : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
    rw [this] at h2
    exact h2.hasDerivWithinAt
  -- image facts: f strictly mono on Ici 1
  have hmono : StrictMonoOn f (Ici 1) := by
    intro a ha b hb hab
    simp only [mem_Ici] at ha hb
    apply mul_lt_mul_of_pos_left _ hs0
    exact Real.log_lt_log (by linarith) hab
  have himg_Ioi : f '' Ioi 1 = Ioi 0 := by
    ext y
    simp only [Set.mem_image, mem_Ioi]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 < Real.log x := Real.log_pos hx
      positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_lt_exp_iff.mpr (div_pos hy hs0)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  have himg_Ici : f '' Ici 1 = Ici 0 := by
    ext y
    simp only [Set.mem_image, mem_Ici]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have : 0 ≤ Real.log x := Real.log_nonneg hx
      rw [hf_def]; positivity
    · intro hy
      refine ⟨Real.exp (y / (s - 1)), ?_, ?_⟩
      · exact Real.one_le_exp_iff.mpr (div_nonneg hy hs0.le)
      · rw [hf_def]
        simp only [Real.log_exp]
        field_simp
  -- ContinuousOn g (f '' Ioi 1) = ContinuousOn g (Ioi 0)
  have hg_cont : ContinuousOn g (f '' Ioi 1) := by
    rw [himg_Ioi]
    apply ContinuousOn.mul
    · apply ContinuousOn.sub _ continuousOn_const
      apply Real.continuousOn_log.mono
      intro u hu
      simp only [mem_Ioi] at hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · exact (Real.continuous_exp.comp continuous_neg).continuousOn
  -- IntegrableOn g (f '' Ici 1) = IntegrableOn g (Ici 0)
  have hg1 : IntegrableOn g (f '' Ici 1) := by
    rw [himg_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have : g = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [this]
    exact e1.sub e2
  -- IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1)
  have hg2 : IntegrableOn (fun x => (g ∘ f) x * f' x) (Ici 1) := by
    -- HasDerivWithinAt f (f' x) (Ici 1) x for x ∈ Ici 1.
    have hff'_Ici : ∀ x ∈ Ici (1:ℝ), HasDerivWithinAt f (f' x) (Ici 1) x := by
      intro x hx
      simp only [mem_Ici] at hx
      have hxne : x ≠ 0 := by linarith
      have hd : HasDerivAt f ((s - 1) * x⁻¹) x := (Real.hasDerivAt_log hxne).const_mul (s - 1)
      have heq : (s - 1) * x⁻¹ = f' x := by rw [hf'_def]; field_simp
      rw [heq] at hd
      exact hd.hasDerivWithinAt
    -- f injective on Ici 1.
    have hinj : InjOn f (Ici 1) := hmono.injOn
    -- transfer hg1 through the integrability change of variables.
    have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul
      (s := Ici (1:ℝ)) (f := f) (f' := f') measurableSet_Ici hff'_Ici hinj g
    rw [hiff] at hg1
    -- relate to our integrand on Ici 1.
    apply hg1.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with x hx
    simp only [mem_Ici] at hx
    have hxpos : (0:ℝ) < x := by linarith
    have hf'pos : 0 < f' x := by rw [hf'_def]; positivity
    simp only [smul_eq_mul, Function.comp, abs_of_pos hf'pos]
    ring
  -- Apply change of variables.
  have hcov := integral_comp_mul_deriv_Ioi hf_cont hft hff' hg_cont hg1 hg2
  rw [hf1] at hcov
  -- RHS: ∫ u in Ioi 0, g u = deriv Gamma 1 - log (s-1)
  have hrhs : ∫ u in Ioi (0:ℝ), g u = deriv Real.Gamma 1 - Real.log (s - 1) := by
    have e1 : IntegrableOn (fun u => Real.log u * Real.exp (-u)) (Ioi 0) :=
      integrableOn_log_mul_exp_neg
    have e2 : IntegrableOn (fun u => Real.log (s - 1) * Real.exp (-u)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul _
    have hsplit : (fun u => g u)
        = fun u => Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u) := by
      funext u; rw [hg_def]; ring
    rw [show (∫ u in Ioi (0:ℝ), g u)
        = ∫ u in Ioi (0:ℝ), (Real.log u * Real.exp (-u) - Real.log (s - 1) * Real.exp (-u))
        from by rw [hsplit]]
    rw [integral_sub e1 e2, integral_log_mul_exp_neg_eq_deriv_Gamma]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  -- LHS: ∫ x in Ioi 1, (g∘f) x * f' x = (s-1) * ∫ x in Ioi 1, log(log x) * x^(-s)
  have hlhs : ∫ x in Ioi (1:ℝ), (g ∘ f) x * f' x
      = (s - 1) * ∫ x in Ioi (1:ℝ), Real.log (Real.log x) * x ^ (-s) := by
    have hpt : ∀ x ∈ Ioi (1:ℝ), (g ∘ f) x * f' x
        = (s - 1) * (Real.log (Real.log x) * x ^ (-s)) := by
      intro x hx
      simp only [mem_Ioi] at hx
      have hxpos : (0:ℝ) < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos hx
      have hlogne : Real.log x ≠ 0 := ne_of_gt hlogpos
      have hs1ne : s - 1 ≠ 0 := ne_of_gt hs0
      simp only [Function.comp, hf_def, hg_def, hf'_def]
      -- log ((s-1) * log x) - log (s-1) = log (log x)
      rw [Real.log_mul hs1ne hlogne]
      -- exp (-((s-1) * log x)) = x ^ (-(s-1))
      have hexp : Real.exp (-((s - 1) * Real.log x)) = x ^ (-(s - 1)) := by
        rw [Real.rpow_def_of_pos hxpos]
        ring_nf
      rw [hexp]
      -- x ^ (-(s-1)) * ((s-1)/x) = (s-1) * x^(-s)
      have hx1 : x ^ (-(s - 1)) * ((s - 1) / x) = (s - 1) * x ^ (-s) := by
        rw [div_eq_mul_inv, ← Real.rpow_neg_one x]
        rw [show x ^ (-(s - 1)) * ((s - 1) * x ^ (-1 : ℝ))
            = (s - 1) * (x ^ (-(s - 1)) * x ^ (-1 : ℝ)) by ring]
        rw [← Real.rpow_add hxpos]
        ring_nf
      rw [show (Real.log (s - 1) + Real.log (Real.log x) - Real.log (s - 1))
          = Real.log (Real.log x) by ring]
      linear_combination Real.log (Real.log x) * hx1
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  rw [hlhs, hrhs] at hcov
  rw [hcov]
  ring

end Issue1584

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


open Real Finset Filter Asymptotics Topology
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
  _ ≥ x * log x - x - log x := by simp only [integral_log, log_one, mul_zero, sub_zero,
    tsub_le_iff_right, sub_add_cancel, le_add_iff_nonneg_right, zero_le_one]
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
    eventually_atTop]
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
    convert! E₁Λ.bounded using 1

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
  convert! HasDerivAt.fun_div (c' := -1 / (t + 2)) (d' := (1 : ℝ)) _ _  _ using 1
  · field
  · apply HasDerivAt.sub_const
    convert! (hasDerivAt_log (by linarith : t + 2 ≠ 0)).neg using 1
    ring_nf
  · exact hasDerivAt_id _
  · linarith

private lemma tendsto_antideriv_log_div_sq :
    Tendsto (fun t ↦ (-log (t + 2) - 1) / (t + 2)) atTop (nhds 0) := by
  have : Tendsto (fun (t : ℝ) ↦ t + 2) atTop atTop := by exact tendsto_atTop_add_const_right atTop 2 tendsto_id
  apply Tendsto.comp (g := (fun t ↦ (-log t - 1) / t)) _ this
  convert! Tendsto.sub (f := (fun t ↦ -log t / t)) (a := 0) _ tendsto_inv_atTop_zero using 1
  · ring_nf
  · ring_nf
  · convert! (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by linarith)).neg using 1
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
    convert! summable_nat_add_iff 1|>.mpr this using 2
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
    · convert! summable_nat_add_iff 3|>.mpr E₁.summable using 4
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
      eventually_atTop, E₁p]
    exact ⟨ log 4 + 4, 1, fun _ ↦ sum_log_prime_div_eq_log ⟩

@[blueprint
  "Mertens-first-theorem-prime-bounded"]
theorem sum_log_prime_div_eq_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (log p) / p) ~[atTop] (fun x ↦ log x) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log)
    convert! sum_log_prime_div_eq_log' using 1

open MeasureTheory
section IntegralIdentity

open intervalIntegral

variable (f : ℕ → ℝ) (x : ℝ) (C : ℝ)

private noncomputable def E₁f := ∑ n ∈ Icc 0 ⌊x⌋₊, f n - log x

attribute [fun_prop] measurable_from_top

private lemma sum_f_eq : ∑ n ∈ Icc 0 ⌊x⌋₊, f n = log x + E₁f f x := by grind [E₁f]

private noncomputable def γf := (∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁f f t) + 1 - log (log 2)

private noncomputable def E₂f := ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n - log (log x) - γf f

noncomputable def inv : ℝ → ℝ := (·⁻¹)
noncomputable def inv_log : ℝ → ℝ := inv ∘ log

private lemma deriv_log_log {x : ℝ} (hx : 1 < x) :
    deriv (fun t ↦ log (log t)) x = (x * (log x)^2)⁻¹ * log x := by
  rw [deriv.log (differentiableAt_log (by linarith)) (by simp; grind), deriv_log]
  field

@[fun_prop]
private lemma ContinuousOn.log_Ioi_one : ContinuousOn log (.Ioi 1) :=
  continuousOn_log.mono (by grind)

@[fun_prop]
private lemma ContinuousOn.log_inv_Ioi_one : ContinuousOn inv_log (.Ioi 1) :=
  log_Ioi_one.inv₀ (by simp; grind)

@[fun_prop]
private lemma ContinuousOn.inv_Ioi_one : ContinuousOn inv (.Ioi 1) :=
  continuousOn_inv₀.mono (by grind)

@[fun_prop]
theorem ContinuousOn.const_smul' {M : Type*} {α : Type*} {β : Type*} [TopologicalSpace α] [SMul M α] [ContinuousConstSMul M α] [TopologicalSpace β] {g : β → α} {s : Set β}
    (hg : ContinuousOn g s) (c : M) : ContinuousOn (c • g) s := hg.const_smul c

@[to_additive (attr := fun_prop)]
theorem ContinuousOn.inv' {G : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace G] [Inv G]
[ContinuousInv G] {f : X → G} {s : Set X}
    (hf : ContinuousOn f s) : ContinuousOn f⁻¹ s := hf.inv

@[fun_prop]
theorem ContinuousOn.pow' {M : Type*} {X : Type*} [TopologicalSpace X] [TopologicalSpace M]
    [Monoid M] [ContinuousMul M] {f : X → M} {s : Set X} (hf : ContinuousOn f s) (n : ℕ) :
    ContinuousOn (f^n) s := hf.pow n

private lemma integral_one_div_mul_log {x : ℝ} (hx : 2 ≤ x) :
    ∫ t in 2..x, (t * (log t)^2)⁻¹ * log t = log (log x) - log (log 2) := by
  rw [← integral_deriv_eq_sub (f := fun t ↦ log (log t))]
  · refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    rw [deriv_log_log (by linarith)]
  · intro t ht
    rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
    have : log t ≠ 0 := by simp; grind
    fun_prop (disch := grind)
  · refine (ContinuousOn.congr (f := (fun t ↦ (t * (log t)^2)⁻¹ * log t)) ?_ ?_).intervalIntegrable
    · apply ContinuousOn.mono (s := .Ioi 1) _ (by grind [Set.uIcc_of_le hx])
      convert (by fun_prop : ContinuousOn (inv * inv_log^2 * log) (.Ioi 1)) using 2
      simp [inv, inv_log, field]
    · intro t ht
      rw [Set.uIcc_of_le hx, Set.mem_Icc] at ht
      exact deriv_log_log (by linarith)

private theorem integrable_const_div_mul_log_sq {x : ℝ} (c : ℝ) (hx : 2 ≤ x) :
    IntegrableOn (fun x ↦ c / (x * log x ^ 2)) (.Ioi x) volume := by
  conv => arg 1; ext t; rw [← mul_one_div]
  apply Integrable.const_mul
  refine integrableOn_Ioi_deriv_of_nonneg' ?_ ?_ tendsto_log_atTop.inv_tendsto_atTop.neg
  · intro t ht
    simp only [Set.mem_Ici] at ht
    have : log t ≠ 0 := by simp; grind
    have : DifferentiableAt ℝ (fun t ↦ -(log t)⁻¹) t := by
      fun_prop (disch := grind)
    convert! this.hasDerivAt using 1
    simp [deriv_inv_log]
    field
  · intro t ht
    simp only [Set.mem_Ioi] at ht
    exact one_div_nonneg.mpr <| mul_nonneg (by linarith) (sq_nonneg _)

private theorem E₁f_div_integrable
    {f : ℕ → ℝ} {x : ℝ} {C : ℝ} (hx : 2 ≤ x) (hbound : ∀ t ≥ 1, |E₁f f t| ≤ C) :
    IntegrableOn (fun t ↦ (t * log t^2)⁻¹ * E₁f f t) (.Ioi x) volume := by
  apply Integrable.mono (integrable_const_div_mul_log_sq C hx)
  · exact Measurable.aestronglyMeasurable (by unfold E₁f; fun_prop)
  filter_upwards [ae_restrict_mem (by measurability)] with t ht
  simp only [Set.mem_Ioi, mul_inv_rev, norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs,
    norm_div] at ht ⊢
  have : 0 < log t := log_pos (by linarith)
  grw [hbound t (by linarith), le_abs_self C]
  simp [field]

/-- move to InvLog.lean -/
@[simp]
theorem deriv_inv_log' : deriv (fun x ↦ (log x)⁻¹) = fun x ↦ -x⁻¹ / (log x ^ 2) :=
  funext fun _ ↦ deriv_inv_log

private theorem E₂f_eq {x : ℝ} (hx : 2 ≤ x) (hbound : ∀ t ≥ 1, |E₁f f t| ≤ C)
    (h0 : f 0 = 0) (h1 : f 1 = 0) :
    E₂f f x = (log x)⁻¹ * E₁f f x - ∫ t in .Ioi x, (t * log t^2)⁻¹ * E₁f f t := by
  have : 0 < log x := log_pos (by linarith)
  suffices ∫ t in 2..x, (t * log t^2)⁻¹ * E₁f f t = ∑ n ∈ Icc 0 ⌊x⌋₊, (log n)⁻¹ * f n -
    (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - log (log x) + log (log 2) by
    have : (∫ t in 2..x, (t * log t^2)⁻¹ * E₁f f t) + ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * E₁f f t
      = ∫ t in .Ioi 2, (t * log t^2)⁻¹ * E₁f f t :=
      integral_interval_add_Ioi (E₁f_div_integrable (by rfl) hbound) (E₁f_div_integrable hx hbound)
    have : (log x)⁻¹ * E₁f f x = (log x)⁻¹ * (∑ n ∈ Icc 0 ⌊x⌋₊, f n) - 1 := by unfold E₁f; field_simp
    unfold E₂f γf; linarith
  have : ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n =
      (∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * log t)
      + ∫ (t : ℝ) in 2..x, (t * log t ^ 2)⁻¹ * (E₁f f t) := by
    simp only [mul_inv_rev, sum_f_eq, mul_add]
    apply intervalIntegral.integral_add
    <;> rw [intervalIntegrable_iff, Set.uIoc_of_le hx]
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (inv * inv_log * inv_log * log) (.Ioi 1)) using 2
      simp [inv, inv_log, field]
    apply Integrable.mono (g := fun t ↦ (log 2 ^ 2)⁻¹ * t⁻¹ * C)
    · apply (ContinuousOn.integrableOn_Icc _).mono_set Set.Ioc_subset_Icc_self
      apply ContinuousOn.mono (s := .Ioi 1) _ (by grind)
      convert (by fun_prop : ContinuousOn (((log 2 ^ 2)⁻¹ * C) • inv) (.Ioi (1:ℝ))) using 2
      simp [inv, field]
    · exact Measurable.aestronglyMeasurable (by unfold E₁f; fun_prop)
    filter_upwards [ae_restrict_mem (by measurability)] with t ht
    simp [Set.mem_Ioc] at ht
    simp only [norm_mul, norm_inv, norm_pow, norm_eq_abs, sq_abs]
    grw [hbound t (by linarith), le_abs_self C]; gcongr; order
  rw [integral_one_div_mul_log hx] at this
  rw [sum_mul_eq_sub_integral_mul₁ _ h0 h1 x (f := fun t ↦ (log t)⁻¹)]
  · suffices ∫ t in .Ioc 2 x, deriv (fun t ↦ (log t)⁻¹) t * ∑ k ∈ Icc 0 ⌊t⌋₊, f k =
        - ∫ t in 2..x, (t * log t ^ 2)⁻¹ * ∑ n ∈ Icc 0 ⌊t⌋₊, f n by linarith
    rw [← intervalIntegral.integral_neg, intervalIntegral.integral_of_le hx]
    apply setIntegral_congr_fun (by measurability)
    intro t ht
    simp [field]
  · intro t ht
    simp at ht
    exact DifferentiableAt.fun_inv (by simp; linarith) (by simp; grind)
  · apply (ContinuousOn.mono (s := .Ioi 1) _ (by grind)).integrableOn_Icc
    rw [deriv_inv_log']
    convert (by fun_prop : ContinuousOn (-inv * inv_log^2) (.Ioi (1:ℝ))) using 2
    simp [inv, inv_log, field]

private theorem integ_div_mul_log_sq {x : ℝ} (C : ℝ) (hx : 2 ≤ x) :
    ∫ (t : ℝ) in .Ioi x, (t * log t ^ 2)⁻¹ * C = C / log x := by
    convert! integral_Ioi_of_hasDerivAt_of_tendsto' (m := 0) (f := (- C / log ·)) ?_
      (integrable_const_div_mul_log_sq C hx) ?_ using 1
    · grind
    · field
    · intro t ht; simp at ht
      convert! (hasDerivAt_const _ (-C)).fun_div (hasDerivAt_log (by linarith)) ?_ using 1
      · grind
      simp; grind
    convert! tendsto_log_atTop.inv_tendsto_atTop.const_mul (-C) using 1
    simp

private theorem E₂f_abs_le {x : ℝ} (hx : 2 ≤ x) (C_lo C_hi : ℝ) (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t)
 (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) (h0 : f 0 = 0) (h1 : f 1 = 0) :
    |E₂f f x| ≤ (C_hi - C_lo) / log x := by
  have : 0 < log x := log_pos (by linarith)
  have hbound : ∀ t ≥ 1, |E₁f f t| ≤ max (-C_lo) C_hi := by
    intro t ht; grw [abs_le, ←h_lo t ht, h_hi t ht]; grind
  have := E₁f_div_integrable hx hbound
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi x) volume := by
    convert integrable_const_div_mul_log_sq C hx using 1; grind
  have : NullMeasurableSet (.Ioi x) volume := by measurability
  rw [E₂f_eq f _ hx hbound h0 h1, abs_le]
  constructor
  · calc
      _ ≥ (log x)⁻¹ * C_lo - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_hi := by
        gcongr with t ht
        · exact h_lo _ (by linarith)
        · exact hinteg C_hi
        · simp at ht
          have : 0 < t := by linarith
          have : 0 < log t := log_pos (by linarith)
          positivity
        simp at ht
        exact h_hi _ (by linarith)
      _ = _ := by rw [integ_div_mul_log_sq C_hi hx]; simp [field]
  · calc
      _ ≤ (log x)⁻¹ * C_hi - ∫ t in .Ioi x, (t * log t ^ 2)⁻¹ * C_lo := by
        gcongr with t ht
        · exact h_hi _ (by linarith)
        · exact hinteg C_lo
        · simp at ht
          have : 0 < t := by linarith
          have : 0 < log t := log_pos (by linarith)
          positivity
        simp at ht
        exact h_lo _ (by linarith)
      _ = _ := by rw [integ_div_mul_log_sq C_lo hx]; simp [field]

private theorem γf_bounds (C_lo C_hi : ℝ) (h_lo : ∀ t ≥ 1, C_lo ≤ E₁f f t)
    (h_hi : ∀ t ≥ 1, E₁f f t ≤ C_hi) :
    γf f ≤ C_hi / (log 2) + 1 - log (log 2) ∧ C_lo / (log 2) + 1 - log (log 2) ≤ γf f := by
  have hbound : ∀ t ≥ 1, |E₁f f t| ≤ max (-C_lo) C_hi := by
    intro t ht; grw [abs_le, ←h_lo t ht, h_hi t ht]; grind
  unfold γf
  rw [← integ_div_mul_log_sq C_hi (by rfl), ← integ_div_mul_log_sq C_lo (by rfl)]
  have := E₁f_div_integrable (by rfl) hbound
  have hinteg (C : ℝ) : IntegrableOn (fun t ↦ (t * log t ^ 2)⁻¹ * C) (.Ioi 2) volume := by
    convert integrable_const_div_mul_log_sq C (by rfl) using 1; grind
  have : NullMeasurableSet (.Ioi (2 : ℝ)) volume := by measurability
  constructor
  · gcongr with t ht
    · exact hinteg C_hi
    · simp at ht
      have : 0 < log t := log_pos (by grind)
      positivity
    simp at ht
    exact h_hi _ (by linarith)
  · gcongr with t ht
    · exact hinteg C_lo
    · simp at ht
      have : 0 < log t := log_pos (by grind)
      positivity
    simp at ht
    exact h_lo _ (by linarith)

end IntegralIdentity

section SecondTheorem

noncomputable abbrev γ : ℝ := γf (fun n ↦ Λ n / n)

noncomputable abbrev E₂Λ (x : ℝ) : ℝ := ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ

/-- For any $x \geq 2$, one has
$$ |E_{2,\Lambda}(x)| \leq \frac{\log 4 + 6}{\log x}.$$
-/
theorem E₂Λ.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log x := by
  let f : ℕ → ℝ := fun n ↦ Λ n / n
  have h₁ : E₁f f = E₁Λ := by ext; simp [E₁Λ, E₁f, f, ←add_sum_Ioc_eq_sum_Icc]
  convert E₂f_abs_le f hx (-2) (log 4 + 4) ?_ ?_ (by simp [f]) (by simp [f]) using 1
  · simp only [E₂Λ, γ, E₂f, zero_le, ← add_sum_Ioc_eq_sum_Icc, CharP.cast_eq_zero, log_zero,
    inv_zero, ArithmeticFunction.map_zero, div_zero, mul_zero, zero_add, γf, mul_inv_rev, h₁, f]
    congr! 4 with x hx
    simp at hx; field
  · congr 1; grind
  · rw [h₁]; intro x hx; exact E₁Λ.ge hx
  rw [h₁]; intro x hx; exact E₁Λ.le hx

noncomputable def M : ℝ := γf (fun p ↦ if p.Prime then log p / p else 0)

noncomputable abbrev E₂p (x : ℝ) : ℝ := ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p - log (log x) - M

theorem E₂p.abs_le {x : ℝ} (hx : 2 ≤ x) :
    |E₂p x| ≤ (log 4 + 6 + E₁) / log x := by
  let f : ℕ → ℝ := fun p ↦ if p.Prime then log p / p else 0
  have h₁ : E₁f f = E₁p := by ext; simp [E₁p, E₁f, f, ← add_sum_Ioc_eq_sum_Icc, sum_filter]
  convert E₂f_abs_le f hx (-2 - E₁) (log 4 + 4) ?_ ?_ (by simp [f]) (by simp [f]) using 1
  · simp only [E₂p, one_div, sum_filter, M, E₂f, mul_ite, mul_zero, zero_le,
    ← add_sum_Ioc_eq_sum_Icc, CharP.cast_eq_zero, log_zero, inv_zero, div_zero, ite_self, zero_add,
    γf, mul_inv_rev, h₁, f]
    congr! 4 with x hx
    · rcases eq_or_ne x 1 with rfl | h
      · simp [Nat.not_prime_one]
      congr 1; simp at hx
      have : 0 < log x := log_pos (by norm_cast; grind)
      field
  · congr 1; grind
  · rw [h₁]; intro x hx; exact E₁p.ge hx
  rw [h₁]; intro x hx; exact E₁p.le hx

private theorem M_bounds :
    M ≤ (log 4 + 4) / (log 2) + 1 - log (log 2) ∧ (-2 - E₁) / (log 2) + 1 - log (log 2) ≤ M := by
  unfold M
  let f : ℕ → ℝ := fun p ↦ if p.Prime then log p / p else 0
  have h₁ : E₁f f = E₁p := by ext; simp [E₁p, E₁f, f, ← add_sum_Ioc_eq_sum_Icc, sum_filter]
  apply γf_bounds <;> rw [h₁] <;> intro; exacts [E₁p.ge, E₁p.le]

theorem M.le : M ≤ (log 4 + 4) / log 2 + 1 - log (log 2) := M_bounds.1

theorem M.ge : M ≥ (-2 - E₁) / log 2 + 1 - log (log 2) := M_bounds.2

theorem E₂Λ.bound : E₂Λ =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6, 2
    intro x hx
    convert E₂Λ.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂Λ.bound' : E₂Λ =o[atTop] (fun _ ↦ (1:ℝ)) := E₂Λ.bound.trans_isLittleO inv_log_eq_o_one

theorem sum_prime_div_eq (x : ℝ) : ∑ p ∈ Ioc 0 ⌊ x ⌋₊ with p.Prime, (1:ℝ) / p = log (log x) + M + E₂p x := by
    ring

theorem E₂p.bound : E₂p =O[atTop] (fun x ↦ 1 / log x) := by
    simp only [one_div, isBigO_iff, norm_eq_abs, norm_inv, eventually_atTop]
    use log 4 + 6 + E₁, 2
    intro x hx
    convert E₂p.abs_le hx using 1
    have : 0 < log x := by apply log_pos; linarith
    grind [abs_of_pos this]

theorem E₂p.bound' : E₂p =o[atTop] (fun _ ↦ (1:ℝ)) := E₂p.bound.trans_isLittleO inv_log_eq_o_one

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

theorem sum_prime_div_eq_log_log' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p - log (log x)) =O[atTop] (fun _ ↦ (1:ℝ)) := by
    simp only [isBigO_iff, norm_eq_abs, one_mem, CStarRing.norm_of_mem_unitary, mul_one,
      eventually_atTop]
    obtain ⟨ C, hC ⟩ := sum_prime_div_eq_log_log
    use C, 2

theorem sum_prime_div_eq_log_log'' : (fun x ↦ ∑ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1:ℝ) / p) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_prime_div_eq_log_log' using 1

end SecondTheorem

theorem log_zeta_eq_sum' {s : ℝ} (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hpow_le (p : Nat.Primes) : (↑p : ℝ) ^ (-s) < 1 :=
    rpow_lt_one_of_one_lt_of_neg (mod_cast p.property.one_lt) (by linarith)
  calc
  _ = ∑' p : Nat.Primes, -log (1 - p ^ (-s)) := by
    rw [← riemannZeta_eulerProduct_exp_log (by simpa using hs)]
    convert log_exp _
    convert Complex.exp_ofReal_re _
    push_cast
    congr! with p
    convert (Complex.ofReal_log _).symm
    · push_cast; congr
      rw [Complex.ofReal_cpow (by positivity)]
      norm_cast
    linarith [hpow_le p]
  _ = _ := by
    sorry


theorem log_zeta_eq_sum (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = ∑' n, Λ n / (n^s * log n) := by
  have hsc : (1 : ℝ) < ((s : ℂ)).re := by simpa using hs
  -- (II) Euler log product
  have hep := riemannZeta_eulerProduct_exp_log (s := (s : ℂ)) hsc
  set S : ℂ := ∑' p : Nat.Primes, -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) with hS
  -- bridge: prime cpow equals real rpow
  have hcpow : ∀ p : Nat.Primes, (p : ℂ) ^ (-(s : ℂ)) = (((p : ℝ) ^ (-s) : ℝ) : ℂ) := by
    intro p
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  -- the real value of each prime term
  set z : Nat.Primes → ℝ := fun p => (p : ℝ) ^ (-s) with hz
  -- z p ∈ (0,1)
  have hz_pos : ∀ p : Nat.Primes, 0 < z p := fun p => by
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.pos
    positivity
  have hz_lt_one : ∀ p : Nat.Primes, z p < 1 := by
    intro p
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    change (p : ℝ) ^ (-s) < 1
    rw [Real.rpow_neg (by positivity), inv_lt_one_iff₀]
    right
    exact (Real.one_lt_rpow_iff_of_pos (by positivity)).mpr (Or.inl ⟨hp1, by linarith⟩)
  -- each summand is the ofReal of a real number
  have hterm : ∀ p : Nat.Primes,
      -Complex.log (1 - (p : ℂ) ^ (-(s : ℂ))) = ((-Real.log (1 - z p) : ℝ) : ℂ) := by
    intro p
    rw [hcpow p]
    have h1z : (0 : ℝ) < 1 - z p := by have := hz_lt_one p; linarith
    rw [show (1 : ℂ) - ((z p : ℝ) : ℂ) = (((1 - z p : ℝ)) : ℂ) by push_cast; ring]
    rw [← Complex.ofReal_log h1z.le]
    push_cast; ring
  -- (III) S is real: S = (Sr : ℂ) with Sr the real sum
  set Sr : ℝ := ∑' p : Nat.Primes, -Real.log (1 - z p) with hSr
  have hSeq : S = (Sr : ℂ) := by
    rw [hS, hSr, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hSim : S.im = 0 := by rw [hSeq]; exact Complex.ofReal_im _
  have hSre : S.re = Sr := by rw [hSeq]; exact Complex.ofReal_re _
  -- (IV) invert exp: log ζ = S
  have hlog_zeta : Complex.log (riemannZeta (s : ℂ)) = S := by
    rw [← hep, Complex.log_exp (by rw [hSim]; exact neg_lt_zero.mpr Real.pi_pos)
      (by rw [hSim]; exact Real.pi_pos.le)]
  -- relate Real.log ζ.re to S.re = Sr
  have hkey : Real.log (riemannZeta (s : ℂ)).re = Sr := by
    have hζim : (riemannZeta (s : ℂ)).im = 0 := riemannZeta_im_eq_zero_of_one_lt hs
    have hζeq : riemannZeta (s : ℂ) = ((riemannZeta (s : ℂ)).re : ℂ) := by
      apply Complex.ext <;> simp [hζim]
    have : Real.log (riemannZeta (s : ℂ)).re
        = (Complex.log (riemannZeta (s : ℂ))).re := by
      conv_rhs => rw [hζeq]
      rw [Complex.log_ofReal_re]
    rw [this, hlog_zeta, hSre]
  rw [hkey]
  -- now goal: Sr = ∑' n, Λ n / (n^s * log n)
  -- (V) expand each prime term via real Taylor series
  have habs : ∀ p : Nat.Primes, |z p| < 1 := by
    intro p
    rw [abs_of_pos (hz_pos p)]; exact hz_lt_one p
  have htaylor : ∀ p : Nat.Primes,
      HasSum (fun n : ℕ => (z p) ^ (n + 1) / (n + 1)) (-Real.log (1 - z p)) :=
    fun p => hasSum_pow_div_log_of_abs_lt_one (habs p)
  have hSr_double : Sr = ∑' (p : Nat.Primes) (n : ℕ), (z p) ^ (n + 1) / (n + 1) := by
    rw [hSr]
    exact tsum_congr fun p => ((htaylor p).tsum_eq).symm
  -- summability of the prime sum ∑ z p
  have hsummable_z : Summable z := Nat.Primes.summable_rpow.mpr (by linarith)
  -- summability of ∑ p, -log(1 - z p)
  have hsummable_prime : Summable (fun p : Nat.Primes => -Real.log (1 - z p)) := by
    have := Real.summable_log_one_add_of_summable hsummable_z.neg
    convert! this.neg using 1
  -- summability of g over the product
  have hg_nonneg : ∀ pk : Nat.Primes × ℕ, 0 ≤ (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1) := by
    intro pk; positivity [hz_pos pk.1]
  have hsummable_g : Summable (fun pk : Nat.Primes × ℕ => (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1)) := by
    rw [summable_prod_of_nonneg hg_nonneg]
    refine ⟨fun p => (htaylor p).summable, ?_⟩
    refine hsummable_prime.congr (fun p => ?_)
    exact ((htaylor p).tsum_eq).symm
  -- pointwise: F (p^(n+1)) = g (p, n)
  have hpoint : ∀ (p : Nat.Primes) (n : ℕ),
      Λ ((p : ℕ) ^ (n + 1)) /
        ((((p : ℕ) ^ (n + 1) : ℕ) : ℝ) ^ s * Real.log (((p : ℕ) ^ (n + 1) : ℕ) : ℝ))
      = (z p) ^ (n + 1) / (n + 1) := by
    intro p n
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    rw [vonMangoldt_apply_pow (Nat.succ_ne_zero n), vonMangoldt_apply_prime p.prop]
    have hcast : (((p : ℕ) ^ (n + 1) : ℕ) : ℝ) = (p : ℝ) ^ (n + 1) := by push_cast; ring
    rw [hcast, Real.log_pow]
    rw [show (z p) ^ (n + 1) = ((p : ℝ) ^ (n + 1)) ^ (-s) by
      rw [hz]; rw [← Real.rpow_natCast ((p : ℝ) ^ (-s)) (n + 1),
        ← Real.rpow_natCast ((p : ℝ)) (n + 1), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity)]; ring_nf]
    rw [Real.rpow_neg (by positivity)]
    field_simp
    push_cast
    ring
  -- (VI) reindex via the prime-power equivalence
  set F : ℕ → ℝ := fun n => Λ n / ((n : ℝ) ^ s * Real.log n) with hF
  -- support of F is contained in prime powers
  have hsupp : Function.support F ⊆ {n : ℕ | IsPrimePow n} := by
    intro n hn
    rw [Function.mem_support] at hn
    simp only [Set.mem_setOf_eq]
    by_contra hpp
    apply hn
    simp only [hF, vonMangoldt_eq_zero_iff.mpr hpp, zero_div]
  -- the product sum equals the subtype sum
  have hprod_eq : (∑' pk : Nat.Primes × ℕ, (z pk.1) ^ (pk.2 + 1) / (pk.2 + 1))
      = ∑' m : {n : ℕ // IsPrimePow n}, F m.val := by
    rw [← Equiv.tsum_eq Nat.Primes.prodNatEquiv (fun m : {n : ℕ // IsPrimePow n} => F m.val)]
    apply tsum_congr
    intro pk
    rw [Nat.Primes.coe_prodNatEquiv_apply, hF]
    exact (hpoint pk.1 pk.2).symm
  -- assemble
  rw [hSr_double, ← hsummable_g.tsum_prod' (fun p => (htaylor p).summable), hprod_eq]
  exact tsum_subtype_eq_of_support_subset hsupp

section
open MeasureTheory Set

-- Helpers for `log_zeta_eq_integ` (#1583): Abel summation / sum-integral interchange.
namespace LogZetaInteg

/-- The summatory coefficient `Λ d / (d log d)`. -/
private noncomputable def c (d : ℕ) : ℝ := Λ d / (d * Real.log d)

/-- The per-index integrand: `c d` times the rpow restricted to `Ici (d:ℝ)`. -/
private noncomputable def f (s : ℝ) (d : ℕ) (x : ℝ) : ℝ :=
    c d * (Set.Ici (d:ℝ)).indicator (fun x => x ^ (-s)) x

@[simp] private lemma c_zero : c 0 = 0 := by simp [c]
@[simp] private lemma c_one : c 1 = 0 := by simp [c, vonMangoldt_apply_one]

/-- `c d ≥ 0` for all `d`. -/
private lemma c_nonneg (d : ℕ) : 0 ≤ c d := by
  unfold c
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd; simp
  · apply div_nonneg vonMangoldt_nonneg
    have : (0:ℝ) ≤ (d:ℝ) := Nat.cast_nonneg d
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    positivity

/-- General comparison majorant: `(log n)^a / n^s` is summable for any real `a` and `s > 1`,
since `(log x)^a = o(x^ε)` for every `ε > 0`. All the summability conditions below reduce to
this by domination. -/
private lemma summable_log_rpow_div_rpow (a : ℝ) {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ => (Real.log n) ^ a / (n:ℝ) ^ s) := by
  have hε : (0:ℝ) < (s - 1) / 2 := by linarith
  refine summable_of_isBigO_nat (g := fun n : ℕ => (n:ℝ) ^ ((s - 1) / 2 - s)) ?_ ?_
  · rw [Real.summable_nat_rpow]; linarith
  · have ho : (fun x : ℝ => (Real.log x) ^ a) =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2)) :=
      (isLittleO_log_rpow_rpow_atTop a hε).isBigO
    have hmul : (fun x : ℝ => (Real.log x) ^ a / x ^ s)
        =O[atTop] (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s) := by
      simpa only [div_eq_mul_inv] using ho.mul (isBigO_refl (fun x : ℝ => (x ^ s)⁻¹) atTop)
    have heq : (fun x : ℝ => x ^ ((s - 1) / 2) / x ^ s)
        =ᶠ[atTop] (fun x : ℝ => x ^ ((s - 1) / 2 - s)) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_sub hx]
    exact (hmul.trans_eventuallyEq heq).natCast_atTop

/-- Real summability of `Λ n / n^s` for `s > 1`: dominated by `log n / n^s` via `Λ n ≤ log n`. -/
private lemma summable_vonMangoldt_div_rpow (s : ℝ) (hs : 1 < s) :
    Summable (fun n : ℕ => (Λ n : ℝ) / (n:ℝ) ^ s) := by
  refine Summable.of_nonneg_of_le (fun n => div_nonneg vonMangoldt_nonneg (by positivity)) ?_
    (summable_log_rpow_div_rpow 1 hs)
  intro n
  rw [Real.rpow_one]
  gcongr
  exact vonMangoldt_le_log

/-- Real summability of `Λ n / (n^s * log n)` for `s > 1` (compare with the previous lemma). -/
private lemma summable_c_term (s : ℝ) (hs : 1 < s) :
    Summable (fun d : ℕ => c d * ((d:ℝ) ^ (1 - s) / (s - 1))) := by
  have hs1 : (0:ℝ) < s - 1 := by linarith
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- Majorise by `(1/(log 2·(s-1)))·(Λ d/d^s)`, summable by `summable_vonMangoldt_div_rpow`.
  refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_)
    ((summable_vonMangoldt_div_rpow s hs).mul_left (1 / (Real.log 2 * (s - 1))))
  · -- `0 ≤ c d * (d^(1-s)/(s-1))`
    refine mul_nonneg (c_nonneg d) (div_nonneg ?_ hs1.le)
    rcases eq_or_ne (d:ℝ) 0 with hd | hd
    · rw [hd, Real.zero_rpow (by linarith : (1 - s) ≠ 0)]
    · positivity
  · -- `c d * (d^(1-s)/(s-1)) ≤ (1/(log 2·(s-1)))·(Λ d/d^s)`
    rcases lt_or_ge d 2 with hd | hd
    · have hc : c d = 0 := by interval_cases d <;> simp
      rw [hc, zero_mul]
      exact mul_nonneg (by positivity) (div_nonneg vonMangoldt_nonneg (by positivity))
    · have hd2 : (2:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
      have hd0 : (0:ℝ) < (d:ℝ) := by linarith
      have hlogge : Real.log 2 ≤ Real.log d := Real.log_le_log (by norm_num) hd2
      have hds : (0:ℝ) < (d:ℝ) ^ s := Real.rpow_pos_of_pos hd0 s
      have hkey : c d * ((d:ℝ) ^ (1 - s) / (s - 1)) = Λ d / ((d:ℝ) ^ s * Real.log d * (s - 1)) := by
        unfold c
        rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hd0, Real.rpow_one, Real.rpow_neg hd0.le]
        field_simp
      -- `Λ d / (d^s·log d·(s-1)) ≤ Λ d / (d^s·log 2·(s-1))` since `log 2 ≤ log d`.
      have hcb : (d:ℝ) ^ s * Real.log 2 * (s - 1) ≤ (d:ℝ) ^ s * Real.log d * (s - 1) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogge hds.le) hs1.le
      rw [hkey, show (1 / (Real.log 2 * (s - 1))) * ((Λ d : ℝ) / (d:ℝ) ^ s)
          = Λ d / ((d:ℝ) ^ s * Real.log 2 * (s - 1)) from by field_simp]
      exact div_le_div_of_nonneg_left vonMangoldt_nonneg (by positivity) hcb

/-- The integration-by-parts identity (#1583), with explicit qualifiers. -/
theorem log_zeta_eq_integ_aux (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s:ℂ)).re =
      (s - 1) * ∫ x in Set.Ioi 1, (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) := by
  rw [Mertens.log_zeta_eq_sum s hs]
  symm
  have hstep1 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s)
        = (∑ d ∈ Finset.Ioc 0 ⌊x⌋₊, c d) * x ^ (-s) := by
    intro x hx
    simp only [Mertens.E₂Λ, c]
    ring
  have hstep2 : ∀ x ∈ Set.Ioi (1:ℝ),
      (Real.log (Real.log x) + γ + E₂Λ x) * x ^ (-s) = ∑' d : ℕ, f s d x := by
    intro x hx
    rw [hstep1 x hx]
    simp only [f]
    rw [Finset.sum_mul]
    have hx0 : (0:ℝ) ≤ x := by have := hx; simp only [Set.mem_Ioi] at this; linarith
    rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊x⌋₊) ?_]
    · apply Finset.sum_congr rfl
      intro d hd
      simp only [Finset.mem_Ioc] at hd
      have hdx : (d:ℝ) ≤ x := by
        rw [← Nat.le_floor_iff hx0]; exact hd.2
      rw [Set.indicator_of_mem (by simpa using hdx)]
    · intro d hd
      simp only [Finset.mem_Ioc, not_and, not_le] at hd
      rcases Nat.eq_zero_or_pos d with hd0 | hd0
      · subst hd0; simp
      · have hfloor : ⌊x⌋₊ < d := hd hd0
        have hdx : x < (d:ℝ) := by
          rw [← Nat.floor_lt hx0]; exact hfloor
        rw [Set.indicator_of_notMem (by simpa using not_le.mpr hdx)]
        ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hstep2]
  have hperterm : ∀ d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · subst hd0; simp [f]
    simp only [f]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_indicator measurableSet_Ici]
    congr 1
    have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd0
    have hdR0 : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    set A : Set ℝ := Set.Ioi (1:ℝ) ∩ Set.Ici (d:ℝ) with hA
    have hae : A =ᵐ[volume] Set.Ioi (d:ℝ) := by
      have h1 : A =ᵐ[volume] (Set.Ici (1:ℝ) ∩ Set.Ici (d:ℝ) : Set ℝ) :=
        MeasureTheory.ae_eq_set_inter MeasureTheory.Ioi_ae_eq_Ici (ae_eq_refl _)
      rw [Set.Ici_inter_Ici, max_eq_right hdR] at h1
      exact h1.trans MeasureTheory.Ioi_ae_eq_Ici.symm
    rw [MeasureTheory.setIntegral_congr_set hae]
    rw [integral_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) hdR0,
      show (-s + 1 : ℝ) = 1 - s by ring]
    have hs1 : (1 - s) ≠ 0 := by linarith
    have hs2 : (s - 1) ≠ 0 := by linarith
    field_simp
    ring
  have hint : ∀ d : ℕ, MeasureTheory.IntegrableOn (f s d) (Set.Ioi (1:ℝ)) := by
    intro d
    unfold f
    apply MeasureTheory.Integrable.const_mul
    rw [show MeasureTheory.Integrable ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
        (volume.restrict (Set.Ioi (1:ℝ)))
      ↔ MeasureTheory.IntegrableOn ((Set.Ici (d:ℝ)).indicator fun x => x ^ (-s))
          (Set.Ioi (1:ℝ)) volume from Iff.rfl,
      MeasureTheory.integrableOn_indicator_iff measurableSet_Ici]
    apply MeasureTheory.IntegrableOn.mono_set
      (integrableOn_Ioi_rpow_of_lt (by linarith : (-s:ℝ) < -1) (by norm_num : (0:ℝ) < 1/2))
    intro x hx
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi] at hx ⊢
    linarith [hx.2]
  have hnorm_int : ∀ d : ℕ,
      ∫ x in Set.Ioi (1:ℝ), ‖f s d x‖ = c d * ((d:ℝ) ^ (1 - s) / (s - 1)) := by
    intro d
    rw [← hperterm d]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hfnn : 0 ≤ f s d x := by
      simp only [f]
      apply mul_nonneg (c_nonneg d)
      by_cases hxd : (d:ℝ) ≤ x
      · rw [Set.indicator_of_mem (by simpa using hxd)]
        exact le_of_lt (Real.rpow_pos_of_pos (by linarith) _)
      · rw [Set.indicator_of_notMem (by simpa using hxd)]
    change ‖f s d x‖ = f s d x
    rw [Real.norm_eq_abs, abs_of_nonneg hfnn]
  have hinterchange : ∫ x in Set.Ioi (1:ℝ), ∑' d : ℕ, f s d x
      = ∑' d : ℕ, ∫ x in Set.Ioi (1:ℝ), f s d x := by
    refine (MeasureTheory.integral_tsum_of_summable_integral_norm hint ?_).symm
    apply (summable_c_term s hs).congr
    intro d
    exact (hnorm_int d).symm
  rw [hinterchange]
  simp_rw [hperterm]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro d
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · subst hd0; simp
  · have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd0
    have hsub : (d:ℝ) ^ (1 - s) = (d:ℝ) ^ (-s) * (d:ℝ) := by
      rw [show (1 - s : ℝ) = -s + 1 by ring, Real.rpow_add hdR, Real.rpow_one]
    have hs1 : s - 1 ≠ 0 := by linarith
    have hneg : (d:ℝ) ^ (-s) = ((d:ℝ) ^ s)⁻¹ := by
      rw [Real.rpow_neg (le_of_lt hdR)]
    unfold c
    rw [hsub, hneg]
    field_simp

end LogZetaInteg
end

private theorem log_zeta_eq_integ (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = (s - 1) * ∫ x in .Ioi 1, (log (log x) + γ + E₂Λ x) * x^(-s) :=
  LogZetaInteg.log_zeta_eq_integ_aux s hs

private theorem mul_integ_log_log_eq (s : ℝ) (hs : 1 < s) :
    (s - 1) * ∫ x in .Ioi 1, log (log x) * x^(-s) = - log (s - 1) + deriv Gamma 1 :=
  mul_integ_log_log_eq_aux s hs

private theorem mul_integ_gamma_eq (s) (hs : 1 < s) : (s - 1) * ∫ x in .Ioi 1, γ * x^(-s) = γ := by
  rw [MeasureTheory.integral_const_mul γ (· ^ (-s)), @integral_Ioi_rpow_of_lt (-s), one_rpow] <;>
    grind

-- Integrability helpers for the integral splitting in `log_zeta_eq` (#1319).
-- Each summand of `(log (log x) + γ + E₂Λ x) * x^(-s)` is separately integrable on `Ioi 1`.

/-- Comparison test for `x ^ (-s)` decay: if `f` is measurable and dominated by `B * x ^ a` on
`Set.Ioi c` (with `0 < c` and `a + 1 < s`), then `fun x ↦ f x * x ^ (-s)` is integrable there.
This is the integral analogue of the summability of `O(x ^ a / x ^ s)` series and packages the
decay estimate reused for each tail in `log_zeta_eq`. -/
private theorem integrableOn_Ioi_mul_rpow_neg_of_abs_le
    {c B a s : ℝ} (hc : 0 < c) (has : a + 1 < s) {f : ℝ → ℝ} (hf : Measurable f)
    (hbound : ∀ x ∈ Set.Ioi c, |f x| ≤ B * x ^ a) :
    MeasureTheory.IntegrableOn (fun x => f x * x ^ (-s)) (Set.Ioi c) := by
  have hg : MeasureTheory.IntegrableOn (fun x => B * x ^ (a - s)) (Set.Ioi c) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : a - s < -1) hc).const_mul B
  refine MeasureTheory.Integrable.mono' hg
    (hf.mul (measurable_id.pow_const (-s))).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  have hxpos : (0:ℝ) < x := hc.trans hx
  have hxs : (0:ℝ) < x ^ (-s) := Real.rpow_pos_of_pos hxpos _
  rw [norm_mul, norm_eq_abs, norm_eq_abs, abs_of_pos hxs]
  calc |f x| * x ^ (-s) ≤ B * x ^ a * x ^ (-s) :=
        mul_le_mul_of_nonneg_right (hbound x hx) hxs.le
    _ = B * x ^ (a - s) := by rw [mul_assoc, ← Real.rpow_add hxpos, sub_eq_add_neg]

/-- `log (log x) * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(log-log singularity at `1` is integrable; `x^(-s)` gives decay). -/
private theorem integrableOn_log_log_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => log (log x) * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1:ℝ) ≤ 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `log (log x)` is integrable (log-log singularity) and `x^(-s) ≤ 1`.
    have hll : MeasureTheory.IntegrableOn (fun x => log (log x)) (Set.Ioc 1 2) := by
      have h : IntervalIntegrable (log ∘ log) MeasureTheory.volume 1 2 := by
        apply MeromorphicOn.intervalIntegrable_log
        intro x hx
        rw [Set.uIcc_of_le (by norm_num : (1:ℝ) ≤ 2)] at hx
        exact (analyticAt_log (by linarith [hx.1] : 0 < x)).meromorphicAt
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).mp h
    have hmul : MeasureTheory.IntegrableOn (fun x => x ^ (-s) * log (log x)) (Set.Ioc 1 2) := by
      apply hll.bdd_mul (c := 1)
      · fun_prop
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith [hx.1] : (0:ℝ) ≤ x) _)]
        calc x ^ (-s) ≤ (1:ℝ) ^ (-s) :=
              Real.rpow_le_rpow_of_nonpos (by norm_num) hx.1.le (by linarith)
          _ = 1 := Real.one_rpow _
    simpa [mul_comm] using hmul
  · -- Tail (`Ioi 2`): `|log (log x)| ≤ (1/ε + |log (log 2)|)·x^ε` with `ε = (s-1)/2`, `ε + 1 < s`.
    set ε := (s - 1) / 2 with hε
    have hεpos : 0 < ε := by rw [hε]; linarith
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := ε) (B := 1 / ε + |log (log 2)|)
      (by norm_num) (by rw [hε]; linarith) (Real.measurable_log.comp Real.measurable_log) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx1 : (1:ℝ) ≤ x ^ ε := Real.one_le_rpow (by linarith) hεpos.le
    have hlogx : 0 < log x := Real.log_pos (by linarith)
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hmono : log 2 ≤ log x := Real.log_le_log (by norm_num) (by linarith)
    have hub : log (log x) ≤ x ^ ε / ε :=
      calc log (log x) ≤ log x := (Real.log_le_sub_one_of_pos hlogx).trans (by linarith)
        _ ≤ x ^ ε / ε := Real.log_le_rpow_div (by linarith) hεpos
    have hlb : log (log 2) ≤ log (log x) := Real.log_le_log hlog2 hmono
    have hxε : 0 ≤ x ^ ε / ε := by positivity
    calc |log (log x)| ≤ x ^ ε / ε + |log (log 2)| := by
          rw [abs_le]
          exact ⟨by linarith [neg_abs_le (log (log 2))],
            by linarith [abs_nonneg (log (log 2))]⟩
      _ ≤ (1 / ε + |log (log 2)|) * x ^ ε := by
          have h2 : |log (log 2)| ≤ |log (log 2)| * x ^ ε := le_mul_of_one_le_right (abs_nonneg _) hx1
          have h1 : x ^ ε / ε = 1 / ε * x ^ ε := by ring
          rw [add_mul]; linarith

/-- `γ * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`. -/
private theorem integrableOn_γ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => γ * x ^ (-s)) (Set.Ioi 1) := by
  exact (integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) one_pos).const_mul γ

/-- `E₂Λ x * x ^ (-s)` is integrable on `Ioi 1` for `s > 1`
(`E₂Λ ~ -log(log x)` near `1`, and `E₂Λ = O(1/log x)` at `∞`). -/
private theorem integrableOn_E₂Λ_mul_rpow (s : ℝ) (hs : 1 < s) :
    MeasureTheory.IntegrableOn (fun x => E₂Λ x * x ^ (-s)) (Set.Ioi 1) := by
  rw [← Set.Ioo_union_Ici_eq_Ioi (by norm_num : (1:ℝ) < 2)]
  apply MeasureTheory.IntegrableOn.union
  · -- Near `1`: `⌊x⌋₊ = 1`, the sum is `0`, so `E₂Λ x = -log (log x) - γ`.
    have hsub : Set.Ioo (1:ℝ) 2 ⊆ Set.Ioi 1 := fun x hx => hx.1
    have h1 := (integrableOn_γ_mul_rpow s hs).mono_set hsub
    have h2 := (integrableOn_log_log_mul_rpow s hs).mono_set hsub
    have hb : MeasureTheory.IntegrableOn
        (fun x => -(log (log x) * x ^ (-s)) - γ * x ^ (-s)) (Set.Ioo 1 2) :=
      h2.neg.sub h1
    apply hb.congr_fun _ measurableSet_Ioo
    intro x hx
    simp only [Set.mem_Ioo] at hx
    have hfloor : ⌊ x ⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]
      exact ⟨by push_cast; linarith [hx.1], by push_cast; linarith [hx.2]⟩
    have hsum : (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / ((d:ℝ) * log d)) = 0 := by rw [hfloor]; norm_num
    change -(log (log x) * x ^ (-s)) - γ * x ^ (-s)
        = (∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d) - log (log x) - γ) * x ^ (-s)
    rw [hsum]; ring
  · -- Tail: `|E₂Λ x| ≤ (log 4 + 6)/log x ≤ (log 4 + 6)/log 2` is bounded (`a = 0`), times decay.
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    refine integrableOn_Ioi_mul_rpow_neg_of_abs_le (a := 0) (B := (log 4 + 6) / log 2)
      (by norm_num) (by linarith) (by fun_prop) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hlog2 : 0 < log 2 := Real.log_pos (by norm_num)
    have hc : 0 ≤ log 4 + 6 := by positivity
    rw [Real.rpow_zero, mul_one]
    have hb2 : (log 4 + 6) / log x ≤ (log 4 + 6) / log 2 :=
      div_le_div_of_nonneg_left hc hlog2 (Real.log_le_log (by norm_num) (le_of_lt hx))
    exact (E₂Λ.abs_le (le_of_lt hx)).trans hb2

@[blueprint
  "log-zeta-eq"
  (title := "An identity for $\\log \\zeta(s)$")
  (statement := /-- If $s > 1$ then $\log\zeta(s) = - \log (s-1) + \Gamma'(1) + \gamma + (s-1) \int_1^\infty E_{2,\Lambda}(x) x^{-s}\ ds$.
-/)
  (proof := /-- Combine the previous four sublemmas.-/)
  (latexEnv := "theorem")
  (discussion := 1319)]
private theorem log_zeta_eq (s : ℝ) (hs : 1 < s) :
    log (riemannZeta (s:ℂ)).re = - log (s - 1) + deriv Gamma 1 + γ + (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x^(-s) := by
  -- Start from the integration-by-parts identity (#1583).
  rw [log_zeta_eq_integ s hs]
  -- Linearity of the integral: split into the three summands (uses the integrability helpers).
  have key : (∫ x in Set.Ioi 1, (log (log x) + γ + E₂Λ x) * x ^ (-s))
      = (∫ x in Set.Ioi 1, log (log x) * x ^ (-s))
        + (∫ x in Set.Ioi 1, γ * x ^ (-s))
        + (∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)) := by
    rw [← MeasureTheory.integral_add (integrableOn_log_log_mul_rpow s hs)
      (integrableOn_γ_mul_rpow s hs)]
    rw [← MeasureTheory.integral_add (f := fun x => log (log x) * x ^ (-s) + γ * x ^ (-s))
      (g := fun x => E₂Λ x * x ^ (-s))
      ((integrableOn_log_log_mul_rpow s hs).add (integrableOn_γ_mul_rpow s hs))
      (integrableOn_E₂Λ_mul_rpow s hs)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    ring
  -- Apply sublemmas #1584 and #1585, then finish algebraically.
  rw [key, mul_add, mul_add, mul_integ_log_log_eq s hs, mul_integ_gamma_eq s hs]

private lemma zeta_pole_mul_re_tendsto_one :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (riemannZeta (s : ℂ)).re)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hofReal :
      Filter.Tendsto (fun s : ℝ => (s : ℂ)) (nhdsWithin 1 (Set.Ioi 1))
        (nhdsWithin (1 : ℂ) ({1} : Set ℂ)ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Set.mem_compl_singleton_iff.mpr (by
        norm_num
        exact ne_of_gt (Set.mem_Ioi.mp hs))
  have hcomplex :
      Filter.Tendsto (fun s : ℝ => ((s : ℂ) - 1) * riemannZeta (s : ℂ))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) :=
    riemannZeta_residue_one.comp hofReal
  have hreal :
      Filter.Tendsto
        (fun s : ℝ => (((s : ℂ) - 1) * riemannZeta (s : ℂ)).re)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 : ℝ)) :=
    (Complex.continuous_re.tendsto (1 : ℂ)).comp hcomplex
  simpa [Complex.ofReal_sub, Complex.ofReal_mul] using hreal

@[blueprint
  "log-zeta-limit"
  (title := "limiting behavior of log zeta")
  (statement := /-- One has $\log \zeta(s) = - \log(s-1) + o(1)$ as $s \to 1^+$.
-/)
  (proof := /-- Start with the asymptotic $\zeta(s) = \frac{1}{s-1} + O(1)$ and take logarithms.
  -/)
  (latexEnv := "sublemma")
  (discussion := 1586)]
private theorem log_zeta_limit :
    Filter.Tendsto
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  have hlog :
      Filter.Tendsto
        (fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re))
        (nhdsWithin 1 (Set.Ioi 1)) (nhds (Real.log 1)) :=
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp
      zeta_pole_mul_re_tendsto_one
  have hEq :
      (fun s : ℝ => Real.log (riemannZeta (s : ℂ)).re + Real.log (s - 1))
        =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
      fun s : ℝ => Real.log ((s - 1) * (riemannZeta (s : ℂ)).re) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s - 1 := sub_pos.mpr (Set.mem_Ioi.mp hs)
    have hzpos : 0 < (riemannZeta (s : ℂ)).re :=
      riemannZeta_re_pos_of_one_lt (Set.mem_Ioi.mp hs)
    rw [Real.log_mul hspos.ne' hzpos.ne']
    ring
  simpa using hlog.congr' (hEq.mono fun s hs => hs.symm)

-- Helpers for `deriv_gamma_add_γ_eq_zero` (#1320): take `s → 1⁺` in `log_zeta_eq`.
section
open MeasureTheory Set

/-- `E₂Λ` is measurable: its Mangoldt-sum part factors through `⌊·⌋₊` and the rest is
continuous/measurable. -/
private lemma measurable_E₂Λ : Measurable E₂Λ := by fun_prop

/-- On `(1,2)` the Mangoldt sum is empty (`⌊x⌋₊ = 1`), so `E₂Λ x = - log (log x) - γ`. -/
private lemma E₂Λ_eq_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    E₂Λ x = - log (log x) - γ := by
  obtain ⟨h1, h2⟩ := hx
  have hf : ⌊x⌋₊ = 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast h1.le, by exact_mod_cast h2⟩
  unfold E₂Λ
  rw [hf]
  simp

/-- Domination of `|E₂Λ|` near `1`: for `x ∈ (1,2)`, `|E₂Λ x| ≤ |log (x-1)| + log 2 + |γ|`,
the RHS being integrable on `(1,2)` (the `log (x-1)` is integrable across the singularity at `1`). -/
private lemma abs_E₂Λ_le_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo (1 : ℝ) 2) :
    |E₂Λ x| ≤ |log (x - 1)| + log 2 + |γ| := by
  obtain ⟨hx1, hx2⟩ := hx
  have hloglog : |log (log x)| ≤ |log (x - 1)| + log 2 := by
    have hxpos : (0:ℝ) < x := by linarith
    have hlogx_pos : 0 < log x := Real.log_pos hx1
    have hxm1 : 0 < x - 1 := by linarith
    have hub : log x ≤ x - 1 := by have := Real.log_le_sub_one_of_pos hxpos; linarith
    have hlb2 : (x - 1) / 2 ≤ log x := by
      have h := Real.log_le_sub_one_of_pos (x := 1 / x) (by positivity)
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one] at h
      simp only [zero_sub] at h
      have h12 : (x - 1) / 2 ≤ 1 - 1 / x := by
        rw [← sub_nonneg]
        have e : (1 - 1 / x) - (x - 1) / 2 = (3 * x - 2 - x ^ 2) / (2 * x) := by field_simp; ring
        rw [e]; exact div_nonneg (by nlinarith [hx1, hx2]) (by positivity)
      linarith
    have hupper : log (log x) ≤ log (x - 1) := Real.log_le_log hlogx_pos hub
    have hlower : log (x - 1) - log 2 ≤ log (log x) := by
      have := Real.log_le_log (show (0:ℝ) < (x - 1) / 2 by positivity) hlb2
      rwa [Real.log_div (by linarith) (by norm_num)] at this
    have h2 : (0:ℝ) ≤ log 2 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    exact ⟨by have := neg_abs_le (log (x - 1)); linarith,
          by have := le_abs_self (log (x - 1)); linarith⟩
  rw [E₂Λ_eq_on_Ioo ⟨hx1, hx2⟩]
  have htri : |(- log (log x) - γ)| ≤ |log (log x)| + |γ| := by
    have h := abs_sub (-log (log x)) γ
    rwa [abs_neg] at h
  linarith

/-- Constant bound on `|E₂Λ|` for `2 ≤ x`, sharpening `E₂Λ.abs_le` via `log 2 ≤ log x`. -/
private lemma abs_E₂Λ_le_const {x : ℝ} (hx : 2 ≤ x) :
    |E₂Λ x| ≤ (log 4 + 6) / log 2 :=
  (E₂Λ.abs_le hx).trans <| div_le_div_of_nonneg_left (by positivity)
    (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) hx)

/-- The near-1 dominating function `|log (x-1)| + log 2 + |γ|` is integrable on `(1,2)`
(it dominates `|E₂Λ|` there, handling the log-log singularity at `1`). -/
private lemma integrableOn_log_sub_one_bound :
    IntegrableOn (fun x => |log (x - 1)| + log 2 + |γ|) (Set.Ioo 1 2) volume := by
  have hlog : IntegrableOn (fun x => |log (x - 1)|) (Set.Ioo 1 2) volume := by
    have h0 : IntervalIntegrable (fun x => log x) volume 0 1 :=
      intervalIntegral.intervalIntegrable_log'
    have h1 : IntervalIntegrable (fun x => log (x - 1)) volume (0 + 1) (1 + 1) :=
      h0.comp_sub_right 1
    norm_num at h1
    exact (h1.1.mono_set Set.Ioo_subset_Ioc_self).abs
  have hc : IntegrableOn (fun _ : ℝ => log 2 + |γ|) (Set.Ioo (1 : ℝ) 2) volume :=
    integrableOn_const (measure_Ioo_lt_top).ne (by finiteness)
  have hsum : IntegrableOn (fun x => |log (x - 1)| + (log 2 + |γ|)) (Set.Ioo 1 2) volume :=
    hlog.add hc
  exact hsum.congr_fun (fun x _ => by ring) measurableSet_Ioo

/-- `E₂Λ` is integrable on every bounded interval `(1, X)` (`X ≥ 2`): log-log singularity near
`1` plus boundedness on `[2, X]`. -/
private lemma integrableOn_E₂Λ_Ioo {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn E₂Λ (Set.Ioo 1 X) volume := by
  have hsub : Set.Ioo (1 : ℝ) X ⊆ Set.Ioo 1 2 ∪ Set.Icc 2 X := by
    intro x hx; simp only [Set.mem_Ioo, Set.mem_union, Set.mem_Icc] at *
    rcases lt_or_ge x 2 with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨h, hx.2.le⟩
  apply IntegrableOn.mono_set _ hsub
  apply IntegrableOn.union
  · have hg := integrableOn_log_sub_one_bound
    refine Integrable.mono' hg measurable_E₂Λ.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_on_Ioo hx
  · refine Integrable.mono' (g := fun _ => (log 4 + 6) / log 2) ?_
      measurable_E₂Λ.aestronglyMeasurable ?_
    · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top) (by finiteness)
    · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
      rw [Real.norm_eq_abs]; exact abs_E₂Λ_le_const hx.1

/-- The error integral, scaled by `(s-1)`, vanishes as `s → 1⁺` (uses `E₂Λ =o(1)`). -/
private lemma sub_one_mul_integral_E₂Λ_tendsto :
    Filter.Tendsto (fun s : ℝ => (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- Choose `X ≥ 2` so that `|E₂Λ x| ≤ ε/2` for `x ≥ X` (from `E₂Λ =o(1)`).
  obtain ⟨X₀, hX₀⟩ : ∃ X, ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := by
    have := E₂Λ.bound'.def (by positivity : (0:ℝ) < ε / 2)
    simp only [Real.norm_eq_abs, abs_one, mul_one] at this
    rw [Filter.eventually_atTop] at this; exact this
  set X := max X₀ 2 with hXdef
  have hX2 : 2 ≤ X := le_max_right _ _
  have hXge : ∀ x ≥ X, |E₂Λ x| ≤ ε / 2 := fun x hx => hX₀ x (le_trans (le_max_left _ _) hx)
  -- `B` is the (finite) mass of `|E₂Λ|` on `(1, X)`.
  set B := ∫ x in Set.Ioo 1 X, |E₂Λ x| with hBdef
  have hB0 : 0 ≤ B := setIntegral_nonneg measurableSet_Ioo (fun x _ => abs_nonneg _)
  refine ⟨min 1 (ε / 2 / (B + 1)), by positivity, ?_⟩
  intro s hs hdist
  simp only [Set.mem_Ioi] at hs
  rw [Real.dist_eq] at hdist
  have hs1 : s - 1 < min 1 (ε / 2 / (B + 1)) := by
    rw [abs_of_pos (by linarith)] at hdist; exact hdist
  have hsm1 : 0 < s - 1 := by linarith
  -- `|E₂Λ|·x^(-s)` is integrable on `(1,∞)` and its subintervals.
  have hintAbs : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi 1) volume := by
    have h2 : IntegrableOn (fun x => |E₂Λ x * x ^ (-s)|) (Set.Ioi 1) volume :=
      (integrableOn_E₂Λ_mul_rpow s hs).abs
    refine h2.congr_fun ?_ measurableSet_Ioi
    intro x hx; simp only [Set.mem_Ioi] at hx
    change |E₂Λ x * x ^ (-s)| = |E₂Λ x| * x ^ (-s)
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  have hintAbsIoc : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioc 1 X) volume :=
    hintAbs.mono_set Set.Ioc_subset_Ioi_self
  have hintAbsIoiX : IntegrableOn (fun x => |E₂Λ x| * x ^ (-s)) (Set.Ioi X) volume :=
    hintAbs.mono_set (Set.Ioi_subset_Ioi (by linarith))
  -- Split `∫_{(1,∞)} = ∫_{(1,X]} + ∫_{(X,∞)}`.
  have hsplit : ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) =
      (∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s)) + ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) := by
    have hu : Set.Ioi (1:ℝ) = Set.Ioc 1 X ∪ Set.Ioi X :=
      (Set.Ioc_union_Ioi_eq_Ioi (by linarith)).symm
    rw [hu, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_left))
      (hintAbs.mono_set (by rw [hu]; exact Set.subset_union_right))]
  -- Piece 1: on `(1,X]`, `x^(-s) ≤ 1`, so the integral is `≤ B`.
  have hp1 : ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ B := by
    rw [hBdef]
    have ha : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioo 1 X) volume := (integrableOn_E₂Λ_Ioo hX2).abs
    have habsIoc : IntegrableOn (fun x => |E₂Λ x|) (Set.Ioc 1 X) volume :=
      ha.congr_set_ae (Ioo_ae_eq_Ioc).symm
    rw [← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_mono_on hintAbsIoc habsIoc measurableSet_Ioc
    intro x hx
    have hx1 : (1:ℝ) ≤ x := by have := hx.1; linarith
    have hle1 : x ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc |E₂Λ x| * x ^ (-s) ≤ |E₂Λ x| * 1 := by gcongr
      _ = |E₂Λ x| := mul_one _
  -- Piece 2: on `(X,∞)`, `|E₂Λ| ≤ ε/2`, and `∫_{(X,∞)} x^(-s) = X^(1-s)/(s-1)`.
  have hp2 : ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ (ε / 2) * (X ^ (1 - s) / (s - 1)) := by
    have hrpow_int : IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.Ioi X) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X)
    have hval : ∫ x in Set.Ioi X, x ^ (-s) = X ^ (1 - s) / (s - 1) := by
      rw [integral_Ioi_rpow_of_lt (by linarith) (by linarith : (0:ℝ) < X),
        show -s + 1 = 1 - s by ring, show (1:ℝ) - s = -(s - 1) by ring]
      rw [div_neg, neg_div, neg_neg]
    rw [← hval, ← integral_const_mul]
    apply setIntegral_mono_on hintAbsIoiX (hrpow_int.const_mul (ε / 2)) measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := by simp only [Set.mem_Ioi] at hx; linarith
    have hnn : 0 ≤ x ^ (-s) := Real.rpow_nonneg hxpos.le _
    have hb : |E₂Λ x| ≤ ε / 2 := hXge x (by simp only [Set.mem_Ioi] at hx; linarith)
    gcongr
  have hXpow : X ^ (1 - s) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  -- Assemble: `(s-1)·∫|E₂Λ|·x^(-s) ≤ (s-1)·B + ε/2`.
  have hbound : (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B + ε / 2 := by
    rw [hsplit, mul_add]
    have ht2 : (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s) ≤ ε / 2 := by
      calc (s - 1) * ∫ x in Set.Ioi X, |E₂Λ x| * x ^ (-s)
          ≤ (s - 1) * ((ε / 2) * (X ^ (1 - s) / (s - 1))) :=
            mul_le_mul_of_nonneg_left hp2 hsm1.le
        _ = (ε / 2) * X ^ (1 - s) := by
              have hne : s - 1 ≠ 0 := by linarith
              field_simp
        _ ≤ (ε / 2) * 1 := by gcongr
        _ = ε / 2 := mul_one _
    have ht1 : (s - 1) * ∫ x in Set.Ioc 1 X, |E₂Λ x| * x ^ (-s) ≤ (s - 1) * B :=
      mul_le_mul_of_nonneg_left hp1 hsm1.le
    linarith
  -- `|(s-1)·∫ E₂Λ·x^(-s)| ≤ (s-1)·∫|E₂Λ|·x^(-s)`.
  have habs_le : |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := by
    rw [abs_mul, abs_of_pos hsm1]
    gcongr
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Set.mem_Ioi] at hx
    change ‖E₂Λ x * x ^ (-s)‖ = |E₂Λ x| * x ^ (-s)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  rw [Real.dist_eq, sub_zero]
  -- `(s-1)·B + ε/2 < ε` since `s - 1 < ε/2/(B+1)`.
  have hfin : (s - 1) * B + ε / 2 < ε := by
    have hlt : s - 1 < ε / 2 / (B + 1) := lt_of_lt_of_le hs1 (min_le_right _ _)
    have hBp : 0 < B + 1 := by linarith
    have h1 : (s - 1) * B ≤ (s - 1) * (B + 1) := by nlinarith
    have h2 : (s - 1) * (B + 1) < (ε / 2 / (B + 1)) * (B + 1) := mul_lt_mul_of_pos_right hlt hBp
    have h3 : (ε / 2 / (B + 1)) * (B + 1) = ε / 2 := by field_simp
    linarith
  calc |(s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s)|
      ≤ (s - 1) * ∫ x in Set.Ioi 1, |E₂Λ x| * x ^ (-s) := habs_le
    _ ≤ (s - 1) * B + ε / 2 := hbound
    _ < ε := hfin

end

@[blueprint
  "Euler-Mascheroni-eq"
  (title := "Compatibility with Mathlib Euler-Mascheroni constant")
  (statement := /-- $\gamma$ is the Euler--Mascheroni constant.
-/)
  (proof := /-- Take limits as $s \to 1$ in the previous asymptotic using known asymptotics for $\zeta(s)$, and using that $- \Gamma'(1)$ is the Euler--Mascheroni constant. -/)
  (latexEnv := "theorem")
  (discussion := 1320)]
theorem deriv_gamma_add_γ_eq_zero : deriv Gamma 1 + γ = 0 := by
  -- For `s > 1`, `log_zeta_eq` rearranges to a constant identity.
  have key : ∀ s : ℝ, 1 < s →
      (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s) = deriv Gamma 1 + γ := by
    intro s hs
    have h := log_zeta_eq s hs
    linarith
  -- The LHS is eventually constant, so its limit is that constant.
  have hconst : Filter.Tendsto
      (fun s : ℝ => (Real.log (riemannZeta (s:ℂ)).re + Real.log (s - 1))
        - (s - 1) * ∫ x in Set.Ioi 1, E₂Λ x * x ^ (-s))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (deriv Gamma 1 + γ)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (key s hs).symm
  -- But the same function tends to `0 - 0` by the two limit lemmas.
  have hlim := log_zeta_limit.sub sub_one_mul_integral_E₂Λ_tendsto
  rw [sub_zero] at hlim
  exact tendsto_nhds_unique hconst hlim

theorem γ.eq_eulerMascheroni : γ = eulerMascheroniConstant := by
  linarith [Real.eulerMascheroniConstant_eq_neg_deriv, deriv_gamma_add_γ_eq_zero]

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
      eventually_atTop]
    obtain ⟨ C, _ ⟩ := sum_mangoldt_div_log_eq_log_log
    use C, 2


@[blueprint
  "Mertens-second-theorem-mangoldt-weak"]
theorem sum_mangoldt_div_log_eq_log_log'' : (fun x ↦ ∑ d ∈ Ioc 0 ⌊ x ⌋₊, (Λ d) / (d * log d)) ~[atTop] (fun x ↦ log (log x)) := by
    apply IsLittleO.isEquivalent (IsBigO.trans_isLittleO _ one_eq_o_log_log)
    convert! sum_mangoldt_div_log_eq_log_log' using 1


lemma HasSum_log_one_sub_one_div_prime {p : ℕ} (hp : p.Prime) :
    HasSum (fun n : ℕ ↦ (-1 : ℝ) / (( n + 1) * p ^ (n + 1))) (log (1 - 1 / p)) := by
  convert! Real.hasSum_pow_div_log_of_abs_lt_one (x := 1 / p) _|>.neg using 1
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
  convert! tsum_zero with p
  grind

lemma tsum_primes_eq_tsum_ite (f : ℕ → ℝ) :
    ∑' (n : Nat.Primes), f n = ∑' (n : ℕ), if n.Prime then f n else 0 := by
  convert! _root_.tsum_subtype Nat.Prime f using 2
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
      convert! HasDerivAt.fun_div (d' := (1 : ℝ)) (hasDerivAt_const ..) _ _ using 1
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
  · convert! integrableOn_add_rpow_Ioi_of_lt (by norm_num : (-2 : ℝ) < -1) (by linarith : -N < 0) using 2
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
    simp only [isBigO_iff, norm_eq_abs, eventually_atTop]
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
     simp only [EventuallyEq.iff_eventually, Pi.div_apply, eventually_atTop]; use 2; intro x hx
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
