import PrimeNumberTheoremAnd.Defs
import PrimeNumberTheoremAnd.PVIdentity
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.style.show false
set_option linter.unusedVariables false
set_option linter.flexible false

/-!
# Series expansion for the logarithmic integral

We prove the well-known series expansion

$$\mathrm{li}(x) = \gamma + \ln(\ln x) + \sum_{n=1}^{\infty} \frac{(\ln x)^n}{n \cdot n!}$$

for $x > 1$, where $\gamma$ is the Euler–Mascheroni constant.

# Key theorems

- li_eq_eulerMascheroni_add_log_log_add_tsum : li x = eulerMascheroniConstant + log (log x) + ∑' n : ℕ, (log x) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial)

# Strategy

This follows from the substitution $t = e^u$ in the definition
$\mathrm{li}(x) = \mathrm{PV}\int_0^x \frac{dt}{\log t}$
which gives $\mathrm{li}(x) = \mathrm{PV}\int_{-\infty}^{\ln x} \frac{e^u}{u}\,du = \mathrm{Ei}(\ln x)$,
and the classical series for the exponential integral
$$\mathrm{Ei}(y) = \gamma + \ln y + \sum_{n=1}^{\infty} \frac{y^n}{n \cdot n!}$$
which is obtained by integrating $(e^u - 1)/u = \sum_{n=0}^{\infty} u^n/(n+1)!$
term by term on $[0, y]$.
-/

open Real Set MeasureTheory Filter Topology Finset
open scoped NNReal ENNReal

namespace LiSeries

/-! ## Part A: Power series for (eᵘ - 1)/u -/

/-- The exponential function has the series `exp u = ∑ u^n / n!`. Shifting the index by 1 and
subtracting the constant term gives `exp u - 1 = ∑_{n≥0} u^{n+1} / (n+1)!`. -/
theorem hasSum_exp_sub_one {u : ℝ} :
    HasSum (fun n : ℕ => u ^ (n + 1) / (n + 1).factorial) (exp u - 1) := by
  have h := NormedSpace.expSeries_div_hasSum_exp u
  rw [show NormedSpace.exp u = exp u from congr_fun exp_eq_exp_ℝ.symm u] at h
  rw [← hasSum_nat_add_iff' 1] at h
  simp only [range_one, sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] at h
  exact h

/-- For `u ≠ 0`, `(exp u - 1) / u = ∑ u^n / (n+1)!`. -/
theorem hasSum_exp_sub_one_div {u : ℝ} (hu : u ≠ 0) :
    HasSum (fun n : ℕ => u ^ n / (n + 1).factorial) ((exp u - 1) / u) := by
  have h := hasSum_exp_sub_one (u := u)
  have key : ∀ n : ℕ, u ^ (n + 1) / ↑(n + 1).factorial = u * (u ^ n / ↑(n + 1).factorial) :=
    fun n => by rw [pow_succ u n]; ring
  simp_rw [key] at h
  rwa [show exp u - 1 = u * ((exp u - 1) / u) from by field_simp,
    hasSum_mul_left_iff hu] at h

/-! ## Part B: Term-by-term integration -/

/-- Bundled continuous map for the n-th term u ↦ uⁿ/(n+1)! of the power series. -/
private noncomputable def termFun (n : ℕ) : C(ℝ, ℝ) :=
  ⟨fun u => u ^ n / ↑(n + 1).factorial, (continuous_pow n).div_const _⟩

private lemma abs_le_max_abs_of_mem_uIcc {a b x : ℝ} (hx : x ∈ Set.uIcc a b) :
    |x| ≤ max |a| |b| := by
  simp only [Set.mem_uIcc] at hx
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact abs_le.mpr ⟨by linarith [neg_abs_le a, le_max_left |a| |b|],
                       by linarith [le_abs_self b, le_max_right |a| |b|]⟩
  · exact abs_le.mpr ⟨by linarith [neg_abs_le b, le_max_right |a| |b|],
                       by linarith [le_abs_self a, le_max_left |a| |b|]⟩

set_option maxHeartbeats 800000 in
private lemma summable_pow_div_succ_factorial (M : ℝ) :
    Summable (fun n : ℕ => M ^ n / ↑(n + 1).factorial) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp M).summable
  apply @Summable.of_norm_bounded ℕ ℝ _ _
    (f := fun n => M ^ n / ↑(n + 1).factorial)
    (g := fun n => ‖M ^ n / ↑n.factorial‖)
  · exact hs.norm
  · intro n
    simp only [norm_div, norm_pow]
    rw [Real.norm_eq_abs (↑(n+1).factorial), abs_of_nonneg (Nat.cast_nonneg' _),
        Real.norm_eq_abs (↑n.factorial), abs_of_nonneg (Nat.cast_nonneg' _)]
    apply div_le_div_of_nonneg_left (pow_nonneg (norm_nonneg M) n)
      (Nat.cast_pos.mpr (Nat.factorial_pos _))
      (Nat.cast_le.mpr (Nat.factorial_le (Nat.le_succ n)))

private lemma summable_termFun_norm (a b : ℝ) :
    Summable fun n : ℕ =>
      ‖(termFun n).restrict ↑(⟨uIcc a b, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
  apply (summable_pow_div_succ_factorial (max |a| |b|)).of_nonneg_of_le
    (fun n => norm_nonneg _) (fun n => ?_)
  rw [ContinuousMap.norm_le _ (by positivity)]
  intro ⟨x, hx⟩
  simp only [termFun, ContinuousMap.restrict_apply, ContinuousMap.coe_mk, Real.norm_eq_abs,
             abs_div, abs_pow, abs_of_nonneg (Nat.cast_nonneg' (α := ℝ) (n + 1).factorial)]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (abs_le_max_abs_of_mem_uIcc hx) n)
    (Nat.cast_nonneg' _)

private lemma integral_term (y : ℝ) (n : ℕ) :
    ∫ u in (0 : ℝ)..y, (u ^ n / ↑(n + 1).factorial) =
      y ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  rw [intervalIntegral.integral_div, integral_pow]
  simp only [zero_pow (Nat.succ_ne_zero n), sub_zero]
  rw [div_div]; congr 1; push_cast; ring

/-- The integral `∫₀ʸ (eᵘ - 1)/u du = ∑ y^(n+1) / ((n+1) · (n+1)!)`.

This is proved by integrating the power series `(eᵘ-1)/u = ∑ uⁿ/(n+1)!` term by term
on `[0, y]`. Each term integrates to `y^(n+1)/((n+1)(n+1)!)`. -/
theorem integral_exp_sub_one_div_eq_tsum (y : ℝ) :
    ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) =
      ∑' n : ℕ, y ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  -- Step 1: Swap ∫ and ∑ using summability of norms
  have hswap := intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
    (summable_termFun_norm 0 y)
  simp only [show ∀ n, (fun x => (termFun n) x) = fun u => u ^ n / ↑(n + 1).factorial from
    fun n => rfl] at hswap
  -- Step 2: Compute each integral
  simp_rw [integral_term] at hswap
  -- hswap: ∑' n, y^{n+1}/((n+1)*(n+1)!) = ∫₀ʸ ∑' n, u^n/(n+1)!
  -- Step 3: Show ∫₀ʸ (exp u - 1)/u = ∫₀ʸ ∑' n, u^n/(n+1)! (they agree a.e.)
  trans (∫ u in (0 : ℝ)..y, ∑' n : ℕ, u ^ n / ↑(n + 1).factorial)
  · apply intervalIntegral.integral_congr_ae
    -- (exp u - 1)/u = ∑ u^n/(n+1)! for u ≠ 0 by hasSum_exp_sub_one_div;
    -- {0} has Lebesgue measure zero, so the equality holds a.e.
    have hae : ∀ᵐ (u : ℝ), u ≠ 0 :=
      ae_iff.mpr (by simp [show (volume : Measure ℝ) {(0 : ℝ)} = 0 from by simp])
    exact hae.mono (fun u hu _ => (hasSum_exp_sub_one_div hu).tsum_eq.symm)
  · exact hswap.symm

/-! ## Part C: The Euler-Mascheroni constant as an integral -/

/-- `γ = -Γ'(1) = -∫₀^∞ log(t) exp(-t) dt`. -/
theorem eulerMascheroni_eq_neg_integral :
    eulerMascheroniConstant = -(∫ t in Ioi (0 : ℝ), log t * exp (-t)) := by
  -- Step 1: Get the complex derivative of GammaIntegral at s = 1
  have hpos : (0 : ℝ) < (1 : ℂ).re := by simp
  have hderiv_integral := Complex.hasDerivAt_GammaIntegral hpos
  -- Step 2: Gamma = GammaIntegral on {s | 0 < s.re}, which is a nhd of 1
  have heq : Complex.Gamma =ᶠ[𝓝 1] Complex.GammaIntegral := by
    have : {s : ℂ | 0 < s.re} ∈ 𝓝 (1 : ℂ) := by
      apply IsOpen.mem_nhds
      · exact isOpen_lt continuous_const Complex.continuous_re
      · simp
    exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨{s : ℂ | 0 < s.re}, this,
      fun s hs => Complex.Gamma_eq_integral hs⟩
  -- Step 3: So Gamma has the same derivative as GammaIntegral at 1
  have hderiv_Gamma := hderiv_integral.congr_of_eventuallyEq heq
  -- Step 4: But we also know the derivative of complex Gamma at 1
  have hderiv_known := Complex.hasDerivAt_Gamma_one
  -- Step 5: By uniqueness of derivatives
  have key := hderiv_Gamma.unique hderiv_known
  -- Step 6: Simplify the integral in `key`
  -- The integrand is ↑t ^ (1 - 1) * (↑(log t) * ↑(rexp (-t)))
  -- Simplify to ↑(log t * exp(-t)) using t^0 = 1
  have simp_integral : (∫ t : ℝ in Ioi 0,
      (t : ℂ) ^ ((1 : ℂ) - 1) * (↑(log t) * ↑(rexp (-t)))) =
      ↑(∫ t : ℝ in Ioi 0, log t * rexp (-t)) := by
    rw [show (1 : ℂ) - 1 = 0 from sub_self 1]
    simp_rw [Complex.cpow_zero, one_mul, ← Complex.ofReal_mul]
    exact integral_ofReal
  rw [simp_integral] at key
  -- key : ↑(∫ t in Ioi 0, log t * rexp (-t)) = -↑eulerMascheroniConstant
  rw [← Complex.ofReal_neg] at key
  have := Complex.ofReal_injective key.symm
  linarith


namespace FubiniLogExpNeg

/-! ## Integrability lemmas -/

lemma integrableOn_log_Ioc : IntegrableOn log (Set.Ioc 0 1) :=
  (intervalIntegral.intervalIntegrable_log' (a := 0) (b := 1)).1

lemma integrableOn_log_mul_exp_neg_Ioc :
    IntegrableOn (fun t => log t * exp (-t)) (Set.Ioc 0 1) :=
  integrableOn_log_Ioc.mul_continuousOn_of_subset
    (continuous_exp.comp continuous_neg).continuousOn
    measurableSet_Ioc isCompact_Icc Ioc_subset_Icc_self

lemma integrableOn_log_mul_exp_neg_Ioi_one :
    IntegrableOn (fun t => log t * exp (-t)) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t => t * exp (-t)) (Set.Ioi 1) := by
    have := (GammaIntegral_convergent (s := 2) (by norm_num : (0 : ℝ) < 2)).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)
    apply this.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    rw [show (2 : ℝ) - 1 = 1 from by norm_num, rpow_one t, mul_comm]
  rw [IntegrableOn] at hg ⊢
  exact hg.mono
    ((measurable_log.mul
        (continuous_exp.comp continuous_neg).measurable).aestronglyMeasurable.restrict)
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [Set.mem_Ioi] at ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
        rw [norm_mul, norm_mul, Real.norm_eq_abs (log t), Real.norm_eq_abs t,
            abs_of_nonneg (log_nonneg ht.le), abs_of_pos ht0]
        exact mul_le_mul_of_nonneg_right (log_le_self ht0.le) (norm_nonneg _))

lemma integrableOn_exp_neg_div_Ioi_one :
    IntegrableOn (fun t => exp (-t) / t) (Set.Ioi 1) := by
  have hg : IntegrableOn (fun t => exp (-t)) (Set.Ioi 1) := by
    have := (GammaIntegral_convergent (s := 1) (by norm_num : (0 : ℝ) < 1)).mono_set
      (Set.Ioi_subset_Ioi zero_le_one)
    apply this.congr
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simp only [Set.mem_Ioi] at ht
    rw [show (1 : ℝ) - 1 = 0 from by norm_num, rpow_zero, mul_one]
  rw [IntegrableOn] at hg ⊢
  exact hg.mono
    ((continuous_exp.comp continuous_neg).measurable.div measurable_id).aestronglyMeasurable.restrict
    (by filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
        simp only [Set.mem_Ioi] at ht
        have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
        rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (exp_pos _), abs_of_pos ht0]
        exact div_le_self (le_of_lt (exp_pos _)) (le_of_lt ht))

/-! ## IBP on `(1, ∞)`: `∫₁^∞ log(t) exp(-t) dt = ∫₁^∞ exp(-t)/t dt` -/

lemma ibp_Ioi_one :
    ∫ t in Set.Ioi (1 : ℝ), log t * exp (-t) =
      ∫ t in Set.Ioi (1 : ℝ), exp (-t) / t := by
  have hlog_deriv : ∀ t ∈ Set.Ioi (1 : ℝ), HasDerivAt log (t⁻¹) t :=
    fun t ht => Real.hasDerivAt_log (ne_of_gt (lt_trans one_pos ht))
  have hv_deriv : ∀ t ∈ Set.Ioi (1 : ℝ), HasDerivAt (fun t => -exp (-t)) (exp (-t)) t := by
    intro t _; have h := (hasDerivAt_neg t).exp.neg; convert h using 1; simp [mul_comm]
  have h_uv'_int : IntegrableOn (log * fun t => exp (-t)) (Set.Ioi 1) :=
    integrableOn_log_mul_exp_neg_Ioi_one
  have h_u'v_int : IntegrableOn ((fun t => t⁻¹) * fun t => -exp (-t)) (Set.Ioi 1) := by
    have := integrableOn_exp_neg_div_Ioi_one.neg
    refine this.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
    simp [Pi.mul_apply, div_eq_mul_inv]; ring
  have h_lim_1 : Tendsto (log * fun t => -exp (-t)) (𝓝[>] (1 : ℝ))
      (𝓝 (log 1 * -exp (-(1 : ℝ)))) := by
    apply Filter.Tendsto.mul
    · exact (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.mono_left
        nhdsWithin_le_nhds
    · exact ((continuous_exp.comp continuous_neg).neg.continuousAt).tendsto.mono_left
        nhdsWithin_le_nhds
  have h_lim_inf : Tendsto (log * fun t => -exp (-t)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t * exp (-t)) atTop (𝓝 0) := by
      simpa using tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h2 : Tendsto (fun t : ℝ => log t * exp (-t)) atTop (𝓝 0) := by
      apply squeeze_zero_norm' _ h1
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with t ht
      rw [norm_mul, Real.norm_of_nonneg (Real.log_nonneg ht),
          Real.norm_of_nonneg (exp_pos _).le]
      exact mul_le_mul_of_nonneg_right (Real.log_le_self (by linarith)) (exp_pos _).le
    show Tendsto (fun t : ℝ => log t * (-exp (-t))) atTop (𝓝 0)
    have h3 := (neg_zero (G := ℝ)) ▸ h2.neg
    exact Filter.Tendsto.congr (fun t => by ring) h3
  rw [integral_Ioi_mul_deriv_eq_deriv_mul hlog_deriv hv_deriv h_uv'_int h_u'v_int
      h_lim_1 h_lim_inf]
  simp only [log_one, zero_mul, sub_zero, zero_sub]
  rw [neg_eq_iff_eq_neg, ← integral_neg]
  exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => by
    simp only [Set.mem_Ioi] at ht; simp [div_eq_mul_inv]; ring)

/-! ## The `(0, 1]` part -/

private lemma intervalIntegrable_expm1_div :
    IntervalIntegrable (fun t => (exp (-t) - 1) / t) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
  apply Integrable.mono' (g := fun _ => (1 : ℝ))
    (integrableOn_const (by exact measure_Ioc_lt_top.ne))
  · exact (((continuous_exp.comp continuous_neg).sub continuous_const).measurable.div
      measurable_id).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    simp only [Set.mem_Ioc] at ht
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht.1, div_le_one ht.1, abs_le]
    exact ⟨by linarith [one_sub_le_exp_neg t],
           by linarith [exp_le_one_iff.mpr (neg_nonpos.mpr ht.1.le)]⟩

private lemma ibp_eps {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∫ t in ε..1, log t * exp (-t) =
      (exp (-ε) - 1) * log ε + ∫ t in ε..1, (exp (-t) - 1) / t := by
  have hne : ∀ x ∈ Set.Icc ε 1, (x : ℝ) ≠ 0 :=
    fun x hx => ne_of_gt (lt_of_lt_of_le hε0 hx.1)
  have hlog_deriv : ∀ x ∈ Set.uIcc ε 1, HasDerivAt log x⁻¹ x := by
    intro x hx; rw [Set.uIcc_of_le hε1.le] at hx
    exact hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hε0 hx.1))
  have hv_deriv : ∀ x ∈ Set.uIcc ε 1, HasDerivAt (fun t => -exp (-t)) (exp (-x)) x := by
    intro x _; have h := (hasDerivAt_neg x).exp; convert h.neg using 1; simp [mul_comm]
  have h_u'_int : IntervalIntegrable (fun x => x⁻¹) volume ε 1 :=
    (continuousOn_inv₀.mono fun x hx => hne x hx).intervalIntegrable_of_Icc hε1.le
  have h_v'_int : IntervalIntegrable (fun x => exp (-x)) volume ε 1 :=
    (continuous_exp.comp continuous_neg).continuousOn.intervalIntegrable_of_Icc hε1.le
  have hIBP := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hlog_deriv hv_deriv h_u'_int h_v'_int
  have h_expm1_int : IntervalIntegrable (fun t => (exp (-t) - 1) / t) volume ε 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc hε1.le
    exact ((continuous_exp.comp continuous_neg).sub continuous_const).continuousOn.div
      continuous_id.continuousOn (fun x hx => hne x hx)
  have h_inv_eq : ∫ t in ε..1, t⁻¹ = -log ε := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hlog_deriv h_u'_int]; simp [log_one]
  have h_inv_exp_eq : ∫ t in ε..1, t⁻¹ * exp (-t) =
      (∫ t in ε..1, (exp (-t) - 1) / t) - log ε := by
    have := intervalIntegral.integral_add h_expm1_int h_u'_int
    have h_eq : (fun x => (exp (-x) - 1) / x + x⁻¹) = fun x => x⁻¹ * exp (-x) := by
      ext x; field_simp; ring
    rw [h_eq] at this; linarith [h_inv_eq]
  have h_ibp_int_eq : ∫ x in ε..1, x⁻¹ * (-exp (-x)) =
      -(∫ t in ε..1, (exp (-t) - 1) / t) + log ε := by
    rw [show (fun x : ℝ => x⁻¹ * (-exp (-x))) = fun x => -(x⁻¹ * exp (-x)) from by ext; ring,
      intervalIntegral.integral_neg, h_inv_exp_eq]; ring
  rw [h_ibp_int_eq] at hIBP
  simp only [log_one, zero_mul] at hIBP
  nlinarith

private lemma nhdsWithin_Ioi_le_nhdsWithin_uIcc :
    𝓝[Set.Ioi 0] (0 : ℝ) ≤ 𝓝[Set.uIcc 0 1] 0 := by
  rw [Set.uIcc_of_le zero_le_one,
    ← nhdsWithin_inter_of_mem
      (show Set.Iio (1 : ℝ) ∈ 𝓝[Set.Ioi 0] 0 from
        nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ) < 1))),
    Set.inter_comm]
  exact nhdsWithin_mono 0 (fun x ⟨h1, h2⟩ => ⟨le_of_lt h1, le_of_lt h2⟩)

lemma ibp_Ioc_zero_one :
    ∫ t in Set.Ioc (0 : ℝ) 1, log t * exp (-t) =
      ∫ t in (0 : ℝ)..1, (exp (-t) - 1) / t := by
  rw [← intervalIntegral.integral_of_le zero_le_one]
  have hf_int : IntervalIntegrable (fun t => log t * exp (-t)) volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mpr
      integrableOn_log_mul_exp_neg_Ioc
  have hg_int := intervalIntegrable_expm1_div
  set F : ℝ → ℝ := fun ε => (∫ t in ε..(1 : ℝ), log t * exp (-t)) -
      (∫ t in ε..(1 : ℝ), (exp (-t) - 1) / t)
  suffices F 0 = 0 by simp [F] at this; linarith
  have hf_intOn : IntegrableOn (fun t => log t * exp (-t)) (Set.uIcc 0 1) :=
    (intervalIntegrable_iff').1 hf_int
  have hg_intOn : IntegrableOn (fun t => (exp (-t) - 1) / t) (Set.uIcc 0 1) :=
    (intervalIntegrable_iff').1 hg_int
  have hF_cts : ContinuousOn F (Set.uIcc 0 1) :=
    (intervalIntegral.continuousOn_primitive_interval_left hf_intOn).sub
      (intervalIntegral.continuousOn_primitive_interval_left hg_intOn)
  have hF_tends_F0 : Tendsto F (𝓝[Set.Ioi 0] 0) (𝓝 (F 0)) :=
    (hF_cts.continuousWithinAt left_mem_uIcc).mono_left nhdsWithin_Ioi_le_nhdsWithin_uIcc
  have h_bdy : Tendsto (fun ε => (exp (-ε) - 1) * log ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h_mul_log : Tendsto (fun x : ℝ => log x * x) (𝓝[>] 0) (𝓝 0) := by
      simpa [rpow_one] using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
    exact squeeze_zero_norm'
      (eventually_nhdsWithin_of_forall fun ε (hε : 0 < ε) => by
        simp only [Real.norm_eq_abs, abs_mul]
        calc |exp (-ε) - 1| * |log ε| = |log ε| * |exp (-ε) - 1| := mul_comm _ _
          _ ≤ |log ε| * |ε| := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
              rw [abs_le, abs_of_pos hε]
              exact ⟨by linarith [one_sub_le_exp_neg ε],
                     by linarith [exp_le_one_iff.mpr (neg_nonpos.mpr hε.le)]⟩)
      (by simpa [norm_zero] using h_mul_log.norm)
  have hF_tends_0 : Tendsto F (𝓝[Set.Ioi 0] 0) (𝓝 0) := by
    apply Tendsto.congr' _ h_bdy
    rw [eventuallyEq_nhdsWithin_iff]
    filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 from by norm_num)] with ε hε hε0
    simp only [F]
    linarith [ibp_eps hε0 hε]
  exact tendsto_nhds_unique hF_tends_F0 hF_tends_0

end FubiniLogExpNeg

open FubiniLogExpNeg in
theorem fubini_log_exp_neg :
    ∫ t in Ioi (0 : ℝ), log t * exp (-t) =
      (∫ t in (0 : ℝ)..1, (exp (-t) - 1) / t) + ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  -- Split ∫_{Ioi 0} = ∫_{Ioc 0 1} + ∫_{Ioi 1}
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 :=
    (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit, setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      integrableOn_log_mul_exp_neg_Ioc integrableOn_log_mul_exp_neg_Ioi_one]
  rw [ibp_Ioc_zero_one, ibp_Ioi_one]


/-- The Euler-Mascheroni constant expressed as a split integral:
    `γ = -∫₀¹ (e^{-t}-1)/t dt - ∫₁^∞ e^{-t}/t dt`.

    This follows from `eulerMascheroni_eq_neg_integral` and `fubini_log_exp_neg`. -/
theorem eulerMascheroni_eq_split_integral :
    eulerMascheroniConstant =
      -(∫ t in (0 : ℝ)..1, (exp (-t) - 1) / t) - ∫ t in Ioi (1 : ℝ), exp (-t) / t := by
  -- Follows from eulerMascheroni_eq_neg_integral and fubini_log_exp_neg
  -- by -(A + B) = -A - B
  have h1 := eulerMascheroni_eq_neg_integral
  have h2 := fubini_log_exp_neg
  have neg_add_eq : ∀ a b : ℝ, -(a + b) = -a - b := fun a b => by ring
  exact h1.trans ((congrArg (- ·) h2).trans (neg_add_eq _ _))

/-! ## Part D: Substitution t = eᵘ in li(x) and PV decomposition -/

/-- For a > 1, the substitution t = eᵘ transforms
    ∫ₐᵇ dt/log(t) into ∫_{log a}^{log b} eᵘ/u du. -/
theorem integral_log_inv_eq_integral_exp_div {a b : ℝ} (ha : 1 < a) (hb : a < b) :
    ∫ t in a..b, 1 / log t = ∫ u in log a..log b, exp u / u := by
  -- Use integral_comp_mul_deriv': ∫ u in α..β, (g ∘ f) u * f' u = ∫ t in f(α)..f(β), g t
  -- with f = exp, α = log a, β = log b, g = (1/log ·)
  -- Then g(eᵘ) · eᵘ = (1/u) · eᵘ = eᵘ/u
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hab : a ≤ b := le_of_lt hb
  -- The change of variables formula gives:
  -- ∫ u in log a..log b, (g ∘ exp) u * exp u = ∫ t in exp(log a)..exp(log b), g t
  -- where g t = 1 / log t
  have key : ∫ u in log a..log b, ((fun t => 1 / log t) ∘ exp) u * exp u =
      ∫ t in exp (log a)..exp (log b), 1 / log t :=
    intervalIntegral.integral_comp_mul_deriv'
      (fun x _ => Real.hasDerivAt_exp x)
      (continuous_exp.continuousOn)
      ?_
  · -- Simplify: exp(log a) = a, exp(log b) = b
    rw [exp_log ha0, exp_log hb0] at key
    rw [← key]
    -- Show integrands agree: (1/log(exp u)) * exp u = exp u / u
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u _
    simp only [Function.comp, Real.log_exp]
    ring
  · -- ContinuousOn (1/log ·) on (exp '' [[log a, log b]])
    -- exp '' [[log a, log b]] ⊆ [[a, b]] where log > 0
    apply ContinuousOn.mono (s := Set.Icc a b)
    · apply ContinuousOn.div continuousOn_const
      · exact continuousOn_log.mono (fun x hx => ne_of_gt (by linarith [hx.1]))
      · intro x hx; exact ne_of_gt (Real.log_pos (by linarith [hx.1]))
    · intro x hx
      have hsub := exp_strictMono.monotone.image_uIcc_subset (a := log a) (b := log b) hx
      rw [exp_log ha0, exp_log hb0] at hsub
      rw [Set.uIcc_of_le (Real.log_le_log ha0 hab)] at hx
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub


/-- The PV integral of eᵘ/u from -∞ to y equals γ + log(y) + ∫₀ʸ (eᵘ-1)/u du for y > 0.
    This is the core analytic identity connecting the Euler-Mascheroni constant
    to the exponential integral. -/
theorem pv_exp_div_eq_gamma_add_log_add_integral {y : ℝ} (hy : 0 < y) :
    lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..y, exp u / u)) =
    eulerMascheroniConstant + log y + ∫ u in (0 : ℝ)..y, ((exp u - 1) / u) := by
  exact _root_.pv_exp_div_eq_gamma_add_log_add_integral hy

/-! ## Part D': Substitution for (0,1) interval -/

/-- The substitution t = eᵘ also works on (0, b) with b < 1, where log t < 0.
    For 0 < a ≤ b < 1, ∫ₐᵇ 1/log(t) dt = ∫_{log a}^{log b} eᵘ/u du. -/
private theorem integral_log_inv_eq_integral_exp_div_of_lt_one {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb1 : b < 1) :
    ∫ t in a..b, 1 / log t = ∫ u in log a..log b, exp u / u := by
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le ha hab
  have key : ∫ u in log a..log b, ((fun t => 1 / log t) ∘ exp) u * exp u =
      ∫ t in exp (log a)..exp (log b), 1 / log t :=
    intervalIntegral.integral_comp_mul_deriv'
      (fun x _ => Real.hasDerivAt_exp x)
      continuous_exp.continuousOn
      ?_
  · rw [exp_log ha, exp_log hb0] at key
    rw [← key]
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u _
    simp only [Function.comp, Real.log_exp]
    ring
  · apply ContinuousOn.mono (s := Set.Icc a b)
    · apply ContinuousOn.div continuousOn_const
      · exact continuousOn_log.mono (fun x hx => ne_of_gt (by linarith [hx.1]))
      · intro x hx; exact ne_of_lt (Real.log_neg (by linarith [hx.1]) (by linarith [hx.2]))
    · intro x hx
      have hsub := exp_strictMono.monotone.image_uIcc_subset (a := log a) (b := log b) hx
      rw [exp_log ha, exp_log hb0] at hsub
      rw [Set.uIcc_of_le (Real.log_le_log ha hab)] at hx
      rw [Set.uIcc_of_le hab] at hsub
      exact hsub

/-! ## Part D'': Connecting li(x) to the PV exponential integral -/

/-- For x > 1 and small ε, the set integral in the definition of li(x) splits into
    two interval integrals. -/
private lemma li_setDiff_eq_split {x ε : ℝ} (hx : 1 < x) (hε : 0 < ε)
    (hε1 : ε < 1) (hεx : 1 + ε < x) :
    ∫ t in (Ioc 0 x \ Ioo (1 - ε) (1 + ε)), (1 : ℝ) / log t =
      (∫ t in (0 : ℝ)..(1 - ε), 1 / log t) + ∫ t in (1 + ε)..x, 1 / log t := by
  have h1mε : 0 < 1 - ε := by linarith
  -- Decompose the set: Ioc 0 x \ Ioo (1-ε) (1+ε) = Ioc 0 (1-ε) ∪ Icc (1+ε) x
  have hdecomp : Ioc 0 x \ Ioo (1 - ε) (1 + ε) = Ioc 0 (1 - ε) ∪ Icc (1 + ε) x := by
    ext t; simp only [Set.mem_diff, Set.mem_Ioc, Set.mem_Ioo, Set.mem_union, Set.mem_Icc]
    constructor
    · intro ⟨⟨h0, hx'⟩, hnotin⟩
      push_neg at hnotin
      by_cases ht : t ≤ 1 - ε
      · left; exact ⟨h0, ht⟩
      · right; exact ⟨hnotin (by linarith), hx'⟩
    · intro h
      rcases h with ⟨h0, ht⟩ | ⟨ht, hx'⟩
      · exact ⟨⟨h0, by linarith⟩, fun ⟨h1, _⟩ => by linarith⟩
      · exact ⟨⟨by linarith, hx'⟩, fun ⟨_, h2⟩ => by linarith⟩
  -- Rewrite using the decomposition
  rw [hdecomp]
  -- Disjointness
  have hdisj : Disjoint (Ioc 0 (1 - ε)) (Icc (1 + ε) x) := by
    apply Set.disjoint_left.mpr
    intro t ht1 ht2; exact absurd (lt_of_le_of_lt ht1.2 (by linarith : 1 - ε < 1 + ε)) (not_lt.mpr ht2.1)
  -- Integrability
  have hint1 : IntegrableOn (fun t => (1 : ℝ) / log t) (Ioc 0 (1 - ε)) := by
    have hlog1mε : log (1 - ε) < 0 := Real.log_neg h1mε (by linarith)
    apply Measure.integrableOn_of_bounded (M := 1 / |log (1 - ε)|) (by exact measure_Ioc_lt_top.ne)
    · exact ((measurable_const.div measurable_log).aestronglyMeasurable)
    · rw [ae_restrict_iff' measurableSet_Ioc]
      apply Filter.Eventually.of_forall
      intro t ht
      rw [norm_div, norm_one, Real.norm_eq_abs, one_div, one_div]
      have hlog_neg : log t < 0 := Real.log_neg ht.1 (by linarith [ht.2])
      apply inv_anti₀ (abs_pos.mpr (ne_of_lt hlog1mε))
      rw [abs_of_neg hlog_neg, abs_of_neg hlog1mε]
      exact neg_le_neg_iff.mpr (Real.log_le_log (by linarith [ht.1]) ht.2)
  have hint2 : IntegrableOn (fun t => (1 : ℝ) / log t) (Icc (1 + ε) x) := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    apply ContinuousOn.div continuousOn_const
    · exact continuousOn_log.mono (fun t ht => ne_of_gt (by linarith [ht.1]))
    · intro t ht; exact ne_of_gt (Real.log_pos (by linarith [ht.1]))
  rw [setIntegral_union hdisj measurableSet_Icc hint1 hint2]
  congr 1
  · exact (intervalIntegral.integral_of_le h1mε.le).symm
  · rw [integral_Icc_eq_integral_Ioc]
    exact (intervalIntegral.integral_of_le (by linarith : (1 : ℝ) + ε ≤ x)).symm

/-- The PV integral of 1/log(t) from 0 to x equals the PV integral of eᵘ/u from -∞ to log(x).
    This is the key substitution connecting li(x) to the exponential integral. -/
-- Helper: IntervalIntegrable for exp u / u on intervals where u ≠ 0
private lemma intervalIntegrable_exp_div_of_pos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun u => exp u / u) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuous_exp.continuousOn continuousOn_id
  intro u hu
  have hmem := Set.mem_uIcc.mp hu
  show id u ≠ 0
  rcases hmem with ⟨h, _⟩ | ⟨h, _⟩ <;> simp [id] <;> linarith

private lemma intervalIntegrable_exp_div_of_neg {a b : ℝ} (ha : a < 0) (hb : b < 0) :
    IntervalIntegrable (fun u => exp u / u) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div continuous_exp.continuousOn continuousOn_id
  intro u hu
  have hmem := Set.mem_uIcc.mp hu
  show id u ≠ 0
  rcases hmem with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [id] <;> linarith

private theorem li_eq_pv_exp_integral {x : ℝ} (hx : 1 < x) :
    li x = lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..log x, exp u / u)) := by
  have hlogx : 0 < log x := Real.log_pos hx
  have hx0 : (0 : ℝ) < x := by linarith
  -- The limit L of the RHS
  set L := ((∫ t in (0:ℝ)..1, (1 - exp (-t)) / t) - ∫ t in Ioi (1:ℝ), exp (-t) / t) +
    (∫ u in (0:ℝ)..log x, (exp u - 1) / u) + log (log x)
  -- Step 1: Build Tendsto for the exp/u side
  have h_tendsto_exp : Tendsto
      (fun ε => (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..log x, exp u / u)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    have h_rw : Tendsto
        (fun ε => (∫ t in ε..1, (1 - exp (-t)) / t) - (∫ t in (1:ℝ)..(1/ε), exp (-t) / t) +
          (∫ u in ε..log x, (exp u - 1) / u) + log (log x))
        (𝓝[>] (0 : ℝ)) (𝓝 L) :=
      ((_root_.tendsto_integral_one_sub_exp_neg_div.sub
        _root_.tendsto_integral_exp_neg_div_Ioi).add
        (_root_.tendsto_integral_exp_sub_one_div hlogx)).add tendsto_const_nhds
    apply h_rw.congr'
    have : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min (log x) 1 := by
      apply nhdsWithin_le_nhds
      exact Iio_mem_nhds (lt_min hlogx one_pos)
    filter_upwards [this, self_mem_nhdsWithin] with ε hε hε_pos
    exact (_root_.pv_rewrite hlogx hε_pos (lt_of_lt_of_le hε (min_le_right _ _))
      (lt_of_lt_of_le hε (min_le_left _ _))).symm
  -- Step 2: Show the li side Tends to the same limit
  -- We show f_li(ε) - f_exp(ε) → 0, then f_li → L
  have h_tendsto_li : Tendsto
      (fun ε => ∫ t in (Ioc 0 x).diff (Ioo (1 - ε) (1 + ε)), (1 : ℝ) / log t)
      (𝓝[>] (0 : ℝ)) (𝓝 L) := by
    suffices hdiff : Tendsto
        (fun ε => (∫ t in (Ioc 0 x).diff (Ioo (1 - ε) (1 + ε)), (1 : ℝ) / log t) -
          ((∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..log x, exp u / u))
        (𝓝[>] (0 : ℝ)) (𝓝 0) by
      have := hdiff.add h_tendsto_exp
      simp only [zero_add] at this
      exact this.congr (fun ε => by ring)
    -- Error term 1: ∫₀^{e^{-1/ε}} 1/log t → 0 as ε → 0+
    -- Strategy: |1/log t| ≤ ε on (0, e^{-1/ε}] (since |log t| ≥ 1/ε), so
    -- |∫| ≤ ε * e^{-1/ε} and ε * e^{-1/ε} → 0 (exponential decay beats polynomial).
    -- Use norm_integral_le_of_norm_le_const + squeeze_zero'.
    have herr1 : Tendsto (fun ε => ∫ t in (0 : ℝ)..exp (-1/ε), 1 / log t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      -- Bound: ‖∫₀^{e^{-1/ε}} 1/log t‖ ≤ ε * exp(-1/ε) ≤ ε → 0
      apply squeeze_zero_norm'
      · -- ‖integral‖ ≤ ε
        filter_upwards [self_mem_nhdsWithin] with ε (hε_pos : 0 < ε)
        have hexp_lt_one : exp (-1/ε) < 1 := by
          rw [exp_lt_one_iff, neg_div]; exact neg_neg_of_pos (div_pos one_pos hε_pos)
        calc ‖∫ t in (0 : ℝ)..exp (-1/ε), 1 / log t‖
            ≤ ε * |exp (-1/ε) - 0| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro t ht
              rw [Set.uIoc_of_le (exp_pos _).le] at ht
              rw [norm_div, norm_one, Real.norm_eq_abs, one_div]
              have hlog_neg : log t < 0 :=
                Real.log_neg ht.1 (lt_of_le_of_lt ht.2 hexp_lt_one)
              have hlog_le : log t ≤ -1/ε := by
                rw [Real.log_le_iff_le_exp ht.1]; exact ht.2
              rw [abs_of_neg hlog_neg]
              have h1e : 1/ε ≤ -log t := by rw [neg_div] at hlog_le; linarith
              calc (-log t)⁻¹ ≤ (1/ε)⁻¹ := inv_anti₀ (by positivity) h1e
                _ = ε := by rw [one_div, inv_inv]
          _ = ε * exp (-1/ε) := by rw [sub_zero, abs_of_pos (exp_pos _)]
          _ ≤ ε * 1 := by
              apply mul_le_mul_of_nonneg_left _ hε_pos.le
              exact exp_le_one_iff.mpr (by rw [neg_div]
                                           exact neg_nonpos.mpr (div_nonneg one_pos.le hε_pos.le))
          _ = ε := mul_one ε
      · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    -- Error term 2: ∫_{-ε}^{log(1-ε)} exp u / u → 0 as ε → 0+
    -- Strategy: on [log(1-ε), -ε], |exp u| ≤ 1 and |u| ≥ ε, so |exp u/u| ≤ 1/ε.
    -- The interval length |log(1-ε)+ε| ≤ ε²/(1-ε) (Taylor bound for log).
    -- So |∫| ≤ (1/ε) * ε²/(1-ε) = ε/(1-ε) → 0.
    have herr2 : Tendsto (fun ε => ∫ u in (-ε)..log (1 - ε), exp u / u)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      apply squeeze_zero_norm'
      · -- ‖∫_{-ε}^{log(1-ε)} exp u / u‖ ≤ ε/(1-ε)
        have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1/2 :=
          nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
        filter_upwards [hev, self_mem_nhdsWithin] with ε hεhalf (hε_pos : 0 < ε)
        have hε1 : ε < 1 := by linarith
        have h1mε : 0 < 1 - ε := by linarith
        -- log(1-ε) < -ε for ε ∈ (0,1)
        have hlog_bound : log (1 - ε) ≤ -ε := by
          have := Real.log_le_sub_one_of_pos h1mε; linarith
        -- -log(1-ε) ≤ ε/(1-ε)
        have hneg_log_bound : -log (1 - ε) ≤ ε / (1 - ε) := by
          have h := Real.log_le_sub_one_of_pos (show 0 < (1-ε)⁻¹ from by positivity)
          rw [Real.log_inv] at h
          have heq : (1 - ε)⁻¹ - 1 = ε / (1 - ε) := by
            field_simp; ring
          linarith
        -- -ε - log(1-ε) ≤ ε²/(1-ε)
        have hlen_bound : -ε - log (1 - ε) ≤ ε ^ 2 / (1 - ε) := by
          have : -log (1 - ε) - ε ≤ ε / (1 - ε) - ε := by linarith
          calc -ε - log (1 - ε) = -log (1 - ε) - ε := by ring
            _ ≤ ε / (1 - ε) - ε := this
            _ = ε ^ 2 / (1 - ε) := by field_simp; ring
        -- On [log(1-ε), -ε], |exp u / u| ≤ 1/ε
        have hlog_neg : log (1 - ε) < 0 := Real.log_neg h1mε (by linarith)
        calc ‖∫ u in (-ε)..log (1 - ε), exp u / u‖
            ≤ (1/ε) * |log (1 - ε) - (-ε)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro u hu
              rw [Set.uIoc_comm, Set.uIoc_of_le (by linarith)] at hu
              -- u ∈ (log(1-ε), -ε], so u < 0 and |u| ≥ ε
              have hu_neg : u < 0 := by linarith [hu.2]
              have hu_le : u ≤ -ε := hu.2
              rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
              rw [abs_of_pos (exp_pos _), abs_of_neg hu_neg]
              -- exp u ≤ 1 since u < 0, and -u ≥ ε
              exact div_le_div₀ zero_le_one (exp_le_one_iff.mpr hu_neg.le) hε_pos (by linarith)
          _ ≤ (1/ε) * (-ε - log (1 - ε)) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              rw [show log (1 - ε) - -ε = -((-ε) - log (1 - ε)) from by ring, abs_neg,
                abs_of_nonneg (by linarith)]
          _ ≤ (1/ε) * (ε ^ 2 / (1 - ε)) := by
              apply mul_le_mul_of_nonneg_left hlen_bound (by positivity)
          _ = ε / (1 - ε) := by field_simp
      · -- ε/(1-ε) → 0 as ε → 0+
        have : Tendsto (fun ε : ℝ => ε / (1 - ε)) (𝓝[>] 0) (𝓝 (0 / (1 - 0))) := by
          apply Tendsto.div
          · exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
          · exact tendsto_nhdsWithin_of_tendsto_nhds (tendsto_const_nhds.sub tendsto_id)
          · simp
        simp at this; exact this
    -- Error term 3: ∫_{log(1+ε)}^ε exp u / u → 0 as ε → 0+
    -- Strategy: on [log(1+ε), ε], exp u ≤ exp ε and u ≥ log(1+ε), so
    -- |exp u/u| ≤ exp(ε)/log(1+ε). The interval length ε - log(1+ε) ≤ ε²/2.
    -- So |∫| ≤ exp(ε)/(log(1+ε)) * ε²/2 ≈ ε/2 → 0.
    have herr3 : Tendsto (fun ε => ∫ u in log (1 + ε)..ε, exp u / u)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      -- Bound: ‖∫_{log(1+ε)}^ε exp u/u‖ ≤ 2 * exp 1 * ε → 0
      apply squeeze_zero_norm'
      · have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1/2 :=
          nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
        filter_upwards [hev, self_mem_nhdsWithin] with ε hεhalf (hε_pos : 0 < ε)
        have hε1 : ε < 1 := by linarith
        have h1pε : 0 < 1 + ε := by linarith
        have hlog_pos : 0 < log (1 + ε) := Real.log_pos (by linarith)
        -- Key bound: log(1+ε) ≥ ε/(1+ε), from log_le_sub_one_of_pos applied to (1+ε)⁻¹
        have hlog_lower : ε / (1 + ε) ≤ log (1 + ε) := by
          have h := Real.log_le_sub_one_of_pos (show 0 < (1+ε)⁻¹ from by positivity)
          rw [Real.log_inv] at h
          have : (1 + ε)⁻¹ - 1 = -(ε / (1 + ε)) := by field_simp; ring
          linarith
        -- Consequence: log(1+ε) ≥ ε/2 for ε < 1
        have hlog_half : ε / 2 ≤ log (1 + ε) := by
          calc ε / 2 ≤ ε / (1 + ε) := by
                apply div_le_div_of_nonneg_left hε_pos.le (by positivity) (by linarith)
            _ ≤ log (1 + ε) := hlog_lower
        -- Interval length bound: ε - log(1+ε) ≤ ε²/(1+ε) ≤ ε²
        have hlen : ε - log (1 + ε) ≤ ε ^ 2 := by
          have : ε - log (1 + ε) ≤ ε - ε / (1 + ε) := by linarith
          calc ε - log (1 + ε) ≤ ε - ε / (1 + ε) := this
            _ = ε ^ 2 / (1 + ε) := by field_simp; ring
            _ ≤ ε ^ 2 / 1 := by
                apply div_le_div_of_nonneg_left (by positivity) one_pos (by linarith)
            _ = ε ^ 2 := div_one _
        -- log(1+ε) ≤ ε (for direction of integral)
        have hlog_upper : log (1 + ε) ≤ ε := by
          have := Real.log_le_sub_one_of_pos h1pε; linarith
        -- On [log(1+ε), ε]: exp u ≤ exp ε ≤ exp 1, u ≥ log(1+ε) > 0
        -- So |exp u / u| ≤ exp 1 / log(1+ε) ≤ exp 1 / (ε/2) = 2*exp(1)/ε
        calc ‖∫ u in log (1 + ε)..ε, exp u / u‖
            ≤ (exp 1 / log (1 + ε)) * |ε - log (1 + ε)| := by
              apply intervalIntegral.norm_integral_le_of_norm_le_const
              intro u hu
              rw [Set.uIoc_of_le hlog_upper] at hu
              rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_pos (exp_pos _), abs_of_pos (lt_of_lt_of_le hlog_pos (le_of_lt hu.1))]
              apply div_le_div₀ (exp_pos 1).le
              · exact exp_le_exp.mpr (le_of_lt (lt_of_le_of_lt hu.2 hε1))
              · exact hlog_pos
              · exact le_of_lt hu.1
          _ ≤ (exp 1 / (ε / 2)) * ε ^ 2 := by
              apply mul_le_mul
              · exact div_le_div_of_nonneg_left (exp_pos 1).le (by positivity) hlog_half
              · rw [abs_of_nonneg (by linarith)]; exact hlen
              · exact abs_nonneg _
              · positivity
          _ = 2 * exp 1 * ε := by field_simp
      · -- 2 * exp 1 * ε → 0 as ε → 0+
        have : Tendsto (fun ε : ℝ => 2 * exp 1 * ε) (𝓝[>] 0) (𝓝 (2 * exp 1 * 0)) :=
          (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).const_mul _
        simp at this; exact this
    -- Combine: the sum of the three error terms → 0
    have herr : Tendsto (fun ε =>
        ((∫ t in (0:ℝ)..exp (-1/ε), 1 / log t) + ∫ u in (-ε)..log (1 - ε), exp u / u) +
        ∫ u in log (1 + ε)..ε, exp u / u)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (herr1.add herr2).add herr3
      simp only [add_zero] at this
      exact this
    -- Show the difference is eventually equal to the sum of three error terms
    apply herr.congr'
    -- For small ε, decompose the difference
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < min (min (1/2) (x - 1)) 1 := by
      apply nhdsWithin_le_nhds
      exact Iio_mem_nhds (lt_min (lt_min (by linarith) (by linarith)) (by linarith))
    filter_upwards [hev, self_mem_nhdsWithin] with ε hε hε_mem
    have hε_pos : (0 : ℝ) < ε := hε_mem
    have hε1 : ε < 1 := lt_of_lt_of_le hε (min_le_right _ _)
    have hεhalf : ε < 1/2 := by
      calc ε < min (min (1/2) (x - 1)) 1 := hε
        _ ≤ min (1/2) (x - 1) := min_le_left _ _
        _ ≤ 1/2 := min_le_left _ _
    have hεx : 1 + ε < x := by
      have : ε < x - 1 := by
        calc ε < min (min (1/2) (x - 1)) 1 := hε
          _ ≤ min (1/2) (x - 1) := min_le_left _ _
          _ ≤ x - 1 := min_le_right _ _
      linarith
    have h1mε : 0 < 1 - ε := by linarith
    have hexp_pos : 0 < exp (-1/ε) := exp_pos _
    have hexp_lt : exp (-1/ε) < 1 - ε := by
      calc exp (-1/ε) ≤ exp (-2) := by
            apply exp_le_exp.mpr
            rw [neg_div, neg_le_neg_iff]
            rw [le_div_iff₀ hε_pos]
            linarith
          _ < 1/2 := by
            -- exp(-2) < exp(0) = 1 < 1/2 is wrong, so we need exp(-2) < 1/2
            -- Use: exp(-1) < 1/2 + 1/2 = 1 and exp(-2) = exp(-1)^2 < 1
            -- Actually, exp(-1) < 1 and exp(-1) < 0.4 (since exp(1) > 2.5)
            -- For a cleaner proof: exp(-2) ≤ 1/(1+2) = 1/3 < 1/2 (by exp(-x) ≤ 1/(1+x))
            -- In Lean, we use: exp x ≤ 1/(1-x) for x < 1, so exp(-2) ≤ ... hmm
            -- Simplest: show exp(-2) < exp(0) / 2... not simple.
            -- Just use: for x ≤ 0, exp(x) ≤ 1 + x + x^2/2 (Taylor bound)
            -- Actually easiest: 2 * exp(-2) = 2/exp(2). Since exp(2) > 1+2 = 3, 2/exp(2) < 2/3 < 1
            calc exp (-2 : ℝ) < exp (-1) := by apply exp_lt_exp.mpr; norm_num
              _ = 1 / exp 1 := by rw [exp_neg, one_div]
              _ ≤ 1 / (1 + 1) := by
                  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
                  exact add_one_le_exp 1
              _ = 1 / 2 := by norm_num
          _ < 1 - ε := by linarith
    -- Rewrite the li integral using li_setDiff_eq_split
    have hsplit := li_setDiff_eq_split hx hε_pos hε1 hεx
    -- The goal uses .diff but hsplit uses \; these are definitionally equal
    -- So we can rewrite the goal using hsplit via `conv`
    conv_rhs => rw [show (Ioc 0 x).diff (Ioo (1 - ε) (1 + ε)) = Ioc 0 x \ Ioo (1 - ε) (1 + ε) from rfl]
    rw [hsplit]
    -- Split ∫₀^{1-ε} at e^{-1/ε}
    rw [show (∫ t in (0:ℝ)..(1 - ε), 1 / log t) =
      (∫ t in (0:ℝ)..exp (-1/ε), 1 / log t) +
      ∫ t in exp (-1/ε)..(1 - ε), 1 / log t from
      (intervalIntegral.integral_add_adjacent_intervals
        (by -- 1/log t is bounded on [0, e^{-1/ε}], hence interval integrable
            rw [intervalIntegrable_iff]
            apply Measure.integrableOn_of_bounded (M := ε) (by
              rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ exp (-1/ε))]
              exact measure_Ioc_lt_top.ne)
            · exact (measurable_const.div measurable_log).aestronglyMeasurable
            · rw [Set.uIoc_of_le (by positivity : (0 : ℝ) ≤ exp (-1/ε))]
              rw [ae_restrict_iff' measurableSet_Ioc]
              apply Filter.Eventually.of_forall
              intro t ht
              rw [norm_div, norm_one, Real.norm_eq_abs, one_div]
              -- Goal: |log t|⁻¹ ≤ ε
              have hlog_neg : log t < 0 := Real.log_neg ht.1 (by
                calc t ≤ exp (-1/ε) := ht.2
                  _ < 1 := by
                    rw [exp_lt_one_iff]; rw [neg_div]; exact neg_neg_of_pos (div_pos one_pos hε_pos))
              have hlog_le : log t ≤ -1/ε := by
                rw [Real.log_le_iff_le_exp ht.1]
                exact ht.2
              rw [abs_of_neg hlog_neg]
              have h1e : 1/ε ≤ -log t := by
                have := hlog_le; rw [neg_div] at this; linarith
              calc (-log t)⁻¹ ≤ (1/ε)⁻¹ := inv_anti₀ (by positivity) h1e
                _ = ε := by rw [one_div, inv_inv])
        (by apply ContinuousOn.intervalIntegrable
            apply ContinuousOn.div continuousOn_const
            · exact continuousOn_log.mono (fun t ht => by
                rw [Set.uIcc_of_le hexp_lt.le] at ht
                exact ne_of_gt (lt_of_lt_of_le hexp_pos ht.1))
            · intro t ht
              rw [Set.uIcc_of_le hexp_lt.le] at ht
              exact ne_of_lt (Real.log_neg (lt_of_lt_of_le hexp_pos ht.1) (by linarith [ht.2])))).symm]
    -- Apply substitution: ∫_{e^{-1/ε}}^{1-ε} 1/log t = ∫_{-1/ε}^{log(1-ε)} exp u / u
    rw [integral_log_inv_eq_integral_exp_div_of_lt_one hexp_pos hexp_lt.le (by linarith)]
    rw [Real.log_exp]
    -- Apply substitution: ∫_{1+ε}^x 1/log t = ∫_{log(1+ε)}^{log x} exp u / u
    rw [integral_log_inv_eq_integral_exp_div (by linarith : 1 < 1 + ε) hεx]
    -- Split the exp/u integrals to isolate error terms
    rw [show (∫ u in (-1/ε)..log (1 - ε), exp u / u) =
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in (-ε)..log (1 - ε), exp u / u from
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_exp_div_of_neg (show -1/ε < 0 by rw [neg_div]; exact neg_lt_zero.mpr (div_pos one_pos hε_pos)) (by linarith))
        (intervalIntegrable_exp_div_of_neg (by linarith) (Real.log_neg h1mε (by linarith)))).symm]
    rw [show (∫ u in log (1 + ε)..log x, exp u / u) =
      (∫ u in log (1 + ε)..ε, exp u / u) + ∫ u in ε..log x, exp u / u from
      (intervalIntegral.integral_add_adjacent_intervals
        (intervalIntegrable_exp_div_of_pos (Real.log_pos (by linarith)) hε_pos)
        (intervalIntegrable_exp_div_of_pos hε_pos hlogx)).symm]
    ring
  -- Step 3: Conclude
  show lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      ∫ t in (Ioc 0 x).diff (Ioo (1 - ε) (1 + ε)), (1 : ℝ) / log t)) =
    lim ((𝓝[>] (0 : ℝ)).map (fun ε =>
      (∫ u in (-1/ε)..(-ε), exp u / u) + ∫ u in ε..log x, exp u / u))
  exact (lim_eq h_tendsto_li).trans (lim_eq h_tendsto_exp).symm

/-! ## Part E: Main theorem -/

/-- The series expansion for the logarithmic integral:
    `li(x) = γ + log(log x) + ∑ (log x)^n / (n * n!)` for `x > 1`. -/
theorem li_eq_eulerMascheroni_add_log_log_add_tsum {x : ℝ} (hx : 1 < x) :
    li x = eulerMascheroniConstant + log (log x) +
      ∑' n : ℕ, (log x) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) := by
  have hlogx : 0 < log x := Real.log_pos hx
  have hpv := pv_exp_div_eq_gamma_add_log_add_integral hlogx
  rw [integral_exp_sub_one_div_eq_tsum (log x)] at hpv
  rw [li_eq_pv_exp_integral hx, hpv]

end LiSeries

-- Re-export the main theorem outside the namespace
theorem li_eq_eulerMascheroni_add_log_log_add_tsum {x : ℝ} (hx : 1 < x) :
    li x = eulerMascheroniConstant + log (log x) +
      ∑' n : ℕ, (log x) ^ (n + 1) / ((↑(n + 1) : ℝ) * ↑(n + 1).factorial) :=
  LiSeries.li_eq_eulerMascheroni_add_log_log_add_tsum hx
