import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.Star
import Mathlib.Data.PNat.Interval
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.SimpleRing.Principal
import PrimeNumberTheoremAnd.PrimaryDefinitions
import PrimeNumberTheoremAnd.Wiener

open Real

blueprint_comment /--
\section{Chirre-Helfgott's estimates for sums of nonnegative arithmetic functions}\label{ch2-sec}

We record some estimates from \cite{ch2} for summing non-negative functions, with a particular interest in estimating $\psi$.
-/


namespace CH2

blueprint_comment /--
\subsection{Fourier-analytic considerations}\label{ch2-fourier-sec}

Some material from \cite[Section 2]{ch2}, slightly rearranged to take advantage of existing results in the repository.
-/

open Real MeasureTheory FourierTransform Chebyshev Asymptotics
open ArithmeticFunction hiding log
open Complex hiding log

lemma summable_nterm_of_log_weight {a : ℕ → ℂ} {β sig : ℝ}
    (hsig : 1 < sig) (ha : Summable (fun n : ℕ ↦ ‖a n‖ / (n * Real.log n ^ β))) :
    Summable (nterm a sig) := by
  have hs : 0 < sig - 1 := sub_pos.mpr hsig
  have hlo : (fun x : ℝ => Real.log x ^ β) =o[Filter.atTop] fun x => x ^ (sig - 1) :=
    isLittleO_log_rpow_rpow_atTop β hs
  have hlo_nat :
      (fun n : ℕ => Real.log (n : ℝ) ^ β) =o[Filter.atTop] fun n => (n : ℝ) ^ (sig - 1) :=
    hlo.comp_tendsto tendsto_natCast_atTop_atTop
  have hlog_le : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Real.log (n : ℝ) ^ β‖ ≤ ‖(n : ℝ) ^ (sig - 1)‖ := by
    simpa using hlo_nat.bound (show (0 : ℝ) < 1 by norm_num)
  have h_event : ∀ᶠ n : ℕ in Filter.atTop,
      ‖(if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig)‖ ≤ ‖a n‖ / ((n : ℝ) * Real.log n ^ β) := by
    filter_upwards [hlog_le, Filter.eventually_ge_atTop (2 : ℕ)] with n hlog hn
    have hnpos : 0 < (n : ℝ) := by positivity
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
    have hpowpos : 0 < Real.log (n : ℝ) ^ β := Real.rpow_pos_of_pos hlogpos _
    have hlog_le' : Real.log (n : ℝ) ^ β ≤ (n : ℝ) ^ (sig - 1) := by
      rwa [Real.norm_of_nonneg hpowpos.le, Real.norm_of_nonneg (Real.rpow_nonneg hnpos.le _)] at hlog
    have hpow_split : (n : ℝ) ^ sig = (n : ℝ) * (n : ℝ) ^ (sig - 1) := by
      conv_lhs => rw [show sig = 1 + (sig - 1) by ring]; rw [Real.rpow_add hnpos, Real.rpow_one]
    rw [show (if n = 0 then 0 else ‖a n‖ / (n : ℝ) ^ sig) = ‖a n‖ / (n : ℝ) ^ sig from
        by simp [show n ≠ 0 by omega], Real.norm_of_nonneg (div_nonneg (norm_nonneg _)
        (Real.rpow_nonneg hnpos.le _)), hpow_split]
    exact div_le_div_of_nonneg_left (norm_nonneg (a n)) (mul_pos hnpos hpowpos)
      (mul_le_mul_of_nonneg_left hlog_le' hnpos.le)
  have hbase : Summable (fun n : ℕ ↦ if n = 0 then 0 else ‖a n‖ / n ^ sig) :=
    Summable.of_norm_bounded_eventually_nat ha h_event
  simpa [nterm] using hbase

lemma fourier_scale_div_noscalar (φ : ℝ → ℂ) (T u : ℝ) (hT : 0 < T) :
    𝓕 (fun t : ℝ ↦ φ (t / T)) u = (T : ℂ) * 𝓕 φ (T * u) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have hcomp : (fun v : ℝ ↦ 𝐞 (-(v * u)) • φ (v / T)) =
      fun v : ℝ ↦ (fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) (v / T) := by
    ext v; congr 2; simp [show (v / T) * (T * u) = v * u from by field_simp [hT.ne']]
  rw [hcomp]
  simpa [abs_of_pos hT, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
    Measure.integral_comp_div (g := fun z : ℝ ↦ 𝐞 (-(z * (T * u))) • φ z) T

@[blueprint
  "ch2-prop-2-3-1"
  (title := "CH2 Proposition 2.3, substep 1")
  (statement := /--
  Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Write $G(s)= \sum_n a_n n^{-s} - \frac{1}{s-1}$ for $\mathrm{Re} s > 1$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \psi(y) = O(1/|y|^\beta)$.  Then for any $x>0$ and $\sigma > 1$
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n^\sigma} \hat \psi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi T} \int_{-T}^{T} \varphi(\frac{t}{T}) G(\sigma+it) x^{it}\ dt + \int_{-T \log x/2\pi}^\infty e^{-y(\sigma-1)} \hat \varphi(y)\ dy) \frac{x^{2-\sigma}}{T}.$$
  -/)
  (proof := /-- Use Lemma \ref{first-fourier} and Lemma \ref{second-fourier}, similar to the proof of `limiting\_fourier\_aux`.
  -/)
  (latexEnv := "sublemma")
  (discussion := 879)]
theorem prop_2_3_1 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (_hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ}
    (hG' : Set.EqOn G (fun s ↦ LSeries a s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0) -- this hypothesis may be unnecessary
    (_hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x sig : ℝ) (hx : 0 < x) (hsig : 1 < sig) :
    (1 / (2 * π)) * ∑' (n : ℕ), (x : ℂ) * LSeries.term a sig n *
      𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I)) +
      (x ^ (2 - sig) / (2 * π * T) : ℝ) *
        (∫ u in Set.Ici (-log x), Real.exp (-u * (sig - 1)) *
          𝓕 (fun t : ℝ ↦ φ (t / T)) (u / (2 * π))) := by
  let phiScaled : ℝ → ℂ := fun t => φ (t / T)
  have hphiScaled_meas : Measurable phiScaled := by simp only [phiScaled]; fun_prop
  have hphiScaled_int : Integrable phiScaled :=
    (MeasureTheory.integrable_comp_mul_right_iff (g := φ) (inv_ne_zero hT.ne')).2 hφ_int |>.congr
      (by simp [phiScaled, div_eq_mul_inv])
  have hsummable : ∀ (σ' : ℝ), 1 < σ' → Summable (nterm a σ') :=
    fun σ' hσ' => summable_nterm_of_log_weight hσ' ha
  have hfirst := @first_fourier x sig phiScaled a hsummable hphiScaled_int hx hsig
  have hsecond := @second_fourier phiScaled hphiScaled_meas hphiScaled_int x sig hx hsig
  have hxpow (t : ℝ) : ‖(x : ℂ) ^ (t * I)‖ = 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]; simp
  let C0 : ℝ := ∑' n : ℕ, nterm a sig n
  have hC0_nonneg : 0 ≤ C0 := tsum_nonneg fun n => by
    by_cases hn : n = 0 <;> simp [nterm, hn, div_nonneg, Real.rpow_nonneg]
  have hLS_bound (t : ℝ) : ‖LSeries a (sig + t * I)‖ ≤ C0 := by
    have hs_term : Summable (fun n : ℕ => ‖LSeries.term a (sig + t * I) n‖) := by
      convert hsummable sig hsig with n; simp [norm_term_eq_nterm_re]
    exact (norm_tsum_le_tsum_norm hs_term).trans (by simp [C0, norm_term_eq_nterm_re])
  have hLS_aesm : AEStronglyMeasurable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    (((continuous_LSeries_aux (hsummable sig hsig)).measurable.mul hphiScaled_meas).mul
      (continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])).measurable).aestronglyMeasurable
  have hLS_int : Integrable (fun t : ℝ ↦ LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul C0) hLS_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hLS_bound t) (norm_nonneg _))
  have hPole_denom_ne (t : ℝ) : sig + t * I - 1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hPole_bound (t : ℝ) : ‖1 / (sig + t * I - 1)‖ ≤ (sig - 1)⁻¹ := by
    have hσpos : 0 < sig - 1 := sub_pos.mpr hsig
    simpa [norm_div, one_div] using one_div_le_one_div_of_le hσpos
      (by simpa [abs_of_pos hσpos] using Complex.abs_re_le_norm (sig + t * I - 1))
  have hcontX : Continuous (fun t : ℝ => (x : ℂ) ^ (t * I)) :=
    continuous_const.cpow (continuous_ofReal.mul continuous_const) (by simp [hx])
  have hPole_aesm :
      AEStronglyMeasurable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    (((by simpa [one_div] using Continuous.inv₀ (by fun_prop) (hPole_denom_ne) :
      Continuous (fun t : ℝ => (1 / (sig + t * I - 1) : ℂ))).measurable.mul hphiScaled_meas).mul
        hcontX.measurable).aestronglyMeasurable
  have hPole_int : Integrable (fun t : ℝ ↦ (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) :=
    .mono' (hphiScaled_int.norm.const_mul (sig - 1)⁻¹) hPole_aesm (.of_forall fun t => by
      simp only [norm_mul, mul_assoc, hxpow, mul_one]
      exact mul_le_mul_of_nonneg_right (hPole_bound t) (norm_nonneg _))
  have hG_rewrite :
      ∫ t : ℝ, phiScaled t * G (sig + t * I) * x ^ (t * I) =
        (∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    rw [← integral_sub hLS_int hPole_int]; congr 1; ext t
    rw [hG' (by simp [hsig] : (sig + t * I).re > 1)]; ring
  have hIcc_to_univ :
      ∫ t in Set.Icc (-T) T, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) := by
    rw [← integral_indicator measurableSet_Icc]
    refine integral_congr_ae (.of_forall fun t => ?_)
    by_cases ht : t ∈ Set.Icc (-T) T
    · simp [ht]
    · simp [ht, hφ_supp _ (show t / T ∉ Set.Icc (-1) 1 from by
        intro ⟨h1, h2⟩; exact ht ⟨by linarith [(le_div_iff₀ hT).mp h1],
          by linarith [(div_le_iff₀ hT).mp h2]⟩)]
  have hG_with_x :
      (1 / (2 * π * T)) *
          ∫ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + t * I) =
        (x / (2 * π * T) : ℂ) *
          ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
            ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) := by
    have hcpow (t : ℝ) : (x : ℂ) ^ (1 + ↑t * I) = x * x ^ (↑t * I) := by
      rw [Complex.cpow_add (x := (x : ℂ)) (y := (1 : ℂ)) (z := t * I)
        (by exact_mod_cast hx.ne')]; simp
    simp_rw [show ∀ t : ℝ, φ (t / T) * G (sig + t * I) * x ^ (1 + ↑t * I) =
        (x : ℂ) * (phiScaled t * G (sig + t * I) * x ^ (↑t * I)) from
      fun t => by rw [hcpow]; simp only [phiScaled]; ring, integral_const_mul, hG_rewrite]; ring
  have hPole_from_second :
      (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
          Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π)) =
        (x / (2 * π * T) : ℂ) *
          ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
    have hpowx : (x ^ (2 - sig) * x ^ (sig - 1) : ℝ) = x := by
      rw [← Real.rpow_add hx]; norm_num
    calc (x ^ (2 - sig) / (2 * π * T) : ℝ) * ∫ u in Set.Ici (-log x),
            Real.exp (-u * (sig - 1)) * 𝓕 phiScaled (u / (2 * π))
        _ = ((x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) : ℂ) *
              ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) := by
            rw [hsecond]; push_cast; ring
        _ = _ := by rw [show (x ^ (2 - sig) / (2 * π * T) * x ^ (sig - 1) : ℝ) = x / (2 * π * T)
              from by rw [div_mul_eq_mul_div, hpowx]]; simp
  have hleft_scale :
      (1 / (2 * π)) * ∑' n : ℕ, (x : ℂ) * LSeries.term a sig n * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
        (x / (2 * π * T) : ℂ) *
          ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) := by
    have hS : ∑' n : ℕ, LSeries.term a sig n * 𝓕 phiScaled ((1 / (2 * π)) * log (n / x)) =
        (T : ℂ) * ∑' n : ℕ, LSeries.term a sig n * 𝓕 φ (T * ((1 / (2 * π)) * log (n / x))) := by
      rw [← tsum_mul_left]; congr with n
      simpa [phiScaled, mul_assoc, mul_left_comm, mul_comm] using
        congrArg (fun z : ℂ => LSeries.term a sig n * z)
          (fourier_scale_div_noscalar φ T ((1 / (2 * π)) * log (↑n / x)) hT)
    simp_rw [hS, ← tsum_mul_left]; field_simp [hT.ne']
  rw [hleft_scale, hfirst]
  rw [show (x / (2 * π * T) : ℂ) * ∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I) =
      (x / (2 * π * T) : ℂ) * ((∫ t : ℝ, LSeries a (sig + t * I) * phiScaled t * x ^ (t * I)) -
        ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I)) +
      (x / (2 * π * T) : ℂ) * ∫ t : ℝ, (1 / (sig + t * I - 1)) * phiScaled t * x ^ (t * I) from
    by rw [mul_sub, sub_add_cancel]]
  rw [← hG_with_x, ← hIcc_to_univ, ← hPole_from_second]

@[blueprint
  "ch2-prop-2-3"
  (title := "CH2 Proposition 2.3")
  (statement := /--
  Let $a_n$ be a sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi(y) = O(1/|y|^\beta)$.  Then for any $x>0$,
  $$ \frac{1}{2\pi} \sum a_n \frac{x}{n} \hat \varphi(\frac{T}{2\pi} \log \frac{n}{x} ) = \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi(y)\ dy) \frac{x}{T}.$$
  -/)
  (proof := /-- Apply Sublemma \ref{ch2-prop-2-3-1} and take the limit as $\sigma \to 1^+$, using the continuity of $G$ and the dominated convergence theorem, as well as the Fourier inversion formula.
  -/)
  (latexEnv := "proposition")
  (discussion := 880)]
theorem prop_2_3 {a : ℕ → ℂ} {T β : ℝ} (hT : 0 < T) (hβ : 1 < β)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / n ^ s - 1 / (s - 1)) { z | z.re > 1 })
    {φ : ℝ → ℂ} (hφ_mes : Measurable φ) (hφ_int : Integrable φ)
    (hφ_cont : ContinuousAt φ 0)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        (∫ t in Set.Icc (-T) T, φ (t/T) * G (1 + t * I) * x ^ (1 + t * I)) +
      (φ 0 - ∫ y in Set.Iic (-T * log x / (2 * π)), 𝓕 φ y) * (x / T) := by
  sorry

@[blueprint
  "ch2-S-def"
  (title := "CH2 Definition of $S$, (2.8)")
  (statement := /--
  $S_\sigma(x)$ is equal to $\sum_{n \leq x} a_n / n^\sigma$ if $\sigma < 1$ and $\sum_{n \geq x} a_n / n^\sigma$ if $\sigma > 1$.
  -/)]
noncomputable def S (a : ℕ → ℝ) (σ x : ℝ) : ℝ :=
  if σ < 1 then ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ σ : ℝ)
  else ∑' (n:ℕ), if n ≥ x then a n / (n ^ σ : ℝ) else 0

@[blueprint
  "ch2-I-def"
  (title := "CH2 Definition of $I$, (2.9)")
  (statement := /--
  $I_\lambda(u) = 1_{[0,\infty)}(\mathrm{sgn}(\lambda)u) e^{-\lambda u}$.
  -/)]
noncomputable def I' (lambda u : ℝ) : ℝ := -- use I' instead of I to avoid clash with Complex.I
  if 0 ≤ lambda * u then exp (-lambda * u) else 0

@[blueprint
  "ch2-2-10"
  (title := "CH2 Equation (2.10)")
  (statement := /--
  $S_\sigma(x) = x^{-\sigma} \sum_n a_n \frac{x}{n} I_\lambda( \frac{T}{2\pi} \log \frac{n}{x} )$
  where $\lambda = 2\pi(\sigma-1)/T$.
  -/)
  (proof := /-- Routine manipulation. -/)
  (latexEnv := "sublemma")
  (discussion := 881)]
theorem S_eq_I (a : ℕ → ℝ) (s x T : ℝ) (hs : s ≠ 1) (hT : 0 < T) (hx : 0 < x) :
    let lambda := (2 * π * (s - 1)) / T
    S a s x = (x ^ (-s) : ℝ) * ∑' (n : ℕ+), a n * (x / n) * I' lambda ((T / (2 * π)) * log (n / x)) := by
  have lambda_mul_u {s T : ℝ} (hT : 0 < T) (u : ℝ) :
      2 * π * (s - 1) / T * (T / (2 * π) * u) = (s - 1) * u := by field_simp [pi_ne_zero]
  by_cases hs_lt : s < 1
  · have hS_def : S a s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n / (n ^ s : ℝ) := if_pos hs_lt
    have h_tsum_eq : x ^ (-s : ℝ) * ∑' n : ℕ+,
        a n * (x / n) * I' (2 * π * (s - 1) / T) ((T / (2 * π)) * log (n / x)) =
        x ^ (-s : ℝ) * ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, a n * (x / n) * (x / n) ^ (s - 1) := by
      have h_cond : x ^ (-s : ℝ) * ∑' n : ℕ+, a n * (x / n) * I' (2 * π * (s - 1) / T)
            ((T / (2 * π)) * log (n / x)) =
          x ^ (-s : ℝ) * ∑' n : ℕ+, if n ≤ ⌊x⌋₊ then a n * (x / n) * (x / n) ^ (s - 1) else 0 := by
        congr 1; congr 1 with n; unfold I'
        have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr n.pos
        simp only [lambda_mul_u hT]
        split_ifs with h1 h2 h3
        · congr 1; rw [rpow_def_of_pos (div_pos hx hn_pos),
            show log (x / n) = log x - log n from log_div hx.ne' hn_pos.ne']
          congr 1; rw [show log (n / x) = log n - log x from
            log_div hn_pos.ne' hx.ne']
          field_simp [hT.ne']; ring
        · exact absurd h1 (not_le.mpr (mul_neg_of_neg_of_pos (sub_neg_of_lt hs_lt)
            (log_pos (by rw [lt_div_iff₀ hx]; linarith [Nat.lt_of_floor_lt (not_le.mp h2)]))))
        · exact absurd h1 (not_not.mpr (mul_nonneg_of_nonpos_of_nonpos (sub_neg_of_lt hs_lt).le
            (log_nonpos (div_pos hn_pos hx).le
              ((div_le_one hx).mpr (le_trans (Nat.cast_le.mpr h3) (Nat.floor_le hx.le))))))
        · simp
      rw [h_cond, tsum_eq_sum (s := Finset.Icc 1 ⟨⌊x⌋₊ + 1, Nat.succ_pos _⟩)]
      · congr 1; rw [← Finset.sum_filter]; field_simp
        refine Finset.sum_bij (fun n _ ↦ n) ?_ ?_ ?_ ?_
        · simp only [Finset.mem_filter, Finset.mem_Icc, PNat.one_le, true_and, and_imp]
          exact fun n hn₁ hn₂ ↦ ⟨PNat.one_le _, hn₂⟩
        · exact fun _ _ _ _ h ↦ Subtype.val_injective h
        · simp only [Finset.mem_Icc, Finset.mem_filter, PNat.one_le, true_and,
            exists_prop, and_imp]
          exact fun b hb₁ hb₂ ↦ ⟨⟨b, hb₁⟩, ⟨Nat.le_succ_of_le hb₂, hb₂⟩, rfl⟩
        · simp only [Finset.mem_filter, Finset.mem_Icc, PNat.one_le, true_and,
            mul_assoc, mul_comm, implies_true]
      · simp +zetaDelta only [Finset.mem_Icc, PNat.one_le, true_and, not_le, ite_eq_right_iff,
          mul_eq_zero, div_eq_zero_iff, Nat.cast_eq_zero, PNat.ne_zero, or_false] at *
        exact fun n hn₁ hn₂ ↦ absurd (Nat.le_succ_of_le hn₂) (not_le_of_gt hn₁)
    simp_all only [ne_eq, div_eq_mul_inv, rpow_neg hx.le, mul_left_comm, mul_comm,
      mul_inv_rev, mul_assoc, Finset.mul_sum ..]
    refine Finset.sum_congr rfl fun n hn ↦ ?_
    have hn_pos : (0 : ℝ) < n := by norm_cast; linarith [Finset.mem_Icc.mp hn]
    rw [mul_rpow (by positivity) (by positivity), inv_rpow (by positivity)]
    ring_nf
    rw [rpow_add hx, rpow_neg_one, rpow_add hn_pos, rpow_neg_one]
    field_simp
  · have hs_def : S a s x = ∑' n : ℕ, if n ≥ x then a n / (n ^ s : ℝ) else 0 := by simp_all [S]
    have hs_ge : ∑' n : ℕ, (if n ≥ x then a n / (n ^ s : ℝ) else 0) =
        ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) :=
      (Subtype.val_injective.tsum_eq fun n hn ↦
        ⟨⟨n, Nat.pos_of_ne_zero fun h ↦ by simp_all [Function.mem_support]⟩, rfl⟩).symm
    have hs_factor : ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n / (n ^ s : ℝ) else 0) =
        x ^ (-s) * ∑' n : ℕ+, (if (n : ℝ) ≥ x then a n * (x / (n : ℝ)) * (x / (n : ℝ)) ^ (s - 1) else 0) := by
      rw [← tsum_mul_left]; congr; ext n
      split_ifs with h
      · have hn : (0 : ℝ) < n := by positivity
        rw [div_eq_mul_inv, div_rpow hx.le hn.le, rpow_sub_one hx.ne', rpow_sub_one hn.ne', rpow_neg hx.le]
        field_simp
      · simp
    convert hs_factor using 3
    · rw [hs_def, hs_ge]
    · ext n; simp only [I', lambda_mul_u hT]
      split_ifs <;> simp_all only [ne_eq, not_lt, ge_iff_le, Nat.cast_pos, PNat.pos,
        rpow_def_of_pos, div_pos_iff_of_pos_left, not_le, mul_zero, mul_eq_mul_left_iff]
      · exact Or.inl (by rw [show (n : ℝ) / x = (x / n)⁻¹ from (inv_div x n).symm, Real.log_inv]; field_simp)
      · linarith [mul_neg_of_pos_of_neg (sub_pos.mpr <| lt_of_le_of_ne hs_lt (Ne.symm ‹_›))
          (log_neg (by positivity : (0 : ℝ) < n / x) <| by rw [div_lt_one hx]; linarith)]
      · linarith [mul_nonneg (sub_nonneg.mpr hs_lt)
          (log_nonneg (by rw [le_div_iff₀ hx]; linarith : (1:ℝ) ≤ n / x))]

@[blueprint
  "ch2-prop-2-4-plus"
  (title := "CH2 Proposition 2.4, upper bound")
  (statement := /--
  Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_+$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_+(y) = O(1/|y|^\beta)$.  Let $\sigma \neq 1$ and write $\lambda = 2\pi(\sigma-1)/T$.  Assume $I_\lambda(y) \leq \hat \varphi_+(y)$ for all $y$. Then for any $x\geq 1$,
  $$ S_\sigma(x) \leq \frac{2\pi x^{1-\sigma}}{T} \varphi_+(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_+(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$
  -/)
  (proof := /-- By the nonnegativity of $a_n$ we have
  $$ S_\sigma(x) \leq x^{-\sigma} \sum_n a_n \frac{x}{n} \hat \varphi_+(\frac{T}{2\pi} \log \frac{n}{x} ).$$
  By Proposition \ref{ch2-prop-2-3} we can express the right-hand side as
  $$ \frac{1}{2\pi i T} \int_{1-iT}^{1+iT} \varphi_+(\frac{s-1}{iT}) G(s) x^{s}\ ds + (\varphi_+(0) - \int_{-\infty}^{-T \log x/2\pi} \hat \varphi_+(y)\ dy) \frac{x}{T}.$$
  If $\lambda > 0$, then $I_\lambda(y)=0$ for negative $y$, so
  $$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq 0.$$
  If $\lambda < 0$, then $I_\lambda(y)=e^{-\lambda y}$ for $y$ negative, so
$$ -\int_{-\infty}^{-T \log x/2π} I_\lambda(y)\ dy \leq e^{\lambda T \log x/2π}/(-\lambda) = x^{\sigma-1}/(-\lambda).$$
hence
$$ -\int_{-\infty}^{-T \log x/2π} \hat \varphi_+(y)\ dy \leq - x^{\sigma-1}/(-\lambda).$$
Since $x^{-\sigma} * (2\pi x / T) * x^{\sigma-1}/(-\lambda) = 1/(1-\sigma)$, the result follows.
  -/)
  (latexEnv := "proposition")
  (discussion := 882)]
theorem prop_2_4_plus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' n, a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_plus : ℝ → ℂ} (hφ_mes : Measurable φ_plus) (hφ_int : Integrable φ_plus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_plus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_plus y‖ ≤ C / |y| ^ β)
    (hI_le_Fourier : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      I' lambda y ≤ ‖𝓕 φ_plus y‖)
    {x : ℝ} (hx : 1 ≤ x) :
    S a σ x ≤
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_plus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_plus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry

@[blueprint
  "ch2-prop-2-4-minus"
  (title := "CH2 Proposition 2.4, lower bound")
  (statement := /--
  Let $a_n$ be a non-negative sequence with $\sum_{n>1} \frac{|a_n|}{n \log^\beta n} < \infty$ for some $\beta > 1$.  Assume that $\sum_n a_n n^{-s} - \frac{1}{s-1}$ extends continuously to a function $G$ defined on $1 + i[-T,T]$.  Let $\varphi_-$ be absolutely integrable, supported on $[-1,1]$, and has Fourier decay $\hat \varphi_-(y) = O(1/|y|^\beta)$.  Let $\sigma \neq 1$ and write $\lambda = 2\pi(\sigma-1)/T$.  Assume $\hat \varphi_-(y) \leq I_\lambda(y)$ for all $y$. Then for any $x\geq 1$ and $\sigma \neq 1$,
  $$ S_\sigma(x) \geq \frac{2\pi x^{1-\sigma}}{T} \varphi_-(0) + \frac{x^{-\sigma}}{T} \int_{-T}^T \varphi_-(t/T) G(1+it) x^{1+it}\ dt - \frac{1_{(-\infty,1)}(\sigma)}{1-\sigma}.$$
  -/)
  (proof := /-- Similar to the proof of Proposition \ref{ch2-prop-2-4-plus}; see \cite[Proposition 2.4]{ch2} for details.
  -/)
  (latexEnv := "proposition")
  (discussion := 883)]
theorem prop_2_4_minus {a : ℕ → ℝ} (ha_pos : ∀ n, a n ≥ 0) {T β σ : ℝ} (hT : 0 < T) (hβ : 1 < β) (hσ : σ ≠ 1)
    (ha : Summable (fun n ↦ ‖a n‖ / (n * log n ^ β)))
    {G : ℂ → ℂ} (hG : ContinuousOn G { z | z.re ≥ 1 ∧ z.im ∈ Set.Icc (-T) T })
    (hG' : Set.EqOn G (fun s ↦ ∑' (n : ℕ+), a n / (n ^ s : ℂ) - 1 / (s - 1)) { z | z.re > 1 })
    {φ_minus : ℝ → ℂ} (hφ_mes : Measurable φ_minus) (hφ_int : Integrable φ_minus)
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ_minus x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ_minus y‖ ≤ C / |y| ^ β)
    (hFourier_le_I : ∀ y : ℝ,
      let lambda := (2 * π * (σ - 1)) / T
      ‖𝓕 φ_minus y‖ ≤ I' lambda y)
    {x : ℝ} (hx : 1 ≤ x) :
    S a σ x ≥
      ((2 * π * (x ^ (1 - σ) : ℝ) / T) * φ_minus 0).re +
      (x ^ (-σ) : ℝ) / T *
        (∫ t in Set.Icc (-T) T, φ_minus (t/T) * G (1 + t * I) * (x ^ (1 + t * I))).re -
      if σ < 1 then 1 / (1 - σ) else 0 := by
  sorry


blueprint_comment /--
\subsection{Extremal approximants to the truncated exponential}\label{ch2-trunc-sec}

In this section we construct extremal approximants to the truncated exponential function and establish their basic properties, following \cite[Section 4]{ch2}, although we skip the proof of their extremality.  As such, the material here is organized rather differently from that in the paper.
-/

noncomputable def coth (z : ℂ) : ℂ := 1 / tanh z

@[blueprint
  "Phi-circ-def"
  (title := "Definition of $\\Phi^{\\pm,\\circ}_\\nu$")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z) := \frac{1}{2} (\coth\frac{w}{2} \pm 1)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_circ (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (1 / 2) * (coth (w / 2) + ε)

@[blueprint
  "Phi-circ-mero"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ meromorphic")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.meromorphic (ν ε : ℝ) : Meromorphic (Phi_circ ν ε) := by
  intro z
  have hw : AnalyticAt ℂ (fun z => (-2 * π * I * z + ν) / 2) z := by fun_prop
  apply MeromorphicAt.fun_mul (MeromorphicAt.const ..)
  apply MeromorphicAt.fun_add _ (MeromorphicAt.const ..)
  apply MeromorphicAt.fun_div (MeromorphicAt.const ..)
  apply (analyticAt_sinh.comp hw).meromorphicAt.fun_div
  apply AnalyticAt.meromorphicAt
  fun_prop

@[to_fun] theorem meromorphicOrderAt_div {𝕜 : Type*} [NontriviallyNormedField 𝕜] {x : 𝕜}
    {f g : 𝕜 → 𝕜} (hf : MeromorphicAt f x) (hg : MeromorphicAt g x) :
    meromorphicOrderAt (f / g) x = meromorphicOrderAt f x - meromorphicOrderAt g x := by
  rw [div_eq_mul_inv, meromorphicOrderAt_mul hf hg.inv, meromorphicOrderAt_inv, sub_eq_add_neg]

lemma sinh_zero_iff (ζ : ℂ) : sinh ζ = 0 ↔ (∃ k : ℤ, ζ = k * π * I) := by
  rw [← mul_left_inj' I_ne_zero, ← Complex.sin_mul_I, zero_mul, Complex.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩; use -k; apply (mul_left_inj' I_ne_zero).mp; rw [hk]; ring_nf; simp; ring
  · rintro ⟨k, hk⟩; use -k; rw [hk]; ring_nf; simp; ring

@[blueprint
  "Phi-circ-poles"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1069)]
theorem Phi_circ.poles (ν ε : ℝ) (_hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z < 0 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by
  let w : ℂ → ℂ := fun z ↦ -2 * π * I * z + ν
  have h_ord_eq : meromorphicOrderAt (Phi_circ ν ε) z < 0 ↔ meromorphicOrderAt (fun z ↦ coth (w z / 2)) z < 0 := by
    rw [show Phi_circ ν ε = (fun _ ↦ (1 / 2 : ℂ)) * (fun z ↦ coth (w z / 2) + ε) from rfl]
    rw [meromorphicOrderAt_mul_of_ne_zero (analyticAt_const (v := (1/2 : ℂ)) (x := z)) (by norm_num : (1/2 : ℂ) ≠ 0)]
    have h_coth_mero : MeromorphicAt (fun z ↦ coth (w z / 2)) z := by
      unfold coth Complex.tanh
      have h_an : AnalyticAt ℂ (fun z ↦ w z / 2) z := by fun_prop
      exact (MeromorphicAt.const 1 z).fun_div ((analyticAt_sinh.comp h_an).meromorphicAt.fun_div (analyticAt_cosh.comp h_an).meromorphicAt)
    constructor
    · intro h
      contrapose! h
      have h_sum := meromorphicOrderAt_add h_coth_mero (MeromorphicAt.const (ε : ℂ) z)
      rw [meromorphicOrderAt_const] at h_sum
      split_ifs at h_sum with h_eps
      · simp_all [gt_iff_lt, add_zero, le_top, inf_of_le_left]
      · exact (le_min (by simpa using h) le_rfl).trans h_sum
    · intro h
      have h_ne : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z ≠ meromorphicOrderAt (fun _ ↦ (ε : ℂ)) z := by
        rw [meromorphicOrderAt_const]; split_ifs <;> simp [h.ne_top, h.ne]
      rw [show (fun z ↦ coth (w z / 2) + ε) = (fun z ↦ coth (w z / 2)) + (fun _ ↦ (ε : ℂ)) from rfl]
      rw [meromorphicOrderAt_add_of_ne h_coth_mero (MeromorphicAt.const (ε : ℂ) z) h_ne]
      simp [h]
  have h_mero_tanh : MeromorphicAt Complex.tanh (w z / 2) := by
    rw [show Complex.tanh = fun x => Complex.sinh x / Complex.cosh x from
      funext Complex.tanh_eq_sinh_div_cosh]
    exact Complex.analyticAt_sinh.meromorphicAt.fun_div Complex.analyticAt_cosh.meromorphicAt
  have h_cosh_eventually_ne : ∀ᶠ (x : ℂ) in nhdsWithin (w z / 2) {w z / 2}ᶜ, Complex.cosh x ≠ 0 := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero Complex.analyticAt_cosh.meromorphicAt).mp
    intro h_top
    have h_zero_nhds : ∀ᶠ x in nhds (w z / 2), Complex.cosh x = 0 := by
      have h_p : ∀ᶠ x in nhdsWithin (w z / 2) {w z / 2}ᶜ, Complex.cosh x = 0 :=
        meromorphicOrderAt_eq_top_iff.mp h_top
      have h_eval : Complex.cosh (w z / 2) = 0 := tendsto_nhds_unique
        (Complex.continuous_cosh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
        (Filter.EventuallyEq.tendsto h_p)
      rw [eventually_nhdsWithin_iff] at h_p
      filter_upwards [h_p] with x hx
      obtain rfl | hne := eq_or_ne x (w z / 2)
      · exact h_eval
      · exact hx hne
    have h_eq : (fun x => Complex.cosh x) =ᶠ[nhds (w z / 2)] (fun x => 0) := h_zero_nhds
    have h_cosh_c : Complex.cosh (w z / 2) = 0 := h_eq.eq_of_nhds
    have h_deriv_eq : Complex.sinh (w z / 2) = 0 := by
      simpa [deriv_const, (Complex.hasDerivAt_cosh (w z / 2)).deriv] using h_eq.deriv_eq
    have key := Complex.cosh_sq_sub_sinh_sq (w z / 2)
    simp [h_cosh_c, h_deriv_eq] at key
  have hne_top_tanh : meromorphicOrderAt Complex.tanh (w z / 2) ≠ ⊤ := by
    apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero h_mero_tanh).mpr
    have h_tanh_eq : ∀ x : ℂ, Complex.tanh x = 0 ↔ Complex.sinh x = 0 ∨ Complex.cosh x = 0 := by
      intro x
      rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff]
    have h_sinh_eventually_ne : ∀ᶠ (x : ℂ) in nhdsWithin (w z / 2) {w z / 2}ᶜ, Complex.sinh x ≠ 0 := by
      apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero Complex.analyticAt_sinh.meromorphicAt).mp
      intro h_top
      have h_zero_nhds : ∀ᶠ x in nhds (w z / 2), Complex.sinh x = 0 := by
        have h_p : ∀ᶠ x in nhdsWithin (w z / 2) {w z / 2}ᶜ, Complex.sinh x = 0 :=
          meromorphicOrderAt_eq_top_iff.mp h_top
        have h_eval : Complex.sinh (w z / 2) = 0 := tendsto_nhds_unique
          (Complex.continuous_sinh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
          (Filter.EventuallyEq.tendsto h_p)
        rw [eventually_nhdsWithin_iff] at h_p
        filter_upwards [h_p] with x hx
        obtain rfl | hne := eq_or_ne x (w z / 2)
        · exact h_eval
        · exact hx hne
      have h_eq : (fun x => Complex.sinh x) =ᶠ[nhds (w z / 2)] (fun x => 0) := h_zero_nhds
      have h_sinh_c : Complex.sinh (w z / 2) = 0 := h_eq.eq_of_nhds
      have h_deriv_eq : Complex.cosh (w z / 2) = 0 := by
        simpa [deriv_const, (Complex.hasDerivAt_sinh (w z / 2)).deriv] using h_eq.deriv_eq
      have key := Complex.cosh_sq_sub_sinh_sq (w z / 2)
      simp [h_sinh_c, h_deriv_eq] at key
    filter_upwards [h_sinh_eventually_ne, h_cosh_eventually_ne] with x hx1 hx2
    intro h
    rcases (h_tanh_eq x).mp h with h1 | h2
    · exact hx1 h1
    · exact hx2 h2
  rw [h_ord_eq]
  have h_pole_iff : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z < 0 ↔ (Complex.sinh (w z / 2) = 0) := by
    have h_mero_w : AnalyticAt ℂ (fun z => w z / 2) z := by dsimp [w]; fun_prop
    have h_deriv_w : deriv (fun z => w z / 2) z ≠ 0 := by
      have hd : HasDerivAt (fun z : ℂ ↦ w z / 2) (-π * I) z := by
        convert (((hasDerivAt_id z).const_mul (-2 * π * I)).add (hasDerivAt_const z (ν:ℂ))).div_const 2 using 1
        ring
      rw [hd.deriv]; simp [pi_ne_zero, I_ne_zero]
    have h_comp : meromorphicOrderAt (fun z ↦ coth (w z / 2)) z = meromorphicOrderAt coth (w z / 2) :=
      meromorphicOrderAt_comp_of_deriv_ne_zero (f := coth) h_mero_w h_deriv_w
    have h_inv : meromorphicOrderAt coth (w z / 2) = -meromorphicOrderAt Complex.tanh (w z / 2) := by
      have hcoth_eq : coth = Complex.tanh⁻¹ := funext fun z => by unfold coth; simp [one_div]
      rw [hcoth_eq]
      exact meromorphicOrderAt_inv
    have h_mero_tanh : MeromorphicAt Complex.tanh (w z / 2) := by
      rw [show Complex.tanh = fun x => Complex.sinh x / Complex.cosh x from
        funext Complex.tanh_eq_sinh_div_cosh]
      exact Complex.analyticAt_sinh.meromorphicAt.fun_div Complex.analyticAt_cosh.meromorphicAt
    have h_pos : (0 < meromorphicOrderAt Complex.tanh (w z / 2)) ↔ (Complex.sinh (w z / 2) = 0) := by
      rw [← tendsto_zero_iff_meromorphicOrderAt_pos h_mero_tanh]
      constructor
      · intro h
        by_cases hc : Complex.cosh (w z / 2) = 0
        · exfalso
          have hsinh_ne : Complex.sinh (w z / 2) ≠ 0 := by
            intro hs
            have key := Complex.cosh_sq_sub_sinh_sq (w z / 2)
            rw [hc, hs] at key
            norm_num at key
          have hord_neg : meromorphicOrderAt Complex.tanh (w z / 2) < 0 := by
            rw [show Complex.tanh = fun x => Complex.sinh x / Complex.cosh x from
                  funext Complex.tanh_eq_sinh_div_cosh]
            have hsinh_mero : MeromorphicAt Complex.sinh (w z / 2) :=
              Complex.analyticAt_sinh.meromorphicAt
            have hcosh_mero : MeromorphicAt Complex.cosh (w z / 2) :=
              Complex.analyticAt_cosh.meromorphicAt
            have hsinh_ord : meromorphicOrderAt Complex.sinh (w z / 2) = 0 := by
              rw [← tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero hsinh_mero]
              exact ⟨Complex.sinh (w z / 2), hsinh_ne,
                     Complex.analyticAt_sinh.continuousAt.continuousWithinAt⟩
            have hcosh_ord : 0 < meromorphicOrderAt Complex.cosh (w z / 2) := by
              rw [← tendsto_zero_iff_meromorphicOrderAt_pos hcosh_mero]
              have hana : AnalyticAt ℂ Complex.cosh (w z / 2) := Complex.analyticAt_cosh
              exact hc ▸ hana.continuousAt.continuousWithinAt
            rw [fun_meromorphicOrderAt_div hsinh_mero hcosh_mero,
                hsinh_ord]
            have hne_top_cosh : meromorphicOrderAt Complex.cosh (w z / 2) ≠ ⊤ := by
              rw [ne_eq, meromorphicOrderAt_eq_top_iff]
              intro h_cosh_zero
              have h_eq_pw : (fun x => Complex.cosh x) =ᶠ[nhdsWithin (w z / 2) {w z / 2}ᶜ]
                  (fun _ => (0 : ℂ)) := h_cosh_zero
              have h_eval : Complex.cosh (w z / 2) = 0 :=
                tendsto_nhds_unique
                  (Complex.continuous_cosh.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
                  h_eq_pw.tendsto
              have h_nhds : (fun x => Complex.cosh x) =ᶠ[nhds (w z / 2)] (fun _ => (0 : ℂ)) := by
                rw [eventually_nhdsWithin_iff] at h_cosh_zero
                filter_upwards [h_cosh_zero] with x hx
                exact if h : x = w z / 2 then h ▸ h_eval else hx h
              have h_deriv := h_nhds.deriv_eq
              rw [deriv_const, (Complex.hasDerivAt_cosh (w z / 2)).deriv] at h_deriv
              exact hsinh_ne h_deriv
            lift meromorphicOrderAt Complex.cosh (w z / 2) to ℤ using hne_top_cosh with m hm
            norm_cast at hcosh_ord ⊢
            omega
          exact absurd hord_neg (not_lt.mpr ((tendsto_zero_iff_meromorphicOrderAt_pos h_mero_tanh).mp h).le)
        · have hcts : ContinuousAt Complex.tanh (w z / 2) := by
            change ContinuousAt (fun z => Complex.sinh z / Complex.cosh z) _
            exact Complex.analyticAt_sinh.continuousAt.div Complex.analyticAt_cosh.continuousAt hc
          have hval : Complex.tanh (w z / 2) = 0 :=
            tendsto_nhds_unique (hcts.tendsto.mono_left nhdsWithin_le_nhds) h
          rw [Complex.tanh_eq_sinh_div_cosh, div_eq_zero_iff] at hval
          exact hval.resolve_right hc
      · intro h
        have hc : Complex.cosh (w z / 2) ≠ 0 := by
          intro heq
          have hsum := Complex.cosh_add_sinh (w z / 2)
          rw [heq, h, zero_add] at hsum
          exact absurd hsum.symm (Complex.exp_ne_zero _)
        have hcts : ContinuousAt Complex.tanh (w z / 2) := by
          change ContinuousAt (fun z => Complex.sinh z / Complex.cosh z) _
          exact Complex.analyticAt_sinh.continuousAt.div Complex.analyticAt_cosh.continuousAt hc
        have hval : Complex.tanh (w z / 2) = 0 := by
          rw [Complex.tanh_eq_sinh_div_cosh, h, zero_div]
        convert hcts.tendsto.mono_left nhdsWithin_le_nhds using 1
        simp [hval]
    rw [h_comp, h_inv]
    have h_finish : -meromorphicOrderAt Complex.tanh (w z / 2) < 0 ↔
        0 < meromorphicOrderAt Complex.tanh (w z / 2) := by
      lift meromorphicOrderAt Complex.tanh (w z / 2) to ℤ using hne_top_tanh with a
      norm_cast; omega
    rw [h_finish, h_pos]
  rw [h_pole_iff, sinh_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    use -k
    apply (mul_left_inj' (show (2 * ↑π * I : ℂ) ≠ 0 by simp [pi_ne_zero])).mp
    field_simp [pi_ne_zero, I_ne_zero] at hk ⊢
    have h1 : 2 * ↑π * I * z = ↑ν - 2 * ↑k * ↑π * I := by rw [← hk]; dsimp [w]; ring
    calc
      (2 * ↑π * z : ℂ) = (2 * ↑π * I * z) * (-I) := by ring_nf; simp
      _ = (↑ν - 2 * ↑k * ↑π * I) * (-I) := by rw [h1]
      _ = 2 * ↑k * ↑π * Complex.I^2 - I * ↑ν := by ring
      _ = 2 * ↑π * ↑(-k) - I * ↑ν := by simp; ring
  · rintro ⟨n, rfl⟩
    use -n
    dsimp [w]
    field_simp [pi_ne_zero, I_ne_zero]
    ring_nf
    simp

@[blueprint
  "Phi-circ-residues"
  (title := "$\\Phi^{\\pm,\\circ}_\\nu$ residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\circ}_\nu(z)$$ at $n - i \nu/2\pi$ is $i/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1071)]
theorem Phi_circ.residue (ν ε : ℝ) (_hν : ν > 0) (n : ℤ) :
    (nhdsWithin (n - I * ν / (2 * π)) {n - I * ν / (2 * π)}ᶜ).Tendsto (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_circ ν ε z) (nhds (I / (2 * π))) := by
  set z₀ : ℂ := n - I * ν / (2 * π)
  set w : ℂ → ℂ := fun z ↦ -2 * π * I * z + ν
  set s : ℂ → ℂ := fun z ↦ w z / 2
  have h_s_z₀ : s z₀ = -n * π * I := by
    dsimp [s, w, z₀]
    field_simp [pi_ne_zero]
    ring_nf
    simp [I_sq]
  have h_cosh_z₀ : Complex.cosh (s z₀) = (-1)^n := by
    rw [h_s_z₀, show -n * π * I = -(n * π * I) by ring, Complex.cosh_neg, Complex.cosh_mul_I]
    norm_cast
    push_cast [Real.cos_int_mul_pi]
    rfl
  have h_sinh_z₀ : Complex.sinh (s z₀) = 0 := by
    rw [h_s_z₀, show -n * π * I = -(n * π * I) by ring, Complex.sinh_neg,
        Complex.sinh_mul_I, Complex.sin_int_mul_pi]
    simp
  have h_s_deriv : HasDerivAt s (-↑π * I) z₀ := by
    dsimp [s, w]
    have h := (((hasDerivAt_id z₀).const_mul (-2 * ↑π * I)).add
                (hasDerivAt_const z₀ (↑ν : ℂ))).div_const 2
    convert h using 1; simp only [mul_one, add_zero]; ring
  have h_sinh_deriv : HasDerivAt (fun z ↦ Complex.sinh (s z)) (-↑π * I * Complex.cosh (s z₀)) z₀ := by
    convert (Complex.hasDerivAt_sinh (s z₀)).comp z₀ h_s_deriv using 1; ring
  have h_slope2 : Filter.Tendsto (fun z => Complex.sinh (s z) / (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (-π * I * Complex.cosh (s z₀))) := by
    have h_eq : slope (fun z => Complex.sinh (s z)) z₀ = fun z => Complex.sinh (s z) / (z - z₀) := by
      ext z; simp [slope, h_sinh_z₀, div_eq_inv_mul]
    have h_slope := h_sinh_deriv.tendsto_slope
    rwa [h_eq] at h_slope
  have h_lim_sinh : Filter.Tendsto (fun z ↦ (z - z₀) / Complex.sinh (s z)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (-π * I * Complex.cosh (s z₀))⁻¹) := by
    simpa [inv_div] using h_slope2.inv₀ (by
      rw [h_cosh_z₀]
      exact mul_ne_zero (by simp [pi_ne_zero, I_ne_zero]) (zpow_ne_zero n (by norm_num)))
  have h_lim_eps : Filter.Tendsto (fun z ↦ (1 / 2 : ℂ) * ε * (z - z₀)) (nhdsWithin z₀ {z₀}ᶜ) (nhds 0) := by
    have h : Filter.Tendsto (fun z => z - z₀) (nhds z₀) (nhds (z₀ - z₀)) :=
      Filter.Tendsto.sub Filter.tendsto_id tendsto_const_nhds
    rw [sub_self] at h
    have h2 := Filter.Tendsto.const_mul ((1 / 2 : ℂ) * ε) h
    rw [mul_zero] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have h_lim_cosh : Filter.Tendsto (fun z ↦ Complex.cosh (s z)) (nhdsWithin z₀ {z₀}ᶜ) (nhds (Complex.cosh (s z₀))) :=
    (by dsimp [s, w]; fun_prop : Continuous (fun z ↦ Complex.cosh (s z))).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [show (I / (2 * π) : ℂ) = (1 / 2 : ℂ) * (-π * I * Complex.cosh (s z₀))⁻¹ * Complex.cosh (s z₀) + 0 by
    rw [add_zero, mul_inv]
    field_simp [show Complex.cosh (s z₀) ≠ 0 by rw [h_cosh_z₀]; exact zpow_ne_zero n (by norm_num),
      show (-↑π * I : ℂ) ≠ 0 by simp [pi_ne_zero, I_ne_zero]]
    ring_nf; simp]
  refine Filter.Tendsto.congr (fun z => ?_) ((h_lim_sinh.const_mul (1 / 2 : ℂ)).mul h_lim_cosh |>.add h_lim_eps)
  rw [Phi_circ, coth]
  dsimp [s, w]
  rw [Complex.tanh_eq_sinh_div_cosh]
  simp [one_div]
  ring

@[blueprint
  "Phi-circ-poles-simple"
  (title := "Phi-circ poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1070)]
theorem Phi_circ.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z = -1 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by
  constructor
  · exact fun h ↦ (Phi_circ.poles ν ε hν z).mp (h ▸ by decide)
  · rintro ⟨n, rfl⟩
    set z₀ := (n : ℂ) - I * ν / (2 * π)
    have hsub : MeromorphicAt (· - z₀ : ℂ → ℂ) z₀ := by fun_prop
    have hf : MeromorphicAt (Phi_circ ν ε) z₀ := (Phi_circ.meromorphic ν ε).meromorphicAt
    have heq : (fun z ↦ (z - z₀) * Phi_circ ν ε z) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] ((· - z₀) * Phi_circ ν ε) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    have hL : (I : ℂ) / (2 * ↑π) ≠ 0 := by
      apply div_ne_zero I_ne_zero
      exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr pi_ne_zero)
    have hord₀ : meromorphicOrderAt ((· - z₀) * Phi_circ ν ε) z₀ = 0 :=
      (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hsub.mul hf)).mp
        ⟨_, hL, (Phi_circ.residue ν ε hν n).congr' heq⟩
    have hord₁ : meromorphicOrderAt (· - z₀ : ℂ → ℂ) z₀ = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hsub]
      exact ⟨1, analyticAt_const, one_ne_zero, by simp⟩
    rw [meromorphicOrderAt_mul hsub hf, hord₁] at hord₀
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (by rintro h; simp [h] at hord₀ : meromorphicOrderAt (Phi_circ ν ε) z₀ ≠ ⊤)
    rw [← hm] at hord₀ ⊢
    have h1 : (↑(1 : ℤ) + ↑m : WithTop ℤ) = ↑(1 + m : ℤ) := by push_cast; ring_nf
    rw [h1] at hord₀
    have : 1 + m = 0 := by exact_mod_cast hord₀
    change (↑m : WithTop ℤ) = ↑(-1 : ℤ); congr 1; omega

@[blueprint
  "B-def"
  (title := "Definition of $B^\\pm$")
  (statement := /--
  $B^\pm(s) = s/2 (\coth(s/2) \pm 1)$ with the convention $B^\pm(0) = 1$.
  -/)]
noncomputable def B (ε : ℝ) (s : ℂ) : ℂ := if s = 0 then 1 else s * (coth (s / 2) + ε) / 2

@[blueprint
  "B-cts"
  (title := "Continuity of $B^\\pm$ at $0$")
  (statement := /--
  $B^\pm$ is continuous at $0$.
  -/)
  (proof := /-- L'H\^opital's rule can be applied to show the continuity at $0$. -/)
  (latexEnv := "lemma")]
theorem B.continuous_zero (ε : ℝ) : ContinuousAt (B ε) 0 := by
  have h_lim : Filter.Tendsto (fun s : ℂ => s * (Complex.cosh (s / 2)) / (2 * Complex.sinh (s / 2)) + ε * s / 2) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
    have h_lim : Filter.Tendsto (fun s : ℂ => s / (2 * Complex.sinh (s / 2))) (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      have h_sinh : Filter.Tendsto (fun s : ℂ => Complex.sinh (s / 2) / s) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
        simpa [div_eq_inv_mul] using HasDerivAt.tendsto_slope_zero
          (HasDerivAt.comp 0 (Complex.hasDerivAt_sinh _)
            (hasDerivAt_id 0 |> HasDerivAt.div_const <| 2))
      convert h_sinh.inv₀ (by norm_num : (1 / 2 : ℂ) ≠ 0) |>
        Filter.Tendsto.const_mul 2⁻¹ using 2 <;> norm_num; ring
    simpa [mul_div_right_comm] using Filter.Tendsto.add
      (h_lim.mul (Complex.continuous_cosh.continuousAt.tendsto.comp
        (continuousWithinAt_id.div_const 2)))
      (Filter.Tendsto.div_const (tendsto_const_nhds.mul continuousWithinAt_id) 2)
  rw [Metric.tendsto_nhdsWithin_nhds] at h_lim
  rw [Metric.continuousAt_iff]
  intro ε hε; rcases h_lim ε hε with ⟨δ, hδ, H⟩; use δ, hδ; intro x hx
  by_cases hx' : x = 0
  · simp_all [B]
  simp_all only [gt_iff_lt, Set.mem_compl_iff, Set.mem_singleton_iff, dist_zero_right, B,
    ↓reduceIte]
  convert H hx' hx using 1; norm_num [coth]
  norm_num [Complex.tanh_eq_sinh_div_cosh]; ring_nf

@[blueprint
  "Phi-star-def"
  (title := "Definition of $\\Phi^{\\pm,\\ast}_\\nu$")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z) := (B^\pm(w) - B^\pm(v)) / (2\pi i)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_star (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (B ε w - B ε ν) / (2 * π * I)

@[blueprint
  "Phi-star-zero"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ at zero")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(0) = 0.$$
  -/)
  (proof := /-- This follows from the definition of $B^\pm$ and the fact that $B^\pm(0) = 1$. -/)]
theorem Phi_star_zero (ν ε : ℝ) : Phi_star ν ε 0 = 0 := by simp [Phi_star]

@[fun_prop]
lemma meromorphic_tanh : Meromorphic Complex.tanh := by
  intro z
  apply MeromorphicAt.div <;> fun_prop

lemma meromorphic_coth : Meromorphic coth := by
  intro z
  apply MeromorphicAt.div <;> fun_prop

lemma meromorphic_coth' : Meromorphic (fun s : ℂ => Complex.cosh s / Complex.sinh s) := by
  have : Meromorphic (fun s : ℂ => 1 / Complex.tanh s) := by
    convert meromorphic_coth using 1
  simpa [Complex.tanh_eq_sinh_div_cosh] using this

lemma meromorphic_coth'' : Meromorphic (fun s : ℂ => Complex.cosh (s / 2) / Complex.sinh (s / 2)) := by
  intro s
  obtain ⟨n, hn⟩ := meromorphic_coth' (s / 2)
  refine ⟨n, ?_⟩
  have h_comp : AnalyticAt ℂ
      (fun z => (z / 2 - s / 2) ^ n •
        (fun s => Complex.cosh s / Complex.sinh s) (z / 2)) s := by
    apply_rules [ContDiffAt.analyticAt]
    have : ContDiffAt ℂ ⊤
        (fun z => (z - s / 2) ^ n •
          (fun s => Complex.cosh s / Complex.sinh s) z) (s / 2) :=
      hn.contDiffAt
    convert this.comp s (contDiffAt_id.div_const 2) using 1
  convert h_comp.mul (show AnalyticAt ℂ (fun _ => 2 ^ n) s from analyticAt_const)
    using 2; norm_num
  rw [show ((_ : ℂ) - s) = 2 * ((_ : ℂ) * (1 / 2) + s * (-1 / 2)) by ring]
  rw [mul_pow]; ring

lemma meromorphicAt_B (ε : ℝ) (z₀ : ℂ) : MeromorphicAt (B ε) z₀ := by
  have h_comp : ∀ z, MeromorphicAt
      (fun s => s * (Complex.cosh (s / 2) / Complex.sinh (s / 2) + ε) / 2) z := by
    have meromorphic_coth'' : Meromorphic (fun s : ℂ => Complex.cosh (s / 2) / Complex.sinh (s / 2)) := by
      exact meromorphic_coth''
    intro z
    exact (by apply_rules [MeromorphicAt.div, MeromorphicAt.add, MeromorphicAt.mul,
      MeromorphicAt.id, MeromorphicAt.const])
  specialize h_comp z₀
  convert h_comp.congr _
  rw [Filter.EventuallyEq, eventually_nhdsWithin_iff]
  unfold B
  rw [Metric.eventually_nhds_iff]
  by_cases h : z₀ = 0
  · simp_all only [gt_iff_lt, dist_zero_right, Set.mem_compl_iff, Set.mem_singleton_iff,
      ↓reduceIte, coth, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, div_left_inj',
        mul_eq_mul_left_iff, add_left_inj, or_false]
    norm_num [Complex.tanh_eq_sinh_div_cosh]
    exact ⟨1, by norm_num⟩
  · simp_all only [gt_iff_lt, Set.mem_compl_iff, Set.mem_singleton_iff, coth, one_div]
    exact ⟨‖z₀‖, norm_pos_iff.mpr h, fun y hy hy' => by
      rw [Complex.tanh_eq_sinh_div_cosh]; aesop⟩

@[blueprint
  "Phi-star-mero"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ meromorphic")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)]
theorem Phi_star.meromorphic (ν ε : ℝ) : Meromorphic (Phi_star ν ε) := by
  intro z₀
  have h_comp : MeromorphicAt (fun z => B ε (-2 * Real.pi * Complex.I * z + ν)) z₀ ∧
      MeromorphicAt (fun _ => B ε ν) z₀ := by
    constructor
    · exact (meromorphicAt_B ε _).comp_analyticAt (by fun_prop)
    · exact MeromorphicAt.const (B ε ↑ν) z₀
  exact (h_comp.1.sub h_comp.2).div (MeromorphicAt.const _ z₀)

@[blueprint
  "Phi-star-poles"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z} \backslash \{0\}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1072)]
theorem Phi_star.poles (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z < 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-star-residues"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\ast}_\nu(z)$$ at $n - i \nu/2\pi$ is $-in/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")
  (discussion := 1073)]
theorem Phi_star.residue (ν ε : ℝ) (hν : ν > 0) (n : ℤ) (hn : n ≠ 0) :
    (nhdsWithin (n - I * ν / (2 * π)) {n - I * ν / (2 * π)}ᶜ).Tendsto
      (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_star ν ε z) (nhds (-I * n / (2 * π))) := by sorry

@[blueprint
  "Phi-star-poles-simple"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)
  (latexEnv := "lemma")]
theorem Phi_star.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z = -1 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by
  constructor
  · exact fun h ↦ (Phi_star.poles ν ε hν z).mp (h ▸ by decide)
  · rintro ⟨n, hn, rfl⟩
    set z₀ := (n : ℂ) - I * ν / (2 * π)
    have hsub : MeromorphicAt (· - z₀ : ℂ → ℂ) z₀ := by fun_prop
    have hf : MeromorphicAt (Phi_star ν ε) z₀ := (Phi_star.meromorphic ν ε).meromorphicAt
    have heq : (fun z ↦ (z - z₀) * Phi_star ν ε z) =ᶠ[nhdsWithin z₀ {z₀}ᶜ] ((· - z₀) * Phi_star ν ε) :=
      Filter.Eventually.of_forall fun _ ↦ rfl
    have hL : -I * ↑n / (2 * ↑(π : ℝ)) ≠ (0 : ℂ) := by
      simp only [neg_mul, ne_eq, div_eq_zero_iff, neg_eq_zero, mul_eq_zero, I_ne_zero,
        Int.cast_eq_zero, false_or, OfNat.ofNat_ne_zero, ofReal_eq_zero, pi_ne_zero, or_self,
        or_false]
      exact_mod_cast hn
    have hord₀ : meromorphicOrderAt ((· - z₀) * Phi_star ν ε) z₀ = 0 :=
      (tendsto_ne_zero_iff_meromorphicOrderAt_eq_zero (hsub.mul hf)).mp
        ⟨_, hL, (Phi_star.residue ν ε hν n hn).congr' heq⟩
    have hord₁ : meromorphicOrderAt (· - z₀ : ℂ → ℂ) z₀ = (1 : ℤ) := by
      rw [meromorphicOrderAt_eq_int_iff hsub]
      exact ⟨1, analyticAt_const, one_ne_zero, by simp⟩
    rw [meromorphicOrderAt_mul hsub hf, hord₁] at hord₀
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp
      (by rintro h; simp [h] at hord₀ : meromorphicOrderAt (Phi_star ν ε) z₀ ≠ ⊤)
    rw [← hm] at hord₀ ⊢
    have h1 : (↑(1 : ℤ) + ↑m : WithTop ℤ) = ↑(1 + m : ℤ) := by push_cast; ring_nf
    rw [h1] at hord₀
    have : 1 + m = 0 := by exact_mod_cast hord₀
    change (↑m : WithTop ℤ) = ↑(-1 : ℤ); congr 1; omega

@[blueprint
  "Phi-cancel"
  (title := "$\\Phi^{\\circ}_\\nu \\pm \\Phi^{\\ast}_\\nu$ pole cancellation")
  (statement := /--
  $\Phi^{\sigma, \circ}_\nu(z) \pm \Phi^{\sigma, \ast}_\nu(z)$ is regular at $\pm 1 - i \nu / 2 \pi$.
  -/)
  (proof := /-- The residues cancel out. -/)
  (latexEnv := "lemma")
  (discussion := 1074)]
theorem Phi_cancel (ν ε σ : ℝ) (hν : ν > 0) (hε : |ε| = 1) :
    meromorphicOrderAt (fun z ↦ Phi_circ ν ε z + σ * Phi_star ν ε z) ≥ 0 := by sorry


@[blueprint
  "phi-pm-def"
  (title := "Definition of $\\varphi^{\\pm}$")
  (statement := /--
  $$\varphi^{\pm}_\nu(t) := 1_{[-1,1]}(t) ( \Phi^{\pm,\circ}_\nu(t) + \mathrm{sgn}(t) \Phi^{\pm,\ast}_\nu(t) ).$$
  -/)]
noncomputable def ϕ_pm (ν ε : ℝ) (t : ℝ) : ℂ :=
  if -1 ≤ t ∧ t ≤ 1 then
    Phi_circ ν ε (t : ℂ) + t.sign * Phi_star ν ε (t : ℂ)
  else 0

@[blueprint
  "phi-c2-left"
  (title := "$\\varphi$ is $C^2$ on [-1,0]")
  (statement := /--
  $\varphi$ is $C^2$ on $[-1,0]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\mathbb{R}$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = \nu$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_left (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc (-1) 0) := by
  have h_diff_circ : ContDiff ℝ 2 (fun t : ℝ => Phi_circ ν ε (t : ℂ)) := by
    have h_diff : ContDiff ℝ 2 (fun t : ℝ => 1 / Complex.tanh ((-2 * Real.pi * Complex.I * t + ν) / 2)) := by
      simp only [Complex.tanh_eq_sinh_div_cosh]
      have h_sinh_cosh_diff : ContDiff ℝ 2 (fun t : ℝ => Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2)) ∧ ContDiff ℝ 2 (fun t : ℝ => Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2)) ∧ ∀ t : ℝ, Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) ≠ 0 := by
        refine ⟨?_, ?_, ?_⟩
        · have h_sinh_entire : ContDiff ℂ 2 Complex.sinh := by
            unfold Complex.sinh
            exact ContDiff.div_const (Complex.contDiff_exp.sub (Complex.contDiff_exp.comp contDiff_neg)) _
          exact h_sinh_entire.restrict_scalars ℝ |> ContDiff.comp <| ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const <| Complex.ofRealCLM.contDiff) contDiff_const) _
        · have h_cosh_entire : ContDiff ℝ 2 (fun t : ℂ => Complex.cosh t) := by
            have : ContDiff ℂ 2 Complex.cosh := by
              unfold Complex.cosh
              exact ContDiff.div_const (Complex.contDiff_exp.add (Complex.contDiff_exp.comp contDiff_neg)) _
            exact this.restrict_scalars ℝ
          exact h_cosh_entire.comp (ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const) _)
        · norm_num [Complex.sinh, Complex.exp_ne_zero]
          norm_num [sub_eq_zero, Complex.exp_ne_zero]
          intro t ht; rw [Complex.exp_eq_exp_iff_exists_int] at ht
          obtain ⟨k, hk⟩ := ht; norm_num [Complex.ext_iff] at hk
          rcases k with ⟨_ | k⟩ <;> norm_num at hk <;> ring_nf at hk <;> norm_num at hk <;>
            cases lt_or_gt_of_ne hlam <;> nlinarith [Real.pi_pos]
      simp_all only [ne_eq, neg_mul, division_def, mul_inv_rev, inv_inv, one_mul]
      exact ContDiff.mul h_sinh_cosh_diff.2.1 (ContDiff.inv h_sinh_cosh_diff.1 fun t => h_sinh_cosh_diff.2.2 t)
    exact ContDiff.mul contDiff_const (h_diff.add contDiff_const)
  have h_diff_star : ContDiff ℝ 2 (fun t : ℝ => Phi_star ν ε (t : ℂ)) := by
    have h_diff_B : ContDiff ℝ 2 (fun t : ℝ => B ε (-2 * Real.pi * Complex.I * t + ν)) := by
      have h_B_rational : ∀ w : ℂ, w ≠ 0 → B ε w = w * (Complex.cosh (w / 2) / Complex.sinh (w / 2) + ε) / 2 := by
        unfold B; unfold coth
        simp +contextual [Complex.tanh_eq_sinh_div_cosh]
      have h_comp : ContDiff ℝ 2 (fun t : ℝ => (-2 * Real.pi * Complex.I * t + ν) * (Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2) / Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) + ε) / 2) := by
        apply_rules [ContDiff.div, ContDiff.mul, ContDiff.add, contDiff_const, contDiff_id]
        · exact Complex.ofRealCLM.contDiff
        · exact Complex.contDiff_exp.comp (ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const) _)
        · exact Complex.contDiff_exp.comp (ContDiff.neg (ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const) _))
        · have h_conj : ContDiff ℝ 2 (fun x : ℝ => Complex.sinh ((-2 * Real.pi * Complex.I * x + ν) / 2)) := by
            have h_conj : ContDiff ℝ 2 (fun x : ℝ => Complex.exp ((-2 * Real.pi * Complex.I * x + ν) / 2)) :=
              Complex.contDiff_exp.comp (ContDiff.div_const (ContDiff.add (ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff) contDiff_const) _)
            simp_all only [ne_eq, Complex.sinh, neg_mul]
            exact ContDiff.div_const (h_conj.sub (Complex.contDiff_exp.comp (by exact ContDiff.neg (by exact ContDiff.div_const (by exact ContDiff.add (ContDiff.neg (by exact ContDiff.mul contDiff_const Complex.ofRealCLM.contDiff)) contDiff_const) _)))) _
          rw [contDiff_iff_contDiffAt] at *
          intro x; specialize h_conj x; exact (by
          convert Complex.conjCLE.contDiff.contDiffAt.comp x h_conj using 1)
        · refine Complex.ofRealCLM.contDiff.comp ?_
          refine ContDiff.inv ?_ ?_
          · norm_num [Complex.normSq, Complex.sinh]
            norm_num [Complex.exp_re, Complex.exp_im]
            exact ContDiff.div_const (ContDiff.add (ContDiff.mul (ContDiff.sub (ContDiff.mul contDiff_const (Real.contDiff_cos.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _))) (ContDiff.mul contDiff_const (Real.contDiff_cos.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _)))) (ContDiff.sub (ContDiff.mul contDiff_const (Real.contDiff_cos.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _))) (ContDiff.mul contDiff_const (Real.contDiff_cos.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _))))) (ContDiff.mul (ContDiff.add (ContDiff.mul contDiff_const (Real.contDiff_sin.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _))) (ContDiff.mul contDiff_const (Real.contDiff_sin.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _)))) (ContDiff.add (ContDiff.mul contDiff_const (Real.contDiff_sin.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _))) (ContDiff.mul contDiff_const (Real.contDiff_sin.comp (by exact ContDiff.div_const (ContDiff.neg (contDiff_const.mul contDiff_id)) _)))))) _
          · norm_num [Complex.sinh, Complex.exp_re, Complex.exp_im, Complex.normSq]
            intro x; ring_nf; norm_num [Real.exp_ne_zero, hlam]
            norm_num [Real.sin_sq, Real.cos_sq, mul_assoc, mul_left_comm, ← Real.exp_add, ← Real.exp_nat_mul]; ring_nf
            cases lt_or_gt_of_ne hlam <;> nlinarith [Real.cos_le_one (Real.pi * x * 2), Real.exp_pos ν, Real.exp_pos (-ν), Real.exp_neg ν, mul_inv_cancel₀ (ne_of_gt (Real.exp_pos ν)), Real.add_one_le_exp ν, Real.add_one_le_exp (-ν)]
      convert h_comp using 1
      ext t; by_cases h : (-(2 * Real.pi * Complex.I * t) + ν : ℂ) = 0 <;> simp_all [Complex.sinh, Complex.cosh]; ring_nf
      norm_num [Complex.ext_iff] at h; aesop
    convert h_diff_B.sub contDiff_const |> fun h => h.div_const (2 * Real.pi * Complex.I) using 1
  have h_eq : ∀ t ∈ Set.Icc (-1 : ℝ) 0, ϕ_pm ν ε t = Phi_circ ν ε (t : ℂ) - (if t = 0 then 0 else Phi_star ν ε (t : ℂ)) := by
    unfold ϕ_pm
    intro t ht
    split_ifs
    · norm_num
      grind
    · rw [Real.sign_of_neg (lt_of_le_of_ne ht.2 ‹_›)]
      norm_num [sub_eq_add_neg]
    · grind
    · grind
  refine ContDiffOn.congr ?_ h_eq
  apply_rules [ContDiffOn.sub, h_diff_circ.contDiffOn, h_diff_star.contDiffOn]
  refine h_diff_star.contDiffOn.congr fun x hx => ?_
  grind [Phi_star, neg_mul, ofReal_zero, mul_zero, neg_zero, zero_add,
    sub_self, zero_div]

lemma h_entire : ContDiffOn ℂ 2
    (fun z => Complex.cosh (z / 2) / Complex.sinh (z / 2))
    (Set.univ \ {z : ℂ | Complex.sinh (z / 2) = 0}) := by
  apply ContDiffOn.div
  · fun_prop
  · fun_prop
  · grind

lemma h_no_zero {ν : ℝ} (hlam : ν ≠ 0) : ∀ t ∈ Set.Icc (0 : ℝ) 1,
    Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) ≠ 0 := by
  norm_num [Complex.sinh, Complex.exp_ne_zero]
  intro t ht₁ ht₂
  rw [sub_eq_zero, Complex.exp_eq_exp_iff_exists_int]
  rintro ⟨⟨_ | k⟩, hk⟩
  <;> norm_num [Complex.ext_iff] at hk <;> ring_nf at hk <;> norm_num at hk
  <;> grind

lemma hc (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (fun t : ℝ => Phi_circ ν ε (t : ℂ)) (Set.Icc 0 1) := by
  refine ContDiff.contDiffOn ?_
  suffices h : ContDiff ℝ 2 (fun t : ℝ => Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2) /
      Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2)) by
    convert h.div_const 2 |> ContDiff.add <| contDiff_const.div_const 2 using 1
    swap; · exact ↑ε
    unfold Phi_circ; ext; norm_num [Complex.tanh_eq_sinh_div_cosh, div_div]; ring_nf
    unfold coth; norm_num [Complex.tanh_eq_sinh_div_cosh]; ring
  refine contDiff_iff_contDiffAt.2 fun t => ?_
  have h_sinh_ne_zero : ∀ t : ℝ,
      Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) ≠ 0 := by
    norm_num [Complex.sinh, Complex.ext_iff]
    norm_num [Complex.exp_re, Complex.exp_im, neg_div]
    intro t ht; contrapose! hlam; simp_all only [sub_eq_iff_eq_add, zero_add,
      mul_eq_mul_right_iff, exp_eq_exp]
    by_cases h : Real.sin (2 * Real.pi * t / 2) = 0
    · cases ht <;> nlinarith [Real.sin_sq_add_cos_sq (2 * Real.pi * t / 2)]
    · exact False.elim <| h <| by nlinarith [Real.exp_pos (ν / 2), Real.exp_pos (-(ν / 2))]
  have h_analytic : AnalyticAt ℂ (fun z : ℂ => Complex.cosh z / Complex.sinh z)
      ((-2 * Real.pi * Complex.I * t + ν) / 2) := by
    apply_rules [AnalyticAt.div, AnalyticAt.mul, analyticAt_id, analyticAt_const]
    · fun_prop (disch := solve_by_elim)
    · norm_num
    · exact Differentiable.analyticAt (Complex.differentiable_exp.sub
        (Complex.differentiable_exp.comp (differentiable_id.neg))) _
    · norm_num
  exact h_analytic.contDiffAt.restrict_scalars ℝ |>.comp t <|
    ContDiffAt.div_const (ContDiffAt.add (ContDiffAt.mul contDiffAt_const <|
    Complex.ofRealCLM.contDiff.contDiffAt) contDiffAt_const) _

@[blueprint
  "phi-c2-right"
  (title := "$\\varphi$ is $C^2$ on [0,1]")
  (statement := /--
  $\varphi$ is $C^2$ on $[0,1]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\mathbb{R}$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = \nu$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_right (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc 0 1) := by
  /- Since `Phi_circ` and `Phi_star` have no poles on ℝ (when ν ≠ 0), they are holomorphic on a
     neighborhood of any real point, hence C^∞ when restricted to ℝ. -/
  have hs : ContDiffOn ℝ 2 (fun t : ℝ => Phi_star ν ε (t : ℂ)) (Set.Icc 0 1) := by
    refine ContDiffOn.div_const ?_ _
    refine ContDiffOn.sub ?_ contDiffOn_const
    have h_simp : ∀ t : ℝ, B ε (-2 * Real.pi * Complex.I * t + ν) =
        (-2 * Real.pi * Complex.I * t + ν) *
        (Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2) /
        Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2) + ε) / 2 := by
      unfold B; unfold coth
      norm_num [Complex.tanh_eq_sinh_div_cosh]
      norm_num [Complex.ext_iff] at *; aesop
    have h_cont_diff : ContDiffOn ℝ 2 (fun t : ℝ =>
        Complex.cosh ((-2 * Real.pi * Complex.I * t + ν) / 2) /
        Complex.sinh ((-2 * Real.pi * Complex.I * t + ν) / 2))
        (Set.Icc (0 : ℝ) 1) := by
      exact h_entire.restrict_scalars ℝ |>.comp
        (ContDiff.contDiffOn (ContDiff.add (ContDiff.mul contDiff_const
        (contDiff_id.comp Complex.ofRealCLM.contDiff)) contDiff_const))
        fun x hx => ⟨Set.mem_univ _, h_no_zero hlam x hx⟩
    simp_all only [ne_eq, neg_mul, div_eq_mul_inv]
    exact ContDiffOn.mul (ContDiffOn.mul (ContDiffOn.add (ContDiffOn.neg
      (ContDiffOn.mul contDiffOn_const Complex.ofRealCLM.contDiff.contDiffOn))
      contDiffOn_const) (h_cont_diff.add contDiffOn_const)) contDiffOn_const
  exact ((hc ν ε hlam).add hs).congr fun t ht => by
    simp only [ϕ_pm]
    rw [if_pos ⟨by linarith [ht.1], ht.2⟩]
    rcases eq_or_lt_of_le ht.1 with rfl | hpos
    · simp [Real.sign_zero, Phi_star_zero]
    · simp [Real.sign_of_pos hpos]

@[blueprint
  "phi-cts"
  (title := "$\\varphi$ is continuous")
  (statement := /--
  $\varphi$ is continuous on $[0,1]$.
  -/)
  (proof := /-- By the preceding lemmas it suffices to verify continuity at $0, -1, 1$.  Continuity at $0$ is clear.  For $t = -1, 1$, by $\coth \frac{w(t)}{2} = \coth \frac{\nu}{2}$, we see that $B^{\pm}(w(t)) = \left(\frac{\nu}{2} - \pi i t\right)\left(\coth \frac{\nu}{2} \pm 1\right)$, and so
\[
\Phi^{\pm,\star}_{\nu}(t) = -t \cdot \frac{1}{2}\left(\coth \frac{\nu}{2} \pm 1\right) = -t\, \Phi^{\pm,\circ}_{\nu}(t);
\]
hence, by Definition \ref{phi-pm-def}, $\varphi^{\pm}_{\nu}(t) = 0$. Thus, $\varphi^{\pm}_{\nu}$ is continuous at $-1$ and at $1$.
 -/)
  (latexEnv := "lemma")
  (discussion := 1075)]
theorem ϕ_continuous (ν ε : ℝ) (hlam : ν ≠ 0) : Continuous (ϕ_pm ν ε) := by
  have tanh_add_pi : ∀ z : ℂ, Complex.tanh (z + ↑Real.pi * I) = Complex.tanh z := by
    intro z
    simp only [Complex.tanh_eq_sinh_div_cosh]
    have h1 : Complex.sinh (z + ↑Real.pi * I) = -Complex.sinh z := by
      simp only [Complex.sinh, Complex.exp_add, Complex.exp_neg]; rw [exp_pi_mul_I]; simp; ring
    have h2 : Complex.cosh (z + ↑Real.pi * I) = -Complex.cosh z := by
      simp only [Complex.cosh, Complex.exp_add, Complex.exp_neg]; rw [exp_pi_mul_I]; simp; ring
    rw [h1, h2, neg_div_neg_eq]
  have tanh_sub_pi : ∀ z : ℂ, Complex.tanh (z - ↑Real.pi * I) = Complex.tanh z := by
    intro z
    have h := tanh_add_pi (z - ↑Real.pi * I)
    rw [sub_add_cancel] at h; exact h.symm
  unfold ϕ_pm
  apply continuous_if
  · intro a ha
    have hfr : frontier {x : ℝ | -1 ≤ x ∧ x ≤ 1} = {-1, 1} := by
      have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by ext; simp
      rw [this, frontier_Icc (by norm_num : (-1 : ℝ) ≤ 1)]
    rw [hfr] at ha
    rcases ha with rfl | rfl
    · unfold Phi_circ Phi_star B coth
      dsimp only []; push_cast; simp only [Real.sign_neg, Real.sign_one, ofReal_neg, ofReal_one]
      have hw_ne : -2 * ↑Real.pi * I * (-1 : ℂ) + ↑ν ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have hν_ne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
      simp only [hw_ne, hν_ne, ↓reduceIte]
      have hw2 : (-2 * ↑Real.pi * I * (-1 : ℂ) + ↑ν) / 2 = ↑ν / 2 + ↑Real.pi * I := by ring
      rw [hw2, tanh_add_pi]
      have hpi : (↑Real.pi : ℂ) * I ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
      grind
    · unfold Phi_circ Phi_star B coth
      dsimp only []; push_cast; simp only [Real.sign_one, ofReal_one]
      have hw_ne : -2 * ↑Real.pi * I * (1 : ℂ) + ↑ν ≠ 0 := by
        intro h; have := congr_arg Complex.im h; simp at this
      have hν_ne : (ν : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlam
      simp only [hw_ne, hν_ne, ↓reduceIte]
      have hw2 : (-2 * ↑Real.pi * I * (1 : ℂ) + ↑ν) / 2 = ↑ν / 2 - ↑Real.pi * I := by ring
      rw [hw2, tanh_sub_pi]
      have hpi : (↑Real.pi : ℂ) * I ≠ 0 := by
        apply mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) I_ne_zero
      field_simp
      ring
  · have hcl : closure {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by
      have : {x : ℝ | -1 ≤ x ∧ x ≤ 1} = Set.Icc (-1) 1 := by ext; simp
      rw [this, closure_Icc]
    rw [hcl]
    have hl := (ϕ_c2_left ν ε hlam).continuousOn
    have hr := (ϕ_c2_right ν ε hlam).continuousOn
    have hunion : Set.Icc (-1 : ℝ) 1 = Set.Icc (-1) 0 ∪ Set.Icc 0 1 := by
      ext x; simp
    rw [hunion]
    intro x hx
    rw [continuousWithinAt_union]
    constructor
    · by_cases hxs : x ∈ Set.Icc (-1 : ℝ) 0
      · exact (hl.congr (fun t ht => by simp [ϕ_pm, show -1 ≤ t from ht.1,
            show t ≤ 1 from le_trans ht.2 (by norm_num : (0 : ℝ) ≤ 1)])) x hxs
      · have : ¬ (nhdsWithin x (Set.Icc (-1 : ℝ) 0)).NeBot := by
          rwa [← mem_closure_iff_nhdsWithin_neBot, closure_Icc]
        rw [Filter.not_neBot] at this; simp [ContinuousWithinAt, this]
    · by_cases hxt : x ∈ Set.Icc (0 : ℝ) 1
      · exact (hr.congr (fun t ht => by simp [ϕ_pm, show -1 ≤ t from le_trans (by norm_num : (-1 : ℝ) ≤ 0) ht.1,
            show t ≤ 1 from ht.2])) x hxt
      · have : ¬ (nhdsWithin x (Set.Icc (0 : ℝ) 1)).NeBot := by
          rwa [← mem_closure_iff_nhdsWithin_neBot, closure_Icc]
        rw [Filter.not_neBot] at this; simp [ContinuousWithinAt, this]
  · exact continuousOn_const

@[blueprint
  "phi-circ-bound-right"
  (title := "Bound on $\\Phi^{\\pm,\\circ}_\\nu$ from above")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- The function $\coth w = 1 + \frac{2}{e^{2w}-1}$ is bounded away from the imaginary line $\Re w = 0$, that is, it is bounded on $\Re w \geq \kappa$ and $\Re w \leq -\kappa$ for any $\kappa > 0$. The map $w(z) = \nu - 2\pi i z$ sends the line $\Im z = -\frac{\nu}{2\pi}$ to the imaginary line, and the region $\Im z \geq c$ is sent to $\Re w \geq 2\pi c + \nu$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_right (ν₀ ν₁ ε c : ℝ) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_circ ν ε z‖ ≤ C := by
  let κ := Real.pi * c + ν₀ / 2
  have hκ : κ > 0 := by
    norm_num +zetaDelta at *
    rw [div_lt_iff₀] at hc <;> nlinarith [Real.pi_pos]
  have hcoth_bound : ∀ u : ℂ, u.re ≥ κ → ‖(Complex.tanh u)⁻¹‖ ≤ (Real.tanh κ)⁻¹ := by
    intros u hu
    have htanh_sq : ‖Complex.tanh u‖ ^ 2 ≥ (Real.sinh u.re / Real.cosh u.re) ^ 2 := by
      have htanh_sq : ‖Complex.tanh u‖ ^ 2 = (Real.sinh u.re ^ 2 + Real.sin u.im ^ 2) /
          (Real.cosh u.re ^ 2 - Real.sin u.im ^ 2) := by
        norm_num [Complex.normSq, Complex.norm_def, Complex.exp_re, Complex.exp_im,
          Complex.sinh, Complex.cosh, Complex.tanh]
        field_simp
        rw [Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity]
        rw [Real.sinh_eq, Real.cosh_eq]; ring_nf
        norm_num [Real.sin_sq, Real.exp_neg]; ring_nf
        rw [show (-2 + Real.cos u.im ^ 2 * 4 + Real.exp u.re ^ 2 + (Real.exp u.re)⁻¹ ^ 2) =
          (-1 / 2 + Real.cos u.im ^ 2 + Real.exp u.re ^ 2 * (1 / 4) +
            (Real.exp u.re)⁻¹ ^ 2 * (1 / 4)) * 4 by ring]
        norm_num; ring
      field_simp
      rw [htanh_sq, mul_div]
      rw [le_div_iff₀]
      · nlinarith only [Real.sin_sq_le_one u.im, Real.sinh_sq u.re]
      · nlinarith only [Real.sin_sq_add_cos_sq u.im, Real.cosh_sq' u.re,
          Real.sinh_pos_iff.mpr (show 0 < u.re by nlinarith [Real.pi_pos])]
    have htanh_ge_tanhκ : Real.sinh u.re / Real.cosh u.re ≥ Real.sinh κ / Real.cosh κ := by
      have htanh_ge_tanhκ : ∀ u v : ℝ, 0 ≤ u → u ≤ v →
          Real.sinh u / Real.cosh u ≤ Real.sinh v / Real.cosh v := by
        intros u v hu hv
        rw [div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]; ring_nf
        rw [show v = u + (v - u) by ring, Real.sinh_add, Real.cosh_add]
        ring_nf; norm_num [Real.sinh_sq]; ring_nf; aesop
      exact htanh_ge_tanhκ _ _ hκ.le hu
    simp_all only [ge_iff_le, norm_inv, Real.tanh_eq_sinh_div_cosh]
    apply inv_anti₀ (div_pos (Real.sinh_pos_iff.mpr hκ) (Real.cosh_pos _))
    calc Real.sinh κ / Real.cosh κ
        _ ≤ Real.sinh u.re / Real.cosh u.re := htanh_ge_tanhκ
        _ ≤ ‖Complex.tanh u‖ := by
            rw [← Real.sqrt_sq (div_nonneg (Real.sinh_nonneg_iff.mpr
              (hκ.le.trans hu)) (Real.cosh_pos _ |>.le))]
            exact Real.sqrt_le_sqrt (by rw [Complex.sq_norm] at htanh_sq; exact htanh_sq)
  use (1 / 2) * ((Real.tanh κ)⁻¹ + |ε|)
  intros ν hν z hz
  have h_w : ‖(Complex.tanh ((-2 * Real.pi * Complex.I * z + ν) / 2))⁻¹‖ ≤
      (Real.tanh κ)⁻¹ := by
    convert hcoth_bound _ _ using 2
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im,
      Complex.mul_im]
    norm_num
    have h1 := hν.1
    have h2 : π * c ≤ π * z.im := mul_le_mul_of_nonneg_left hz (le_of_lt Real.pi_pos)
    change π * c + ν₀ / 2 ≤ (2 * π * z.im + ν) * 2 / 4
    linarith
  unfold Phi_circ
  norm_num [coth]
  exact le_trans (norm_add_le _ _) (add_le_add (by simpa using h_w)
    (by norm_num [Complex.norm_def, Complex.normSq]))

@[blueprint
  "phi-circ-bound-left"
  (title := "Bound on $\\Phi^{\\pm,\\circ}_\\nu$ from below")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_left (ν₀ ν₁ ε c : ℝ) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_circ ν ε z‖ ≤ C := by
  set κ := -(ν₁ + 2 * Real.pi * c) / 2 with hκ_def
  have hκ_pos : 0 < κ := by
    rw [lt_div_iff₀] at hc <;> nlinarith [Real.pi_pos]
  have hRe_w : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      Complex.re ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) ≤ -κ := by
    norm_num [hκ_def]; intros; nlinarith [Real.pi_pos]
  have hcoth_bound : ∀ z : ℂ, Complex.re z ≤ -κ →
      ‖Complex.cosh z / Complex.sinh z‖ ≤
        (Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) := by
    intros z hz
    have hsinh : ‖Complex.sinh z‖ ≥ (Real.exp (-z.re) - Real.exp z.re) / 2 := by
      norm_num [Complex.sinh, Complex.norm_def, Complex.normSq]
      norm_num [Complex.exp_re, Complex.exp_im]
      gcongr
      refine Real.le_sqrt_of_sq_le ?_
      nlinarith [Real.sin_sq_add_cos_sq z.im, Real.exp_pos z.re, Real.exp_pos (-z.re),
        mul_pos (Real.exp_pos z.re) (Real.exp_pos (-z.re))]
    have hcosh : ‖Complex.cosh z‖ ≤ (Real.exp z.re + Real.exp (-z.re)) / 2 := by
      norm_num [Complex.cosh, Complex.exp_re, Complex.exp_im]
      gcongr
      exact le_trans (norm_add_le ..) (by norm_num [Complex.norm_exp])
    rw [norm_div]
    rw [div_le_div_iff₀] <;>
      try linarith [Real.exp_pos κ, Real.exp_lt_exp.mpr (show -κ < κ by linarith)]
    · have h_exp_bounds : Real.exp z.re ≤ Real.exp (-κ) ∧ Real.exp (-z.re) ≥ Real.exp κ :=
        ⟨Real.exp_le_exp.mpr hz, Real.exp_le_exp.mpr (by linarith)⟩
      nlinarith [Real.exp_pos κ, Real.exp_pos (-κ),
        Real.exp_lt_exp.2 (show -κ < κ by linarith)]
    · exact lt_of_lt_of_le
        (div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by linarith))) zero_lt_two) hsinh
  use (1 / 2) * ((Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) + |ε|)
  intros ν hν z hz
  have hcoth_w : ‖Complex.cosh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) /
      Complex.sinh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2)‖ ≤
      (Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) :=
    hcoth_bound _ (hRe_w ν hν z hz)
  have h_triangle : ‖(1 / 2) * (Complex.cosh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) /
      Complex.sinh ((-2 * Real.pi * Complex.I * z + (ν : ℂ)) / 2) + ε)‖ ≤
      (1 / 2) * ((Real.exp κ + Real.exp (-κ)) / (Real.exp κ - Real.exp (-κ)) + |ε|) := by
    norm_num at *
    exact le_trans (norm_add_le ..) (add_le_add (by simpa using hcoth_w) (by norm_num))
  convert h_triangle using 1
  unfold Phi_circ coth
  norm_num [Complex.tanh_eq_sinh_div_cosh]

@[blueprint
  "phi-star-bound-right"
  (title := "Bound on $\\Phi^{\\pm,\\ast}_\\nu$ from above")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- The bound on $\Phi^{\pm,\star}_{\nu}$ follows from the bound on $\Phi^{\pm,\circ}_{\nu}$ by $\Phi^{\pm,\star}(z) = \frac{1}{2\pi i}\bigl(w\,\Phi^{\pm,\circ}(w) - \nu\,\Phi^{\pm,\circ}(\nu)\bigr)$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_right (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by
  obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_right ν₀ ν₁ ε c hc
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ‖B ε ν‖ ≤ C₂ := by
    have hB_def : ∀ ν ∈ Set.Icc ν₀ ν₁, B ε ν =
        ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2 := by
      unfold B coth
      norm_num [Complex.tanh_eq_sinh_div_cosh]
      intros; linarith
    have h_cont : ContinuousOn
        (fun ν : ℝ => ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2)
        (Set.Icc ν₀ ν₁) := by
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.mul Complex.continuous_ofReal.continuousOn
        (ContinuousOn.add ?_ continuousOn_const)
      refine ContinuousOn.div ?_ ?_ ?_
      · exact Continuous.continuousOn (by continuity)
      · exact Continuous.continuousOn (by continuity)
      · intro x hx
        have h3 : (↑x / 2 : ℂ) = ↑(x / 2) := by push_cast; ring
        rw [h3]
        exact_mod_cast ne_of_gt (by rw [Real.sinh_eq]; nlinarith [Real.exp_lt_exp.mpr (show -(x/2) < x/2 by linarith [hx.1])])
    obtain ⟨C₂, hC₂⟩ := IsCompact.exists_bound_of_continuousOn
      CompactIccSpace.isCompact_Icc h_cont
    exact ⟨C₂, fun ν hν => by aesop⟩
  have h_bound : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c →
      ‖Phi_star ν ε z‖ ≤
        (‖z‖ * (2 * Real.pi * C₁) + ν₁ * C₁ + C₂) / (2 * Real.pi) := by
    intro ν hν z hz
    have h_norm_B : ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤
        ‖z‖ * (2 * Real.pi * C₁) + ν₁ * C₁ := by
      have h1 : ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤
          ‖-2 * Real.pi * I * z + ν‖ * C₁ := by
        by_cases h : -2 * Real.pi * I * z + ν = 0 <;>
        simp_all only [gt_iff_lt, Set.mem_Icc, ge_iff_le, Phi_circ, one_div, norm_inv, and_imp, B,
          ↓reduceIte,Complex.norm_mul, Complex.norm_ofNat, Complex.norm_div]
        · norm_num [Complex.ext_iff] at h
          rw [div_lt_iff₀] at hc <;> nlinarith [Real.pi_pos]
        · have := hC₁ ν hν.1 hν.2 z hz
          rw [mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
      have h2 : ‖-2 * Real.pi * I * z + ν‖ ≤ 2 * Real.pi * ‖z‖ + ν₁ := by
        refine le_trans (norm_add_le ..) ?_
        norm_num [abs_of_nonneg Real.pi_pos.le]
        cases abs_cases ν <;> linarith [hν.1, hν.2]
      nlinarith [show 0 ≤ C₁ from le_trans (norm_nonneg _) (hC₁ ν hν z hz)]
    have h_eq : ‖Phi_star ν ε z‖ =
        ‖B ε (-2 * Real.pi * I * z + ν) - B ε ν‖ / (2 * Real.pi) := by
      unfold Phi_star
      norm_num [abs_of_nonneg Real.pi_pos.le]
    exact h_eq ▸ div_le_div_of_nonneg_right
      (le_trans (norm_sub_le ..) (add_le_add h_norm_B (hC₂ ν hν))) (by positivity)
  use (|2 * Real.pi * C₁| + |ν₁ * C₁ + C₂|) / (2 * Real.pi)
  intro ν hν z hz
  convert le_trans (h_bound ν hν z hz) _ using 1
  rw [div_mul_eq_mul_div]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  cases abs_cases (2 * Real.pi * C₁) <;>
    cases abs_cases (ν₁ * C₁ + C₂) <;>
      nlinarith [norm_nonneg z, Real.pi_pos]

@[blueprint
  "phi-star-bound-left"
  (title := "Bound on $\\Phi^{\\pm,\\ast}_\\nu$ from below")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_left (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by
  obtain ⟨C₁, hC₁⟩ := ϕ_circ_bound_left ν₀ ν₁ ε c hc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ‖B ε ν‖ ≤ M := by
    have hB_def : ∀ ν : ℝ, ν ≠ 0 →
        B ε ν = ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2 := by
      intros ν hν_nonzero
      simp [B, ofReal_eq_zero, hν_nonzero, coth, Complex.tanh_eq_sinh_div_cosh]
    have hB_cont : ContinuousOn
        (fun ν : ℝ => ν * (Complex.cosh (ν / 2) / Complex.sinh (ν / 2) + ε) / 2)
        (Set.Icc ν₀ ν₁) := by
      refine ContinuousOn.div_const ?_ _
      refine ContinuousOn.mul (Complex.continuous_ofReal.continuousOn)
        (ContinuousOn.add ?_ continuousOn_const)
      refine ContinuousOn.div ?_ ?_ ?_
      · fun_prop
      · fun_prop
      · norm_num [Complex.sinh]
        intro x hx₁ hx₂
        apply sub_ne_zero_of_ne
        apply ne_of_apply_ne Complex.re
        norm_num [Complex.exp_re]
        grind
    obtain ⟨M, hM⟩ := IsCompact.exists_bound_of_continuousOn
      CompactIccSpace.isCompact_Icc hB_cont
    refine ⟨M, fun ν hν => ?_⟩
    specialize hB_def ν (by linarith [hν.1])
    grind
  have hB : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      ‖B ε (-2 * Real.pi * I * z + ν)‖ ≤ (2 * Real.pi * ‖z‖ + ν₁) * C₁ := by
    intro ν hν z hz
    have hB_eq : B ε (-2 * Real.pi * I * z + ν) =
        (-2 * Real.pi * I * z + ν) * Phi_circ ν ε z := by
      unfold B Phi_circ
      split_ifs <;> simp_all [Complex.ext_iff]
      · rw [lt_div_iff₀] at hc <;> nlinarith [Real.pi_pos]
      · constructor <;> ring
    rw [hB_eq, norm_mul]
    gcongr
    · exact add_nonneg (mul_nonneg (mul_nonneg zero_le_two Real.pi_pos.le) (norm_nonneg _))
        (by linarith)
    · refine le_trans (norm_add_le _ _) ?_
      norm_num [abs_of_nonneg Real.pi_pos.le]
      cases abs_cases ν <;> linarith [hν.1, hν.2]
    · exact hC₁ ν hν z hz
  have hPhi_star_bound : ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c →
      ‖Phi_star ν ε z‖ ≤ ((2 * Real.pi * ‖z‖ + ν₁) * C₁ + M) / (2 * Real.pi) := by
    intros ν hν z hz
    have h : ‖Phi_star ν ε z‖ ≤
        (‖B ε (-2 * Real.pi * I * z + ν)‖ + ‖B ε ν‖) / (2 * Real.pi) := by
      rw [CH2.Phi_star]
      norm_num [abs_of_nonneg Real.pi_pos.le]
      bound
    exact h.trans (by gcongr <;> linarith [hB ν hν z hz, hM ν hν])
  exact ⟨((2 * Real.pi * 0 + ν₁) * C₁ + M) / (2 * Real.pi) +
    (2 * Real.pi * C₁) / (2 * Real.pi), fun ν hν z hz =>
    le_trans (hPhi_star_bound ν hν z hz) (by
      ring_nf; norm_num [Real.pi_pos.ne']
      norm_num [mul_assoc, mul_comm, mul_left_comm, Real.pi_ne_zero]
      linarith [
        show 0 ≤ C₁ from le_trans (norm_nonneg _) (hC₁ ν hν z hz),
        show 0 ≤ M from le_trans (norm_nonneg _) (hM ν hν),
        show 0 ≤ C₁ * (ν₁ * (Real.pi⁻¹ * (‖z‖ * (1 / 2)))) from
          mul_nonneg (le_trans (norm_nonneg _) (hC₁ ν hν z hz))
            (mul_nonneg (by linarith) (mul_nonneg (inv_nonneg.2 Real.pi_pos.le)
              (mul_nonneg (norm_nonneg _) (by norm_num)))),
        show 0 ≤ M * (Real.pi⁻¹ * (‖z‖ * (1 / 2))) from by
          apply mul_nonneg (le_trans (norm_nonneg _) (hM ν hν))
          positivity
      ])⟩


@[blueprint
  "B-plus-mono"
  (title := "$B^+$ is increasing")
  (statement := /--
  For real $t$, $B^+(t)$ is increasing.
  -/)
  (proof := /-- For all $t \neq 0$, by the identities $2\cosh\frac{t}{2}\sinh\frac{t}{2} = \sinh t$ and $2\sinh^2\frac{t}{2} = \cosh t - 1$,
\[
\frac{dB^{\pm}(t)}{dt} = \frac{\cosh\frac{t}{2}\sinh\frac{t}{2} - \frac{t}{2} \pm \sinh^2\frac{t}{2}}{2\sinh^2\frac{t}{2}} = \frac{\pm(e^{\pm t} - (1 \pm t))}{4\sinh^2\frac{t}{2}}.
\]
Since $e^u$ is convex, $e^u \geq 1 + u$ for all $u \in \mathbb{R}$. We apply this inequality with $u = t$ and $u = -t$ and obtain the conclusion for $t \neq 0$. Since $B^{\pm}(t)$ is continuous at $t = 0$, we are done.
. -/)
  (latexEnv := "lemma")
  (discussion := 1077)]
theorem B_plus_mono : Monotone (fun t:ℝ ↦ (B 1 t).re) := by
  have B_plus_re_eq : ∀ t : ℝ, t ≠ 0 → (B 1 (t : ℂ)).re = t * Real.exp t / (Real.exp t - 1) := by
    intro t ht
    unfold B
    unfold coth; norm_num [ Complex.tanh, Complex.exp_re, Complex.exp_im ] ; ring_nf;
    norm_num [ Complex.cosh, Complex.sinh, Complex.exp_re, Complex.exp_im, ht ] ; ring_nf;
    norm_num [ Complex.normSq, Complex.exp_re, Complex.exp_im ] ; ring_nf;
    field_simp;
    rw [ one_add_div, ← add_div, div_eq_div_iff ] <;> ring_nf <;> norm_num [ sub_ne_zero, ht, Real.exp_ne_zero ];
    · simpa [ ← Real.exp_add ] using by ring_nf;
    · cases lt_or_gt_of_ne ht <;> linarith;
    · exact fun h => ht <| by rw [ add_eq_zero_iff_eq_neg ] at h; replace h := congr_arg Real.log h; norm_num at h; linarith;
    · cases lt_or_gt_of_ne ht <;> linarith
  have f_le_one_neg : ∀ t : ℝ, t < 0 → t * Real.exp t / (Real.exp t - 1) ≤ 1 := by
    intro t ht
    rw [ div_le_iff_of_neg ] <;> nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ]
  have f_ge_one_pos : ∀ t : ℝ, 0 < t → 1 ≤ t * Real.exp t / (Real.exp t - 1) := by
    intro t ht
    rw [ le_div_iff₀ ] <;> try linarith [ Real.add_one_le_exp t ];
    nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ]
  have f_mono_pos : MonotoneOn (fun t : ℝ ↦ t * Real.exp t / (Real.exp t - 1)) (Set.Ioi 0) := by
    have h_deriv_pos : ∀ t > 0, deriv (fun t => t * Real.exp t / (Real.exp t - 1)) t ≥ 0 := by
      intro t ht; norm_num [ Real.differentiableAt_exp, ne_of_gt, ht, ne_of_gt, Real.exp_pos t, ne_of_gt, sub_pos, Real.exp_pos, ht, sub_ne_zero.mpr, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t, ne_of_gt, ht, Real.exp_pos t ];
      exact div_nonneg ( by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ] ) ( sq_nonneg _ )
    intro a ha b hb hab
    have h_mean_val : ∀ a b : ℝ, 0 < a → a < b → ∃ c ∈ Set.Ioo a b, deriv (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) c = ( (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) b - (fun t : ℝ => t * Real.exp t / (Real.exp t - 1)) a ) / (b - a) := by
      intros a b ha hb; apply_rules [ exists_deriv_eq_slope ];
      · exact continuousOn_of_forall_continuousAt fun t ht => ContinuousAt.div ( ContinuousAt.mul continuousAt_id ( Real.continuous_exp.continuousAt ) ) ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) ( sub_ne_zero_of_ne ( by linarith [ Real.add_one_le_exp t, ht.1 ] ) );
      · exact DifferentiableOn.div ( DifferentiableOn.mul differentiableOn_id ( Real.differentiable_exp.differentiableOn ) ) ( DifferentiableOn.sub ( Real.differentiable_exp.differentiableOn ) ( differentiableOn_const _ ) ) fun x hx => ne_of_gt ( by norm_num; linarith [ hx.1 ] );
    cases eq_or_lt_of_le hab
    · aesop
    obtain ⟨ c, hc₁, hc₂ ⟩ := h_mean_val a b ha ‹_›
    have := h_deriv_pos c ( lt_trans ha.out hc₁.1 )
    rw [ hc₂, ge_iff_le, le_div_iff₀ (by lia) ] at this
    linarith
  have f_mono_neg : MonotoneOn (fun t : ℝ ↦ t * Real.exp t / (Real.exp t - 1)) (Set.Iio 0) := by
    have h_deriv_nonneg : ∀ t : ℝ, t < 0 → 0 ≤ deriv (fun t => t * Real.exp t / (Real.exp t - 1)) t := by
      intro t ht; norm_num [ Real.differentiableAt_exp, ne_of_lt, ht, sub_ne_zero ];
      exact div_nonneg ( by nlinarith [ Real.exp_pos t, Real.exp_neg t, mul_inv_cancel₀ ( ne_of_gt ( Real.exp_pos t ) ), Real.add_one_le_exp t, Real.add_one_le_exp ( -t ) ] ) ( sq_nonneg _ );
    intros t ht u hu htu;
    by_contra h_contra; push_neg at h_contra; (
    obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo t u, deriv (fun t => t * Real.exp t / (Real.exp t - 1)) c = (u * Real.exp u / (Real.exp u - 1) - t * Real.exp t / (Real.exp t - 1)) / (u - t) := by
      apply_rules [ exists_deriv_eq_slope ]
      · exact htu.lt_of_ne ( by rintro rfl; linarith )
      · exact continuousOn_of_forall_continuousAt fun x hx => ContinuousAt.div ( ContinuousAt.mul continuousAt_id ( Real.continuous_exp.continuousAt ) ) ( ContinuousAt.sub ( Real.continuous_exp.continuousAt ) continuousAt_const ) ( sub_ne_zero_of_ne ( by norm_num; linarith [ hx.1, hx.2, ht.out, hu.out ] ) )
      · exact fun x hx => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.div ( differentiableAt_id.mul ( Real.differentiableAt_exp ) ) ( Real.differentiableAt_exp.sub_const _ ) ( sub_ne_zero_of_ne ( by norm_num; linarith [ hx.1, hx.2, hu.out, ht.out ] ) ) )
    rw [ eq_div_iff ] at hc <;> nlinarith [ hc.1.1, hc.1.2, h_deriv_nonneg c ( by linarith [ hc.1.1, hc.1.2, hu.out ] ) ]);
  intro t₁ t₂ ht;
  by_cases h₁ : t₁ = 0 <;> by_cases h₂ : t₂ = 0
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · grind [one_re, B, ofReal_eq_zero, ofReal_one]
  · simp only [ne_eq, B, ofReal_eq_zero, ofReal_one] at B_plus_re_eq
    simp only [B, ofReal_eq_zero, ofReal_one, h₁, h₂, ite_false, div_ofNat_re, mul_re, ofReal_re, add_re, one_re, ofReal_im, add_im, one_im]
    simp_all
    grind [MonotoneOn]

lemma B_im_eq_zero (ε : ℝ) (t : ℝ) : (B ε t).im = 0 := by
  unfold B; split
  · rw [one_im]
  · rw [coth, show (t : ℂ) / 2 = (t / 2 : ℝ) from by push_cast; ring,
      show tanh ((t / 2 : ℝ) : ℂ) = ⟨tanh (t / 2), 0⟩ from ext (tanh_ofReal_re _) (tanh_ofReal_im _)]
    simp [ofReal_im, ofReal_re]

theorem B_plus_real (t : ℝ) : (B 1 t).im = 0 := B_im_eq_zero 1 t

@[blueprint
  "B-minus-mono"
  (title := "$B^-$ is decreasing")
  (statement := /--
  For real $t$, $B^-(t)$ is decreasing.
  -/)
  (proof := /-- Similar to previous.
. -/)
  (latexEnv := "lemma")
  (discussion := 1078)]
theorem B_minus_mono : Antitone (fun t:ℝ ↦ (B (-1) t).re) := by
  have hasDerivAt_div_exp (c : ℝ) (hne : rexp c - 1 ≠ 0) :
      HasDerivAt (fun s => s / (rexp s - 1))
        ((1 * (rexp c - 1) - c * rexp c) / (rexp c - 1) ^ 2) c :=
    (hasDerivAt_id c).div (show HasDerivAt (fun s => rexp s - 1) (rexp c) c by
      have := (Real.hasDerivAt_exp c).sub (hasDerivAt_const c (1 : ℝ))
      simp only [sub_zero] at this; exact this) hne
  have deriv_nonpos (c : ℝ) (hne : rexp c - 1 ≠ 0) :
      (1 * (rexp c - 1) - c * rexp c) / (rexp c - 1) ^ 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg
      (by nlinarith [Real.exp_pos c, Real.exp_neg c,
        mul_inv_cancel₀ (ne_of_gt (Real.exp_pos c)),
        Real.add_one_le_exp c, Real.add_one_le_exp (-c)])
      (sq_nonneg _)
  have mvt_anti (t1 t2 : ℝ) (hall : ∀ x, t1 ≤ x → x ≤ t2 → rexp x - 1 ≠ 0) (hlt : t1 < t2) :
      t2 / (rexp t2 - 1) ≤ t1 / (rexp t1 - 1) := by
    obtain ⟨c, hc, hc_eq⟩ : ∃ c ∈ Set.Ioo t1 t2,
        deriv (fun s => s / (rexp s - 1)) c =
          ((fun s => s / (rexp s - 1)) t2 - (fun s => s / (rexp s - 1)) t1) / (t2 - t1) := by
      rw [show (fun s => s / (rexp s - 1)) = (_root_.id / fun x => rexp x - 1) from by
        ext x; simp [_root_.id]]
      exact exists_deriv_eq_slope _ hlt
        (ContinuousOn.div continuousOn_id
          (ContinuousOn.sub Real.continuous_exp.continuousOn continuousOn_const)
          (fun x hx => hall x hx.1 hx.2))
        (DifferentiableOn.div differentiableOn_id
          (DifferentiableOn.sub Real.differentiable_exp.differentiableOn (differentiableOn_const _))
          (fun x hx => hall x (le_of_lt hx.1) (le_of_lt hx.2)))
    have hne := hall c (le_of_lt hc.1) (le_of_lt hc.2)
    rw [(hasDerivAt_div_exp c hne).deriv] at hc_eq
    have := deriv_nonpos c hne; rw [hc_eq] at this
    cases div_nonpos_iff.mp this with
    | inl h => linarith [h.1] | inr h => linarith [h.2]
  have exp_sub_pos (x : ℝ) (hx : 0 < x) : rexp x - 1 > 0 := by linarith [Real.add_one_le_exp x]
  have exp_sub_neg (x : ℝ) (hx : x < 0) : rexp x - 1 < 0 := by
    nlinarith [Real.exp_pos x, Real.exp_neg x,
      mul_inv_cancel₀ (ne_of_gt (Real.exp_pos x)), Real.add_one_le_exp (-x)]
  have div_exp_le_one (t : ℝ) (ht : 0 < t) : t / (rexp t - 1) ≤ 1 := by
    rw [div_le_iff₀ (exp_sub_pos t ht)]; linarith [Real.add_one_le_exp t]
  have div_exp_ge_one (t : ℝ) (ht : t < 0) : 1 ≤ t / (rexp t - 1) := by
    rw [le_div_iff_of_neg (exp_sub_neg t ht)]
    nlinarith [Real.exp_pos t, Real.exp_neg t,
      mul_inv_cancel₀ (ne_of_gt (Real.exp_pos t)),
      Real.add_one_le_exp t, Real.add_one_le_exp (-t)]
  suffices heq : (fun t:ℝ ↦ (B (-1) t).re) =
      fun t : ℝ => if t = 0 then (1 : ℝ) else t / (rexp t - 1) by
    rw [heq]; intro a b hab
    rcases eq_or_lt_of_le hab with rfl | hlt; · rfl
    simp only
    by_cases ha0 : a = 0
    · subst ha0; simp only [ite_true, show ¬b = 0 from by linarith, ite_false]
      exact div_exp_le_one b (by linarith)
    · by_cases hb0 : b = 0
      · subst hb0; simp only [ite_true, ha0, ite_false]
        exact div_exp_ge_one a (lt_of_le_of_ne (not_lt.mp (fun h => ha0 (by linarith))) ha0)
      · simp only [ha0, hb0, ite_false]
        by_cases hpos : 0 < a
        · exact mvt_anti a b (fun x hxa hxb => ne_of_gt (exp_sub_pos x (by linarith))) hlt
        · push_neg at hpos
          have ha_neg : a < 0 := lt_of_le_of_ne hpos ha0
          by_cases hneg : b < 0
          · exact mvt_anti a b (fun x hxa hxb => ne_of_lt (exp_sub_neg x (by linarith))) hlt
          · push_neg at hneg
            have hb_pos : 0 < b := lt_of_le_of_ne hneg (Ne.symm hb0)
            linarith [div_exp_le_one b hb_pos, div_exp_ge_one a ha_neg]
  funext t; split
  · next h => subst h; unfold B; simp
  · next ht =>
    unfold B coth
    have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    simp only [ht', ↓reduceIte, one_div]
    rw [show ((-1 : ℝ) : ℂ) = -1 from by push_cast; ring]
    conv_lhs => rw [show (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) from by push_cast; ring]
    rw [show Complex.tanh ((t / 2 : ℝ) : ℂ) = ((Real.tanh (t / 2) : ℝ) : ℂ) from by
        apply Complex.ext <;> simp,
      show ((Real.tanh (t / 2) : ℝ) : ℂ)⁻¹ = ((Real.tanh (t / 2))⁻¹ : ℝ) from by push_cast; ring,
      show (↑t * (↑(Real.tanh (t / 2))⁻¹ + (-1 : ℂ)) / 2 : ℂ) =
        ((t * ((Real.tanh (t / 2))⁻¹ + (-1 : ℝ)) / 2 : ℝ) : ℂ) from by push_cast; ring]
    simp only [Complex.ofReal_re]; rw [Real.tanh_eq]
    have h2 : rexp (t / 2) - rexp (-(t / 2)) ≠ 0 := by
      intro h; exact ht (by linarith [Real.exp_injective (show rexp (t/2) = rexp (-(t/2)) by linarith)])
    have h3 : rexp t - 1 ≠ 0 := by
      intro h; exact ht ((Real.exp_eq_one_iff t).mp (by linarith))
    rw [inv_div]; field_simp
    nlinarith [show rexp t = rexp (t / 2) * rexp (t / 2) by rw [← Real.exp_add]; ring_nf,
      show rexp (t / 2) * rexp (-(t / 2)) = 1 by rw [← Real.exp_add]; simp,
      Real.exp_pos (t/2), Real.exp_pos (-(t/2))]

theorem B_minus_real (t : ℝ) : (B (-1) t).im = 0 := B_im_eq_zero (-1) t

noncomputable def E (z : ℂ) : ℂ := Complex.exp (2 * π * I * z)

@[blueprint
  "varphi-fourier-ident"
  (title := "Fourier transform of $\\varphi$")
  (statement := /--
\[
\widehat{\varphi^{\pm}_{\nu}}(x) = \int_{-1}^{1} \varphi^{\pm}_{\nu}(t)\, e(-tx)\, dt = \int_{-1}^{0} \bigl(\Phi^{\pm,\circ}_{\nu}(t) - \Phi^{\pm,\star}_{\nu}(t)\bigr) e(-tx)\, dt + \int_0^1 \bigl(\Phi^{\pm,\circ}_{\nu}(t) + \Phi^{\pm,\star}_{\nu}(t)\bigr) e(-tx)\, dt.
\]
  -/)
  (proof := /-- By the definition of the Fourier transform, and the fact that $\varphi^{\pm}_{\nu}$ is supported on $[-1,1]$. -/)
  (latexEnv := "sublemma")
  (discussion := 1079)]
theorem varphi_fourier_ident (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) :
    𝓕 (ϕ_pm ν ε) x = ∫ t in Set.Icc (-1:ℝ) 0, ((Phi_circ ν ε t - Phi_star ν ε t) * (E (-t * x))) +
    ∫ t in Set.Icc 0 (1:ℝ), ((Phi_circ ν ε t + Phi_star ν ε t) * (E (-t * x))) := by
    sorry

@[blueprint
  "shift-upwards"
  (title := "Contour shifting upwards")
  (statement := /-- If $x < 0$, then
\begin{equation}\label{eq:1.5}
\widehat{\varphi^{\pm}_{\nu}}(x) = \int_{-1+i\infty}^{-1} \bigl(\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz + \int_{1}^{1+i\infty} \bigl(\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz + 2\int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\end{equation}
  -/)
  (proof := /-- Since $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ has no poles in the upper half plane, we can shift contours upwards, as we may: for $\Im z \to \infty$, $e(-zx) = e^{-2\pi i z x}$ decays exponentially on $\Im z$, while, by Lemma~1.3, $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ grows at most linearly, and so the contribution of a moving horizontal segment goes to $0$ as $\Im z \to \infty$. -/)
  (latexEnv := "sublemma")
  (discussion := 1080)]
theorem shift_upwards (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (-1 + I * t) - Phi_star ν ε (-1 + I * t)) * E (-(-1 + I * ↑t) * x) - I *
    ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (1 + I * t) + Phi_star ν ε (1 + I * t)) * (E (-(1 + I * ↑t) * x))) +
    2 * ∫ t in Set.Icc 0 T, (Phi_star ν ε (I * t) * E (-(I * ↑t) * x)))) (nhds (𝓕 (ϕ_pm ν ε) x)) := by
    sorry

@[blueprint
  "B-affine-periodic"
  (title := "$B^\\pm$ affine periodic")
  (statement := /-- For any integer $m$,
$$ B^\pm(w(z-m)) = B^\pm(w(z) + 2\pi i m) = B^\pm(w(z)) + 2\pi i m\, \Phi^{\pm,\circ}_{\nu}(z). $$
    -/)
  (proof := /-- This follows from the $\pi i$-periodicity of coth. -/)
  (latexEnv := "sublemma")
  (discussion := 1081)]
theorem B_affine_periodic (ν ε : ℝ) (_hν : ν > 0) (z : ℂ) (m : ℤ)
    (hw : -2 * π * I * z + ν ≠ 0)
    (hwm : -2 * π * I * (z - m) + ν ≠ 0) :
    B ε (-2 * π * I * (z - m) + ν) =
      B ε (-2 * π * I * z + ν) + 2 * π * I * m * Phi_circ ν ε z := by
  unfold B Phi_circ coth
  have h_tanh_periodic :
      Complex.tanh ((-2 * Real.pi * I * (z - m) + ν) / 2) =
        Complex.tanh ((-2 * Real.pi * I * z + ν) / 2) := by
    rw [Complex.tanh_eq_sinh_div_cosh, Complex.tanh_eq_sinh_div_cosh]
    ring_nf; norm_num [Complex.sinh, Complex.cosh]; ring_nf
    norm_num [Complex.exp_add, Complex.exp_sub]; ring_nf
    have hexp : Complex.exp (Real.pi * I * m) = (-1) ^ m := by
      rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]; ring_nf
    norm_num [hexp]; ring_nf
    rcases Int.even_or_odd' m with ⟨k, rfl | rfl⟩ <;>
      norm_num [zpow_add₀, zpow_mul]
    ring_nf; norm_num [Complex.exp_ne_zero] at *
    rw [show -(Complex.exp (-(Real.pi * I * z)) * Complex.exp (ν * (1 / 2))) -
          Complex.exp (Real.pi * I * z) * Complex.exp (-(ν * (1 / 2))) =
        -(Complex.exp (-(Real.pi * I * z)) * Complex.exp (ν * (1 / 2)) +
          Complex.exp (Real.pi * I * z) *
            Complex.exp (-(ν * (1 / 2)))) from by ring,
      inv_neg]
    ring
  grind

@[blueprint
  "phi_star-affine-periodic"
  (title := "$\\Phi^{\\pm,\\ast}_\\nu$ affine periodic")
  (statement := /-- For any integer $m$,
$$ \Phi^{\pm,\star}_{\nu}(z-m) = \Phi^{\pm,\star}_{\nu}(z) + m\, \Phi^{\pm,\circ}_{\nu}(z). $$
    -/)
  (proof := /-- Follows from previous lemma. -/)
  (latexEnv := "sublemma")
  (discussion := 1082)]
theorem phi_star_affine_periodic (ν ε : ℝ) (hν : ν > 0) (z : ℂ) (m : ℤ)
    (hw : -2 * π * I * z + ν ≠ 0)
    (hwm : -2 * π * I * (z - m) + ν ≠ 0) :
    Phi_star ν ε (z - m) = Phi_star ν ε z + m * Phi_circ ν ε z := by
  have hB := B_affine_periodic ν ε hν z m hw hwm
  have h_sub : Phi_star ν ε (z - m) =
      (B ε (-2 * Real.pi * I * z + ν) +
        2 * Real.pi * I * m * Phi_circ ν ε z - B ε ν) /
      (2 * Real.pi * I) := by
    rw [Phi_star, hB]
  have h_def : Phi_star ν ε z =
      (B ε (-2 * Real.pi * I * z + ν) - B ε ν) /
      (2 * Real.pi * I) := by
    simp [Phi_star]
  rw [h_sub, h_def]
  field_simp
  ring

@[blueprint
  "shift-upwards-simplified"
  (title := "Simplified formula for upward contour shift")
  (statement := /-- If $x < 0$, then $\widehat{\varphi^{\pm}_{\nu}}(x)$ equals
$$
\frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
$$
  -/)
  (proof := /-- We have $\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z) = -\Phi^{\pm,\star}_{\nu}(z+1)$ and $\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z) = \Phi^{\pm,\star}_{\nu}(z-1)$, and so the formula in the previous lemma simplifies to
\begin{align*}
&2\int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z-1)x)\, dz - \int_0^{i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z+1)x)\, dz\\
&= (2 - e(x) - e(-x)) \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(\frac{iy}{2\pi}\right) e\!\left(\frac{xy}{2\pi}\right)\, dy = \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
\end{align*}
  -/)
  (latexEnv := "sublemma")
  (discussion := 1083)]
theorem shift_upwards_simplified (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν + t) - B ε ν) * Real.exp (x * t))) (nhds (𝓕 (ϕ_pm ν ε) x)) := by
    sorry

@[blueprint
  "shift-downwards"
  (title := "Contour shifting downwards")
  (statement := /-- If $x > 0$, then
\begin{align}\label{eq:1.6}
\widehat{\varphi^{\pm}_{\nu}}(x) &= \left(\int_{-1}^{-1-i\infty} + \int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}}\right) \bigl(\Phi^{\pm,\circ}_{\nu}(z) - \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz \notag\\
&\quad + \int_{-\frac{1}{2}}^{\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz - \int_{-\frac{1}{2}}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz + \int_0^{\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz \notag\\
&\quad + \left(\int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} + \int_{1-i\infty}^{1}\right) \bigl(\Phi^{\pm,\circ}_{\nu}(z) + \Phi^{\pm,\star}_{\nu}(z)\bigr) e(-zx)\, dz.
\end{align}
  -/)
  (proof := /-- We would like to integrate along $\Re z = 0$, but $\Phi^{\pm,\circ}_{\nu}(z)$ has a pole at $z = -\frac{i\nu}{2\pi}$; when dealing with this issue, we have to take care not to introduce poles on the lines $\Re z = -1$ and $\Re z = 1$ by separating $\Phi^{\pm,\circ}_{\nu}$ and $\Phi^{\pm,\star}_{\nu}$ prematurely. As $\Im z \to -\infty$, $e(-zx) = e^{-2\pi i z x}$ decays exponentially on $\Im z$, while, by Lemma~1.3, $\Phi^{\pm,\circ}_{\nu}(z) \pm \Phi^{\pm,\star}_{\nu}(z)$ grows at most linearly. -/)
  (latexEnv := "sublemma")
  (discussion := 1084)]
theorem shift_downwards (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (-1 - I * t) - Phi_star ν ε (-1 -  I * t)) * E (-(-1 - I * t) * x)) + I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (-1/2 - I * t) - Phi_star ν ε (-1/2 - I * t)) * E (-(-1/2 - I * t) * x)) + ∫ t in Set.Icc (-1/2:ℝ) (1/2:ℝ), (Phi_circ ν ε t * E (-t * x)) - ∫ t in Set.Icc (-1/2:ℝ) 0, (Phi_star ν ε t * E (-t * x)) + ∫ t in Set.Icc 0 (1/2:ℝ), (Phi_star ν ε t * E (-t * x)) - I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (1/2 - I * t) - Phi_star ν ε (1/2 - I * t)) * E (- (1/2 - I * t) * x)) + I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (1 - I * t) + Phi_star ν ε (1 - I * t)) * E (- (1 - I * t) * x))) (nhds (𝓕 (ϕ_pm ν ε) x)) := by
    sorry

@[blueprint
  "first-contour-limit"
  (title := "First contour limit")
  (statement := /--
\[
\int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz + \int_{-\frac{1}{2}}^{\frac{1}{2}} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz + \int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} \Phi^{\pm,\circ}_{\nu}(z)\, e(-zx)\, dz = e\!\left(-\!\left(-\frac{i\nu}{2\pi}\right)x\right) = e^{-\nu x}
\]
  -/)
  (proof := /-- since the pole is at $-\frac{i\nu}{2\pi}$, the residue of $\Phi^{\pm,\circ}_{\nu}(z)$ at the pole is $\frac{i}{2\pi}$, and our path goes clockwise.
. -/)
  (latexEnv := "sublemma")
  (discussion := 1085)]
theorem first_contour_limit (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (-1/2 - I * t)) * E (-(-1/2 - I * ↑t) * x)) + ∫ t in Set.Icc (-1/2:ℝ) (1/2:ℝ), (Phi_circ ν ε t * E (-t * x)) + I * ∫ t in Set.Icc 0 T, ((Phi_circ ν ε (1/2 - I * t)) * E (- (1/2 - I * ↑t) * x))) (nhds (Complex.exp (-ν * x))) := by
    sorry

@[blueprint
  "second-contour-limit"
  (title := "Second contour limit")
  (statement := /--
\[
-\int_{-\frac{1}{2}-i\infty}^{-\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_{-\frac{1}{2}}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz = \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\]
  -/)
  (proof := /-- Again by Cauchy's theorem and decay as $\Im z \to -\infty$ -/)
  (latexEnv := "sublemma")
  (discussion := 1086)]
theorem second_contour_limit (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (-1/2 - I * t)) * E (-(-1/2 - I * ↑t) * x)) - I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (I * t)) * E (-(I * ↑t) * x)) - (I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (I * t)) * E (-(I * ↑t) * x)))) (nhds 0) := by
    sorry

@[blueprint
  "third-contour-limit"
  (title := "Third contour limit")
  (statement := /--
\[
\int_0^{\frac{1}{2}} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz + \int_{\frac{1}{2}}^{\frac{1}{2}-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz = -\int_{-i\infty}^{0} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz.
\]
  -/)
  (proof := /-- Similar to previous. -/)
  (latexEnv := "sublemma")
  (discussion := 1087)]
theorem third_contour_limit (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ ∫ t in Set.Icc 0 (1/2:ℝ), (Phi_star ν ε t * E (-t * x)) + I * ∫ t in Set.Icc 0 T, ((Phi_star ν ε (1/2 - I * t)) * E (- (1/2 - I * ↑t) * x))) (nhds 0) := by
    sorry

@[blueprint
  "shift-downwards-simplified"
  (title := "Simplified formula for downward contour shift")
  (statement := /--
If $x > 0$, then $\widehat{\varphi^{\pm}_{\nu}}(x) - e^{-\nu x}$ equals
$$ - \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu) - B^{\pm}(\nu - y))\, e^{-xy}\, dy. $$
  -/)
  (proof := /-- \begin{align*}
&2\int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-zx)\, dz - \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z-1)x)\, dz - \int_0^{-i\infty} \Phi^{\pm,\star}_{\nu}(z)\, e(-(z+1)x)\, dz\\
&= (2 - e(x) - e(-x)) \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(-\frac{iy}{2\pi}\right) e\!\left(-\frac{yx}{2\pi i}\right) d\!\left(-\frac{iy}{2\pi}\right)\\
&= -\frac{2i}{\pi}\sin^2 \pi x \int_0^{\infty} \Phi^{\pm,\star}_{\nu}\!\left(-\frac{iy}{2\pi}\right) e^{-xy}\, dy = -\frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu - y) - B^{\pm}(\nu))\, e^{-xy}\, dy.
\end{align*}
 -/)
  (latexEnv := "sublemma")
  (discussion := 1088)]
theorem shift_downwards_simplified (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν - t) - B ε ν) * Real.exp (-x * t))) (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x))) := by
    sorry

@[blueprint
  "fourier-formula-neg"
  (title := "Fourier formula for negative $x$")
  (statement := /--
Let $\nu > 0$, $x < 0$. Then
$$
\widehat{\varphi^{\pm}_{\nu}}(x) - I_{\nu}(x) = \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu + y) - B^{\pm}(\nu))\, e^{xy}\, dy.
$$
  -/)
  (proof := /-- This follows from the previous lemma. -/)
  (latexEnv := "lemma")
  (discussion := 1089)]
theorem fourier_formula_neg (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x < 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν + t) - B ε ν) * Real.exp (x * t))) (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x))) := by
    sorry

@[blueprint
  "fourier-formula-pos"
  (title := "Fourier formula for positive $x$")
  (statement := /--
Let $\nu > 0$, $x > 0$. Then
$$
\widehat{\varphi^{\pm}_{\nu}}(x) - e^{-\nu x} = - \frac{\sin^2 \pi x}{\pi^2} \int_0^{\infty} (B^{\pm}(\nu) - B^{\pm}(\nu - y))\, e^{-xy}\, dy.
$$
  -/)
  (proof := /-- This follows from the previous lemma. -/)
  (latexEnv := "lemma")
  (discussion := 1090)]
theorem fourier_formula_pos (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) (hx : x > 0) :
    Filter.atTop.Tendsto (fun T:ℝ ↦ - (Real.sin (π * x))^2 / π^2 * ∫ t in Set.Icc 0 T, ((B ε (ν - t) - B ε ν) * Real.exp (-x * t))) (nhds (𝓕 (ϕ_pm ν ε) x - Complex.exp (-ν * x))) := by
    sorry

@[blueprint
  "fourier-real"
  (title := "Fourier transform of $\\varphi$ real")
  (statement := /--
$\widehat{\varphi^{\pm}_{\nu}}(x)$ is real.
  -/)
  (proof := /-- This follows from the symmetries of $\varphi^{\pm}_{\nu}$. -/)
  (latexEnv := "lemma")
  (discussion := 1225)]
theorem fourier_real (ν ε : ℝ) (hlam : ν ≠ 0) (x : ℝ) : (𝓕 (ϕ_pm ν ε) x).im = 0 := by
    sorry

@[blueprint
  "Inu_def"
  (title := "Definition of $I_\\nu$")
  (statement := /-- For $\nu > 0$, define $I_\nu(x) := 1_{[0,\infty)}(x) e^{-\nu x}$. -/)]
noncomputable def I (ν : ℝ) (x : ℝ) : ℝ := if 0 ≤ x then Real.exp (-ν * x) else 0

@[blueprint
  "Inu_bounds"
  (title := "Bound for $I_\\nu$")
  (statement := /--
For all $x \in \mathbb{R}$,
$$
    \widehat{\varphi_\nu^-}(x) \leq I_\nu(x) \leq \widehat{\varphi_\nu^+}(x).
$$-/)
  (proof := /-- By Lemmas \ref{B-plus-mono}, \ref{B-minus-mono}, the integrands in Lemmas \ref{fourier-formula-neg}, \ref{fourier-formula-pos} are non-negative. Hence, the bound holds for all $x \neq 0$. By definition, $I_\nu$ is right-continuous. Since $\varphi_\nu^\pm \in L^1(\mathbb{R})$, $\widehat{\varphi_\nu^\pm}$ is continuous on $\mathbb{R}$. Thus, letting $x \to 0^+$, we see that the bound holds for $x = 0$ as well.  -/)
  (latexEnv := "corollary")
  (discussion := 1224)]
theorem Inu_bounds (ν x : ℝ) (hν : ν > 0) :
    (𝓕 (ϕ_pm ν (-1)) x).re ≤ I ν x ∧ I ν x ≤ (𝓕 (ϕ_pm ν 1) x).re := by
    sorry

@[blueprint
  "varphi-abs"
  (title := "$\\varphi$ absolutely continuous")
  (statement := /-- The function $\varphi_\nu^\pm$ is absolutely continuous. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $\varphi_\nu^\pm$ is absolutely continuous because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1226)]
theorem varphi_abs (ν ε : ℝ) (hlam : ν ≠ 0) : AbsolutelyContinuous (ϕ_pm ν ε) := by
    sorry

@[blueprint
  "varphi-integ"
  (title := "$\\varphi$ integrable")
  (statement := /-- The function $\varphi_\nu^\pm$ is integrable. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $\varphi_\nu^\pm$ is integrable because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1227)]
theorem varphi_integ (ν ε : ℝ) (hlam : ν ≠ 0) : Integrable (ϕ_pm ν ε) := by
    sorry

@[blueprint
  "varphi-deriv-integ"
  (title := "$\\varphi'$ integrable")
  (statement := /-- The function $(\varphi_\nu^\pm)'$ is integrable. -/)
  (proof := /-- Apply Lemmas \ref{phi-c2-left}, \ref{phi-c2-right}, \ref{phi-cts} We know $(\varphi_\nu^\pm)'$ is integrable because it is $C^1$ on $[-1, 0]$ and $[0, 1]$, and identically $0$ outside $[-1, 1]$./
-/)
  (latexEnv := "lemma")
  (discussion := 1228)]
theorem varphi_deriv_integ (ν ε : ℝ) (hlam : ν ≠ 0) : Integrable (deriv (ϕ_pm ν ε)) := by
    sorry

@[blueprint
  "varphi-deriv-tv"
  (title := "$\\varphi'$ total variation")
  (statement := /-- The function $(\varphi_\nu^\pm)'$ has finite total variation. -/)
  (proof := /-- Since $(\varphi_\nu^\pm)'$ is $C^1$ on $[-1, 0]$ and on $[0, 1]$, the $L^1$ norm of $(\varphi_\nu^\pm)''$ on each of these intervals is finite, and so $(\varphi_\nu^\pm)'$ has finite total variation on each of them. As $(\varphi_\nu^\pm)'$ has right and left limits at $-1$, $0$ and $1$, the jumps at those points are finite, and so their contribution to $\|(\varphi_\nu^\pm)'\|_{\mathrm{TV}}$ is finite.
/
-/)
  (latexEnv := "lemma")
  (discussion := 1229)]
theorem varphi_deriv_tv (ν ε : ℝ) (hlam : ν ≠ 0) : BoundedVariationOn (deriv (ϕ_pm ν ε)) Set.univ := by
    sorry

@[blueprint
  "varphi-fourier-decay"
  (title := "$\\varphi$ Fourier decay")
  (statement := /-- For $|x| \to \infty$, $\widehat{\varphi_\nu^\pm}(x) = O(1/x^2)$. -/)
  (proof := /-- For $f$ absolutely continuous with $f, f' \in L^1(\mathbb{R})$, integration by parts gives us that $\hat{f}(x) = \widehat{f'}(x)/(2\pi i x)$. If $f' \in L^1(\mathbb{R})$ with $\|f'\|_{\mathrm{TV}} < \infty$, then, again by integration by parts, $|\widehat{f'}(x)| \leq |f'|_{\mathrm{TV}}/(2\pi x)$. We are done by the preceding lemmas. -/)
  (latexEnv := "corollary")
  (discussion := 1230)]
theorem varphi_fourier_decay (ν ε : ℝ) (hlam : ν ≠ 0) : IsBigO Filter.atTop (fun x:ℝ ↦ (𝓕 (ϕ_pm ν ε) x).re) (fun x:ℝ ↦ 1 / x ^ 2)  := by
    sorry

@[blueprint
  "varphi-fourier-minus-error"
  (title := "$L^1$ error bound for Fourier transform of $\\varphi^-$")
  (statement := /--
\[
\int_{-\infty}^{\infty} (I_\nu(x) - \hat{\varphi_\nu^-}(x))\, dx = \frac{1}{\nu} - \frac{1}{e^\nu - 1}.
\]
  -/)
  (proof := /--
  We know that $\varphi_\nu^\pm$ is continuous and in $L^1(\mathbb{R})$; by Corollary \ref{varphi-fourier-decay}, $\widehat{\varphi_\nu^\pm}$ is in $L^1(\mathbb{R})$. Hence, Fourier inversion holds everywhere, and in particular for $t = 0$:
\[
\varphi_\nu^\pm(0) = \int_{-\infty}^{\infty} \widehat{\varphi_\nu^\pm}(x)\, dx.
\]
By definition, $\varphi_\nu^\pm(0) = \Phi_\nu^{\pm,\circ}(0)$, and, by definition, $\Phi_\nu^{-,\circ}(0) = \frac{1}{e^\nu - 1}$ and $\Phi_\nu^{+,\circ}(0) = \frac{1}{1 - e^{-\nu}}$. Thus,
\[
\int_{-\infty}^{\infty} (I_\nu(x) - \widehat{\varphi_\nu^-}(x))\, dx = \frac{1}{\nu} - \frac{1}{e^\nu - 1},
\]
\[
\int_{-\infty}^{\infty} (\widehat{\varphi_\nu^+}(x) - I_\nu(x))\, dx = \frac{1}{1 - e^{-\nu}} - \frac{1}{\nu},
\]
since $\int_{-\infty}^{\infty} I_\nu(x)\, dx = 1/\nu$. We are done by Corollary \ref{Inu_bounds}.
-/)
  (latexEnv := "proposition")
  (discussion := 1231)]
theorem varphi_fourier_minus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, (I ν x - (𝓕 (ϕ_pm ν (-1)) x).re) = 1 / ν - 1 / (Real.exp ν - 1) := by
    sorry

@[blueprint
  "varphi-fourier-plus-error"
  (title := "$L^1$ error bound for Fourier transform of $\\varphi^+$")
  (statement := /--
\[
\int_{-\infty}^{\infty} (\hat{\varphi_\nu^+}(x) - I_\nu(x))\, dx = \frac{1}{1 - e^{-\nu}} - \frac{1}{\nu}.
\]
  -/)
  (proof := /-- See previous. -/)
  (latexEnv := "proposition")
  (discussion := 1232)]
theorem varphi_fourier_plus_error (ν : ℝ) (hν : ν > 0) :
    ∫ x in Set.univ, ((𝓕 (ϕ_pm ν 1) x).re - I ν x) = 1 / (1 - Real.exp (-ν)) - 1 / ν := by
    sorry

@[blueprint
  "CH2-lemma-4-2a"
  (title := "CH2 Lemma 4.2(a)")
  (statement := /--
If $|\Im z| \leq \frac{\pi}{4}$, then $|(z \coth z)'| < 1$.  -/)
  (proof := /-- Since $z\coth(z)$ is regular at $0$ and an even function, we see that $f(z) := (z \coth z)'$ and $f(z)/z$ are regular at $0$, and hence analytic on the strip $|\Im z| \leq \frac{\pi}{2}$. We see from $f(z) = \coth z - z\operatorname{csch}^2 z$ that $f(z)$ has at most exponential growth as $\Re z \to \pm\infty$ within the strip. Hence, by Phragm\'{e}n--Lindel\"{o}f, it is enough to verify the inequalities $|f(z)/z| \leq 1$ for $\Im z = \pm\frac{\pi}{2}$ and $|f(z)| \leq 1$ for $\Im z = \pm\frac{\pi}{4}$; by complex conjugation, it suffices to check them for $\Im z = \frac{\pi}{2}$ and $\Im z = \frac{\pi}{4}$.

By the above, $f(z) = \frac{(\sinh 2z)/2 - z}{\sinh^2 z}$. Now, for $z = x + i\frac{\pi}{4}$ with $x \in \mathbb{R}$, we have $\sinh 2z = i\cosh 2x$ and $\sinh^2 z = -\frac{1}{2} + \frac{i}{2}\sinh 2x$, and so $|f(z)|^2 = \frac{(\cosh 2x - \pi/2)^2 + 4x^2}{1 + \sinh^2 2x}$. By $1 + \sinh^2 2x = \cosh^2 2x$,
\[
|f(z)|^2 = 1 - \frac{\pi \cosh 2x - \pi^2/4 - 4x^2}{\cosh^2 2x}.
\]
Since $\cosh 2x = 1 + 2\sinh^2 x \geq 1 + 2x^2$, $\pi > \frac{\pi^2}{4}$ and $2\pi > 4$, the numerator here is positive. We conclude that $|f(z)|^2 < 1$ for $z = x + i\frac{\pi}{4}$, as was desired.

For $z = x + i\frac{\pi}{2}$ with $x \in \mathbb{R}$, we have $\coth z = \tanh x$ and $\operatorname{csch}^2 z = -\operatorname{sech}^2 x$. Then $|f(z)|^2 = (\tanh x + x\operatorname{sech}^2 x)^2 + \left(\frac{\pi}{2}\operatorname{sech}^2 x\right)^2$. Since $\operatorname{sech}^2 x - 1 = -\tanh^2 x$, this is equal to
\[
\tanh^2 x \operatorname{sech} x\!\left(\cosh x + 2x\operatorname{csch} x - |z|^2(\operatorname{sech} x + \cosh x)\right) + |z|^2.
\]
Since $|z|^2 \geq \frac{\pi^2}{4} > 2$, it suffices to show that $2x\operatorname{csch} x - 2\operatorname{sech} x - \cosh x \leq 0$ for all $x \in \mathbb{R}$; by parity, it is enough to check all $x \geq 0$. The statement is then equivalent to $g(x) = 2x - 2\tanh x - \sinh x \cosh x \leq 0$, since $\sinh x \geq 0$. That follows from $g'(x) = 2\tanh^2 x - \cosh^2 x - \sinh^2 x = -2\sinh^2 x \tanh^2 x - 1 \leq 0$ (by $1 - \cosh^2 x = -\sinh^2 x$) and $g(0) = 0$.
-/)
  (latexEnv := "sublemma")
  (discussion := 1233)]
theorem CH2_lemma_4_2a (z : ℂ) (hz : |z.im| ≤ π / 4) : ‖deriv (fun z:ℂ ↦ z * coth z) z‖ < 1 := by
    sorry

@[blueprint
  "CH2-lemma-4-2b"
  (title := "CH2 Lemma 4.2(b)")
  (statement := /--
If $|\Im z| \leq \frac{\pi}{2}$, then $|(z \coth z)'| \leq |z|$. -/)
  (proof := /-- See previous. -/)
  (latexEnv := "sublemma")
  (discussion := 1234)]
theorem CH2_lemma_4_2b (z : ℂ) (hz : |z.im| ≤ π / 2) : ‖deriv (fun z:ℂ ↦ z * coth z) z‖ ≤ ‖z‖ := by
    sorry



/-
\begin{lemma}
Let $\Phi^{\pm,\circ}_\nu(z)$ and $\Phi^{\pm,\star}_\nu(z)$ be as in \eqref{eq:defPhi} for $\nu > 0$. Then:
\begin{itemize}
    \item $\Phi^{\pm,\circ}_\nu(z)$ is a meromorphic function whose poles, all of them simple, are at $n - \frac{i\nu}{2\pi}$, $n \in \mathbb{Z}$; the residue at every pole is $\frac{i}{2\pi}$. Moreover, $\Phi^{\pm,\circ}_\nu(z) = \overline{\Phi^{\pm,\circ}_\nu(-\bar{z})}$.
    \item $\Phi^{\pm,\star}_\nu(z)$ is a meromorphic function whose poles, all of them simple, are at $n - \frac{i\nu}{2\pi}$, $n \in \mathbb{Z} \setminus \{0\}$; the residue at $n - \frac{i\nu}{2\pi}$ is $-\frac{in}{2\pi}$. Moreover, $\Phi^{\pm,\star}_\nu(z) = -\overline{\Phi^{\pm,\star}_\nu(-\bar{z})}$.
\end{itemize}
On every region $\{z : \Im z \geq c\}$, $c > -\frac{\nu}{2\pi}$, or $\{z : \Im z \leq c\}$, $c < -\frac{\nu}{2\pi}$, the function $\Phi^{\pm,\circ}_\nu(z)$ is bounded and $\Phi^{\pm,\star}_\nu(z) = O(|z| + 1)$. Moreover, these bounds hold uniformly for all $\nu$ in an interval $[\nu_0, \nu_1]$, with conditions $c > -\frac{\nu_0}{2\pi}$, $c < -\frac{\nu_1}{2\pi}$, respectively.

We have $\Phi^{\sigma,\star}_\nu(0) = 0$. For $z$ with $0 \leq \Re z \leq \frac{1}{4}$, and for either sign $\sigma = \pm$,
\[
\left|(\Phi^{\pm,\star}_\nu)'(z)\right| \leq 1, \quad |\Phi^{\sigma,\star}_\nu(\pm z)| \leq |z|, \quad |(\Phi^{\sigma,\circ}_\nu \pm \Phi^{\sigma,\star}_\nu)(\pm 1 \mp z)| \leq |z|.
\]
Moreover, for $z$ purely imaginary, $(\Phi^{\sigma,\star}_\nu)'(\pm z)$, which is purely real, is of constant sign.

Note that $\Phi^{\sigma,\circ}_\nu(z) \pm \Phi^{\sigma,\star}_\nu(z)$ is regular at $\pm 1 - \frac{i\nu}{2\pi}$, since the residues cancel out.

Our convention is that all signs denoted by $\pm$ in the same equation are the same, $\mp$ is the opposite sign, and $\sigma$ denotes a sign that may or may not be the same.
\end{lemma}

\begin{proof}
The statements on poles and residues follow directly from \eqref{eq:defPhi}; so do the statements on $\overline{\Phi^{\pm,\circ}_\nu(z)}$ and $\overline{\Phi^{\pm,\star}_\nu(z)}$. The statements on the boundedness of $\Phi^{\sigma,\circ}_\nu(z)$ and the growth of $\Phi^{\sigma,\star}_\nu(z)$ follow from \eqref{eq:defPhi} and the fact that $\coth(w)$ is bounded on $\Re w \geq c$ for $c > 0$ arbitrary and on $\Re w \leq c$ for $c < 0$ arbitrary. Since $|\Phi^{\sigma,\star}_\nu(-z)| = |\Phi^{\sigma,\star}_\nu(z)|$ and $|(\Phi^{\sigma,\circ}_\nu - \Phi^{\sigma,\star}_\nu)(-1 + z)| = |(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)|$, it is left to check that $|\Phi^{\sigma,\star}_\nu(z)| \leq |z|$ and $|(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)| \leq |z|$.

By \eqref{eq:defPhi}, $\Phi^{\pm,\star}_\nu(0) = 0$ and $(\Phi^{\pm,\star}_\nu)'(z) = -\frac{d}{dw}\!\left(\frac{w}{2}\coth\frac{w}{2}\right) \mp \frac{1}{2}$ at $w = -2\pi iz + \nu$. Hence, for $0 \leq \Re z \leq \frac{1}{4}$, by Lemma~4.2, $|(\Phi^{\pm,\star}_\nu)'(z)| \leq 1$, and so $|(\Phi^{\pm,\star}_\nu)(z)| \leq |z|$; moreover, $(\Phi^{\pm,\star}_\nu)'(z)$ does not change sign for $z$ purely imaginary, as $\tanh w$ is real, and the term $\mp\frac{1}{2}$ always dominates. By \eqref{eq:comb}, $(\Phi^{\pm,\circ}_\nu + \Phi^{\pm,\star}_\nu)(1) = 0$ and $(\Phi^{\pm,\circ}_\nu + \Phi^{\pm,\star}_\nu)'(z) = -\frac{d}{dw}\!\left(\frac{w}{2}\coth\frac{w}{2}\right) \mp \frac{1}{2}$ at $w = -2\pi i(z-1) + \nu$. Hence, again by Lemma~4.2, for $0 \leq \Re z \leq \frac{1}{4}$, $|(\Phi^{\sigma,\circ}_\nu + \Phi^{\sigma,\star}_\nu)(1 - z)| \leq |z|$.
\end{proof}

\begin{lemma}
For $z \in \mathbb{C}$, $\lambda \in \mathbb{R} \setminus \{0\}$, define
\[
\Phi^\pm_\lambda(z) = \Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z) + \operatorname{sgn}(\lambda)\operatorname{sgn}(\Re z)\,\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z),
\]
where $\Phi^{\pm,\circ}_{|\lambda|}$, $\Phi^{\pm,\star}_{|\lambda|}$ are as in \eqref{eq:defPhi}, and $\operatorname{sgn}(0) = 0$. Let $T > 0$, and let $z(s) = \frac{s-1}{iT}$.

Then, for $s \in \mathbb{C}$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = \overline{\Phi^\pm_\lambda(z(\bar{s}))}. \label{eq:conjsym}
\end{equation}
Let $\sigma \in \mathbb{R} \setminus \{1\}$. Let $\lambda = \frac{2\pi}{T}(\sigma - 1)$ and write $\theta(s) = 1 - \frac{s - \sigma}{iT}$. If $\Im s > 0$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = i\operatorname{sgn}(\lambda)\left(-\frac{\theta(s)}{2}\cot(\pi\theta(s)) + \frac{\theta(1+iT)}{2}\cot(\pi\theta(1+iT)) \pm \frac{1 - z(s)}{2}\right). \label{eq:Phieval}
\end{equation}
\end{lemma}

\begin{proof}
When we evaluate $\Phi^\pm_\lambda$ at $z(s)$, we evaluate $\Phi^{\pm,\circ}_{|\lambda|}$ and $\Phi^{\pm,\star}_{|\lambda|}$ at $\operatorname{sgn}(\lambda)z(s)$, and so the variable $w$ in \eqref{eq:defPhi} is given by
\begin{equation}
w = -2\pi i\operatorname{sgn}(\lambda)\frac{s-1}{iT} + |\lambda| = \operatorname{sgn}(\lambda)\!\left(-\frac{2\pi}{T}(s-1) + \lambda\right) = -\operatorname{sgn}(\lambda)\frac{2\pi}{T}(s - \sigma). \label{eq:wform}
\end{equation}
In particular, when we conjugate $s$, we conjugate $w$. We thus see from \eqref{eq:defPhi} that
\[
\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) = \overline{\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(\bar{s}))}, \quad \Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) = -\overline{\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(\bar{s}))},
\]
and thus, since $\operatorname{sgn}(\Re z(s)) = -\operatorname{sgn}(\Re z(\bar{s}))$, \eqref{eq:conjsym} holds.

If $\Im s > 0$,
\begin{equation}
\Phi^\pm_\lambda(z(s)) = \Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) + \operatorname{sgn}(\lambda)\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) \label{eq:Phipos}
\end{equation}
because $\Im s > 0$ implies $\Re z(s) > 0$. Since $\coth$ is an odd function, \eqref{eq:defPhi} and \eqref{eq:wform} give us
\begin{align*}
\Phi^{\pm,\circ}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) &= \frac{1}{2}\!\left(-\operatorname{sgn}(\lambda)\coth\frac{\pi(s-\sigma)}{T} \pm 1\right), \\
\Phi^{\pm,\star}_{|\lambda|}(\operatorname{sgn}(\lambda)z(s)) &= \frac{i}{2\pi}\!\left(\frac{\lambda}{2}\coth\frac{\lambda}{2} - \frac{\pi(s-\sigma)}{T}\coth\frac{\pi(s-\sigma)}{T} \pm \operatorname{sgn}(\lambda)\pi i z(s)\right).
\end{align*}
Thus, for $\Im s > 0$, \eqref{eq:Phipos} gives us
\[
\Phi^\pm_\lambda(z(s)) = -\operatorname{sgn}(\lambda)\frac{i(s-\sigma)}{2T} + \frac{1}{2}\!\left(\coth\frac{\pi(s-\sigma)}{T} - \frac{i\lambda}{4\pi}\coth\frac{\lambda}{2}\right) \pm \frac{1 - z(s)}{2}.
\]
So, by $\coth u = -i\cot(u/i)$, $\coth(-u) = -\coth u$, $\cot(\pi - u) = -\cot u$ and $\theta(s) = 1 - \frac{s - \sigma}{iT}$,
\[
\Phi^\pm_\lambda(z(s)) = i\operatorname{sgn}(\lambda)\!\left(-\frac{\theta(s)}{2}\cot(\pi\theta(s)) - \frac{i\lambda}{4\pi}\cot\frac{\lambda}{2i}\right) \pm \frac{1 - z(s)}{2}.
\]
Since $\theta(1 + iT) = \frac{\sigma - 1}{iT} = \frac{\lambda}{2\pi i}$, we have $\cot\frac{\lambda}{2i} = \cot(\pi\theta(1 + iT))$.
\end{proof}
-/





blueprint_comment /--
\subsection{Contour shifting}\label{ch2-contour-sec}

TODO: incorporate material from \cite[Section 5]{ch2}.
-/

blueprint_comment /--
\subsection{The main theorem}\label{ch2-main-thm-sec}

TODO: incorporate material from \cite[Section 6]{ch2}.
-/

blueprint_comment /--
\subsection{Applications to psi}\label{ch2-psi-sec}

TODO: incorporate material from \cite[Section 7]{ch2} onwards.
-/



@[blueprint
  "CH2-cor-1-2-a"
  (title := "Corollary 1.2, part a")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$|\psi(x) - x \cdot \frac{\pi}{T} \coth(\frac{\pi}{T})| \leq \pi T^{-1} \cdot x + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \sqrt{x},$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_a {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    |ψ x - x * π * T⁻¹ * (coth (π * T⁻¹)).re| ≤
      π * T⁻¹ * x + ((1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π))) * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-2-b"
  (title := "Corollary 1.2, part b")
  (statement := /--
  Assume the Riemann hypothesis holds up to height $T \geq 10^7$. For $x > \max(T,10^9)$,
$$\sum_{n \leq x} \frac{\Lambda(n)}{n} \leq \pi \sqrt{T}^{-1} + \frac{1}{2\pi} \log^2(T/(2\pi)) - \frac{1}{6\pi} \log(T/(2\pi)) \frac{1}{x},$$
where $\gamma = 0.577215...$ is Euler’s constant.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_2_b {T x : ℝ} (hT : 1e7 ≤ T) (RH : riemannZeta.RH_up_to T) (hx : max T 1e9 < x) :
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n ≤
      π * Real.sqrt T⁻¹ + (1 / (2 * π)) * log (T / (2 * π)) ^ 2 - (1 / (6 * π)) * log (T / (2 * π)) / x := by sorry

@[blueprint
  "CH2-cor-1-3-a"
  (title := "Corollary 1.3, part a")
  (statement := /--
For $x \geq 1$,
$$|\psi(x) - x| \leq \pi \cdot 3 \cdot 10^{-12} \cdot x + 113.67 \sqrt{x},$$
where $\psi(x)$ is the Chebyshev function.
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_a (x : ℝ) (hx : 1 ≤ x) :
    |ψ x - x| ≤ π * 3 * 10 ^ (-12 : ℝ) * x + 113.67 * Real.sqrt x := by sorry

@[blueprint
  "CH2-cor-1-3-b"
  (title := "Corollary 1.3, part b")
  (statement := /--
For $x \geq 1$,
$$ \sum_{n \leq x} \frac{\Lambda(n)}{n} = \log x - \gamma + O^*(\pi \cdot \sqrt{3} \cdot 10^{-12} + 113.67 / x).$$
  -/)
  (proof := /-- TBD. -/)
  (latexEnv := "corollary")]
theorem cor_1_3_b (x : ℝ) (hx : 1 ≤ x) : ∃ E,
    ∑ n ∈ Finset.Iic (⌊x⌋₊), Λ n / n =
      log x - eulerMascheroniConstant + E ∧ |E| ≤ π * Real.sqrt 3 * 10 ^ (-12 : ℝ) + 113.67 / x := by sorry

end CH2
