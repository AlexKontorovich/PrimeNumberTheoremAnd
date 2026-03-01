import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.Data.PNat.Interval
import Mathlib.Data.Real.CompleteField
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.StarOrdered
import Mathlib.MeasureTheory.Integral.Gamma
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

open Real  MeasureTheory FourierTransform Chebyshev
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
    (hφ_supp : ∀ x, x ∉ Set.Icc (-1) 1 → φ x = 0)
    (hφ_Fourier : ∃ C : ℝ, ∀ y : ℝ, y ≠ 0 → ‖𝓕 φ y‖ ≤ C / |y| ^ β)
    (x : ℝ) (hx : 0 < x) :
    (1 / (2 * π)) * ∑' (n : ℕ+), a n * (x / n) * 𝓕 φ ((T / (2 * π)) * log (n / x)) =
      (1 / (2 * π * T)) *
        ∫ t in Set.Icc (-T) T, φ (t/T) * G (1 + t * I) * x ^ (1 + t * I) +
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
  (title := "Definition of Phi-circ")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z) := \frac{1}{2} (\coth\frac{w}{2} \pm 1)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_circ (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (1 / 2) * (coth (w / 2) + ε)

@[blueprint
  "Phi-circ-mero"
  (title := "Phi-circ meromorphic")
  (statement := /--
  $$\Phi^{\pm,\circ}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.meromorphic (ν ε : ℝ) (hν : ν > 0) : Meromorphic (Phi_circ ν ε) := by sorry

@[blueprint
  "Phi-circ-poles"
  (title := "Phi-circ poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.poles (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z < 0 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-circ-poles-simple"
  (title := "Phi-circ poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\circ}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_circ ν ε) z = -1 ↔ ∃ n : ℤ, z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-circ-residues"
  (title := "Phi-circ residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\circ}_\nu(z)$$ at $n - i \nu/2\pi$ is $i/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\circ}_\nu$ and the properties of the $\coth$ function. -/)]
theorem Phi_circ.residue (ν ε : ℝ) (hν : ν > 0) (n : ℤ) :
    (nhds (n - I * ν / (2 * π))).Tendsto (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_circ ν ε z) (nhds (I / (2 * π))) := by sorry

@[blueprint
  "B-def"
  (title := "Definition of B")
  (statement := /--
  $B^\pm(s) = s/2 (\coth(s/2) \pm 1)$ with the convention $B^\pm(0) = 1$.
  -/)]
noncomputable def B (ε : ℝ) (s : ℂ) : ℂ := if s = 0 then 1 else s * (coth (s / 2) + ε) / 2

@[blueprint
  "B-cts"
  (title := "Continuity of $B$ at 0")
  (statement := /--
  $B^\pm$ is continuous at $0$.
  -/)
  (proof := /-- L'H\^opital's rule can be applied to show the continuity at $0$. -/)]
theorem B.continuous_zero (ε : ℝ) : ContinuousAt (B ε) 0 := by
  sorry

@[blueprint
  "Phi-star-def"
  (title := "Definition of Phi-star")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z) := (B^\pm(w) - B^\pm(v)) / (2\pi i)$$
  where $$w = -2\pi i z + \nu.$$
  -/)]
noncomputable def Phi_star (ν ε : ℝ) (z : ℂ) : ℂ :=
  let w := -2 * π * I * z + (ν : ℂ)
  (B ε w - B ε ν) / (2 * π * I)

@[blueprint
  "Phi-star-zero"
  (title := "Phi-star at zero")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(0) = 0.$$
  -/)
  (proof := /-- This follows from the definition of $B^\pm$ and the fact that $B^\pm(0) = 1$. -/)]
theorem Phi_star_zero (ν ε : ℝ) : Phi_star ν ε 0 = 0 := by sorry

@[blueprint
  "Phi-star-mero"
  (title := "Phi-star meromorphic")
  (statement := /--
  $$\Phi^{\pm,\ast}_\nu(z)$$ is meromorphic.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)]
theorem Phi_star.meromorphic (ν ε : ℝ) (hν : ν > 0) : Meromorphic (Phi_star ν ε) := by sorry

@[blueprint
  "Phi-star-poles"
  (title := "Phi-star poles")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are of the form $n - i \nu/2\pi$ for $n \in \mathbb{Z} \backslash \{0\}$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)]
theorem Phi_star.poles (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z < 0 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-star-poles-simple"
  (title := "Phi-star poles simple")
  (statement := /--
  The poles of $$\Phi^{\pm,\ast}_\nu(z)$$ are all simple.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)]
theorem Phi_star.poles_simple (ν ε : ℝ) (hν : ν > 0) (z : ℂ) :
    meromorphicOrderAt (Phi_star ν ε) z = -1 ↔ ∃ n : ℤ, n ≠ 0 ∧ z = n - I * ν / (2 * π) := by sorry

@[blueprint
  "Phi-star-residues"
  (title := "Phi-star residues")
  (statement := /--
  The residue of $$\Phi^{\pm,\ast}_\nu(z)$$ at $n - i \nu/2\pi$ is $-in/2\pi$.
  -/)
  (proof := /-- This follows from the definition of $\Phi^{\pm,\ast}_\nu$ and the properties of the $B^\pm$ function. -/)]
theorem Phi_star.residue (ν ε : ℝ) (hν : ν > 0) (n : ℤ) (hn : n ≠ 0) :
    (nhds (n - I * ν / (2 * π))).Tendsto
      (fun z ↦ (z - (n - I * ν / (2 * π))) * Phi_star ν ε z) (nhds (-I * n / (2 * π))) := by sorry

@[blueprint
  "Phi-cancel"
  (title := "Phi pole cancellation")
  (statement := /--
  $\Phi^{\sigma, \circ}_\nu(z) \pm \Phi^{\sigma, \ast}_\nu(z)$ is regular at $\pm 1 - i ν / 2 \pi$.
  -/)
  (proof := /-- The residues cancel out. -/)]
theorem Phi_cancel (ν ε σ : ℝ) (hν : ν > 0) (hε : |ε| = 1) :
    meromorphicOrderAt (fun z ↦ Phi_circ ν ε z + σ * Phi_star ν ε z) ≥ 0 := by sorry


@[blueprint
  "phi-pm-def"
  (title := "Definition of phi-pm")
  (statement := /--
  $$\varphi^{\pm}_\nu(t) := 1_{[-1,1]}(t) ( \Phi^{\pm,\circ}_\nu(t) + \mathrm{sgn}(t) \Phi^{\pm,\ast}_\nu(t) ).$$
  -/)]
noncomputable def ϕ_pm (ν ε : ℝ) (t : ℝ) : ℂ :=
  if -1 ≤ t ∧ t ≤ 1 then
    Phi_circ ν ε (t : ℂ) + t.sign * Phi_star ν ε (t : ℂ)
  else 0

@[blueprint
  "phi-c2-left"
  (title := "phi is C2 on [-1,0]")
  (statement := /--
  $\varphi$ is $C^2$ on $[-1,0]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\R$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = ∌u$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_left (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc (-1) 0) := by sorry

@[blueprint
  "phi-c2-right"
  (title := "phi is C2 on [0,1]")
  (statement := /--
  $\varphi$ is $C^2$ on $[0,1]$.
  -/)
  (proof := /-- Since $\Phi^{\pm, \circ}_\nu(z)$ and $\Phi^{\pm, \circ}_\nu(z)$ have no poles on $\R$, they have no poles on some open neighborhood of $[-1,1]$. Hence they are $C^2$ on this interval.  Since $w(0) = \nu$, we see that $\Phi^{\pm, \ast}_\nu(0)=0$, giving the claim. -/)
  (latexEnv := "lemma")]
theorem ϕ_c2_right (ν ε : ℝ) (hlam : ν ≠ 0) : ContDiffOn ℝ 2 (ϕ_pm ν ε) (Set.Icc 0 1) := by sorry

@[blueprint
  "phi-cts"
  (title := "phi is continuous")
  (statement := /--
  $\varphi$ is continuous on $[0,1]$.
  -/)
  (proof := /-- By the preceding lemmas it suffices to verify continuity at $0, -1, 1$.  Continuity at $0$ is clear.  For $t = -1, 1$, by $\coth \frac{w(t)}{2} = \coth \frac{\nu}{2}$, we see that $B^{\pm}(w(t)) = \left(\frac{\nu}{2} - \pi i t\right)\left(\coth \frac{\nu}{2} \pm 1\right)$, and so
\[
\Phi^{\pm,\star}_{\nu}(t) = -t \cdot \frac{1}{2}\left(\coth \frac{\nu}{2} \pm 1\right) = -t\, \Phi^{\pm,\circ}_{\nu}(t);
\]
hence, by Definition \ref{phi-pm-def}, $\varphi^{\pm}_{\nu}(t) = 0$. Thus, $\varphi^{\pm}_{\nu}$ is continuous at $-1$ and at $1$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_continuous (ν ε : ℝ) (hlam : ν ≠ 0) : Continuous (ϕ_pm ν ε) := by
  sorry

@[blueprint
  "phi-circ-bound-right"
  (title := "bound on phi-circ-right")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- The function $\coth w = 1 + \frac{2}{e^{2w}-1}$ is bounded away from the imaginary line $\Re w = 0$, that is, it is bounded on $\Re w \geq \kappa$ and $\Re w \leq -\kappa$ for any $\kappa > 0$. The map $w(z) = \nu - 2\pi i z$ sends the line $\Im z = -\frac{\nu}{2\pi}$ to the imaginary line, and the region $\Im z \geq c$ is sent to $\Re w \geq 2\pi c + \nu$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_right (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_circ ν ε z‖ ≤ C := by sorry

@[blueprint
  "phi-circ-bound-left"
  (title := "bound on phi-circ-left")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\circ}_{\nu}(z)| \leq C$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_circ_bound_left (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_circ ν ε z‖ ≤ C := by sorry

@[blueprint
  "phi-star-bound-right"
  (title := "bound on phi-star-right")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c > - \nu_0/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \geq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- The bound on $\Phi^{\pm,\star}_{\nu}$ follows from the bound on $\Phi^{\pm,\circ}_{\nu}$ by $\Phi^{\pm,\star}(z) = \frac{1}{2\pi i}\bigl(w\,\Phi^{\pm,\circ}(w) - \nu\,\Phi^{\pm,\circ}(\nu)\bigr)$.
 -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_right (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c > -ν₀ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≥ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by sorry

@[blueprint
  "phi-star-bound-left"
  (title := "bound on phi-star-left")
  (statement := /--
  Let $0 < \nu_0 \leq \nu_1$ and $c < - \nu_1/2\pi$, then there exists $C$ such that for all $\nu \in [\nu_0, \nu_1]$, $\Im z \leq c$ one has $|\Phi^{\pm,\star}_{\nu}(z)| \leq C (|z|+1)$.
  -/)
  (proof := /-- Similar to previous lemma. -/)
  (latexEnv := "lemma")]
theorem ϕ_star_bound_left (ν₀ ν₁ ε c : ℝ) (hν₀ : 0 < ν₀) (hν₁ : ν₀ ≤ ν₁) (hc : c < -ν₁ / (2 * π)) :
    ∃ C : ℝ, ∀ ν ∈ Set.Icc ν₀ ν₁, ∀ z : ℂ, z.im ≤ c → ‖Phi_star ν ε z‖ ≤ C * (‖z‖ + 1) := by sorry

/- \begin{lemma}
For real $t$, $B^+(t)$ is increasing and $B^-(t)$ is decreasing.
\end{lemma}

\begin{proof}
For all $t \neq 0$, by the identities $2\cosh\frac{t}{2}\sinh\frac{t}{2} = \sinh t$ and $2\sinh^2\frac{t}{2} = \cosh t - 1$,
\[
\frac{dB^{\pm}(t)}{dt} = \frac{\cosh\frac{t}{2}\sinh\frac{t}{2} - \frac{t}{2} \pm \sinh^2\frac{t}{2}}{2\sinh^2\frac{t}{2}} = \frac{\pm(e^{\pm t} - (1 \pm t))}{4\sinh^2\frac{t}{2}}.
\]
Since $e^u$ is convex, $e^u \geq 1 + u$ for all $u \in \mathbb{R}$. We apply this inequality with $u = t$ and $u = -t$ and obtain the conclusion for $t \neq 0$. Since $B^{\pm}(t)$ is continuous at $t = 0$, we are done.
\end{proof} -/









blueprint_comment /--
TODO: Lemmas 4.2, 4.3, 4.4
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
